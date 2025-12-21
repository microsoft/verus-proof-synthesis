//! This file contains the trusted implementation for
//! `FileBackedPersistentMemoryRegions`, a collection of persistent
//! memory regions backed by files. It implements trait
//! `PersistentMemoryRegions`.

use builtin::*;
use builtin_macros::*;
use crate::pmem::pmemspec_t::{
    copy_from_slice, maybe_corrupted, PersistentMemoryByte, PersistentMemoryConstants, PersistentMemoryRegion,
    PersistentMemoryRegionView, PersistentMemoryRegions, PersistentMemoryRegionsView,
    PmemError,
};
use crate::pmem::pmcopy_t::*;
use deps_hack::rand::Rng;
use deps_hack::winapi::ctypes::c_void;
use deps_hack::winapi::shared::winerror::SUCCEEDED;
use deps_hack::winapi::um::errhandlingapi::GetLastError;
use deps_hack::winapi::um::fileapi::{CreateFileA, CREATE_NEW, DeleteFileA, OPEN_EXISTING};
use deps_hack::winapi::um::handleapi::{CloseHandle, INVALID_HANDLE_VALUE};
use deps_hack::winapi::um::memoryapi::{FILE_MAP_ALL_ACCESS, FlushViewOfFile, MapViewOfFile, UnmapViewOfFile};
use deps_hack::winapi::um::winbase::CreateFileMappingA;
use deps_hack::winapi::um::winnt::{
    FILE_ATTRIBUTE_NORMAL, FILE_ATTRIBUTE_TEMPORARY, FILE_SHARE_DELETE, FILE_SHARE_READ,
    FILE_SHARE_WRITE, GENERIC_READ, GENERIC_WRITE, HANDLE, PAGE_READWRITE, ULARGE_INTEGER,
};
use std::cell::RefCell;
use std::convert::*;
use std::ffi::CString;
use std::rc::Rc;
use std::slice;
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::_mm_clflush;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::_mm_sfence;
    
// The `MemoryMappedFile` struct represents a memory-mapped file.

pub struct MemoryMappedFile {
    media_type: MemoryMappedFileMediaType,  // type of media on which the file is stored
    size: usize,                            // number of bytes in the file
    h_file: HANDLE,                         // handle to the file
    h_map_file: HANDLE,                     // handle to the mapping
    h_map_addr: HANDLE,                     // address of the first byte of the mapping
    num_bytes_sectioned: usize,             // how many bytes allocated to `MemoryMappedFileSection`s
}

impl MemoryMappedFile {
    // The function `from_file` memory-maps a file and returns a
    // `MemoryMappedFile` to represent it.

    fn from_file(path: &str, size: usize, media_type: MemoryMappedFileMediaType,
                 open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                 -> Result<Self, PmemError>
    {
        unsafe {
            // Since str in rust is not null terminated, we need to convert it to a null-terminated string.
            let path_cstr = match std::ffi::CString::new(path) {
                Ok(p) => p,
                Err(_) => {
                    eprintln!("Could not convert path {} to string", path);
                    return Err(PmemError::InvalidFileName);
                }
            };

            // Windows can only create files with size < 2^64 so we need to convert `size` to a `u64`.
            let size_as_u64: u64 =
                match size.try_into() {
                    Ok(sz) => sz,
                    Err(_) => {
                        eprintln!("Could not convert size {} into u64", size);
                        return Err(PmemError::CannotOpenPmFile);
                    }
                };

            let create_or_open = match open_behavior {
                FileOpenBehavior::CreateNew => CREATE_NEW,
                FileOpenBehavior::OpenExisting => OPEN_EXISTING,
            };
            let attributes = match close_behavior {
                FileCloseBehavior::TestingSoDeleteOnClose => FILE_ATTRIBUTE_TEMPORARY,
                FileCloseBehavior::Persistent => FILE_ATTRIBUTE_NORMAL,
            };

            // Open or create the file with `CreateFileA`.
            let h_file = CreateFileA(
                path_cstr.as_ptr(),
                GENERIC_READ | GENERIC_WRITE,
                FILE_SHARE_WRITE | FILE_SHARE_READ | FILE_SHARE_DELETE,
                core::ptr::null_mut(),
                create_or_open,
                attributes,
                core::ptr::null_mut()
            );

            if h_file.is_null() || h_file == INVALID_HANDLE_VALUE {
                let error_code = GetLastError();
                match open_behavior {
                    FileOpenBehavior::CreateNew =>
                        eprintln!("Could not create new file {}. err={}", path, error_code),
                    FileOpenBehavior::OpenExisting =>
                        eprintln!("Could not open existing file {}. err={}", path, error_code),
                };
                return Err(PmemError::CannotOpenPmFile);
            }

            let mut li: ULARGE_INTEGER = std::mem::zeroed();
            *li.QuadPart_mut() = size_as_u64;

            // Create a file mapping object backed by the file
            let h_map_file = CreateFileMappingA(
                h_file,
                core::ptr::null_mut(),
                PAGE_READWRITE,
                li.u().HighPart,
                li.u().LowPart,
                core::ptr::null_mut()
            );

            if h_map_file.is_null() {
                eprintln!("Could not create file mapping object for {}.", path);
                return Err(PmemError::CannotOpenPmFile);
            }

            // Map a view of the file mapping into the address space of the process
            let h_map_addr = MapViewOfFile(
                h_map_file,
                FILE_MAP_ALL_ACCESS,
                0,
                0,
                size,
            );

            if h_map_addr.is_null() {
                let err = GetLastError();
                eprintln!("Could not map view of file, got error {}", err);
                return Err(PmemError::CannotOpenPmFile);
            }

            if let FileCloseBehavior::TestingSoDeleteOnClose = close_behavior {
                // After opening the file, mark it for deletion when the file is closed.
                // Obviously, we should only do this during testing!
                DeleteFileA(path_cstr.as_ptr());
            }

            let mmf = MemoryMappedFile {
                media_type,
                size,
                h_file,
                h_map_file,
                h_map_addr,
                num_bytes_sectioned: 0,
            };
            Ok(mmf)
        }
    }
}

impl Drop for MemoryMappedFile {
    fn drop(&mut self)
    {
        unsafe {
            UnmapViewOfFile(self.h_map_addr);
            CloseHandle(self.h_map_file);
            CloseHandle(self.h_file);
        }
    }
}

// The `MemoryMappedFileSection` struct represents a section of a memory-mapped file.
// It contains a reference to the `MemoryMappedFile` it's a section of so that the
// `MemoryMappedFile` isn't dropped until this `MemoryMappedFileSection1 is dropped.

#[verifier::external_body]
pub struct MemoryMappedFileSection {
    mmf: Rc<RefCell<MemoryMappedFile>>,     // the memory-mapped file this is a section of
    media_type: MemoryMappedFileMediaType,  // type of media on which the file is stored
    size: usize,                            // number of bytes in the section
    h_map_addr: HANDLE,                     // address of the first byte of the section
}

impl MemoryMappedFileSection {
    fn new(mmf: Rc<RefCell<MemoryMappedFile>>, len: usize) -> Result<Self, PmemError>
    {
        let mut mmf_borrowed = mmf.borrow_mut();
        let offset = mmf_borrowed.num_bytes_sectioned;
        let offset_as_isize: isize = match offset.try_into() {
            Ok(off) => off,
            Err(_) => {
                eprintln!("Can't express offset {} as isize", offset);
                return Err(PmemError::AccessOutOfRange)
            },
        };

        if offset + len > mmf_borrowed.size {
            eprintln!("Can't allocate {} bytes because only {} remain", len, mmf_borrowed.size - offset);
            return Err(PmemError::AccessOutOfRange);
        }
        
        let h_map_addr = unsafe { (mmf_borrowed.h_map_addr as *mut u8).offset(offset_as_isize) };

        mmf_borrowed.num_bytes_sectioned += len;
        let media_type = mmf_borrowed.media_type.clone();

        std::mem::drop(mmf_borrowed);
        
        let section = Self {
            mmf,
            media_type,
            size: len,
            h_map_addr: h_map_addr as HANDLE,
        };
        Ok(section)
    }

    // The function `flush` flushes updated parts of the
    // memory-mapped file back to the media.

    fn flush(&mut self) {
        unsafe {
            match self.media_type {
                MemoryMappedFileMediaType::BatteryBackedDRAM => {
                    // If using battery-backed DRAM, there's no need
                    // to flush cache lines, since those will be
                    // flushed during the battery-enabled graceful
                    // shutdown after power loss.
                    _mm_sfence();
                },
                _ => {
                    let hr = FlushViewOfFile(
                        self.h_map_addr as *const c_void,
                        self.size
                    );

                    if !SUCCEEDED(hr) {
                        panic!("Failed to flush view of file. err={}", hr);
                    }
                },
            }
        }
    }
}

verus! {

// The `MemoryMappedFileMediaType` enum represents a type of media
// from which a file can be memory-mapped.

#[derive(Clone)]
pub enum MemoryMappedFileMediaType {
    HDD,
    SSD,
    BatteryBackedDRAM,
}

#[derive(Clone, Copy)]
pub enum FileOpenBehavior {
    CreateNew,
    OpenExisting,
}

#[derive(Clone, Copy)]
pub enum FileCloseBehavior {
    TestingSoDeleteOnClose,
    Persistent,
}

// The `FileBackedPersistentMemoryRegion` struct represents a
// persistent-memory region backed by a memory-mapped file.

#[allow(dead_code)]
pub struct FileBackedPersistentMemoryRegion
{
    section: MemoryMappedFileSection,
}

impl FileBackedPersistentMemoryRegion
{
    #[verifier::external_body]
    fn new_internal(path: &str, media_type: MemoryMappedFileMediaType, region_size: u64,
                    open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                    -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        let mmf = MemoryMappedFile::from_file(
            path,
            region_size as usize,
            media_type,
            open_behavior,
            close_behavior
        )?;
        let mmf =
            Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let section = MemoryMappedFileSection::new(mmf, region_size as usize)?;
        Ok(Self { section })
    }

    pub fn new(path: &str, media_type: MemoryMappedFileMediaType, region_size: u64,
               close_behavior: FileCloseBehavior) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, media_type, region_size, FileOpenBehavior::CreateNew, close_behavior)
    }

    pub fn restore(path: &str, media_type: MemoryMappedFileMediaType, region_size: u64)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, media_type, region_size, FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent)
    }

    #[verifier::external_body]
    fn new_from_section(section: MemoryMappedFileSection) -> (result: Self)
    {
        Self{ section }
    }

    #[verifier::external_body]
    fn get_slice_at_offset(&self, addr: u64, len: u64) -> (result: Result<&[u8], PmemError>)
        requires 
            0 <= addr <= addr + len <= self@.len()
        ensures 
            match result {
                Ok(slice) => if self.constants().impervious_to_corruption {
                    slice@ == self@.committed().subrange(addr as int, addr + len)
                } else {
                    let addrs = Seq::new(len as nat, |i: int| addr + i);
                    maybe_corrupted(slice@, self@.committed().subrange(addr as int, addr + len), addrs)
                }
                _ => false
            }
    {
        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. The precondition ensures that addr + len are 
        // in bounds, and when we set up the region we ensured that 
        // in-bounds accesses cannot overflow isize.
        let addr_on_pm: *const u8 = unsafe {
            (self.section.h_map_addr as *const u8).offset(addr.try_into().unwrap())
        };

        // SAFETY: The precondition establishes that num_bytes bytes
        // from addr_on_pmem are valid bytes on PM. The bytes will not 
        // be modified during this call since the system is single threaded.
        let pm_slice: &[u8] = unsafe {
            core::slice::from_raw_parts(addr_on_pm, len as usize)
        };

        Ok(pm_slice)
    }
}

impl PersistentMemoryRegion for FileBackedPersistentMemoryRegion
{
    closed spec fn view(&self) -> PersistentMemoryRegionView;
    closed spec fn inv(&self) -> bool;
    closed spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn get_region_size(&self) -> u64
    {
        self.section.size as u64
    }

    fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy 
    {
        let pm_slice = self.get_slice_at_offset(addr, S::size_of() as u64)?;
        let ghost addrs = Seq::new(S::spec_size_of() as nat, |i: int| addr + i);
        let ghost true_bytes = self@.committed().subrange(addr as int, addr + S::spec_size_of());
        let ghost true_val = S::spec_from_bytes(true_bytes);
        let mut maybe_corrupted_val = MaybeCorruptedBytes::new();

        maybe_corrupted_val.copy_from_slice(pm_slice, Ghost(true_val), Ghost(addrs),
                                            Ghost(self.constants().impervious_to_corruption));
        
        Ok(maybe_corrupted_val)
    }

    #[verifier::external_body]
    fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        let pm_slice = self.get_slice_at_offset(addr, num_bytes)?;

        // Allocate an unaligned buffer to copy the bytes into
        let unaligned_buffer = copy_from_slice(pm_slice);

        Ok(unaligned_buffer)
    }

    #[verifier::external_body]
    fn write(&mut self, addr: u64, bytes: &[u8])
    {
        let addr_on_pm: *mut u8 = unsafe {
            (self.section.h_map_addr as *mut u8).offset(addr.try_into().unwrap())
        };
        let slice: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(addr_on_pm, bytes.len()) };
        slice.copy_from_slice(bytes)
    }

    #[verifier::external_body]
    #[allow(unused_variables)]
    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S)
        where
            S: PmCopy + Sized
    {
        let num_bytes: usize = S::size_of() as usize;

        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *mut u8 = unsafe {
            (self.section.h_map_addr as *mut u8).offset(addr.try_into().unwrap())
        };

        // convert the given &S to a pointer, then a slice of bytes
        let s_pointer = to_write as *const S as *const u8;

        unsafe {
            std::ptr::copy_nonoverlapping(s_pointer, addr_on_pm, num_bytes);
        }
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        self.section.flush();
    }
}

// The `FileBackedPersistentMemoryRegions` struct contains a
// vector of volatile memory regions. It implements the trait
// `PersistentMemoryRegions` so that it can be used by a multilog.

pub struct FileBackedPersistentMemoryRegions
{
    media_type: MemoryMappedFileMediaType,           // common media file type used
    regions: Vec<FileBackedPersistentMemoryRegion>,  // all regions
}

impl FileBackedPersistentMemoryRegions {
    #[verifier::external_body]
    fn new_internal(path: &str, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
                    open_behavior: FileOpenBehavior, close_behavior: FileCloseBehavior)
                    -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        let mut total_size: usize = 0;
        for &region_size in region_sizes {
            let region_size = region_size as usize;
            if region_size >= usize::MAX - total_size {
                eprintln!("Cannot allocate {} bytes because, combined with the {} allocated so far, it would exceed usize::MAX", region_size, total_size);
                return Err(PmemError::AccessOutOfRange);
            }
            total_size += region_size;
        }
        let mmf = MemoryMappedFile::from_file(
            path,
            total_size,
            media_type.clone(),
            open_behavior,
            close_behavior
        )?;
        let mmf =
            Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let mut regions = Vec::<FileBackedPersistentMemoryRegion>::new();
        for &region_size in region_sizes {
            let region_size: usize = region_size as usize;
            let section = MemoryMappedFileSection::new(mmf.clone(), region_size)?;
            let region = FileBackedPersistentMemoryRegion::new_from_section(section);
            regions.push(region);
        }
        Ok(Self { media_type, regions })
    }

    // The static function `new` creates a
    // `FileBackedPersistentMemoryRegions` object by creating a file
    // and dividing it into memory-mapped sections.
    //
    // `path` -- the path to use for the file
    //
    // `media_type` -- the type of media the path refers to
    //
    // `region_sizes` -- a vector of region sizes, where
    // `region_sizes[i]` is the length of file `log<i>`
    //
    // `close_behavior` -- what to do when the file is closed
    pub fn new(path: &str, media_type: MemoryMappedFileMediaType, region_sizes: &[u64],
               close_behavior: FileCloseBehavior)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        Self::new_internal(path, media_type, region_sizes, FileOpenBehavior::CreateNew, close_behavior)
    }

    // The static function `restore` creates a
    // `FileBackedPersistentMemoryRegions` object by opening an
    // existing file and dividing it into memory-mapped sections.
    //
    // `path` -- the path to use for the file
    //
    // `media_type` -- the type of media the path refers to
    //
    // `region_sizes` -- a vector of region sizes, where
    // `region_sizes[i]` is the length of file `log<i>`
    pub fn restore(path: &str, media_type: MemoryMappedFileMediaType, region_sizes: &[u64])
                   -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < region_sizes@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true
            }
    {
        Self::new_internal(
            path, media_type, region_sizes, FileOpenBehavior::OpenExisting, FileCloseBehavior::Persistent
        )
    }
}

impl PersistentMemoryRegions for FileBackedPersistentMemoryRegions {
    closed spec fn view(&self) -> PersistentMemoryRegionsView;
    closed spec fn inv(&self) -> bool;
    closed spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn get_num_regions(&self) -> usize
    {
        self.regions.len()
    }

    #[verifier::external_body]
    fn get_region_size(&self, index: usize) -> u64
    {
        self.regions[index].get_region_size()
    }


    #[verifier::external_body]
    fn read_aligned<S>(&self, index: usize, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy
    {
        self.regions[index].read_aligned::<S>(addr)
    }

    #[verifier::external_body]
    fn read_unaligned(&self, index: usize, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>)
    {
        self.regions[index].read_unaligned(addr, num_bytes)
    }

    #[verifier::external_body]
    fn write(&mut self, index: usize, addr: u64, bytes: &[u8])
    {
        self.regions[index].write(addr, bytes)
    }

    #[verifier::external_body]
    fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S)
        where
            S: PmCopy + Sized
    {
        self.regions[index].serialize_and_write(addr, to_write);
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        match self.media_type {
            MemoryMappedFileMediaType::BatteryBackedDRAM => {
                // If using battery-backed DRAM, a single sfence
                // instruction will fence all of memory, so
                // there's no need to iterate through all the
                // regions. Also, there's no need to flush cache
                // lines, since those will be flushed during the
                // battery-enabled graceful shutdown after power
                // loss.
                unsafe {
                    core::arch::x86_64::_mm_sfence();
                }
            },
            _ => {
                for region in &mut self.regions {
                    region.flush();
                }
            },
        }
    }
}

}
