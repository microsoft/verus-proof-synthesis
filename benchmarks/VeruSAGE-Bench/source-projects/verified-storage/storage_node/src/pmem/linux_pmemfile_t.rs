use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use core::ffi::c_void;
use core::slice;
use std::{cell::RefCell, convert::TryInto, ffi::CString, rc::Rc};

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use deps_hack::{
    pmem::pmem_memcpy_nodrain_helper, pmem_drain, pmem_errormsg, pmem_flush, pmem_map_file,
    pmem_memcpy_nodrain, pmem_unmap, rand::Rng, PMEM_FILE_CREATE, PMEM_FILE_EXCL,
};

pub struct MemoryMappedFile {
    virt_addr: *mut u8,
    size: usize,
    num_bytes_sectioned: usize,
}

impl Drop for MemoryMappedFile
{
    fn drop(&mut self)
    {
        unsafe { pmem_unmap(self.virt_addr as *mut c_void, self.size) };
    }
}

impl MemoryMappedFile
{
    // TODO: detailed information for error returns
    fn from_file<'a>(file_to_map: &str, size: usize, file_open_behavior: FileOpenBehavior,
                     persistent_memory_check: PersistentMemoryCheck) -> Result<Self, PmemError>
    {
        let mut mapped_len = 0;
        let mut is_pm = 0;
        let file = CString::new(file_to_map).map_err(|_| PmemError::InvalidFileName )?;
        let file = file.as_c_str();

        let require_pm = match persistent_memory_check {
            PersistentMemoryCheck::CheckForPersistentMemory => true,
            PersistentMemoryCheck::DontCheckForPersistentMemory => false,
        };
        let create_flags = match file_open_behavior {
            FileOpenBehavior::CreateNew => PMEM_FILE_CREATE | PMEM_FILE_EXCL,
            FileOpenBehavior::OpenExisting => 0,
        };

        let addr = unsafe {
            pmem_map_file(
                file.as_ptr(),
                size,
                create_flags.try_into().unwrap(),
                0666,
                &mut mapped_len,
                &mut is_pm,
            )
        };

        if addr.is_null() {
            eprintln!("{}", unsafe {
                CString::from_raw(pmem_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            Err(PmemError::CannotOpenPmFile)
        } else if is_pm == 0 && require_pm {
            eprintln!("{}", unsafe {
                CString::from_raw(pmem_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            Err(PmemError::NotPm)
        } else if addr as isize >= isize::MAX + mapped_len as isize {
            // By checking that no access to bytes between 0 and the length of the PM region
            // will overflow isize, we can assume later that all accesses are valid and will 
            // not violate the safety conditions of methods like raw ptr offset on the virtual 
            // address.
            Err(PmemError::AccessOutOfRange)
        } else {
            Ok(Self {
                virt_addr: addr as *mut u8,
                size: mapped_len.try_into().unwrap(),
                num_bytes_sectioned: 0,
            })
        }
    }
}

#[verifier::external_body]
pub struct MemoryMappedFileSection {
    mmf: Rc<RefCell<MemoryMappedFile>>,
    virt_addr: *mut u8,
    size: usize,
}

impl MemoryMappedFileSection
{
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

        mmf_borrowed.num_bytes_sectioned += len;
        let new_virt_addr = unsafe { mmf_borrowed.virt_addr.offset(offset_as_isize) };

        std::mem::drop(mmf_borrowed);

        let section = Self {
            mmf,
            virt_addr: new_virt_addr,
            size: len,
        };
        Ok(section)
    }
}

verus! {

#[derive(Clone, Copy)]
pub enum FileOpenBehavior {
    CreateNew,
    OpenExisting,
}

#[derive(Clone, Copy)]
pub enum PersistentMemoryCheck {
    CheckForPersistentMemory,
    DontCheckForPersistentMemory,
}

pub struct FileBackedPersistentMemoryRegion
{
    section: MemoryMappedFileSection,
}

impl FileBackedPersistentMemoryRegion
{
    #[verifier::external_body]
    fn new_internal(path: &str, region_size: u64, open_behavior: FileOpenBehavior,
                    persistent_memory_check: PersistentMemoryCheck)
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
            open_behavior,
            persistent_memory_check,
        )?;
        let mmf = Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let section = MemoryMappedFileSection::new(mmf, region_size as usize)?;
        Ok(Self { section })
    }

    pub fn new(path: &str, region_size: u64, persistent_memory_check: PersistentMemoryCheck)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_size, FileOpenBehavior::CreateNew, persistent_memory_check)
    }

    pub fn restore(path: &str, region_size: u64) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(region) => region.inv() && region@.len() == region_size,
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_size, FileOpenBehavior::OpenExisting,
                           PersistentMemoryCheck::DontCheckForPersistentMemory)
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
        let raw_addr = addr as isize;

        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. The precondition ensures that addr + len are 
        // in bounds, and when we set up the region we ensured that 
        // in-bounds accesses cannot overflow isize.
        let addr_on_pm: *const u8 = unsafe {
            self.section.virt_addr.offset(raw_addr)
        };

        // SAFETY: The precondition establishes that num_bytes bytes
        // from addr_on_pmem are valid bytes on PM. The bytes will not 
        // be modified during this call since the system is single threaded.
        let pm_slice: &[u8] = unsafe {
            std::slice::from_raw_parts(addr_on_pm, len as usize)
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
        // SAFETY: The `offset` method is safe as long as both the start
        // and resulting pointer are in bounds and the computed offset does
        // not overflow `isize`. `addr` and `num_bytes` are unsigned and
        // the precondition requires that `addr + num_bytes` is in bounds.
        // The precondition does not technically prevent overflowing `isize`
        // but the value is large enough (assuming a 64-bit architecture)
        // that we will not violate this restriction in practice.
        // TODO: put it in the precondition anyway
        let addr_on_pm: *mut u8 = unsafe {
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // pmem_memcpy_nodrain() does a memcpy to PM with no cache line flushes or
        // ordering; it makes no guarantees about durability. pmem_flush() does cache
        // line flushes but does not use an ordering primitive, so updates are still
        // not guaranteed to be durable yet.
        // Verus doesn't like calling pmem_memcpy_nodrain directly because it returns
        // a raw pointer, so we define a wrapper around pmem_memcpy_nodrain in deps_hack
        // that does not return anything and call that instead
        unsafe {
            pmem_memcpy_nodrain_helper(
                addr_on_pm as *mut c_void,
                bytes.as_ptr() as *const c_void,
                bytes.len()
            );
        }
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
            self.section.virt_addr.offset(addr.try_into().unwrap())
        };

        // convert the given &S to a pointer, then a slice of bytes
        let s_pointer = to_write as *const S as *const u8;

        // pmem_memcpy_nodrain() does a memcpy to PM with no cache line flushes or
        // ordering; it makes no guarantees about durability. pmem_flush() does cache
        // line flushes but does not use an ordering primitive, so updates are still
        // not guaranteed to be durable yet.
        // Verus doesn't like calling pmem_memcpy_nodrain directly because it returns
        // a raw pointer, so we define a wrapper around pmem_memcpy_nodrain in deps_hack
        // that does not return anything and call that instead
        unsafe {
            pmem_memcpy_nodrain_helper(
                addr_on_pm as *mut c_void,
                s_pointer as *const c_void,
                num_bytes
            );
        }
    }

    #[verifier::external_body]
    fn flush(&mut self)
    {
        // `pmem_drain()` invokes an ordering primitive to drain store buffers and
        // ensure that all cache lines that were flushed since the previous ordering
        // primitive are durable. This guarantees that all updates made with `write`/
        // `serialize_and_write` since the last `flush` call will be durable before
        // any new updates become durable.
        unsafe { pmem_drain(); }
    }
}

pub struct FileBackedPersistentMemoryRegions {
    regions: Vec<FileBackedPersistentMemoryRegion>,
}

impl FileBackedPersistentMemoryRegions {
    // TODO: detailed information for error returns
    #[verifier::external_body]
    #[allow(dead_code)]
    pub fn new_internal(path: &str, region_sizes: &[u64], open_behavior: FileOpenBehavior,
                        persistent_memory_check: PersistentMemoryCheck) -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        let mut total_size: usize = 0;
        for &region_size in region_sizes {
            let region_size = region_size as usize;
            if region_size >= usize::MAX - total_size {
                return Err(PmemError::AccessOutOfRange);
            }
            total_size += region_size;
        }
        let mmf = MemoryMappedFile::from_file(
            path,
            total_size,
            open_behavior,
            persistent_memory_check,
        )?;
        let mmf = Rc::<RefCell<MemoryMappedFile>>::new(RefCell::<MemoryMappedFile>::new(mmf));
        let mut regions = Vec::<FileBackedPersistentMemoryRegion>::new();
        for &region_size in region_sizes {
            let region_size: usize = region_size as usize;
            let section = MemoryMappedFileSection::new(mmf.clone(), region_size)?;
            let region = FileBackedPersistentMemoryRegion::new_from_section(section);
            regions.push(region);
        }
        Ok(Self { regions })
    }
    
    pub fn new(path: &str, region_sizes: &[u64], persistent_memory_check: PersistentMemoryCheck)
               -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_sizes, FileOpenBehavior::CreateNew, persistent_memory_check)
    }
    
    pub fn restore(path: &str, region_sizes: &[u64], persistent_memory_check: PersistentMemoryCheck)
                   -> (result: Result<Self, PmemError>)
        ensures
            match result {
                Ok(regions) => {
                    &&& regions.inv()
                    &&& regions@.no_outstanding_writes()
                    &&& regions@.len() == region_sizes@.len()
                    &&& forall |i| 0 <= i < regions@.len() ==> #[trigger] regions@[i].len() == region_sizes@[i]
                },
                Err(_) => true,
            }
    {
        Self::new_internal(path, region_sizes, FileOpenBehavior::OpenExisting, persistent_memory_check)
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
        unsafe { pmem_drain(); }
    }
}

}
