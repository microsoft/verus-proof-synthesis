use deps_hack::{pmsized_primitive, PmSized};
use vstd::prelude::*;

// The unsafe trait PmSized provides non-const exec methods that return the size and alignment
// of a type as calculated by the PmSize derive macro. This trait is visible to Verus via
// an external trait specification, which axiomatizes that the size and alignment given by these
// methods match that which is given by the spec functions. Due to limitations in Verus and Rust,
// we can't make implementations of this trait or its methods constant. We use the trait
// ConstPmSized below, which is not visible to Verus, to obtain constant size and alignment values,
// which are checked at compile time and should be returned by the methods of this trait.
//
// Ideally, this would be a constant trait defined within Verus, with verified methods. This is
// not currently possible due to limitations in Verus, so we have to use this workaround.
pub unsafe trait PmSized: SpecPmSized {
    fn size_of() -> usize;
    fn align_of() -> usize;
}

// ConstPmSized's associated constants store the size and alignment of an implementing
// type as calculated by the PmSized derive macro. This trait is not visible to Verus,
// since Verus does not currently support associated constants. The size_of and align_of
// methods in PmSized, which ARE visible to Verus but are external-body, return
// these associated constants.
pub unsafe trait ConstPmSized {
    const SIZE: usize;
    const ALIGN: usize;
}

// This unsafe marker trait is a supertrait of SpecPmSized to ensure that
// types cannot safely provide their own implementations of SpecPmSized.
// This is a workaround for the fact that Verus does not support unsafe traits;
// only externally-defined traits can be unsafe.
pub unsafe trait UnsafeSpecPmSized {}

// Arrays are PmSized, but since the implementation is generic
// we provide a manual implementation here rather than using the pmsized_primitive!
// macro. These traits are unsafe and must be implemented outside of verus!.
unsafe impl<T: PmSized, const N: usize> PmSized for [T; N] {
    fn size_of() -> usize {
        N * T::size_of()
    }

    fn align_of() -> usize {
        T::align_of()
    }
}

unsafe impl<T: PmSized, const N: usize> UnsafeSpecPmSized for [T; N] {}

unsafe impl<T: PmSized + ConstPmSized, const N: usize> ConstPmSized for [T; N] {
    const SIZE: usize = N * T::SIZE;
    const ALIGN: usize = T::ALIGN;
}
verus! {

pub fn main() {
}

/*util_v*/

pub open spec fn nat_seq_max(seq: Seq<nat>) -> nat
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0]
    } else if seq.len() == 0 {
        0
    } else {
        let later_max = nat_seq_max(seq.drop_first());
        if seq[0] >= later_max {
            seq[0]
        } else {
            later_max
        }
    }
}

/*pmem\pmcopy_t*/

pub broadcast group pmcopy_axioms {
    axiom_bytes_len,
    axiom_to_from_bytes,
}

pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

// PmCopyHelper is a subtrait of PmCopy that exists to provide a blanket
// implementation of these methods for all PmCopy objects.
pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    spec fn bytes_parseable(bytes: Seq<u8>) -> bool;

    spec fn spec_crc(self) -> u64;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    #[verifier::external_body]
    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        unimplemented!()
    }

    open spec fn spec_crc(self) -> u64 {
        spec_crc_u64(self.spec_to_bytes())
    }

    open spec fn bytes_parseable(bytes: Seq<u8>) -> bool {
        Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
    }
}

#[verifier::external_body]
pub broadcast proof fn axiom_bytes_len<S: PmCopy>(s: S)
    ensures
        #[trigger] s.spec_to_bytes().len() == S::spec_size_of(),
{
    unimplemented!()
}

#[verifier::external_body]
pub broadcast proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
    ensures
        s == #[trigger] S::spec_from_bytes(s.spec_to_bytes()),
{
    unimplemented!()
}

impl PmCopy for u64 {

}

global size_of usize == 8;

global size_of isize == 8;

pub trait SpecPmSized: UnsafeSpecPmSized {
    spec fn spec_size_of() -> nat;

    spec fn spec_align_of() -> nat;
}

pmsized_primitive!(u8);

pmsized_primitive!(u64);

pmsized_primitive!(u128);

pmsized_primitive!(usize);

pmsized_primitive!(isize);

pmsized_primitive!(bool);

impl<T: PmSized, const N: usize> SpecPmSized for [T; N] {
    open spec fn spec_size_of() -> nat {
        (N * T::spec_size_of()) as nat
    }

    open spec fn spec_align_of() -> nat {
        T::spec_align_of()
    }
}

#[verifier::opaque]
pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat {
    let misalignment = offset % align;
    if misalignment > 0 {
        // we can safely cast this to a nat because it will always be the case that
        // misalignment <= align
        (align - misalignment) as nat
    } else {
        0
    }
}

pub const fn padding_needed(offset: usize, align: usize) -> (out: usize)
    requires
        align > 0,
    ensures
        out <= align,
        out as nat == spec_padding_needed(offset as nat, align as nat),
{
    reveal(spec_padding_needed);
    let misalignment = offset % align;
    if misalignment > 0 {
        align - misalignment
    } else {
        0
    }
}

/*pmem\pmemspec_t*/

pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

pub const CDB_FALSE: u64 = 0xa32842d19001605e;
  // CRC(b"0")
pub const CDB_TRUE: u64 = 0xab21aa73069531b7;
  // CRC(b"1")
pub struct PersistentMemoryByte {
    pub state_at_last_flush: u8,
    pub outstanding_write: Option<u8>,
}

impl PersistentMemoryByte {
    pub open spec fn write(self, byte: u8) -> Self {
        Self { state_at_last_flush: self.state_at_last_flush, outstanding_write: Some(byte) }
    }

    pub open spec fn flush_byte(self) -> u8 {
        match self.outstanding_write {
            None => self.state_at_last_flush,
            Some(b) => b,
        }
    }

    pub open spec fn flush(self) -> Self {
        Self { state_at_last_flush: self.flush_byte(), outstanding_write: None }
    }
}

pub struct PersistentMemoryRegionView {
    pub state: Seq<PersistentMemoryByte>,
}

impl PersistentMemoryRegionView {
    pub open spec fn len(self) -> nat {
        self.state.len()
    }

    pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self {
        Self {
            state: self.state.map(
                |pos: int, pre_byte: PersistentMemoryByte|
                    if addr <= pos < addr + bytes.len() {
                        pre_byte.write(bytes[pos - addr])
                    } else {
                        pre_byte
                    },
            ),
        }
    }

    pub open spec fn flush(self) -> Self {
        Self { state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()) }
    }

    pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool {
        forall|k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
    }

    pub open spec fn no_outstanding_writes(self) -> bool {
        Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
    }

    pub open spec fn committed(self) -> Seq<u8> {
        self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
    }
}

pub struct PersistentMemoryConstants {
    pub impervious_to_corruption: bool,
}

pub trait PersistentMemoryRegion: Sized {
    spec fn view(&self) -> PersistentMemoryRegionView;

    spec fn inv(&self) -> bool;

    spec fn constants(&self) -> PersistentMemoryConstants;

    #[verifier::external_body]
    fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S) where S: PmCopy + Sized
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(addr as int, to_write.spec_to_bytes()),
            self@.flush().committed().subrange(addr as int, addr + S::spec_size_of())
                == to_write.spec_to_bytes(),
    {
        //unimplemented!()
    }
}

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
}

/*pmem\pmemutil_v*/

#[verifier::external_body]
pub fn calculate_crc<S>(val: &S) -> (out: u64) where S: PmCopy + Sized
    requires
// this is true in the default implementation of `spec_crc`, but
// an impl of `PmCopy` can override the default impl, so
// we have to require it here

        val.spec_crc() == spec_crc_u64(val.spec_to_bytes()),
    ensures
        val.spec_crc() == out,
        spec_crc_u64(val.spec_to_bytes()) == out,
{
    unimplemented!()
}

/*pmem\traits_t*/

#[verifier::external_trait_specification]
pub trait ExPmSized: SpecPmSized {
    type ExternalTraitSpecificationFor: PmSized;

    fn size_of() -> (out: usize)
        ensures
            out as int == Self::spec_size_of(),
    ;

    fn align_of() -> (out: usize)
        ensures
            out as int == Self::spec_align_of(),
    ;
}

#[verifier::external_trait_specification]
pub trait ExUnsafeSpecPmSized {
    type ExternalTraitSpecificationFor: UnsafeSpecPmSized;
}

// The specifications of these methods in ExPmSized are
// not useable in verified code; use these verified wrappers
// instead to obtain the runtime size and alignment of a type.
pub fn size_of<S: PmSized>() -> (out: usize)
    ensures
        out as nat == S::spec_size_of(),
{
    S::size_of()
}

pub fn align_of<S: PmSized>() -> (out: usize)
    ensures
        out as nat == S::spec_align_of(),
{
    S::align_of()
}

/*log\inv_v*/

pub open spec fn metadata_types_set(mem: Seq<u8>) -> bool {
    &&& {
        let metadata_pos = ABSOLUTE_POS_OF_GLOBAL_METADATA as int;
        let crc_pos = ABSOLUTE_POS_OF_GLOBAL_CRC as int;
        let metadata = GlobalMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()),
        );
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& GlobalMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
    &&& {
        let metadata_pos = ABSOLUTE_POS_OF_REGION_METADATA as int;
        let crc_pos = ABSOLUTE_POS_OF_REGION_CRC as int;
        let metadata = RegionMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()),
        );
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& RegionMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
    &&& {
        let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
        let cdb = u64::spec_from_bytes(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()));
        let metadata_pos = if cdb == CDB_TRUE {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
        } else {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
        };
        let metadata = LogMetadata::spec_from_bytes(
            extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()),
        );
        let crc_pos = if cdb == CDB_TRUE {
            ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE
        } else {
            ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE
        };
        let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
        &&& u64::bytes_parseable(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()))
        &&& cdb == CDB_TRUE || cdb == CDB_FALSE
        &&& LogMetadata::bytes_parseable(
            extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()),
        )
        &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }
}

/*log\layout_v*/

pub const ABSOLUTE_POS_OF_GLOBAL_METADATA: u64 = 0;

pub const ABSOLUTE_POS_OF_GLOBAL_CRC: u64 = 32;

pub const ABSOLUTE_POS_OF_REGION_METADATA: u64 = 40;

pub const ABSOLUTE_POS_OF_REGION_CRC: u64 = 72;

pub const ABSOLUTE_POS_OF_LOG_CDB: u64 = 80;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE: u64 = 88;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE: u64 = 128;

pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE: u64 = 120;

pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE: u64 = 160;

pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;

pub const MIN_LOG_AREA_SIZE: u64 = 1;

pub const LOG_PROGRAM_GUID: u128 = 0x8eecd9dea2de4443903e2acf951380bf;

pub const LOG_PROGRAM_VERSION_NUMBER: u64 = 1;

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct GlobalMetadata {
    pub version_number: u64,
    pub length_of_region_metadata: u64,
    pub program_guid: u128,
}

impl PmCopy for GlobalMetadata {

}

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct RegionMetadata {
    pub region_size: u64,
    pub log_area_len: u64,
    pub log_id: u128,
}

impl PmCopy for RegionMetadata {

}

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct LogMetadata {
    pub log_length: u64,
    pub _padding: u64,
    pub head: u128,
}

impl PmCopy for LogMetadata {

}

pub open spec fn extract_global_metadata(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(
        mem,
        ABSOLUTE_POS_OF_GLOBAL_METADATA as nat,
        GlobalMetadata::spec_size_of() as nat,
    )
}

pub open spec fn deserialize_global_metadata(mem: Seq<u8>) -> GlobalMetadata {
    let bytes = extract_global_metadata(mem);
    GlobalMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_global_crc(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_global_crc(mem: Seq<u8>) -> u64 {
    let bytes = extract_global_crc(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn extract_region_metadata(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(
        mem,
        ABSOLUTE_POS_OF_REGION_METADATA as nat,
        RegionMetadata::spec_size_of() as nat,
    )
}

pub open spec fn deserialize_region_metadata(mem: Seq<u8>) -> RegionMetadata {
    let bytes = extract_region_metadata(mem);
    RegionMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_region_crc(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_region_crc(mem: Seq<u8>) -> u64 {
    let bytes = extract_region_crc(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn extract_log_cdb(mem: Seq<u8>) -> Seq<u8> {
    extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_log_cdb(mem: Seq<u8>) -> u64 {
    let bytes = extract_log_cdb(mem);
    u64::spec_from_bytes(bytes)
}

pub open spec fn deserialize_and_check_log_cdb(mem: Seq<u8>) -> Option<bool> {
    let log_cdb = deserialize_log_cdb(mem);
    if log_cdb == CDB_FALSE {
        Some(false)
    } else if log_cdb == CDB_TRUE {
        Some(true)
    } else {
        None
    }
}

pub open spec fn get_log_metadata_pos(cdb: bool) -> u64 {
    if cdb {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE
    }
}

pub open spec fn extract_log_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8> {
    let pos = get_log_metadata_pos(cdb);
    extract_bytes(mem, pos as nat, LogMetadata::spec_size_of() as nat)
}

pub open spec fn deserialize_log_metadata(mem: Seq<u8>, cdb: bool) -> LogMetadata {
    let bytes = extract_log_metadata(mem, cdb);
    LogMetadata::spec_from_bytes(bytes)
}

pub open spec fn extract_log_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8> {
    let pos = if cdb {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE
    } else {
        ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE
    };
    extract_bytes(mem, pos as nat, u64::spec_size_of() as nat)
}

pub open spec fn deserialize_log_crc(mem: Seq<u8>, cdb: bool) -> u64 {
    let bytes = extract_log_crc(mem, cdb);
    u64::spec_from_bytes(bytes)
}

/*log\setup_v*/

spec fn memory_correctly_set_up_on_region(mem: Seq<u8>, region_size: u64, log_id: u128) -> bool {
    let global_crc = deserialize_global_crc(mem);
    let global_metadata = deserialize_global_metadata(mem);
    let region_crc = deserialize_region_crc(mem);
    let region_metadata = deserialize_region_metadata(mem);
    let log_cdb = deserialize_and_check_log_cdb(mem);
    let log_metadata = deserialize_log_metadata(mem, false);
    let log_crc = deserialize_log_crc(mem, false);
    &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
    &&& mem.len() == region_size
    &&& global_crc == global_metadata.spec_crc()
    &&& region_crc == region_metadata.spec_crc()
    &&& log_crc == log_metadata.spec_crc()
    &&& global_metadata.program_guid == LOG_PROGRAM_GUID
    &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
    &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
    &&& region_metadata.region_size == region_size
    &&& region_metadata.log_id == log_id
    &&& region_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
    &&& log_cdb == Some(false)
    &&& log_metadata.head == 0
    &&& log_metadata.log_length == 0
}

fn write_setup_metadata_to_region<PMRegion: PersistentMemoryRegion>(
    pm_region: &mut PMRegion,
    region_size: u64,
    log_id: u128,
)
    requires
        old(pm_region).inv(),
        old(pm_region)@.no_outstanding_writes(),
        old(pm_region)@.len() == region_size,
        region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
    ensures
        pm_region.inv(),
        pm_region.constants() == old(pm_region).constants(),
        memory_correctly_set_up_on_region(
            pm_region@.flush().committed(),  // it'll be correct after the next flush
            region_size,
            log_id,
        ),
        metadata_types_set(pm_region@.flush().committed()),
{
    broadcast use pmcopy_axioms;
    // Initialize global metadata and compute its CRC

    let global_metadata = GlobalMetadata {
        program_guid: LOG_PROGRAM_GUID,
        version_number: LOG_PROGRAM_VERSION_NUMBER,
        length_of_region_metadata: size_of::<RegionMetadata>() as u64,
    };
    let global_crc = calculate_crc(&global_metadata);

    // Initialize region metadata and compute its CRC
    let region_metadata = RegionMetadata {
        region_size,
        log_id,
        log_area_len: region_size - ABSOLUTE_POS_OF_LOG_AREA,
    };
    let region_crc = calculate_crc(&region_metadata);

    // Obtain the initial CDB value
    let cdb = CDB_FALSE;

    // Initialize log metadata and compute its CRC
    let log_metadata = LogMetadata { head: 0, _padding: 0, log_length: 0 };
    let log_crc = calculate_crc(&log_metadata);

    assert(pm_region@.no_outstanding_writes());
    reveal(spec_padding_needed);
    // Write all metadata structures and their CRCs to memory
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_METADATA, &global_metadata);
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_CRC, &global_crc);
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_METADATA, &region_metadata);
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_CRC, &region_crc);
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_CDB, &cdb);
    pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE, &log_metadata);
    pm_region.serialize_and_write(
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + size_of::<LogMetadata>() as u64,
        &log_crc,
    );

    proof {
        // We want to prove that if we parse the result of
        // flushing memory, we get the desired metadata.
        // Prove that if we extract pieces of the flushed memory,
        // we get the little-endian encodings of the desired
        // metadata. By using the `=~=` operator, we get Z3 to
        // prove this by reasoning about per-byte equivalence.
        let mem = pm_region@.flush().committed();
        assert(extract_bytes(
            mem,
            ABSOLUTE_POS_OF_GLOBAL_METADATA as nat,
            GlobalMetadata::spec_size_of(),
        ) =~= global_metadata.spec_to_bytes());
        assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of())
            =~= global_crc.spec_to_bytes());

        assert(extract_bytes(
            mem,
            ABSOLUTE_POS_OF_REGION_METADATA as nat,
            RegionMetadata::spec_size_of(),
        ) =~= region_metadata.spec_to_bytes());
        assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of())
            =~= region_crc.spec_to_bytes());

        assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as nat, u64::spec_size_of())
            =~= CDB_FALSE.spec_to_bytes());
        assert(extract_bytes(
            mem,
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as nat,
            LogMetadata::spec_size_of(),
        ) =~= log_metadata.spec_to_bytes());
        assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as nat, u64::spec_size_of())
            =~= log_crc.spec_to_bytes());

        // Asserting these two postconditions here helps Verus finish out the proof.
        assert(memory_correctly_set_up_on_region(mem, region_size, log_id));
        assert(metadata_types_set(mem));
    }
}

} // verus!
