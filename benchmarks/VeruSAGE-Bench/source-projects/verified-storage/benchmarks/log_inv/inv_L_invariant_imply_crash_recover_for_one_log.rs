use deps_hack::{PmSized, pmsized_primitive};

verus! {
    pub fn main()
    {
    }

    /***inv_v***/
    pub open spec fn metadata_consistent_with_info(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
    ) -> bool
    {
        let mem = pm_region_view.committed();
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        // No outstanding writes to global metadata, region metadata, or the log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB as int)
        // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(get_log_metadata_pos(cdb) as int,
                                                        get_log_crc_end(cdb) as int)

        // All the CRCs match
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()

        // Various fields are valid and match the parameters to this function
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    }

    pub open spec fn info_consistent_with_log_area(
        log_area_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        // `info` satisfies certain invariant properties
        &&& info.log_area_len >= MIN_LOG_AREA_SIZE
        &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
        &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
        &&& info.head + info.log_plus_pending_length <= u128::MAX

        // `info` and `state` are consistent with each other
        &&& state.log.len() == info.log_length
        &&& state.pending.len() == info.log_plus_pending_length - info.log_length
        &&& state.head == info.head
        &&& state.capacity == info.log_area_len

        // The log area is consistent with `info` and `state`
        &&& forall |pos_relative_to_head: int| {
                let log_area_offset =
                    #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                   info.head_log_area_offset as int,
                                                                   info.log_area_len as int);
                let pmb = log_area_view.state[log_area_offset];
                &&& 0 <= pos_relative_to_head < info.log_length ==> {
                      &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
                      &&& pmb.outstanding_write.is_none()
                   }
                &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                       pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
                &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len ==>
                       pmb.outstanding_write.is_none()
            }
    }

    pub open spec fn info_consistent_with_log_area_in_region(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
        &&& info_consistent_with_log_area(
               get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat),
               info,
               state
           )
    }

    proof fn lemma_invariants_imply_crash_recover_for_one_log(
        pm_region_view: PersistentMemoryRegionView,
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
        ensures
            recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())
    {
        reveal(spec_padding_needed);

        // For the metadata, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        //     state `mem` must match the committed state
        //     `pm_region_view.committed()`, and
        // (2) wherever the crashed-into state matches the committed
        //     state on a per-byte basis, any `extract_bytes` results
        //     will also match.
        //
        // Therefore, since the metadata in
        // `pm_region_view.committed()` matches `state` (per the
        // invariants), the metadata in `mem` must also match `state`.

        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
        lemma_establish_subrange_equivalence(mem, pm_region_view.committed());

        // The tricky part is showing that the result of `extract_log` will produce the desired result.
        // Use `=~=` to ask Z3 to prove this equivalence by proving it holds on each byte.

        let log_view = get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat);
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(log_view);
        assert(recover_log_from_log_area_given_metadata(log_view.committed(), info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
        assert(recover_log(mem, info.log_area_len as int, info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
    }




    /***log/layout*/
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

    impl PmCopy for GlobalMetadata {}

    #[repr(C)]
    #[derive(PmSized, Copy, Clone, Default)]
    pub struct RegionMetadata {
        pub region_size: u64,
        pub log_area_len: u64,
        pub log_id: u128,
    }

    impl PmCopy for RegionMetadata {}

    #[repr(C)]
    #[derive(PmSized, Copy, Clone, Default)]
    pub struct LogMetadata {
        pub log_length: u64,
        pub _padding: u64,
        pub head: u128,
    }

    impl PmCopy for LogMetadata {}

    pub open spec fn extract_global_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as nat, GlobalMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_global_metadata(mem: Seq<u8>) -> GlobalMetadata
    {
        let bytes = extract_global_metadata(mem);
        GlobalMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_global_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_global_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_global_crc(mem);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn extract_region_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as nat, RegionMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_region_metadata(mem: Seq<u8>) -> RegionMetadata
    {
        let bytes = extract_region_metadata(mem);
        RegionMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_region_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_region_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_region_crc(mem);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn get_log_metadata_pos(cdb: bool) -> u64
    {
        if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE } else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
    }

    pub open spec fn get_log_crc_end(cdb: bool) -> u64
    {
        (get_log_metadata_pos(cdb) + LogMetadata::spec_size_of() + u64::spec_size_of()) as u64
    }

    pub open spec fn extract_log_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = get_log_metadata_pos(cdb);
        extract_bytes(mem, pos as nat, LogMetadata::spec_size_of() as nat)
    }

    pub open spec fn deserialize_log_metadata(mem: Seq<u8>, cdb: bool) -> LogMetadata
    {
        let bytes = extract_log_metadata(mem, cdb);
        LogMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn extract_log_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = if cdb { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                  else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
        extract_bytes(mem, pos as nat, u64::spec_size_of() as nat)
    }

    pub open spec fn deserialize_log_crc(mem: Seq<u8>, cdb: bool) -> u64
    {
        let bytes = extract_log_crc(mem, cdb);
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn relative_log_pos_to_log_area_offset(
        pos_relative_to_head: int,
        head_log_area_offset: int,
        log_area_len: int
    ) -> int
    {
        let log_area_offset = head_log_area_offset + pos_relative_to_head;
        if log_area_offset >= log_area_len {
            log_area_offset - log_area_len
        }
        else {
            log_area_offset
        }
    }

    pub open spec fn extract_log_from_log_area(log_area: Seq<u8>, head: int, log_length: int) -> Seq<u8>
    {
        let head_log_area_offset = head % (log_area.len() as int);
        Seq::<u8>::new(log_length as nat, |pos_relative_to_head: int|
                       log_area[relative_log_pos_to_log_area_offset(pos_relative_to_head, head_log_area_offset,
                                                                    log_area.len() as int)])
    }

    pub open spec fn recover_log_from_log_area_given_metadata(
        log_area: Seq<u8>,
        head: int,
        log_length: int,
    ) -> Option<AbstractLogState>
    {
        if log_length > log_area.len() || head + log_length > u128::MAX
        {
            None
        }
        else {
            Some(AbstractLogState {
                head,
                log: extract_log_from_log_area(log_area, head, log_length),
                pending: Seq::<u8>::empty(),
                capacity: log_area.len() as int
            })
        }
    }

    pub open spec fn recover_log(
        mem: Seq<u8>,
        log_area_len: int,
        head: int,
        log_length: int,
    ) -> Option<AbstractLogState>
    {
        recover_log_from_log_area_given_metadata(
            extract_bytes(mem, ABSOLUTE_POS_OF_LOG_AREA as nat, log_area_len as nat), head, log_length
        )
    }

    pub open spec fn recover_given_cdb(
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool
    ) -> Option<AbstractLogState>
    {
        if mem.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            // To be valid, the memory's length has to be big enough to store at least
            // `MIN_LOG_AREA_SIZE` in the log area.
            None
        }
        else {
            let global_metadata = deserialize_global_metadata(mem);
            let global_crc = deserialize_global_crc(mem);
            if global_crc != global_metadata.spec_crc() {
                // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
                // encoded as bytes.
                None
            }
            else {
                if global_metadata.program_guid != LOG_PROGRAM_GUID {
                    // To be valid, the global metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if global_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if global_metadata.length_of_region_metadata != RegionMetadata::spec_size_of() {
                        // To be valid, the global metadata's encoding of the region metadata's
                        // length has to be what we expect. (This version of the code doesn't
                        // support any other length of region metadata.)
                        None
                    }
                    else {
                        let region_metadata = deserialize_region_metadata(mem);
                        let region_crc = deserialize_region_crc(mem);
                        if region_crc != region_metadata.spec_crc() {
                            // To be valid, the region metadata CRC has to be a valid CRC of the region
                            // metadata encoded as bytes.
                            None
                        }
                        else {
                            // To be valid, the region metadata's region size has to match the size of the
                            // region given to us. Also, its metadata has to match what we expect
                            // from the list of regions given to us. Finally, there has to be
                            // sufficient room for the log area.
                            if {
                                ||| region_metadata.region_size != mem.len()
                                ||| region_metadata.log_id != log_id
                                ||| region_metadata.log_area_len < MIN_LOG_AREA_SIZE
                                ||| mem.len() < ABSOLUTE_POS_OF_LOG_AREA + region_metadata.log_area_len
                            } {
                                None
                            }
                            else {
                                let log_metadata = deserialize_log_metadata(mem, cdb);
                                let log_crc = deserialize_log_crc(mem, cdb);
                                if log_crc != log_metadata.spec_crc() {
                                    // To be valid, the log metadata CRC has to be a valid CRC of the
                                    // log metadata encoded as bytes. (This only applies to the
                                    // "active" log metadata, i.e., the log metadata
                                    // corresponding to the current CDB.)
                                    None
                                }
                                else {
                                    recover_log(mem, region_metadata.log_area_len as int, log_metadata.head as int,
                                                log_metadata.log_length as int)
                                }
                            }
                        }
                    }
                }
                else {
                    // This version of the code doesn't know how to parse metadata for any other
                    // versions of this code besides 1. If we reach this point, we're presumably
                    // reading metadata written by a future version of this code, which we can't
                    // interpret.
                    None
                }
            }
        }
    }

	#[verifier::external_body]
    pub proof fn lemma_establish_subrange_equivalence(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    )
        ensures
            forall |i: int, j: int| mem1.subrange(i, j) =~= mem2.subrange(i, j) ==>
                #[trigger] mem1.subrange(i, j) == #[trigger] mem2.subrange(i, j)
	{
		unimplemented!()
	}

    /***log\logimpl*/
    pub struct LogInfo {
        pub log_area_len: u64,
        pub head: u128,
        pub head_log_area_offset: u64,
        pub log_length: u64,
        pub log_plus_pending_length: u64,
    }

    /***log\logspec*/
    #[verifier::ext_equal]
    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub pending: Seq<u8>,
        pub capacity: int,
    }

    impl AbstractLogState {

        pub open spec fn drop_pending_appends(self) -> Self
        {
            Self { pending: Seq::<u8>::empty(), ..self }
        }
    }


    /*pmem\pmcopy*/
    pub broadcast group pmcopy_axioms {
        axiom_bytes_len,
        axiom_to_from_bytes
    }

    pub trait PmCopy : PmSized + SpecPmSized + Sized + Copy {}

    pub trait PmCopyHelper : PmCopy {
 
        spec fn spec_to_bytes(self) -> Seq<u8>;

        spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        spec fn spec_crc(self) -> u64;
    }

    impl<T> PmCopyHelper for T where T: PmCopy {
        closed spec fn spec_to_bytes(self) -> Seq<u8>;

        // The definition is closed because no one should need to reason about it,
        // thanks to `axiom_to_from_bytes`.
        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self
        {
            // If the bytes represent some valid `Self`, pick such a `Self`.
            // Otherwise, pick an arbitrary `Self`. (That's how `choose` works.)
            choose |x: T| x.spec_to_bytes() == bytes
        }

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_to_bytes())
        }

//        open spec fn bytes_parseable(bytes: Seq<u8>) -> bool
//        {
//            Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
//        }
    }
    
	#[verifier::external_body]
    pub broadcast proof fn axiom_bytes_len<S: PmCopy>(s: S)
        ensures 
            #[trigger] s.spec_to_bytes().len() == S::spec_size_of()
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub broadcast proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
        ensures 
            s == #[trigger] S::spec_from_bytes(s.spec_to_bytes())
	{
		unimplemented!()
	}

    impl PmCopy for u64 {}

    global size_of usize == 8;

    global size_of isize == 8;

    pub trait SpecPmSized : UnsafeSpecPmSized {

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
        open spec fn spec_size_of() -> nat
        {
            (N * T::spec_size_of()) as nat
        }   

        open spec fn spec_align_of() -> nat
        {
            T::spec_align_of()
        }
    }

    #[verifier::opaque]
    pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat
    {
        let misalignment = offset % align;
        if misalignment > 0 {
            // we can safely cast this to a nat because it will always be the case that
            // misalignment <= align
            (align - misalignment) as nat
        } else {
            0
        }
    }

    // This function calculates the amount of padding needed to align the next field in a struct.
    // It's const, so we can use it const contexts to calculate the size of a struct at compile time.
    // This function is also verified.
    pub const fn padding_needed(offset: usize, align: usize) -> (out: usize) 
        requires 
            align > 0,
        ensures 
            out <= align,
            out as nat == spec_padding_needed(offset as nat, align as nat)
    {
        reveal(spec_padding_needed);
        let misalignment = offset % align;
        if misalignment > 0 {
            align - misalignment
        } else {
            0
        }
    }


    /*pmem\pmemspec*/
    pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

    pub open spec fn const_persistence_chunk_size() -> int { 8 }

    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    impl PersistentMemoryByte {

        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }
    }

    pub struct PersistentMemoryRegionView
    {
        pub state: Seq<PersistentMemoryByte>,
    }

    impl PersistentMemoryRegionView
    {
 
        pub open spec fn len(self) -> nat
        {
            self.state.len()
        }

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
        }

        pub open spec fn chunk_corresponds_ignoring_outstanding_writes(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
        }

        pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
        }

        pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool
        {
            &&& bytes.len() == self.len()
            &&& forall |chunk| {
                  ||| self.chunk_corresponds_ignoring_outstanding_writes(chunk, bytes)
                  ||| self.chunk_corresponds_after_flush(chunk, bytes)
              }
        }
    }

    pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8>
    {
        bytes.subrange(pos as int, (pos + len) as int)
    }


    /*pmem\pmemutil*/
	#[verifier::external_body]
    pub proof fn lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(
        pm_region_view: PersistentMemoryRegionView,
    )
        ensures
            forall |s, addr: int| {
                &&& pm_region_view.can_crash_as(s)
                &&& 0 <= addr < s.len()
                &&& pm_region_view.state[addr].outstanding_write.is_none()
            } ==> #[trigger] s[addr] == pm_region_view.committed()[addr]
	{
		unimplemented!()
	}


        /*pmem\subregion*/
pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: nat,
    len: nat,
) -> PersistentMemoryRegionView
    recommends
        0 <= start,
        0 <= len,
        start + len <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(start as int, (start + len) as int) }
}

    /*pmem\traits_t*/
    #[verifier::external_trait_specification]
    pub trait ExPmSized : SpecPmSized {
        type ExternalTraitSpecificationFor: PmSized;

        fn size_of() -> (out: usize)
            ensures 
                out as int == Self::spec_size_of();
        fn align_of() -> (out: usize)
            ensures 
                out as int == Self::spec_align_of();
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
            out as nat == S::spec_size_of()
    {
        S::size_of()
    }

    pub fn align_of<S: PmSized>() -> (out: usize)
        ensures 
            out as nat == S::spec_align_of()
    {
        S::align_of()
    }
}

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
pub unsafe trait PmSized : SpecPmSized {
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

// Arrays are PmSized and PmSafe, but since the implementation is generic
// we provide a manual implementation here rather than using the pmsized_primitive!
// macro. These traits are unsafe and must be implemented outside of verus!.
unsafe impl<T: PmSized, const N: usize> PmSized for [T; N] {
    fn size_of() -> usize 
    {
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
use vstd::prelude::*;


verus! {

    pub open spec fn nat_seq_max(seq: Seq<nat>) -> nat 
        recommends 
            0 < seq.len(),
        decreases seq.len()
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

}
