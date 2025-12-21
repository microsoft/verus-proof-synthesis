use deps_hack::{PmSized, pmsized_primitive};
use vstd::prelude::*;


verus! {

    pub fn main()
    {
    }

    /*log\layout*/

    #[repr(C)]
    #[derive(PmSized, Copy, Clone, Default)]

    pub struct LogMetadata {
        pub log_length: u64,
        pub _padding: u64,
        pub head: u128,
    }

    impl PmCopy for LogMetadata {}


    /*log\logimpl_t*/
    pub struct TrustedPermission {
        ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedPermission {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            (self.is_state_allowable)(state)
        }
    }


    /*log\logimpl_v*/

    pub struct LogInfo {
        pub log_area_len: u64,
        pub head: u128,
        pub head_log_area_offset: u64,
        pub log_length: u64,
        pub log_plus_pending_length: u64,
    }

    pub struct UntrustedLogImpl {
        cdb: bool,
        info: LogInfo,
        state: Ghost<AbstractLogState>,
    }

    impl UntrustedLogImpl
    {
        exec fn update_inactive_log_metadata<PMRegion>(
            &self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            subregion: &WriteRestrictedPersistentMemorySubregion,
            Ghost(log_id): Ghost<u128>,
            Ghost(prev_info): Ghost<LogInfo>,
            Ghost(prev_state): Ghost<AbstractLogState>,
            Tracked(perm): Tracked<&TrustedPermission>,
        )
            where
                PMRegion: PersistentMemoryRegion,
            requires
                subregion.inv(old::<&mut _>(wrpm_region), perm),
                subregion.len() == LogMetadata::spec_size_of() + u64::spec_size_of(),
                subregion.view(old::<&mut _>(wrpm_region)).no_outstanding_writes(),
                forall |addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
            ensures
                subregion.inv(wrpm_region, perm),
                ({
                    let state_after_flush = subregion.view(wrpm_region).flush().committed();
                    let log_metadata_bytes = extract_bytes(state_after_flush, 0, LogMetadata::spec_size_of());
                    let log_crc_bytes = extract_bytes(state_after_flush, LogMetadata::spec_size_of(), u64::spec_size_of());
                    let log_metadata = LogMetadata::spec_from_bytes(log_metadata_bytes);
                    let log_crc = u64::spec_from_bytes(log_crc_bytes);
                    let new_metadata = LogMetadata {
                        head: self.info.head,
                        _padding: 0,
                        log_length: self.info.log_length,
                    };
                    let new_crc = new_metadata.spec_crc();

                    &&& log_crc == log_metadata.spec_crc()
                    &&& log_metadata.head == self.info.head
                    &&& log_metadata.log_length == self.info.log_length

                    &&& log_metadata_bytes == new_metadata.spec_to_bytes()
                    &&& log_crc_bytes == new_crc.spec_to_bytes()
                }),
        {
            broadcast use pmcopy_axioms;

            // Encode the log metadata as bytes, and compute the CRC of those bytes

            let info = &self.info;
            let log_metadata = LogMetadata {
                head: info.head,
                _padding: 0,
                log_length: info.log_length
            };
            let log_crc = calculate_crc(&log_metadata);

            assert(log_metadata.spec_to_bytes().len() == LogMetadata::spec_size_of());
            assert(log_crc.spec_to_bytes().len() == u64::spec_size_of());

            // Write the new metadata to the inactive header (without the CRC)
            subregion.serialize_and_write_relative(wrpm_region, 0, &log_metadata, Tracked(perm));
            subregion.serialize_and_write_relative(wrpm_region, size_of::<LogMetadata>() as u64, &log_crc, Tracked(perm));

            // Prove that after the flush, the log metadata will be reflected in the subregion's
            // state.

            proof {
                let state_after_flush = subregion.view(wrpm_region).flush().committed();
                assert(extract_bytes(state_after_flush, 0, LogMetadata::spec_size_of())
                       =~= log_metadata.spec_to_bytes());
                assert(extract_bytes(state_after_flush, LogMetadata::spec_size_of(), u64::spec_size_of())
                       =~= log_crc.spec_to_bytes());
            }
        }
    }

    /*log\logspec_t*/
    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub pending: Seq<u8>,
        pub capacity: int,
    }


    /*util_v*/
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

    /*pmem\pmcopy_t*/
   pub broadcast group pmcopy_axioms {
        axiom_bytes_len,
        axiom_to_from_bytes
    }

    pub trait PmCopy : PmSized + SpecPmSized + Sized + Copy {}

    // PmCopyHelper is a subtrait of PmCopy that exists to provide a blanket
    // implementation of these methods for all PmCopy objects. 
    pub trait PmCopyHelper : PmCopy {
 
        spec fn spec_to_bytes(self) -> Seq<u8>;

        spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        spec fn spec_crc(self) -> u64;
    }

    impl<T> PmCopyHelper for T where T: PmCopy {

        closed spec fn spec_to_bytes(self) -> Seq<u8>;

	#[verifier::external_body]
        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self
	{
		unimplemented!()
	}

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_to_bytes())
        }

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

	#[verifier::external_body]
    pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat
	{
		unimplemented!()
	}

    #[verifier::external_body]
    pub const fn padding_needed(offset: usize, align: usize) -> (out: usize) 
        requires 
            align > 0,
        ensures 
            out <= align,
            out as nat == spec_padding_needed(offset as nat, align as nat)
    {
        unimplemented!()
    }
 

    /*pmem\pmemspec_t*/
    pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    impl PersistentMemoryByte
    {
        pub open spec fn write(self, byte: u8) -> Self
        {
            Self {
                state_at_last_flush: self.state_at_last_flush,
                outstanding_write: Some(byte),
            }
        }

        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self {
                state_at_last_flush: self.flush_byte(),
                outstanding_write: None,
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

        pub open spec fn write(self, addr: int, bytes: Seq<u8>) -> Self
        {
            Self {
                state: self.state.map(|pos: int, pre_byte: PersistentMemoryByte|
                                         if addr <= pos < addr + bytes.len() { pre_byte.write(bytes[pos - addr]) }
                                         else { pre_byte }),
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self {
                state: self.state.map(|_addr, b: PersistentMemoryByte| b.flush()),
            }
        }

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
        }

        pub open spec fn no_outstanding_writes(self) -> bool
        {
            Self::no_outstanding_writes_in_range(self, 0, self.state.len() as int)
        }

        pub open spec fn committed(self) -> Seq<u8>
        {
            self.state.map(|_addr, b: PersistentMemoryByte| b.state_at_last_flush)
        }
    }

    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }


    pub trait PersistentMemoryRegion : Sized
    {
    }
 
    pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8>
    {
        bytes.subrange(pos as int, (pos + len) as int)
    }

    /*pmem\pmemutil_v*/
	#[verifier::external_body]
    pub fn calculate_crc<S>(val: &S) -> (out: u64)
        where
            S: PmCopy + Sized,
        requires
            // this is true in the default implementation of `spec_crc`, but
            // an impl of `PmCopy` can override the default impl, so
            // we have to require it here
            val.spec_crc() == spec_crc_u64(val.spec_to_bytes())
        ensures
            val.spec_crc() == out,
            spec_crc_u64(val.spec_to_bytes()) == out,
	{
		unimplemented!()
	}

    /*pmem\subregion_v*/

pub struct WriteRestrictedPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WriteRestrictedPersistentMemorySubregion
{
	#[verifier::external_body]
    pub closed spec fn start(self) -> nat
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn len(self) -> nat
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool
	{
		unimplemented!()
	}

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool
    {
        self.is_writable_absolute_addr_fn()(addr + self.start())
    }

	#[verifier::external_body]
    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
	{
		unimplemented!()
	}

    pub open spec fn inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& self.view(wrpm).len() == self.len()
        &&& self.opaque_inv(wrpm, perm)
    }

	#[verifier::external_body]
    pub exec fn serialize_and_write_relative<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + S::spec_size_of() <= self.view(old::<&mut _>(wrpm)).len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + S::spec_size_of()),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(relative_addr as int, to_write.spec_to_bytes()),
	{
		unimplemented!()
	}
    }

/*pmem\wrpm_t*/
pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
}

pub struct WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pm_region: PMRegion,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
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

// Arrays are PmSized but since the implementation is generic
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
