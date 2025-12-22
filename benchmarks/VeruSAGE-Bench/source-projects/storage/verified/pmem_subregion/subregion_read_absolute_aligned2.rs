use vstd::prelude::*;
use deps_hack::{pmsized_primitive};
use std::mem::MaybeUninit;


verus! {

    pub fn main()
    {
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

        spec fn bytes_parseable(bytes: Seq<u8>) -> bool;
    }

    impl<T> PmCopyHelper for T where T: PmCopy {
        closed spec fn spec_to_bytes(self) -> Seq<u8>;

        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        open spec fn bytes_parseable(bytes: Seq<u8>) -> bool;
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

    #[verifier::external_body]
    #[verifier::reject_recursive_types(S)]
    pub struct MaybeCorruptedBytes<S>
        where 
            S: PmCopy
    {
        val: Box<MaybeUninit<S>>,
    }

    impl<S> MaybeCorruptedBytes<S>
        where 
            S: PmCopy 
    {
 
        pub closed spec fn view(self) -> Seq<u8>;
    }

    global size_of usize == 8;

    global size_of isize == 8;

    pub trait SpecPmSized : UnsafeSpecPmSized {
        spec fn spec_size_of() -> nat;
        spec fn spec_align_of() -> nat;
    }


    pmsized_primitive!(u8);

    pmsized_primitive!(u64);

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


    /*pmem\pmemspect_t*/
    pub enum PmemError {
        InvalidFileName,
        CannotOpenPmFile,
        NotPm,
        PmdkError,
        AccessOutOfRange,
    }

    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
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
    }

    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }

    pub trait PersistentMemoryRegion : Sized
    {

        spec fn view(&self) -> PersistentMemoryRegionView;

        spec fn inv(&self) -> bool;

        spec fn constants(&self) -> PersistentMemoryConstants;

        fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
            where 
                S: PmCopy + Sized,
            requires
                self.inv(),
                0 <= addr < addr + S::spec_size_of() <= self@.len(),
                self@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
                // We must have previously written a serialized S to this addr
                S::bytes_parseable(self@.committed().subrange(addr as int, addr + S::spec_size_of()))
            ensures
                match bytes {
                    Ok(bytes) => {
                        let true_bytes = self@.committed().subrange(addr as int, addr + S::spec_size_of());
                        let addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| i + addr);
                        // If the persistent memory regions are impervious
                        // to corruption, read returns the last bytes
                        // written. Otherwise, it returns a
                        // possibly-corrupted version of those bytes.
                        if self.constants().impervious_to_corruption {
                            bytes@ == true_bytes
                        }
                        else {
                            maybe_corrupted(bytes@, true_bytes, addrs)
                        }
                    }
                    _ => false,
                }
        ;
    }


/*pmem\subregion_v*/


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

pub struct WriteRestrictedPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
}

impl PersistentMemorySubregion
{

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
    {
        self.start() + self.len()
    }

    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView
    {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& pm.inv()
        &&& pm@.len() <= u64::MAX
        &&& self.view(pm).len() == self.len()
        &&& self.start() + self.len() <= pm@.len()
    }

    pub exec fn read_absolute_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr < absolute_addr + S::spec_size_of() <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start(),
            ),
            S::bytes_parseable(
                self.view(pm).committed().subrange(absolute_addr - self.start(),
                                                   absolute_addr + S::spec_size_of() - self.start())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }

        pm.read_aligned::<S>(absolute_addr)
    }
}

pub struct WritablePersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
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
