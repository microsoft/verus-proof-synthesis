use vstd::prelude::*;
use deps_hack::{pmsized_primitive};

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
    }

    impl<T> PmCopyHelper for T where T: PmCopy {

        closed spec fn spec_to_bytes(self) -> Seq<u8>;

        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;
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
    pub open spec fn const_persistence_chunk_size() -> int { 8 }

    #[verifier::ext_equal]
    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    impl PersistentMemoryByte {

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
    }

    #[verifier::ext_equal]
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

        pub open spec fn no_outstanding_writes_in_range(self, i: int, j: int) -> bool
        {
            forall |k| i <= k < j ==> (#[trigger] self.state[k].outstanding_write).is_none()
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

    #[verifier::ext_equal]
    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }

    pub trait PersistentMemoryRegion : Sized {}


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

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
    recommends
        0 <= start,
        0 <= len,
        start + len <= v1.len(),
        v1.len() == v2.len()
{
    forall |addr: int| {
       ||| 0 <= addr < start
       ||| start + len <= addr < v1.len()
       ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
    } ==> v1.state[addr] == #[trigger] v2.state[addr]
}
    #[verifier::ext_equal]

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


    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_view_@
    }

    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool
    {
        self.is_writable_absolute_addr_fn_@
    }

    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(wrpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants()
        &&& wrpm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= wrpm@.len()
        &&& self.view(wrpm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
        &&& forall |alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>| {
              &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
              &&& self.initial_region_view().len() == alt_region_view.len()
              &&& views_differ_only_where_subregion_allows(self.initial_region_view(), alt_region_view,
                                                         self.start(), self.len(),
                                                         self.is_writable_absolute_addr_fn())
           } ==> perm.check_permission(alt_crash_state)
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

    pub exec fn serialize_and_write_absolute<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(absolute_addr - self.start(),
                                                                  to_write.spec_to_bytes()),
    {

        /*
         * either use broadcast here or the axiom::<S>
         *
         * don't put the broadcast outside this function, otherwise there will be cyclic reference
         * broadcast use should be in a different file from where the axiom-group is defined
         */

//        broadcast use pmcopy_axioms;
        proof{
            axiom_bytes_len::<S>(*to_write);
        }

        let ghost bytes = to_write.spec_to_bytes();

        assert(bytes.len() == S::spec_size_of());

        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.serialize_and_write(absolute_addr, to_write, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }
}
    #[verifier::ext_equal]

pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
}
    #[verifier::ext_equal]

pub struct WritablePersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

/*pmem\wrpm_t*/

pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
}

    #[verifier::ext_equal]

pub struct WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pm_region: PMRegion,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<Perm, PMRegion> WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
 
    pub closed spec fn view(&self) -> PersistentMemoryRegionView;

    pub closed spec fn inv(&self) -> bool;
    pub closed spec fn constants(&self) -> PersistentMemoryConstants;

	#[verifier::external_body]
    pub exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            old(self)@.no_outstanding_writes_in_range(addr as int, addr + S::spec_size_of()),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| old(self)@.write(addr as int, to_write.spec_to_bytes()).can_crash_as(s)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@ == old(self)@.write(addr as int, to_write.spec_to_bytes()),
	{
		unimplemented!()
	}

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

// Arrays are PmSized and but since the implementation is generic
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
