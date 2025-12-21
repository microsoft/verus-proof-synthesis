use builtin::*;
use builtin_macros::*;
use deps_hack::{crc64fast::Digest, pmsized_primitive};
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

// Arrays are PmSized and PmSafe, but since the implementation is generic
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

/*pmem\crc*/

#[verifier::external_body]
struct ExternalDigest {
    digest: Digest,
}

pub struct CrcDigest {
    digest: ExternalDigest,
    bytes_in_digest: Ghost<Seq<Seq<u8>>>,
}

impl CrcDigest {
    pub closed spec fn bytes_in_digest(self) -> Seq<Seq<u8>>;

    #[verifier::external_body]
    pub fn new() -> (output: Self)
        ensures
            output.bytes_in_digest() == Seq::<Seq<u8>>::empty(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn write<S>(&mut self, val: &S) where S: PmCopy
        ensures
            self.bytes_in_digest() == old(self).bytes_in_digest().push(val.spec_to_bytes()),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn sum64(&self) -> (output: u64)
        requires
            self.bytes_in_digest().len() != 0,
        ensures
            ({
                let all_bytes_seq = self.bytes_in_digest().flatten();
                &&& output == spec_crc_u64(all_bytes_seq)
                &&& output.spec_to_bytes() == spec_crc_bytes(all_bytes_seq)
            }),
    {
        unimplemented!()
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

    spec fn spec_crc(self) -> u64;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    open spec fn spec_crc(self) -> u64 {
        spec_crc_u64(self.spec_to_bytes())
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

/*pmem\pmemspec_t*/

pub open spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8> {
    spec_crc_u64(bytes).spec_to_bytes()
}

pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

/*pmem\pmemutil*/

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
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
    let mut digest = CrcDigest::new();
    digest.write(val);
    let result = digest.sum64();

    result
}

} // verus!
