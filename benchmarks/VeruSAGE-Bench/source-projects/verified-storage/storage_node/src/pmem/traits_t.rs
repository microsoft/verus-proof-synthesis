//! This file defines external and unsafe traits PmSized 
//! and PmSafe that are used to prove that accesses to PM
//! are safe. Aside from the hardcoded unsafe implementations
//! in this file, these traits should *ONLY* be implemented
//! via derive macros, which are defined in the pmsafe crate.
//! 
//! Both reading and writing to PM are potentially dangerous
//! operations. It is not crash-safe to write a structure with
//! references to external resources (e.g., references, raw pointers,
//! file descriptors), as these resources may be lost in a crash,
//! causing a dangling reference upon recovery. The PmSafe marker
//! trait establishes which types are safe to write to PM and can
//! only be derived for safe types.
//! 
//! To read safely from PM, we need to know the runtime size and
//! alignment of the structure we are reading so that we can 
//! eventually cast the read bytes to a more useful type without
//! risking UB. The PmSized and ConstPmSized traits provide 
//! methods to calculate the runtime size and alignment alongside
//! the SpecPmSized trait (defined in pmem/pmcopy_t.rs) and check
//! that the calculated size is correct, which helps us ensure 
//! that proofs use the correct size for structures. 

use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;
use deps_hack::PmSafe;

use super::pmcopy_t::SpecPmSized;

// The `PmSafe` marker trait indicates whether a structure is safe to 
// write to PM. This trait should only implemented via its derive macro
// for user-defined structures.
pub unsafe trait PmSafe {}

// Numeric types and arrays are all always PmSafe.
// The PmSafe derive macro can derive PmSafe for any structure
// that contains only PmSafe types.
unsafe impl PmSafe for u8 {}
unsafe impl PmSafe for u16 {}
unsafe impl PmSafe for u32 {}
unsafe impl PmSafe for u64 {}
unsafe impl PmSafe for u128 {}
unsafe impl PmSafe for usize {}
unsafe impl PmSafe for i8 {}
unsafe impl PmSafe for i16 {}
unsafe impl PmSafe for i32 {}
unsafe impl PmSafe for i64 {}
unsafe impl PmSafe for i128 {}
unsafe impl PmSafe for isize {}
unsafe impl<T: PmSafe, const N: usize> PmSafe for [T; N] {}

// These types are PmSafe because they do not contain references to external
// resources. Note, however, that extra care must be taken when *reading* them,
// as attempting to cast invalid bytes to one of these types will cause UB.
// Any type that we wish to read from PM must implement the PmCopy trait,
// defined in pmem/pmcopy_t.rs, which provides additional conditions and methods
// for making sure such reads are safe.
unsafe impl PmSafe for bool {}
unsafe impl PmSafe for char {}
unsafe impl PmSafe for f32 {} 
unsafe impl PmSafe for f64 {}

verus! {
    #[verifier::external_trait_specification]
    pub trait ExPmSafe {
        type ExternalTraitSpecificationFor: PmSafe;
    }

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
unsafe impl<T: PmSafe + PmSized, const N: usize> PmSized for [T; N] {
    fn size_of() -> usize 
    {
        N * T::size_of()
    }
    
    fn align_of() -> usize {
        T::align_of()
    }
}

unsafe impl<T: PmSafe + PmSized, const N: usize> UnsafeSpecPmSized for [T; N] {}

unsafe impl<T: PmSafe + PmSized + ConstPmSized, const N: usize> ConstPmSized for [T; N] {
    const SIZE: usize = N * T::SIZE;
    const ALIGN: usize = T::ALIGN;
}