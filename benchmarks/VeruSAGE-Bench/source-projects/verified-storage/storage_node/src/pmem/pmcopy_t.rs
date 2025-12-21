//! This file contains the trusted specification of several traits that 
//! help us prove that reading from PM is safe. Some of the traits in this 
//! file correspond to macros defined in the `pmsafe` crate in this repository.
//! It is also related to some external traits defined and specified 
//! in pmem/traits_t.rs.
//! 
//! Both reading and writing to PM is potentially dangerous; this file 
//! focuses on ensuring that reads are safe. We want to be able to 
//! read bytes from PM and then cast them to some target type T,
//! but this may result in undefined behavior if the bytes are 
//! an invalid T value. Thus, before doing such a cast, we 
//! need to be sure that 1) the bytes we are reading have been 
//! properly initialized with a valid T and 2) they have not been
//! corrupted. 
//! 
//! We also need to be sure that proofs use the correct size for T.
//! This is tricky, because Verus has no way of obtaining the size 
//! in bytes of a structure. Rust's std::mem::size_of function
//! can give the size of a type in constant contexts, but this is 
//! an exec function that cannot be used in spec or proof code.
//! 
//! This file contains the `PmCopy` trait, which indicates whether
//! a type is safe to copy from PM and defines some methods and 
//! axioms for dealing with such structures.

use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::layout::*;
use crate::pmem::traits_t::{PmSafe, PmSized, ConstPmSized, UnsafeSpecPmSized};

use deps_hack::{crc64fast::Digest, pmsized_primitive};
use core::slice;
use std::convert::TryInto;
use std::ptr;
use std::mem::MaybeUninit;

verus! {
    pub broadcast group pmcopy_axioms {
        axiom_bytes_len,
        axiom_to_from_bytes
    }

    // PmCopy provides functions to help reason about copying data to and from persistent memory.
    // It is a subtrait of PmSafe (a marker trait indicating that the type is safe to write to persistent memory)
    // and PmSized/SpecPmSized (which provide reliable information about the size of the implementing struct in 
    // bytes for use in ghost code).

    // PmCopy (together with the PmCopyHelper trait, which provides a blanket implementation of 
    // method we want PmCopy objects to have) indicates whether an object is safe to 
    // read from PM and provides methods to help prove that such reads are safe. 
    // It is a subtrait of several unsafe traits -- PmSafe and PmSized -- that should
    // only be implemented by structures using #[derive]. 
    // 
    // There is currently no derive macro for PmCopy, but since it is a safe trait with 
    // no associated functions, it can be implemented directly in safe, verified code.
    // If compilation of such an implementation succeeds, the implementor is safe
    // to read from PM.
    //
    // Implicit in this definition is that `PmCopy` types must be repr(C);
    // the macros that derive `PmSized` and `PmSafe` require that the deriving
    // type be repr(C), as this is the best way to ensure a predictable in-memory
    // layout and size.
    pub trait PmCopy : PmSized + SpecPmSized + Sized + PmSafe + Copy {}

    // PmCopyHelper is a subtrait of PmCopy that exists to provide a blanket
    // implementation of these methods for all PmCopy objects. 
    pub trait PmCopyHelper : PmCopy {
        // `spec_to_bytes` is an uninterpreted method that returns a byte
        // representation of `self`. 
        spec fn spec_to_bytes(self) -> Seq<u8>;

        // `spec_from_bytes` is the inverse of spec_to_bytes. It only returns
        // valid instances of T, because only valid instances of T can be
        // converted to bytes using `spec_to_bytes`. Its relationship 
        // to `spec_to_bytes` is axiomatized by `axiom_to_from_bytes`.
        spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        spec fn bytes_parseable(bytes: Seq<u8>) -> bool;

        // `spec_crc` returns the CRC of the given value as a u64. 
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

        open spec fn bytes_parseable(bytes: Seq<u8>) -> bool
        {
            Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
        }
    }

    // The two following axioms are brodcast in the `pmcopy_axioms`
    // group. 

    // `axiom_bytes_len` axiomatizes the fact that a byte 
    // representation of some PmCopy value S has size
    // S::spec_size_of(). Since `spec_to_bytes` is uninterpreted,
    // we cannot prove that this is true; the PmSized macro helps
    // us check that this is the case, but that macro still must 
    // be audited to ensure that S::spec_size_of() and the runtime 
    // size_of functions return the same value.
    pub broadcast proof fn axiom_bytes_len<S: PmCopy>(s: S)
        ensures 
            #[trigger] s.spec_to_bytes().len() == S::spec_size_of()
    {
        admit();
    }

    // `axiom_to_from_bytes` axiomatizes the fact that converting any
    // PmCopy value `s` to bytes and back results in the original value. 
    // This axiom has no preconditions because `s` is necessarily
    // a valid instance of its type.
    pub broadcast proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
        ensures 
            s == #[trigger] S::spec_from_bytes(s.spec_to_bytes())
    {
        admit();
    }

    // u64 must implement PmCopy for CRC management
    impl PmCopy for u64 {}

    // MaybeCorruptedBytes<S> is a container for bytes that have been read 
    // from PM and represent a valid S in the absence of corruption. It 
    // provides methods to help check that the bytes have not been corrupted
    // and then cast them to an S. 
    // 
    // This structure is external_body because it uses a `MaybeUninit` to store
    // the bytes. We cannot cast the bytes to an S before checking for corruption, 
    // as this could cause UB if the bytes are corrupted. Using `MaybeUninit` 
    // avoids UB and also ensures that the DRAM location of the S is properly
    // aligned, which is also important for safety when we eventually cast 
    // the bytes to an S.
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
        // The constructor doesn't have a postcondition because we do not know anything about 
        // the state of the bytes yet.
        #[verifier::external_body]
        pub exec fn new() -> (out: Self)
        {
            MaybeCorruptedBytes { 
                val: Box::<S>::new_uninit()
            }
        }

        // The view of a `MaybeCorruptedBytes<S>` is a sequence of bytes.
        // This spec fn is uninterpreted; its relationship to S's `spec_to_bytes`
        // is established in the postconditions of other `MaybeCorruptedBytes`
        // methods.
        pub closed spec fn view(self) -> Seq<u8>;

        // `copy_from_slice` copies bytes from a location on PM to a 
        // `MaybeCorruptedBytes<S>`. The precondition requires that we 
        // have previously initialized the PM bytes as a valid S `true_val`,
        // but not that the bytes are uncorrupted. 
        #[verifier::external_body]
        pub exec fn copy_from_slice(
            &mut self, 
            bytes: &[u8], 
            Ghost(true_val): Ghost<S>,
            Ghost(addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>
        )
            requires 
                if impervious_to_corruption {
                    bytes@ == true_val.spec_to_bytes()
                } else {
                    maybe_corrupted(bytes@, true_val.spec_to_bytes(), addrs)
                },
                bytes@.len() == S::spec_size_of(),
            ensures 
                self@ == bytes@
        {
            self.copy_from_slice_helper(bytes);
        }

        // This helper method lets us work around the lack of Verus support for &mut and
        // a bug where the body of some external_body functions may be checked by the verifier.
        // It casts the contents of self to a slice of `MaybeUninit<u8>`, then copies the given
        // byte slice to this location. All of the code in this function is safe -- it's safe
        // to cast a MaybeUninit value to a slice of MaybeUninit bytes, and it is safe to 
        // copy initialized bytes to this slice. `MaybeUninit::write_slice` will panic if 
        // the two slices have different lengths; since this method is external, it cannot 
        // have a precondition, but the public wrapper around this function `copy_from_slice`
        // requires that the provided PM byte slice is the correct size.
        // TODO: remove this helper function and move its body back into `copy_from_slice` once 
        // https://github.com/verus-lang/verus/issues/1151 is fixed
        #[verifier::external]
        #[inline(always)]
        fn copy_from_slice_helper(
            &mut self, 
            bytes: &[u8], 
        ) 
        {
            // convert the MaybeUninit<S> to a mutable slice of `MaybeUninit<u8>`
            let mut self_bytes = self.val.as_bytes_mut();
            // copy bytes from the given slice to the mutable slice of `MaybeUninit<u8>`.
            // This returns a slice of initialized bytes, but it does NOT change the fact that 
            // the original S is still MaybeUninit
            // TODO: in newer versions of Rust, write_slice is renamed to copy_from_slice
            MaybeUninit::write_slice(self_bytes, bytes);
        }


        // This method returns the `MaybeUninit` value stored in self as an immutable slice of 
        // bytes. This is safe here because there are no invalid values of u8; even if the slice
        // constitutes an invalid S, the returned &[u8] will be valid, so assuming that it is 
        // initialized is safe. We use this method to obtain a concrete byte representation of
        // for use in CRC checking.
        #[verifier::external_body]
        pub exec fn as_slice(&self) -> (out: &[u8])
            ensures 
                out@ == self@
        {
            let bytes = self.val.as_bytes();
            // SAFETY: even if we haven't initialized the bytes, there are no invalid values of u8, so we can 
            // safely assume that these bytes are initialized (even if the S may not be)
            unsafe { MaybeUninit::slice_assume_init_ref(bytes) }
        }

        // This method assumes that the `MaybeUninit` value of S in self is, in fact, init. 
        // This method can only be invoked once the caller has proven that the bytes are not 
        // corrupted and that they represent a valid S.
        #[verifier::external_body]
        pub exec fn extract_init_val(self, Ghost(true_val): Ghost<S>, Ghost(true_bytes): Ghost<Seq<u8>>, Ghost(impervious_to_corruption): Ghost<bool>) -> (out: Box<S>)
            requires 
                if impervious_to_corruption {
                    true 
                } else {
                    &&& true_bytes == true_val.spec_to_bytes()
                    &&& self@ == true_bytes
                }
            ensures 
                out == true_val
        {
            // SAFETY: The precondition establishes that self@ -- the ghost view of the maybe-corrupted bytes
            // written to self.val -- are equivalent to the serialization of the true value; i.e., we must have 
            // proven that the bytes are not corrupted, and therefore self.val is initialized.
            unsafe { self.val.assume_init() }
        }
    }

    impl MaybeCorruptedBytes<u64> {
        // This method assumes that the CDB is initialized and returns a Box<u64> without
        // requiring a CRC check first. This is necessary because we check the CDB for 
        // corruption by checking its own value directly; it does not have a separate CRC
        // to compare to. Thus, we need an initialized u64 representation of the CDB
        // prior to the corruption check, which we cannot obtain with `extract_init_val`.
        // Since there are no invalid values of u64, it is always safe to assume that
        // a u64 is initialized. We further require that we've previously durably initialized
        // these bytes as one of the two valid CDB values, so this method cannot be used
        // on arbitrary u64s. 
        #[verifier::external_body]
        pub exec fn extract_cdb(
            self, 
            Ghost(true_bytes): Ghost<Seq<u8>>, 
            Ghost(addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>
        ) -> (out: Box<u64>)
            requires 
                if impervious_to_corruption {
                    self@ == true_bytes
                } else {
                    maybe_corrupted(self@, true_bytes, addrs)
                },
                ({
                    let true_val = u64::spec_from_bytes(true_bytes);
                    ||| true_val == CDB_TRUE
                    ||| true_val == CDB_FALSE
                }),
            ensures 
                out.spec_to_bytes() == self@
        {
            // SAFETY: there are not invalid u64 values, so it is safe to assume that any value we read
            // from a CDB location can be treated as initialized. This function makes no promises about 
            // the value of the CDB -- just that we can treat the view as equal to the output of this
            // function -- so we still have to check the CDB for corruption.
            unsafe { self.val.assume_init() }
        }  
    }

    // Our trusted specification of primitive sizes assumes that usize and 
    // isize are 8 bytes. These directives have Verus check this assumption.
    global size_of usize == 8;
    global size_of isize == 8;

    // SpecPmSized defines the spec counterparts of the external trait
    // PmSized, which provides methods for calculating the size 
    // of a user-defined structure that needs to be stored on PM. 
    // PmSized can only be derived via a trusted macro (defined in the
    // pmsafe crate) and uses compile-time assertions to check that
    // the calculated size is the same as the true size. This helps
    // us check that we are using the correct size for PM-resident
    // structures in ghost code, where their size is not usually
    // accessible.
    //
    // Due to restrictions on const traits and associated constants
    // in Rust and Verus, these spec methods must be defined in a separate
    // trait from the exec methods they specify. SpecPmSized is a subtrait
    // of the external unsafe trait UnsafeSpecPmSized to ensure that 
    // structures only implement it if they use the provided derive macros.
    pub trait SpecPmSized : UnsafeSpecPmSized {
        spec fn spec_size_of() -> nat;
        spec fn spec_align_of() -> nat;
    }

    // User-defined structures that derive PmSized have their 
    // size calculated based on the size and alignment of the
    // struct's fields. The size and alignment of safe primitives
    // are hardcoded in pmsafe/pmsafe_macros.rs and implementations
    // for primitive types based on these values are generated
    // by the pmsized_primitive! macro. The macro also generates
    // compile-time assertions to check that the hardcoded sizes
    // and alignments are correct.
    pmsized_primitive!(u8);
    pmsized_primitive!(u16);
    pmsized_primitive!(u32);
    pmsized_primitive!(u64);
    pmsized_primitive!(u128);
    pmsized_primitive!(usize);
    pmsized_primitive!(i8);
    pmsized_primitive!(i16);
    pmsized_primitive!(i32);
    pmsized_primitive!(i64);
    pmsized_primitive!(i128);
    pmsized_primitive!(isize);
    pmsized_primitive!(bool);
    pmsized_primitive!(char);
    // floats are not currently supported by the verifier
    // pmsized_primitive!(f32);
    // pmsized_primitive!(f64);

    // Arrays are PmSized and PmSafe, but since the implementation is generic
    // we provide a manual implementation here rather than using the macro.
    // Unsafe implementations of PmSized and UnsafeSpecPmSized live in traits_t.rs
    impl<T: PmSafe + PmSized, const N: usize> SpecPmSized for [T; N] {
        open spec fn spec_size_of() -> nat
        {
            (N * T::spec_size_of()) as nat
        }   

        open spec fn spec_align_of() -> nat
        {
            T::spec_align_of()
        }
    }

    // This spec function implements an algorithm for determining the amount of 
    // padding needed before the next field in a repr(C) structure to ensure it is aligned.
    // This is the same algorithm described here:
    // https://doc.rust-lang.org/reference/type-layout.html#the-c-representation
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

}
