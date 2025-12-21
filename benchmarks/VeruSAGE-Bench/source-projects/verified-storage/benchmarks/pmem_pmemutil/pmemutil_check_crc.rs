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


    /*pmem/pmemspec_t*/
    pub closed spec fn maybe_corrupted_byte(byte: u8, true_byte: u8, addr: int) -> bool;

    pub open spec fn all_elements_unique(seq: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
    }

    pub open spec fn maybe_corrupted(bytes: Seq<u8>, true_bytes: Seq<u8>, addrs: Seq<int>) -> bool {
        &&& bytes.len() == true_bytes.len() == addrs.len()
        &&& forall |i: int| #![auto] 0 <= i < bytes.len() ==> maybe_corrupted_byte(bytes[i], true_bytes[i], addrs[i])
    }

    pub open spec fn spec_crc_bytes(bytes: Seq<u8>) -> Seq<u8> {
        spec_crc_u64(bytes).spec_to_bytes()
    }

    pub closed spec fn spec_crc_u64(bytes: Seq<u8>) -> u64;

	#[verifier::external_body]
    pub proof fn axiom_bytes_uncorrupted2(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                         y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>)
        requires
            maybe_corrupted(x_c, x, x_addrs),
            maybe_corrupted(y_c, y, y_addrs),
            y_c == spec_crc_bytes(x_c),
            y == spec_crc_bytes(x),
            all_elements_unique(x_addrs),
            all_elements_unique(y_addrs),
        ensures
            x == x_c
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub exec fn compare_crcs(crc1: &[u8], crc2: u64) -> (out: bool)
        requires 
            crc1@.len() == u64::spec_size_of()
        ensures 
            out ==> crc1@ == crc2.spec_to_bytes(),
            !out ==> crc1@ != crc2.spec_to_bytes()
	{
		unimplemented!()
	}


    /*pmem\pmemutil_v*/
    pub fn check_crc(
        data_c: &[u8],
        crc_c: &[u8],
        Ghost(mem): Ghost<Seq<u8>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
        Ghost(data_addrs): Ghost<Seq<int>>,
        Ghost(crc_addrs): Ghost<Seq<int>>,
    ) -> (b: bool)
        requires
            data_addrs.len() <= mem.len(),
            crc_addrs.len() <= mem.len(),
            crc_c@.len() == u64::spec_size_of(),
            all_elements_unique(data_addrs),
            all_elements_unique(crc_addrs),
            ({
                let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                &&& if impervious_to_corruption {
                        &&& data_c@ == true_data_bytes
                        &&& crc_c@ == true_crc_bytes
                    }
                    else {
                        &&& maybe_corrupted(data_c@, true_data_bytes, data_addrs)
                        &&& maybe_corrupted(crc_c@, true_crc_bytes, crc_addrs)
                    }
            })
        ensures
            ({
                let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
                let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);
                true_crc_bytes == spec_crc_bytes(true_data_bytes) ==> {
                    if b {
                        &&& data_c@ == true_data_bytes
                        &&& crc_c@ == true_crc_bytes
                    }
                    else {
                        !impervious_to_corruption
                    }
                }
            })
    {
        // Compute a CRC for the bytes we read.
        let computed_crc = calculate_crc_bytes(data_c);

        // Check whether the CRCs match. This is done in an external body function so that we can convert the maybe-corrupted
        // CRC to a u64 for comparison to the computed CRC.
        let crcs_match = compare_crcs(crc_c, computed_crc);

        proof {
            let true_data_bytes = Seq::new(data_addrs.len(), |i: int| mem[data_addrs[i] as int]);
            let true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i]]);

            // We may need to invoke `axiom_bytes_uncorrupted` to justify that since the CRCs match,
            // we can conclude that the data matches as well. That axiom only applies in the case
            // when all three of the following conditions hold: (1) the last-written CRC really is
            // the CRC of the last-written data; (2) the persistent memory regions aren't impervious
            // to corruption; and (3) the CRC read from disk matches the computed CRC. If any of
            // these three is false, we can't invoke `axiom_bytes_uncorrupted`, but that's OK
            // because we don't need it. If #1 is false, then this lemma isn't expected to prove
            // anything. If #2 is false, then no corruption has happened. If #3 is false, then we've
            // detected corruption.
            if {
                &&& true_crc_bytes == spec_crc_bytes(true_data_bytes)
                &&& !impervious_to_corruption
                &&& crcs_match
            } {
                axiom_bytes_uncorrupted2(data_c@, true_data_bytes, data_addrs, crc_c@, true_crc_bytes, crc_addrs);
            }
        }

        crcs_match
    }

	#[verifier::external_body]
    pub fn calculate_crc_bytes(val: &[u8]) -> (out: u64) 
        ensures 
            out == spec_crc_u64(val@),
            out.spec_to_bytes() == spec_crc_bytes(val@),
	{
		unimplemented!()
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
