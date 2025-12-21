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

/*********log\layout_v.rs*/

pub const ABSOLUTE_POS_OF_GLOBAL_METADATA: u64 = 0;

pub const ABSOLUTE_POS_OF_LOG_CDB: u64 = 80;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE: u64 = 88;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE: u64 = 128;

pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;

#[repr(C)]
#[derive(PmSized, Copy, Clone, Default)]
pub struct LogMetadata {
    pub log_length: u64,
    pub _padding: u64,
    pub head: u128,
}

impl PmCopy for LogMetadata {

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

#[verifier::external_body]
pub proof fn lemma_establish_subrange_equivalence(mem1: Seq<u8>, mem2: Seq<u8>)
    ensures
        forall|i: int, j: int|
            mem1.subrange(i, j) =~= mem2.subrange(i, j) ==> #[trigger] mem1.subrange(i, j)
                == #[trigger] mem2.subrange(i, j),
{
    unimplemented!()
}

/*********util_v.rs********/

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

/*******pmem\pmcopy_t.rs******/

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
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    // The definition is closed because no one should need to reason about it,
    // thanks to `axiom_to_from_bytes`.
    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        // If the bytes represent some valid `Self`, pick such a `Self`.
        // Otherwise, pick an arbitrary `Self`. (That's how `choose` works.)
        choose|x: T| x.spec_to_bytes() == bytes
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

// This function calculates the amount of padding needed to align the next field in a struct.
// It's const, so we can use it const contexts to calculate the size of a struct at compile time.
// This function is also verified.
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

/*****pmem\pmemspect_t.rs******/

pub const CDB_FALSE: u64 = 0xa32842d19001605e;
  // CRC(b"0")
pub const CDB_TRUE: u64 = 0xab21aa73069531b7;
  // CRC(b"1")
pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
}

/*********pmem\traits_t.rs*****/

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

/********log\inv_v.rs******/

pub open spec fn active_metadata_bytes_are_equal(pm_bytes1: Seq<u8>, pm_bytes2: Seq<u8>) -> bool {
    let cdb1 = deserialize_and_check_log_cdb(pm_bytes1);
    let cdb2 = deserialize_and_check_log_cdb(pm_bytes2);

    &&& cdb1.is_Some()
    &&& cdb2.is_Some()
    &&& cdb1 == cdb2
    &&& pm_bytes1.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    ) == pm_bytes2.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    )
    &&& {
        let metadata_pos = if cdb1.unwrap() {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int
        } else {
            ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int
        };
        pm_bytes1.subrange(
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
        ) == pm_bytes2.subrange(
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
        )
    }
}

#[verifier::external_body]
pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
    ensures
        forall|i: int, j, k: int, l: int|
            0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i)
                == mem1.subrange(k, l),
{
    unimplemented!()
}

pub proof fn lemma_header_bytes_equal_implies_active_metadata_bytes_equal(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
)
    requires
        ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
        ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
        mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int)
            =~= mem2.subrange(
            ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
            ABSOLUTE_POS_OF_LOG_AREA as int,
        ),
        deserialize_and_check_log_cdb(mem1) is Some,
    ensures
        active_metadata_bytes_are_equal(mem1, mem2),
{
    reveal(spec_padding_needed);
    lemma_establish_subrange_equivalence(mem1, mem2);

    lemma_auto_smaller_range_of_seq_is_subrange(mem1);

    let cdb = deserialize_and_check_log_cdb(mem1).unwrap();
    let log_metadata_pos = get_log_metadata_pos(cdb);

    assert(mem1.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    ) == mem2.subrange(
        ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
    ));
    assert(mem1.subrange(
        log_metadata_pos as int,
        log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
    ) == mem2.subrange(
        log_metadata_pos as int,
        log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of(),
    ));
}

} // verus!
