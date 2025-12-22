use deps_hack::{pmsized_primitive, PmSized};
use vstd::prelude::*;
verus! {

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

pub const ABSOLUTE_POS_OF_GLOBAL_METADATA: u64 = 0;

pub const ABSOLUTE_POS_OF_LOG_CDB: u64 = 80;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE: u64 = 88;

pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE: u64 = 128;

pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;

#[repr(C)]
#[derive(PmSized, Copy, Clone,
    Default)]
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



pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self {
        choose|x: T| x.spec_to_bytes() == bytes
    }
}

#[verifier::external_body]
pub proof fn axiom_bytes_len<S: PmCopy>(s: S)
    ensures
        #[trigger] s.spec_to_bytes().len() == S::spec_size_of(),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn axiom_to_from_bytes<S: PmCopy>(s: S)
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
pub open spec fn spec_padding_needed(offset: nat, align: nat) -> nat
    {
        let misalignment = offset % align;
        if misalignment > 0 {
            (align - misalignment) as nat
        } else {
            0
        }
    }

pub const CDB_FALSE: u64 = 0xa32842d19001605e;

pub const CDB_TRUE: u64 = 0xab21aa73069531b7;

pub open spec fn extract_bytes(bytes: Seq<u8>, pos: nat, len: nat) -> Seq<u8> {
    bytes.subrange(pos as int, (pos + len) as int)
}

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

pub fn main() {
}

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
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

} // verus!
pub unsafe trait PmSized: SpecPmSized {
    fn size_of() -> usize;
    fn align_of() -> usize;
}
pub unsafe trait ConstPmSized {
    const SIZE: usize;
    const ALIGN: usize;
}
pub unsafe trait UnsafeSpecPmSized {}
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
