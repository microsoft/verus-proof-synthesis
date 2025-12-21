use deps_hack::pmsized_primitive;
use std::mem::MaybeUninit;
use vstd::prelude::*;
verus! {

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

        pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
    pub const CDB_TRUE: u64  = 0xab21aa73069531b7; // CRC(b"1")

#[verifier(external_body)]
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

#[verifier(external_body)]
    pub proof fn axiom_corruption_detecting_boolean(cdb_c: Seq<u8>, cdb: Seq<u8>, addrs: Seq<int>)
        requires
            maybe_corrupted(cdb_c, cdb, addrs),
            all_elements_unique(addrs),
            cdb.len() == u64::spec_size_of(),
            cdb_c == CDB_FALSE.spec_to_bytes() || cdb_c == CDB_TRUE.spec_to_bytes(),
            cdb == CDB_FALSE.spec_to_bytes() || cdb == CDB_TRUE.spec_to_bytes(),
        ensures
            cdb_c == cdb
{
    unimplemented!()
}


pub trait PmCopy: PmSized + SpecPmSized + Sized + Copy {

}

pub trait PmCopyHelper: PmCopy {
    spec fn spec_to_bytes(self) -> Seq<u8>;

    spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    spec fn bytes_parseable(bytes: Seq<u8>) -> bool;
}

impl<T> PmCopyHelper for T where T: PmCopy {
    closed spec fn spec_to_bytes(self) -> Seq<u8>;

    closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

    open spec fn bytes_parseable(bytes: Seq<u8>) -> bool {
        Self::spec_from_bytes(bytes).spec_to_bytes() == bytes
    }
}

impl PmCopy for u64 {

}

#[verifier::external_body]
#[verifier::reject_recursive_types(S)]
pub struct MaybeCorruptedBytes<S> where S: PmCopy {
    val: Box<MaybeUninit<S>>,
}

impl<S> MaybeCorruptedBytes<S> where S: PmCopy {
    pub closed spec fn view(self) -> Seq<u8>;
}

impl MaybeCorruptedBytes<u64> {
    #[verifier::external_body]
    pub exec fn extract_cdb(
        self,
        Ghost(true_bytes): Ghost<Seq<u8>>,
        Ghost(addrs): Ghost<Seq<int>>,
        Ghost(impervious_to_corruption): Ghost<bool>,
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
            out.spec_to_bytes() == self@,
    {
        unimplemented!()
    }
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
pub fn check_cdb(
    cdb_c: MaybeCorruptedBytes<u64>,
    Ghost(mem): Ghost<Seq<u8>>,
    Ghost(impervious_to_corruption): Ghost<bool>,
    Ghost(cdb_addrs): Ghost<Seq<int>>,
) -> (result: Option<bool>)
    requires
        forall|i: int| 0 <= i < cdb_addrs.len() ==> cdb_addrs[i] <= mem.len(),
        all_elements_unique(cdb_addrs),
        ({
            let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
            let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            &&& u64::bytes_parseable(true_cdb_bytes)
            &&& true_cdb == CDB_FALSE || true_cdb == CDB_TRUE
            &&& if impervious_to_corruption {
                cdb_c@ == true_cdb_bytes
            } else {
                maybe_corrupted(cdb_c@, true_cdb_bytes, cdb_addrs)
            }
        }),
    ensures
        ({
            let true_cdb_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[cdb_addrs[i]]);
            let true_cdb = u64::spec_from_bytes(true_cdb_bytes);
            match result {
                Some(b) => if b {
                    true_cdb == CDB_TRUE
                } else {
                    true_cdb == CDB_FALSE
                },
                None => !impervious_to_corruption,
            }
        }),
{
    let ghost extract_cdb_ghost0: Seq<u8> = arbitrary(); // TODO - replace with correct value
    let ghost extract_cdb_ghost1: Seq<int> = arbitrary(); // TODO - replace with correct value
    let ghost extract_cdb_ghost2: bool = arbitrary(); // TODO - replace with correct value    
    let cdb_val = cdb_c.extract_cdb(
        Ghost(extract_cdb_ghost0),
        Ghost(extract_cdb_ghost1),
        Ghost(extract_cdb_ghost2),
    );
    if *cdb_val == CDB_FALSE {
        let ret = Some(false);
        ret
    } else if *cdb_val == CDB_TRUE {
        let ret = Some(true);
        ret
    } else {
        let ret = None;
        ret
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
