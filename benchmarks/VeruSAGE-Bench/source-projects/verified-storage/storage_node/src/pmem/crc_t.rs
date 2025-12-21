use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use deps_hack::crc64fast::Digest;

verus! {

    // Helper struct to hide the external crc64fast Digest type
    // from Verus while still keeping ghost state associated with it
    #[verifier::external_body]
    struct ExternalDigest
    {
        digest: Digest
    }

    // A structure for obtaining CRCs of multiple PmCopy objects
    // and writing proofs about them.
    pub struct CrcDigest
    {
        digest: ExternalDigest,
        bytes_in_digest: Ghost<Seq<Seq<u8>>>,
    }

    impl CrcDigest
    {
        pub closed spec fn bytes_in_digest(self) -> Seq<Seq<u8>>
        {
            self.bytes_in_digest@
        }

        #[verifier::external_body]
        pub fn new() -> (output: Self)
            ensures
                output.bytes_in_digest() == Seq::<Seq<u8>>::empty()
        {
            Self {
                digest: ExternalDigest{ digest: Digest::new() },
                bytes_in_digest: Ghost(Seq::<Seq<u8>>::empty())
            }
        }

        #[verifier::external_body]
        pub fn write<S>(&mut self, val: &S)
            where
                S: PmCopy,
            ensures
                self.bytes_in_digest() == old(self).bytes_in_digest().push(val.spec_to_bytes())
        {
            // Cast `val` to bytes, then add them to the digest.
            // The crc64fast crate that we use computes the CRC iteratively and does
            // not store copies of the bytes we write to the digest, so this
            // will (hopefully) not incur any copying beyond what is directly
            // necessary to compute the CRC.
            let num_bytes: usize = S::size_of().try_into().unwrap();
            let s_pointer = val as *const S;
            let bytes_pointer = s_pointer as *const u8;
            // SAFETY: `bytes_pointer` always points to `num_bytes` consecutive, initialized
            // bytes because it was obtained by casting a regular Rust object reference
            // to a raw pointer.
            let bytes = unsafe {
                std::slice::from_raw_parts(bytes_pointer, num_bytes)
            };
            self.digest.digest.write(bytes);
        }

        #[verifier::external_body]
        pub fn write_bytes(&mut self, val: &[u8])
            ensures 
                self.bytes_in_digest() == old(self).bytes_in_digest().push(val@)
        {
            self.digest.digest.write(val);
        }

        // Compute and return the CRC for all bytes in the digest.
        #[verifier::external_body]
        pub fn sum64(&self) -> (output: u64)
            requires
                self.bytes_in_digest().len() != 0
            ensures
                ({
                    let all_bytes_seq = self.bytes_in_digest().flatten();
                    &&& output == spec_crc_u64(all_bytes_seq)
                    &&& output.spec_to_bytes() == spec_crc_bytes(all_bytes_seq)
                })

        {
            self.digest.digest.sum64()
        }
    }
}