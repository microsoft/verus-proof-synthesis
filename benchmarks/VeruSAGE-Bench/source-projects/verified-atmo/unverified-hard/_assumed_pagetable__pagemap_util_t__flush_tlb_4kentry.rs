use vstd::prelude::*;

fn main() {}

verus!{

pub type CpuId = usize;

pub type VAddr = usize;

pub type PAddr = usize;

// File: pagetable/entry.rs
pub struct MapEntry {
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
}


// File: pagetable/pagemap_util_t.rs
// TODO: how to prove this .....
pub fn flush_tlb_4kentry(tlbmap_4k: Ghost<Seq<Map<VAddr, MapEntry>>>, va: Ghost<VAddr>) -> (ret:
    Ghost<Seq<Map<VAddr, MapEntry>>>)
    requires
        NUM_CPUS > 0,
        tlbmap_4k@.len() == NUM_CPUS,
    ensures
        ret@.len() == NUM_CPUS,
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> !(ret@[cpu_id as int].contains_key(va@)),
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> ret@[cpu_id as int].submap_of(tlbmap_4k@[cpu_id as int]),
{
    let mut cpu_id = 0;
    let mut ret_map = tlbmap_4k;

    for cpu_id in 0..NUM_CPUS
    {
        proof {
            let tlbmap = ret_map@[cpu_id as int].remove(va@);
            let tlbseq = ret_map@.update(cpu_id as int, tlbmap);
            ret_map@ = tlbseq;
        }
    }
    ret_map
}


// File: lemma/lemma_u.rs
#[verifier(external_body)]
pub broadcast proof fn map_equal_implies_submap_each_other<K, V>(a: Map<K, V>, b: Map<K, V>)
    requires
        a =~= b,
    ensures
        #[trigger] a.submap_of(b),
        b.submap_of(a),
	{
		unimplemented!()
	}


// File: define.rs
pub const NUM_CPUS: usize = 32;


}
