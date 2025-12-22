use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type CpuId = usize;

pub type PagePtr = usize;

pub type VAddr = usize;

pub type PAddr = usize;

pub type PageMapPtr = usize;

pub type Pcid = usize;

pub type IOid = usize;

pub type L4Index = usize;

pub type L3Index = usize;

pub type L2Index = usize;

pub type L1Index = usize;

pub const MEM_1g_MASK: u64 = 0x0000_fffc_0000_0000;


// File: pagetable/pagemap.rs
pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,  // pub level: Ghost<usize>,
    // not used for now.
}

impl PageMap {

    pub open spec fn wf(&self) -> bool {
        &&& self.ar.wf()
        &&& self.spec_seq@.len() == 512
        &&& forall|i: int|
            #![trigger usize2page_entry(self.ar@[i])]
            0 <= i < 512 ==> (usize2page_entry(self.ar@[i])
                =~= self.spec_seq@[i])
            // &&&
            // forall|i:int|
            //     #![trigger usize2page_entry(self.ar@[i]).is_empty()]
            //     0<=i<512 ==> (usize2page_entry(self.ar@[i]).is_empty() <==> self.ar@[i] == 0)

    }

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            0 <= index < 512,
    {
        self.spec_seq@[index as int]
    }

	#[verifier::external_body]
    pub fn get(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
        ensures
            ret =~= self[index],
	{
		unimplemented!()
	}

}



// File: pagetable/entry.rs
#[derive(Clone,Debug)]
pub struct PageEntryPerm {
    pub present: bool,
    pub ps: bool,
    pub write: bool,
    pub execute_disable: bool,
    pub user: bool,
}

#[derive(Clone,Debug)]
pub struct PageEntry {
    pub addr: PAddr,
    pub perm: PageEntryPerm,
    // pub ps: bool,
}

impl PageEntry {

    pub open spec fn is_empty(&self) -> bool {
        &&& self.addr == 0
        &&& self.perm.present == false
        &&& self.perm.ps == false
        &&& self.perm.write == false
        &&& self.perm.execute_disable == false
        &&& self.perm.user == false
    }

}


pub struct MapEntry {
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
}

pub open spec fn usize2present(v: usize) -> bool {
    (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0
}

pub open spec fn usize2ps(v: usize) -> bool {
    (v & PAGE_ENTRY_PS_MASK as usize) != 0
}

pub open spec fn usize2write(v: usize) -> bool {
    (v & PAGE_ENTRY_WRITE_MASK as usize) != 0
}

pub open spec fn usize2execute_disable(v: usize) -> bool {
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0
}

pub open spec fn usize2user(v: usize) -> bool {
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
}

pub open spec fn spec_usize2page_entry_perm(v: usize) -> PageEntryPerm {
    PageEntryPerm {
        present: usize2present(v),
        ps: usize2ps(v),
        write: usize2write(v),
        execute_disable: usize2execute_disable(v),
        user: usize2user(v),
    }
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
pub fn usize2page_entry_perm(v: usize) -> (ret: PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v),
        v == 0 ==> ret.present == false && ret.ps == false && ret.write == false
            && ret.execute_disable == false && ret.user == false,
{
    unimplemented!()
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_usize2page_entry))]
pub fn usize2page_entry(v: usize) -> (ret: PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v),
        v == 0 ==> ret.addr == 0 && ret.perm.present == false && ret.perm.ps == false
            && ret.perm.write == false && ret.perm.execute_disable == false && ret.perm.user
            == false,
{
    unimplemented!()
}


pub open spec fn spec_usize2page_entry(v: usize) -> PageEntry {
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

pub open spec fn spec_usize2pa(v: usize) -> PAddr {
    v & MEM_MASK as usize
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v: usize) -> (ret: PAddr)
    ensures
        ret =~= spec_usize2pa(v),
        MEM_valid(ret),
{
    unimplemented!()
}


// File: pagetable/pagetable_spec.rs
pub struct PageTable {
    pub cr3: PageMapPtr,
    pub pcid: Option<Pcid>,
    pub ioid: Option<IOid>,
    pub kernel_l4_end: usize,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index)>>,
    pub l2_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index, L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub mapping_4k: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_2m: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_1g: Ghost<Map<VAddr, MapEntry>>,
    pub kernel_entries: Ghost<Seq<PageEntry>>,
    pub tlb_mapping_4k: Ghost<Seq<Map<VAddr, MapEntry>>>,
    pub tlb_mapping_2m: Ghost<Seq<Map<VAddr, MapEntry>>>,
    pub tlb_mapping_1g: Ghost<Seq<Map<VAddr, MapEntry>>>,
}

impl PageTable {

    pub open   spec fn pcid_ioid_wf(&self) -> bool {
        self.pcid.is_Some() != self.ioid.is_Some()
    }

    pub open   spec fn tlb_wf(&self) -> bool {
        &&& self.tlb_mapping_4k@.len() == NUM_CPUS
        &&& self.tlb_mapping_2m@.len() == NUM_CPUS
        &&& self.tlb_mapping_1g@.len() == NUM_CPUS
    }

    pub open   spec fn tlb_submap_of_mapping(&self) -> bool {
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> self.tlb_mapping_4k@[cpu_id as int].submap_of(
                self.mapping_4k@,
            ) && self.tlb_mapping_2m@[cpu_id as int].submap_of(self.mapping_2m@)
                && self.tlb_mapping_1g@[cpu_id as int].submap_of(self.mapping_1g@)
    }

    pub open   spec fn wf_l4(&self) -> bool {
        // &&&
        // self.cr3 != 0
        &&& self.l4_table@.dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table@[self.cr3].addr()
        &&& self.l4_table@[self.cr3].is_init()
        &&& self.l4_table@[self.cr3].value().wf()
        //L4 table only maps to L3
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]

            #![trigger self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            #![trigger self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
                == false && self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
                == false && self.cr3
                != self.l4_table@[self.cr3].value()[i].addr
        // no self mapping
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]

            #![trigger self.l4_table@[self.cr3].value()[i].addr]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.cr3
                != self.l4_table@[self.cr3].value()[i].addr
        //all l4 points to valid l3 tables
        &&& forall|i: L4Index|
            #![trigger self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                && !self.l4_table@[self.cr3].value()[i].perm.ps ==> self.l3_tables@.dom().contains(
                self.l4_table@[self.cr3].value()[i].addr,
            )
            //no hugepage in L4 (hardware limit)
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.ps]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> !self.l4_table@[self.cr3].value()[i].perm.ps
    }

    pub open   spec fn disjoint_l4(&self) -> bool {
        &&& forall|i: L4Index, j: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present]

            #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present, self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[j].addr]
            i != j && self.kernel_l4_end <= i < 512
                && self.l4_table@[self.cr3].value()[i].perm.present && self.kernel_l4_end <= j < 512
                && self.l4_table@[self.cr3].value()[j].perm.present
                ==> self.l4_table@[self.cr3].value()[i].addr
                != self.l4_table@[self.cr3].value()[j].addr
    }

    pub open   spec fn wf_l3(&self) -> bool {
        // &&&
        // self.l3_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].addr()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].is_init()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].value().wf()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].value().wf()
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_rev_map@.dom().contains(p)]
            #![trigger self.l3_rev_map@[p]]
            self.l3_tables@.dom().contains(p) ==> self.kernel_l4_end <= self.l3_rev_map@[p] < 512
                && self.l3_rev_map@.dom().contains(p) && self.spec_resolve_mapping_l4(
                self.l3_rev_map@[p],
            ).is_Some() && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).get_Some_0().addr
                == p
            //L3 tables does not map to L4 or L1
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present ==> self.l3_tables@.dom().contains(
                self.l3_tables@[p].value()[i].addr,
            ) == false && self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l3_tables@[p].value()[i].addr
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
        // #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]

            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps ==> self.l2_tables@.dom().contains(
                self.l3_tables@[p].value()[i].addr,
            )
    }

    pub open   spec fn disjoint_l3(&self) -> bool {
            //L3 tables unique within
        &&& forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
            // #![trigger self.l3_tables@[p].value()[l3i].perm.present, self.l3_tables@[p].value()[l3j].perm.present]
            #![trigger self.l3_tables@[p].value()[l3i].addr,
                self.l3_tables@[p].value()[l3j].addr]
            self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512
                && self.l3_tables@[p].value()[l3i].perm.present
                && self.l3_tables@[p].value()[l3j].perm.present
                && !self.l3_tables@[p].value()[l3i].perm.ps
                && !self.l3_tables@[p].value()[l3j].perm.ps ==> self.l3_tables@[p].value()[l3i].addr
                != self.l3_tables@[p].value()[l3j].addr
            //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            // #![trigger self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pi].value()[l3i].addr,
                self.l3_tables@[pj].value()[l3j].addr]
            pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj)
                && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present
                && self.l3_tables@[pj].value()[l3j].perm.present
                && !self.l3_tables@[pi].value()[l3i].perm.ps
                && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==> self.l3_tables@[pi].value()[l3i].addr
                != self.l3_tables@[pj].value()[l3j].addr
    }

    pub open   spec fn wf_l2(&self) -> bool {
        // &&&
        // self.l2_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].addr()]
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].is_init()]
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].value().wf()]
            self.l2_tables@.dom().contains(p)
                ==> self.l2_tables@[p].value().wf()
        // all l2 tables exist in l3 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_rev_map@[p]]
            #![trigger self.l2_rev_map@.dom().contains(p)]
            self.l2_tables@.dom().contains(p) ==> self.l2_rev_map@.dom().contains(p)
                && self.kernel_l4_end <= self.l2_rev_map@[p].0 < 512 && 0 <= self.l2_rev_map@[p].1
                < 512 && self.spec_resolve_mapping_l3(
                self.l2_rev_map@[p].0,
                self.l2_rev_map@[p].1,
            ).is_Some() && self.spec_resolve_mapping_l3(
                self.l2_rev_map@[p].0,
                self.l2_rev_map@[p].1,
            ).get_Some_0().addr == p
            // L2 does not map to L4, L3, or self
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present ==> self.l2_tables@.dom().contains(
                self.l2_tables@[p].value()[i].addr,
            ) == false && self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l2_tables@[p].value()[i].addr
        // all l2 points to valid l1 tables
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].perm.ps]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && !self.l2_tables@[p].value()[i].perm.ps ==> self.l1_tables@.dom().contains(
                self.l2_tables@[p].value()[i].addr,
            )
    }

    pub open   spec fn disjoint_l2(&self) -> bool {
            // L2 mappings are unique within
        // &&& forall|p: PageMapPtr, l2i: L2Index, l2j: L2Index|
        //     // #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[l2i].perm.present, self.l2_tables@[p].value()[l2j].perm.present, self.l2_tables@[p].value()[l2i].perm.ps, self.l2_tables@[p].value()[l2j].perm.ps]
        //     self.l2_tables@.dom().contains(p) && l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512
        //         && self.l2_tables@[p].value()[l2i].perm.present
        //         && self.l2_tables@[p].value()[l2j].perm.present
        //         && !self.l2_tables@[p].value()[l2i].perm.ps
        //         && !self.l2_tables@[p].value()[l2j].perm.ps ==> self.l2_tables@[p].value()[l2i].addr
        //         != self.l2_tables@[p].value()[l2j].addr
            // L2 mappings are unique
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
            // #![trigger self.l2_tables@.dom().contains(pi), self.l2_tables@.dom().contains(pj),
            //     self.l2_tables@[pi].value()[l2i].perm.present, self.l2_tables@[pj].value()[l2j].perm.present,
            //     self.l2_tables@[pi].value()[l2i].perm.ps, self.l2_tables@[pj].value()[l2j].perm.ps, 
            //     self.l2_tables@[pi].value()[l2i].addr,
            //     self.l2_tables@[pj].value()[l2j].addr]
            #![trigger self.l2_tables@[pi].value()[l2i].addr, self.l2_tables@[pj].value()[l2j].addr]
            self.l2_tables@.dom().contains(pi) && self.l2_tables@.dom().contains(pj)
                && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pi].value()[l2i].perm.present
                && self.l2_tables@[pj].value()[l2j].perm.present
                && !self.l2_tables@[pi].value()[l2i].perm.ps
                && !self.l2_tables@[pj].value()[l2j].perm.ps
                ==> 
                ( pi != pj ==> self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr)
                &&
                ( pi == pj && l2i != l2j ==> self.l2_tables@[pi].value()[l2i].addr != self.l2_tables@[pj].value()[l2j].addr)
    }

    pub open   spec fn wf_l1(&self) -> bool {
        // &&&
        // self.l1_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].addr()]
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].is_init()]
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].value().wf()]
            self.l1_tables@.dom().contains(p)
                ==> self.l1_tables@[p].value().wf()
        // all l1 tables exist in l2 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_rev_map@.dom().contains(p)]
            #![trigger self.l1_rev_map@[p]]
            self.l1_tables@.dom().contains(p) ==> self.l1_rev_map@.dom().contains(p)
                && self.kernel_l4_end <= self.l1_rev_map@[p].0 < 512 && 0 <= self.l1_rev_map@[p].1
                < 512 && 0 <= self.l1_rev_map@[p].2 < 512 && self.spec_resolve_mapping_l2(
                self.l1_rev_map@[p].0,
                self.l1_rev_map@[p].1,
                self.l1_rev_map@[p].2,
            ).is_Some() && self.spec_resolve_mapping_l2(
                self.l1_rev_map@[p].0,
                self.l1_rev_map@[p].1,
                self.l1_rev_map@[p].2,
            ).get_Some_0().addr == p
            // no l1 tables map to other levels
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)]
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)]
            #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present ==> self.l2_tables@.dom().contains(
                self.l1_tables@[p].value()[i].addr,
            ) == false && self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l1_tables@[p].value()[i].addr
        // no hugepage in l1
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm.ps]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> !self.l1_tables@[p].value()[i].perm.ps
    }

    pub open   spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm, self.l4_table@[self.cr3].value()[i].perm.user]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm, self.l3_tables@[p].value()[i].perm.user]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                ==> self.l3_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].perm, self.l2_tables@[p].value()[i].perm.user]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                ==> self.l2_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm, self.l1_tables@[p].value()[i].perm.user]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> self.l1_tables@[p].value()[i].perm.user
    }

    pub open   spec fn present_or_zero(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].is_empty()]
            self.kernel_l4_end <= i < 512 && !self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].is_empty()]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l3_tables@[p].value()[i].perm.present
                ==> self.l3_tables@[p].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].is_empty()]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l2_tables@[p].value()[i].perm.present
                ==> self.l2_tables@[p].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].is_empty()]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l1_tables@[p].value()[i].perm.present
                ==> self.l1_tables@[p].value()[i].is_empty()
    }

    pub open   spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm]
            // #![trigger self.l4_table@[self.cr3].value()[i].perm.execute_disable]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.write
                && !self.l4_table@[self.cr3].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm]
            // #![trigger self.l3_tables@[p].value()[i].perm.execute_disable]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps
                ==> self.l3_tables@[p].value()[i].perm.write
                && !self.l3_tables@[p].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger  self.l2_tables@[p].value()[i].perm]
            // #![trigger self.l2_tables@[p].value()[i].perm.execute_disable]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && !self.l2_tables@[p].value()[i].perm.ps
                ==> self.l2_tables@[p].value()[i].perm.write
                && !self.l2_tables@[p].value()[i].perm.execute_disable
    }

    pub open   spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l3_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l2_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l1_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&&
        self.l4_table@.dom().disjoint(self.l3_tables@.dom())
        &&&
        self.l4_table@.dom().disjoint(self.l2_tables@.dom())
        &&&
        self.l4_table@.dom().disjoint(self.l1_tables@.dom())
        &&&
        self.l3_tables@.dom().disjoint(self.l2_tables@.dom())
        &&&
        self.l3_tables@.dom().disjoint(self.l1_tables@.dom())
        &&&
        self.l2_tables@.dom().disjoint(self.l1_tables@.dom())
    }

    pub open   spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
    {
        if self.l4_table@[self.cr3].value()[l4i].perm.present || l4i < self.kernel_l4_end {
            Some(self.l4_table@[self.cr3].value()[l4i])
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<
        PageEntry,
    >
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        } else if !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.present
            || !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.ps {
            None
        } else {
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open   spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<
        PageEntry,
    >
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        } else if !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.present
            || self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.ps {
            None
        } else {
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open   spec fn spec_resolve_mapping_2m_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i).is_None() {
            None
        } else if !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.present
            || !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.ps {
            None
        } else {
            Some(
                self.l2_tables@[self.spec_resolve_mapping_l3(
                    l4i,
                    l3i,
                ).get_Some_0().addr].value()[l2i],
            )
        }
    }

    pub open   spec fn spec_resolve_mapping_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i).is_None() {
            None
        } else if !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.present
            || self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.ps {
            None
        } else {
            Some(
                self.l2_tables@[self.spec_resolve_mapping_l3(
                    l4i,
                    l3i,
                ).get_Some_0().addr].value()[l2i],
            )
        }
    }

    pub open   spec fn spec_resolve_mapping_4k_l1(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L1Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
    {
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_None() {
            None
        } else if !self.l1_tables@[self.spec_resolve_mapping_l2(
            l4i,
            l3i,
            l2i,
        ).get_Some_0().addr].value()[l1i].perm.present {
            None
        } else {
            Some(
                self.l1_tables@[self.spec_resolve_mapping_l2(
                    l4i,
                    l3i,
                    l2i,
                ).get_Some_0().addr].value()[l1i],
            )
        }

    }

    pub open   spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
            self.mapping_4k@.dom().contains(va) ==> va_4k_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                ==> self.mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                && self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some()
                ==> self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].addr
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).get_Some_0().addr
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].write
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).get_Some_0().perm.write
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].execute_disable
                == self.spec_resolve_mapping_4k_l1(
                l4i,
                l3i,
                l2i,
                l1i,
            ).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_4k@.dom().contains(va), page_ptr_valid(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) ==> page_ptr_valid(self.mapping_4k@[va].addr)
    }

    pub open   spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
            self.mapping_2m@.dom().contains(va) ==> va_2m_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                ==> self.mapping_2m@.dom().contains(spec_index2va((l4i, l3i, l2i, 0)))
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                && self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).is_Some()
                ==> self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].addr
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().addr
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].write
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().perm.write
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].execute_disable
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_2m@.dom().contains(va), page_ptr_2m_valid(self.mapping_2m@[va].addr)]
            self.mapping_2m@.dom().contains(va) ==> page_ptr_2m_valid(self.mapping_2m@[va].addr)
    }

    pub open   spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
            self.mapping_1g@.dom().contains(va) ==> va_1g_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 ==> self.mapping_1g@.dom().contains(
                spec_index2va((l4i, l3i, 0, 0)),
            ) == self.spec_resolve_mapping_1g_l3(l4i, l3i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ).is_Some() ==> self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].addr
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().addr
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].write
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().perm.write
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].execute_disable
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_1g@.dom().contains(va), page_ptr_1g_valid(self.mapping_1g@[va].addr)]
            self.mapping_1g@.dom().contains(va) ==> page_ptr_1g_valid(self.mapping_1g@[va].addr)
    }

    pub open   spec fn kernel_entries_wf(&self) -> bool {
        &&& self.kernel_l4_end < 512
        &&& self.kernel_entries@.len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries@[i as int]]
            0 <= i < self.kernel_l4_end ==> self.kernel_entries@[i as int]
                == self.l4_table@[self.cr3].value()[i]
    }

	#[verifier::external_body]
    pub closed   spec fn wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed   spec fn levels_wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed   spec fn disjoint_wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed   spec fn mappings_wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed   spec fn additonal_wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub broadcast proof fn reveal_page_table_wf(&self)
        ensures
            #[trigger] self.wf() <==> {
                &&& self.levels_wf()
                &&& self.disjoint_wf()
                &&& self.mappings_wf()
                &&& self.additonal_wf()
            },
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub broadcast proof fn reveal_page_table_levels_wf(&self)
        ensures
            #[trigger] self.levels_wf() <==> {
                &&& self.wf_l4()
                &&& self.wf_l3()
                &&& self.wf_l2()
                &&& self.wf_l1()
        },
	{
		unimplemented!()
	}

	#[verifier::external_body]
     pub broadcast proof fn reveal_page_table_disjoint_wf(&self)
        ensures
            #[trigger] self.disjoint_wf() <==> {
                &&& self.disjoint_l4()
                &&& self.disjoint_l3()
                &&& self.disjoint_l2()
     },
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub broadcast proof fn reveal_page_table_mappings_wf(&self)
        ensures
            #[trigger] self.mappings_wf() <==> {
                &&& self.wf_mapping_4k()
                &&& self.wf_mapping_2m()
                &&& self.wf_mapping_1g()
    },
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub broadcast proof fn reveal_page_table_addtional_wf(&self)
        ensures
            #[trigger] self.additonal_wf() <==> {
                &&& self.user_only()
                &&& self.rwx_upper_level_entries()
                &&& self.present_or_zero()
                // &&&
                // self.no_self_mapping()
                &&& self.table_pages_wf()
                &&& self.kernel_entries_wf()
                &&& self.pcid_ioid_wf()
                &&& self.tlb_wf()
                &&& self.tlb_submap_of_mapping()
    },
	{
		unimplemented!()
	}

}



// File: array.rs
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

}



// File: pagetable/pagetable_impl_base.rs
impl PageTable {

    pub fn get_entry_1g_l3(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) =~= ret,
    {
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        broadcast use PageTable::reveal_page_table_disjoint_wf;
        broadcast use PageTable::reveal_page_table_mappings_wf;
        broadcast use PageTable::reveal_page_table_addtional_wf;

        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.present && l3_entry.perm.ps {
            Some(l3_entry)
        } else {
            None
        }
    }

}



// File: util/page_ptr_util_u.rs
pub open spec fn MEM_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}


pub open spec fn page_ptr_valid(ptr: usize) -> bool {
    &&& ptr % 0x1000 == 0
    &&& ptr / 0x1000 < NUM_PAGES
}

pub open spec fn page_ptr_2m_valid(ptr: usize) -> bool {
    ((ptr % (0x200000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

pub open spec fn page_ptr_1g_valid(ptr: usize) -> bool {
    ((ptr % (0x40000000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4k_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_va_4k_valid))]
pub fn va_4k_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_4k_valid(va),
{
    unimplemented!()
}

pub open spec fn spec_va_2m_valid(va: usize) -> bool {
    (va & (!MEM_2m_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_2m_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_2m_valid(va),
{
    unimplemented!()
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_1g_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_1g_valid(va),
{
    unimplemented!()
}

pub open spec fn spec_va_1g_valid(va: usize) -> bool {
    (va & (!MEM_1g_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_index2va(i: (L4Index, L3Index, L2Index, L1Index)) -> usize
    recommends
        i.0 <= 0x1ff,
        i.1 <= 0x1ff,
        i.2 <= 0x1ff,
        i.3 <= 0x1ff,
{
    (i.0 as usize) << 39 & (i.1 as usize) << 30 & (i.2 as usize) << 21 & (i.3 as usize) << 12
}


// File: define.rs
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

pub const NUM_PAGES: usize = 2 * 1024 * 1024;

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

pub const NUM_CPUS: usize = 32;

pub const PAGE_ENTRY_WRITE_SHIFT: u64 = 1;

pub const PAGE_ENTRY_USER_SHIFT: u64 = 2;

pub const PAGE_ENTRY_PS_SHIFT: u64 = 7;

pub const PAGE_ENTRY_EXECUTE_SHIFT: u64 = 63;

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << PAGE_ENTRY_WRITE_SHIFT;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << PAGE_ENTRY_USER_SHIFT;

pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << PAGE_ENTRY_PS_SHIFT;

pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << PAGE_ENTRY_EXECUTE_SHIFT;


}
