use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type IOid = usize;
pub type Pcid = usize;
pub type ProcPtr = usize;
pub type VAddr = usize;
pub type PAddr = usize;
pub type PageMapPtr = usize;
pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;

type PagePtr = usize;

#[repr(align(4096))]
pub struct DeviceTable {
    ar: [usize; 512],
}


// File: util/page_ptr_util_u.rs
//
pub open spec fn MEM_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}
// File: pagetable/pagemap.rs
pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,  // pub level: Ghost<usize>,
    // not used for now.
}

impl PageMap {

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            0 <= index < 512,
    {
        self.spec_seq@[index as int]
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

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            self.kernel_l4_end <= i < 512 ==> self.l4_table@[self.cr3].value()[i].is_empty()
        &&& self.l3_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
    }

    pub open   spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom() + self.l4_table@.dom()
    }

    pub open   spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> {
        self.mapping_4k@
    }

    pub open   spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> {
        self.mapping_2m@
    }

    pub open   spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> {
        self.mapping_1g@
    }

	#[verifier::external_body]
    pub closed   spec fn wf(&self) -> bool {
		unimplemented!()
	}


}



// File: memory_manager/pci_bitmap.rs
pub struct PCIBitMap {
    pub bit_map: [[[u8; 32]; 256]; IOID_MAX],  //32MB
    pub ghost_map: Ghost<Map<(IOid, u8, u8, u8), bool>>,
}

impl PCIBitMap {

    pub open spec fn wf(&self) -> bool {
        &&& (forall|ioid: IOid, bus: u8, dev: u8, fun: u8|
            #![auto]
            0 <= ioid < IOID_MAX && 0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8
                <==> self.ghost_map@.dom().contains((ioid, bus, dev, fun)))
    }

}



// File: memory_manager/root_table.rs
#[repr(align(4096))]
pub struct RootTable {
    root: [usize; 512],
    seq_ar: Ghost<Seq<Seq<Seq<Option<(IOid, usize)>>>>>,
    deviecs: [DeviceTable; 256],
}

impl RootTable {

	#[verifier::external_body]
    pub closed spec fn wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn resolve(&self, bus: u8, dev: u8, fun: u8) -> Option<(IOid, usize)>
        recommends
            self.wf(),
            0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8,
	{
		unimplemented!()
	}

}



// File: memory_manager/spec_impl.rs
pub struct MemoryManager {
    pub kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>,
    pub kernel_entries_ghost: Ghost<Seq<PageEntry>>,
    pub free_pcids: ArrayVec<Pcid, PCID_MAX>,
    pub pcid_to_proc_ptr: Array<Option<ProcPtr>, PCID_MAX>,
    pub page_tables: Array<Option<PageTable>, PCID_MAX>,
    pub page_table_pages: Ghost<Map<PagePtr, Pcid>>,
    pub free_ioids: ArrayVec<IOid, IOID_MAX>,  //actual owners are procs
    pub ioid_to_proc_ptr: Array<Option<ProcPtr>, IOID_MAX>,
    pub iommu_tables: Array<Option<PageTable>, IOID_MAX>,
    pub iommu_table_pages: Ghost<Map<PagePtr, IOid>>,
    pub root_table: RootTable,
    pub root_table_cache: Ghost<Seq<Seq<Seq<Option<(IOid, usize)>>>>>,
    // pub device_table:MarsArray<MarsArray<Option<(u8,u8,u8)>,256>,IOID_MAX>,
    // pub ioid_device_table: Ghost<Seq<Set<(u8,u8,u8)>>>,
    pub pci_bitmap: PCIBitMap,
}

impl MemoryManager {

    pub open spec fn pcid_to_proc_ptr(&self, pcid: Pcid) -> ProcPtr
        recommends
            self.pcid_active(pcid),
    {
        self.pcid_to_proc_ptr@[pcid as int].unwrap()
    }

    pub open spec fn pcid_active(&self, pcid: Pcid) -> bool {
        &&& 0 <= pcid < PCID_MAX
        &&& self.get_free_pcids_as_set().contains(pcid) == false
    }

    pub open spec fn ioid_to_proc_ptr(&self, ioid: IOid) -> ProcPtr
        recommends
            self.ioid_active(ioid),
    {
        self.ioid_to_proc_ptr@[ioid as int].unwrap()
    }

    pub open spec fn ioid_active(&self, ioid: IOid) -> bool {
        &&& 0 <= ioid < IOID_MAX
        &&& self.get_free_ioids_as_set().contains(ioid) == false
    }

    pub open spec fn pagetables_wf(&self) -> bool {
        &&& self.free_pcids.wf()
        &&& self.free_pcids@.no_duplicates()
        &&& forall|i: int|
            #![trigger self.free_pcids@[i]]
            0 <= i < self.free_pcids.len() ==> self.free_pcids@[i] < PCID_MAX
        &&& self.page_tables.wf()
        &&& forall|pcid: Pcid|
            #![trigger self.page_tables@[pcid as int].unwrap()]
            0 <= pcid < PCID_MAX ==> self.page_tables@[pcid as int].is_Some() && (
            self.get_free_pcids_as_set().contains(pcid)
                ==> self.page_tables@[pcid as int].unwrap().is_empty())
                && self.page_tables@[pcid as int].unwrap().wf()
                && self.page_tables@[pcid as int].unwrap().pcid =~= Some(pcid)
                && self.page_tables@[pcid as int].unwrap().page_closure().subset_of(
                self.page_table_pages@.dom(),
            ) && self.page_tables@[pcid as int].unwrap().kernel_entries@
                =~= self.kernel_entries_ghost@
                && self.page_tables@[pcid as int].unwrap().kernel_l4_end
                == KERNEL_MEM_END_L4INDEX
            // for now, we disable hugepages
             && self.page_tables@[pcid as int].unwrap().mapping_2m().dom() == Set::<VAddr>::empty()
                && self.page_tables@[pcid as int].unwrap().mapping_1g().dom() == Set::<
                VAddr,
            >::empty()
        &&& forall|pcid_i: Pcid, pcid_j: Pcid|
            #![trigger self.page_tables@[pcid_i as int].unwrap().page_closure(), self.page_tables@[pcid_j as int].unwrap().page_closure()]
            0 <= pcid_i < PCID_MAX && 0 <= pcid_j < PCID_MAX && pcid_i != pcid_j
                ==> self.page_tables@[pcid_i as int].unwrap().page_closure().disjoint(
                self.page_tables@[pcid_j as int].unwrap().page_closure(),
            )
    }

    pub open spec fn iommutables_wf(&self) -> bool {
        &&& self.free_ioids.wf()
        &&& self.free_ioids@.no_duplicates()
        &&& forall|i: int|
            #![trigger self.free_ioids@[i]]
            0 <= i < self.free_ioids.len() ==> self.free_ioids@[i] < IOID_MAX
        &&& self.iommu_tables.wf()
        &&& forall|ioid: IOid|
            #![trigger self.iommu_tables@[ioid as int].unwrap()]
            0 <= ioid < IOID_MAX ==> self.iommu_tables@[ioid as int].is_Some() && (
            self.get_free_ioids_as_set().contains(ioid)
                ==> self.iommu_tables@[ioid as int].unwrap().is_empty())
                && self.iommu_tables@[ioid as int].unwrap().wf()
                && self.iommu_tables@[ioid as int].unwrap().ioid =~= Some(ioid)
                && self.iommu_tables@[ioid as int].unwrap().page_closure().subset_of(
                self.iommu_table_pages@.dom(),
            ) && self.iommu_tables@[ioid as int].unwrap().kernel_l4_end
                == 0  // for now, we disable hugepages
             && self.iommu_tables@[ioid as int].unwrap().mapping_2m().dom() == Set::<VAddr>::empty()
                && self.iommu_tables@[ioid as int].unwrap().mapping_1g().dom() == Set::<
                VAddr,
            >::empty()
        &&& forall|ioid_i: IOid, ioid_j: IOid|
            #![trigger self.iommu_tables@[ioid_i as int].unwrap().page_closure(), self.iommu_tables@[ioid_j as int].unwrap().page_closure()]
            0 <= ioid_i < IOID_MAX && 0 <= ioid_j < IOID_MAX && ioid_i != ioid_j
                ==> self.iommu_tables@[ioid_i as int].unwrap().page_closure().disjoint(
                self.iommu_tables@[ioid_j as int].unwrap().page_closure(),
            )
    }

    pub open spec fn no_memory_leak(&self) -> bool {
        &&&
        forall|p:PagePtr| 
         #![trigger self.page_table_pages@.dom().contains(p), self.page_table_pages@[p]]
            self.page_table_pages@.dom().contains(p)
            ==>
            0 <= self.page_table_pages@[p] < PCID_MAX
            &&
            self.get_pagetable_page_closure_by_pcid(self.page_table_pages@[p]).contains(p)
        &&&
        forall|p:PagePtr| 
         #![trigger self.iommu_table_pages@.dom().contains(p), self.iommu_table_pages@[p]]
            self.iommu_table_pages@.dom().contains(p)
            ==>
            0 <= self.iommu_table_pages@[p] < IOID_MAX
            &&
            self.get_iommu_table_page_closure_by_ioid(self.iommu_table_pages@[p]).contains(p)
    }

    pub open spec fn pagetable_iommu_table_disjoint(&self) -> bool {
        self.page_table_pages@.dom().disjoint(self.iommu_table_pages@.dom())
    }

    pub open spec fn kernel_entries_wf(&self) -> bool {
        &&& self.kernel_entries.wf()
        &&& self.kernel_entries_ghost@.len() == KERNEL_MEM_END_L4INDEX
        &&& forall|i: int|
            #![trigger self.kernel_entries@[i]]
            #![trigger self.kernel_entries_ghost@[i]]
            0 <= i < KERNEL_MEM_END_L4INDEX ==> self.kernel_entries_ghost@[i] =~= usize2page_entry(
                self.kernel_entries@[i],
            )
    }

    pub open spec fn root_table_wf(&self) -> bool {
        &&& self.root_table.wf()
        &&& self.pci_bitmap.wf()
        // &&& forall|bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8 && self.root_table.resolve(
        //         bus,
        //         dev,
        //         fun,
        //     ).is_Some() ==> 0 <= self.root_table.resolve(bus, dev, fun).get_Some_0().0 < IOID_MAX
        //         && self.get_free_ioids_as_set().contains(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //     ) == false && self.root_table.resolve(bus, dev, fun).get_Some_0().1
        //         == self.get_iommu_table_by_ioid(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //     ).unwrap().cr3
        // &&& forall|bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8 && self.root_table.resolve(
        //         bus,
        //         dev,
        //         fun,
        //     ).is_Some() ==> self.pci_bitmap@[(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //         bus,
        //         dev,
        //         fun,
        //     )] == true
        // &&& forall|ioid: IOid, bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= ioid < IOID_MAX && self.get_free_ioids_as_set().contains(ioid) && 0 <= bus < 256
        //         && 0 <= dev < 32 && 0 <= fun < 8 ==> self.pci_bitmap@[(ioid, bus, dev, fun)]
        //         == false
        // &&
        // self.ioid_device_table@.len() == IOID_MAX
        // &&
        // forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.ioid_device_table@[ioid as int].finite()
        // &&
        // forall|ioid:Pcid, i:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && self.device_table@[ioid as int]@[i].is_Some() ==>
        //     (
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().0<256
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().1<32
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().2<8
        //         // &&
        //         // self.ioid_device_table@[ioid as int].contains(self.device_table@[ioid as int]@[i].get_Some_0())
        //     )
        // &&
        // forall|ioid:Pcid, dev:(u8,u8,u8)| #![auto] 0<=ioid<IOID_MAX && self.ioid_device_table@[ioid as int].contains(dev) ==>
        //     (
        //         0<=dev.0<256
        //         &&
        //         0<=dev.1<32
        //         &&
        //         0<=dev.2<8
        //         &&
        //         exists|_ioid:Pcid, _i:int| #![auto] 0<=_ioid<IOID_MAX && 0<=_i<256 && self.device_table@[ioid as int]@[i].is_Some() && dev =~= self.device_table@[ioid as int]@[i].get_Some_0()
        //     )
        // &&
        // forall|ioid:Pcid, i:int, j:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && 0<=j<256 && self.device_table@[ioid as int]@[i].is_Some() && self.device_table@[ioid as int]@[j].is_Some()==>
        // (
        //     self.device_table@[ioid as int]@[i].get_Some_0() =~= self.device_table@[ioid as int]@[j].get_Some_0() == false
        // )
        // &&
        // forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table.resolve(bus,dev,fun).is_Some() ==>
        //     (
        //         exists|i:int|#![auto]  0<i<256 && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].is_Some()
        //             && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].get_Some_0() =~= (bus,dev,fun)
        //     )

    }

    pub open spec fn root_table_cache_wf(&self) -> bool {
        &&& self.root_table_cache@.len() == 256
        &&& forall|bus: u8|
            #![auto]
            0 <= bus < 256 ==> self.root_table_cache@[bus as int].len() == 32
        &&& forall|bus: u8, dev: u8|
            #![auto]
            0 <= bus < 256 && 0 <= dev < 32 ==> self.root_table_cache@[bus as int][dev as int].len()
                == 8
        &&& forall|bus: u8, dev: u8, fun: u8|
            #![auto]
            0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8
                && self.root_table_cache@[bus as int][dev as int][fun as int].is_Some()
                ==> self.root_table_cache@[bus as int][dev as int][fun as int]
                =~= self.root_table.resolve(bus, dev, fun)
    }

    pub open spec fn get_pagetable_by_pcid(&self, pcid: Pcid) -> Option<PageTable>
        recommends
            0 <= pcid < PCID_MAX,
    {
        self.page_tables@[pcid as int]
    }

    pub open spec fn get_pagetable_mapping_by_pcid(&self, pcid: Pcid) -> Map<VAddr, MapEntry>
        recommends
            0 <= pcid < PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables@[pcid as int].unwrap().mapping_4k()
    }

    pub open spec fn get_pagetable_page_closure_by_pcid(&self, pcid: Pcid) -> Set<PagePtr>
        recommends
            0 <= pcid < PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables[pcid as int].unwrap().page_closure()
    }

    pub open spec fn get_free_pcids_as_set(&self) -> Set<IOid> {
        self.free_pcids@.to_set()
    }

    pub open spec fn get_free_ioids_as_set(&self) -> Set<IOid> {
        self.free_ioids@.to_set()
    }

    pub open spec fn get_iommu_table_by_ioid(&self, ioid: IOid) -> Option<PageTable>
        recommends
            0 <= ioid < IOID_MAX,
    {
        self.iommu_tables[ioid as int]
    }

    pub open spec fn get_iommu_table_mapping_by_ioid(&self, ioid: IOid) -> Map<VAddr, MapEntry>
        recommends
            0 <= ioid < IOID_MAX,
            self.get_iommu_table_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().mapping_4k()
    }

    pub open spec fn get_iommu_table_page_closure_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends
            0 <= ioid < IOID_MAX,
            self.get_iommu_table_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().page_closure()
    }

    pub open spec fn pcid_to_proc_wf(&self) -> bool {
        &&& self.pcid_to_proc_ptr.wf()
        &&& forall|pcid: Pcid|
            #![trigger self.pcid_active(pcid)]
            #![trigger self.pcid_to_proc_ptr@[pcid as int]]
            0 <= pcid < PCID_MAX ==> self.pcid_active(pcid)
                == self.pcid_to_proc_ptr@[pcid as int].is_Some()
    }

    pub open spec fn ioid_to_proc_wf(&self) -> bool {
        &&& self.ioid_to_proc_ptr.wf()
        &&& forall|ioid: IOid|
            #![trigger self.ioid_active(ioid)]
            #![trigger self.ioid_to_proc_ptr@[ioid as int]]
            0 <= ioid < IOID_MAX ==> self.ioid_active(ioid)
                == self.ioid_to_proc_ptr@[ioid as int].is_Some()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.pagetables_wf()
        &&& self.iommutables_wf()
        &&& self.pagetable_iommu_table_disjoint()
        &&& self.root_table_wf()
        &&& self.root_table_cache_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_to_proc_wf()
        &&& self.ioid_to_proc_wf()
        &&& self.no_memory_leak()
    }

    pub fn alloc_page_table(&mut self, new_proc_ptr: ProcPtr) -> (ret: Pcid)
        requires
            old(self).wf(),
            old(self).free_pcids.len() > 0,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            // self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom(),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                p != ret ==> self.pcid_active(p) == old(self).pcid_active(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) && p != ret ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) && p != ret ==> old(self).pcid_to_proc_ptr(p)
                    == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            self.pcid_to_proc_ptr(ret) == new_proc_ptr,
            self.pcid_active(ret),
            !old(self).pcid_active(ret),
            self.get_pagetable_mapping_by_pcid(ret).dom() == Set::<PagePtr>::empty(),
    {
        let new_pcid = *self.free_pcids.pop_unique();
        self.pcid_to_proc_ptr.set(new_pcid, Some(new_proc_ptr));
        assert(self.pagetables_wf()) by {
            seq_pop_unique_lemma::<Pcid>();
            seq_update_lemma::<Option<PageTable>>();
            assert(forall|pcid: Pcid|
                pcid != new_pcid ==> old(self).get_free_pcids_as_set().contains(pcid)
                    == self.get_free_pcids_as_set().contains(pcid));
        };
        assert(self.iommutables_wf());
        assert(self.pagetable_iommu_table_disjoint());
        assert(self.root_table_wf());
        assert(self.root_table_cache_wf());
        assert(self.kernel_entries_wf());
        assert(self.pcid_to_proc_wf()) by {
            set_lemma::<Pcid>();
            seq_pop_unique_lemma::<Pcid>();
            seq_update_lemma::<ProcPtr>();
            //    assert(
            //         forall|pcid:Pcid|
            //         #![trigger self.pcid_active(pcid)]
            //         #![trigger self.pcid_to_proc_ptr@[pcid as int]]
            //         pcid != new_pcid ==>
            //         self.pcid_active(pcid) == self.pcid_to_proc_ptr@[pcid as int].is_Some()
            //    );
        };
        assert(self.ioid_to_proc_wf());
        new_pcid
    }


}



// File: array.rs
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends self.seq@.len() == N,
                   0 <= i < N,
    {
        self.seq@[i]
    }

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

}


impl<A, const N: usize> Array<A, N> {

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, out: A)
        requires
            0 <= i < N,
            old(self).wf(),
        ensures
            self.seq@ =~= old(self).seq@.update(i as int, out),
            self.wf(),
	{
		unimplemented!()
	}

}



// File: array_vec.rs
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T: Copy, const N: usize> ArrayVec<T, N> {
    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_len(),
    {
        unimplemented!()
    }

    pub open spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        unimplemented!()
    }

    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

    pub open spec fn view(&self) -> Seq<T>
        recommends self.wf(),
    {
        self.view_until(self.len() as nat)
    }

    pub open spec fn view_until(&self, len: nat) -> Seq<T>
        recommends
            0 <= len <= self.len() as nat,
    {
        self.data@.subrange(0,len as int)
    }

    pub open spec fn wf(&self) -> bool {
        &&& 0 <= N <= usize::MAX
        &&& self.len() <= self.capacity()
        &&& self.data.wf()
    }

	#[verifier::external_body]
    pub fn pop_unique(&mut self) -> (ret: &T)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
            old(self)@.no_duplicates(),
        ensures
            self.wf(),
            self@.len() == old(self)@.len() - 1,
            ret == old(self)@[old(self).len() - 1],
            self@ =~= old(self)@.drop_last(),
            self@.no_duplicates(),
	{
		unimplemented!()
	}

}



// File: lemma/lemma_t.rs
#[verifier(external_body)]
pub proof fn set_lemma<A>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, e: A|
            (s1 + s2).insert(e) == s1 + (s2.insert(e)) && s1 + (s2.insert(e)) == s2 + (s1.insert(e))
                && (s1 + s2).insert(e) == s2 + (s1.insert(e)) && (!(s1 + s2).contains(e)
                <==> !s1.contains(e) && !s2.contains(
                e,
            )),
// forall|s1:Set<A>, s2:Set<A>, s3:Set<A>, s4:Set<A>, e:A|
//     (!(s1 + s2 + s3 + s4).contains(e)) <==> (!s1.contains(e) && !s2.contains(e) && !s3.contains(e) && !s4.contains(e))

{
}



// File: lemma/lemma_u.rs
	#[verifier::external_body]
pub proof fn seq_pop_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int|
            s.len() >= 1 && s.no_duplicates() && 0 <= i < s.len() - 1 ==> !s.drop_last().contains(s[s.len() - 1]) && s.drop_last()[i] == s[i],
        forall|s: Seq<A>, v: A|
            s.len() >= 1 && s.no_duplicates() && s[s.len() - 1] == v ==> s.drop_last().to_set().contains(v)
                == false,
        forall|s: Seq<A>, v: A|
            s.len() >= 1 && s.no_duplicates() && s[s.len() - 1] != v ==> s.drop_last().to_set().contains(v)
                == s.to_set().contains(v),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn seq_update_lemma<A>()
    ensures
        forall|s: Seq<A>, i: int, j: int, v: A|
            0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, v)[i] == s[i]
                && s.update(j, v)[j] == v,
        forall|s: Seq<A>, i: int, v: A|
            #![trigger s.update(i,v)[i]]
            0 <= i < s.len() ==> s.update(i, v)[i] == v,
	{
		unimplemented!()
	}


// File: define.rs
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

pub const PCID_MAX: usize = 4096;

pub const IOID_MAX: usize = 4096;

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

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
