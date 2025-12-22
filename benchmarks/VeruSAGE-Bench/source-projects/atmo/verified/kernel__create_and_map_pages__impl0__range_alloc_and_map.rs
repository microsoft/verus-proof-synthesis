use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type IOid = usize;
pub type CpuId = usize;
pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointIdx = usize;
pub type EndpointPtr = usize;
pub type ContainerPtr = usize;
pub type PagePtr = usize;
pub type PageMapPtr = usize;
pub type Pcid = usize;
pub type PAddr = usize;
pub type VAddr = usize;
pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;
pub type SLLIndex = i32;
pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;
pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;
pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;

pub const NUM_CPUS: usize = 32;
pub const MAX_NUM_THREADS_PER_PROC: usize = 128;
pub const MAX_NUM_THREADS_PER_ENDPOINT: usize = 128;
pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 128;
pub const CONTAINER_PROC_LIST_LEN: usize = 10;
pub const CONTAINER_CHILD_LIST_LEN: usize = 10;
pub const PROC_CHILD_LIST_LEN: usize = 10;
pub const CONTAINER_ENDPOINT_LIST_LEN: usize = 10;
pub const MAX_CONTAINER_SCHEDULER_LEN: usize = 10;
pub const PAGE_SZ_4k: usize = 1usize << 12;
pub const PAGE_SZ_2m: usize = 1usize << 21;
pub const PAGE_SZ_1g: usize = 1usize << 30;


#[repr(align(4096))]
pub struct DeviceTable {
    ar: [usize; 512],
}

pub open spec fn MEM_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}


// File: slinkedlist/node.rs
#[derive(Debug)]
pub struct Node<T> {
    pub value: Option<T>,
    pub next: SLLIndex,
    pub prev: SLLIndex,
}


// File: slinkedlist/spec_impl_u.rs
#[verifier::reject_recursive_types(T)]
pub struct StaticLinkedList<T, const N: usize> {
    pub ar: [Node<T>; N],
    pub spec_seq: Ghost<Seq<T>>,
    pub value_list: Ghost<Seq<SLLIndex>>,
    pub value_list_head: SLLIndex,
    pub value_list_tail: SLLIndex,
    pub value_list_len: usize,
    pub free_list: Ghost<Seq<SLLIndex>>,
    pub free_list_head: SLLIndex,
    pub free_list_tail: SLLIndex,
    pub free_list_len: usize,
    pub size: usize,
    pub arr_seq: Ghost<Seq<Node<T>>>,
}

impl<T, const N: usize> StaticLinkedList<T, N> {

    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.value_list_len,
            self.wf() ==> l == self.len(),
            self.wf() ==> l == self@.len(),
    {
        unimplemented!()
    }

    pub open spec fn unique(&self) -> bool {
        forall|i: int, j: int|
            #![trigger self.spec_seq@[i], self.spec_seq@[j]]
            0 <= i < self.len() && 0 <= j < self.len() && i != j ==> self.spec_seq@[i]
                != self.spec_seq@[j]
    }

    pub open spec fn view(&self) -> Seq<T> {
        self.spec_seq@
    }

	#[verifier::external_body]
    pub closed spec fn get_node_ref(&self, v: T) -> SLLIndex
        recommends
            self.wf(),
            self@.contains(v),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub closed spec fn wf(&self) -> bool {
		unimplemented!()
	}


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

pub open spec fn spec_usize2page_entry(v: usize) -> PageEntry {
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

pub open spec fn spec_usize2pa(v: usize) -> PAddr {
    v & MEM_MASK as usize
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



// File: allocator/page.rs
#[derive(Clone, Copy)]
pub struct Page {
    pub addr: PagePtr,
    pub state: PageState,
    pub is_io_page: bool,
    pub rev_pointer: SLLIndex,
    pub ref_count: usize,
    pub owning_container: Option<ContainerPtr>,
    pub mappings: Ghost<Set<(Pcid, VAddr)>>,
    pub io_mappings: Ghost<Set<(IOid, VAddr)>>,
}


// File: allocator/page_allocator_spec_impl.rs
pub struct PageAllocator {
    pub page_array: Array<Page, NUM_PAGES>,
    pub free_pages_4k: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub free_pages_2m: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub free_pages_1g: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub allocated_pages_4k: Ghost<Set<PagePtr>>,
    pub allocated_pages_2m: Ghost<Set<PagePtr>>,
    pub allocated_pages_1g: Ghost<Set<PagePtr>>,
    pub mapped_pages_4k: Ghost<Set<PagePtr>>,
    pub mapped_pages_2m: Ghost<Set<PagePtr>>,
    pub mapped_pages_1g: Ghost<Set<PagePtr>>,
    // pub available_pages: Ghost<Set<PagePtr>>,
    pub page_perms_4k: Tracked<Map<PagePtr, PagePerm4k>>,
    pub page_perms_2m: Tracked<Map<PagePtr, PagePerm2m>>,
    pub page_perms_1g: Tracked<Map<PagePtr, PagePerm1g>>,
    pub container_map_4k: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
    pub container_map_2m: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
    pub container_map_1g: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
}

impl PageAllocator {

    pub open spec fn page_is_mapped(&self, p: PagePtr) -> bool {
        ||| self.mapped_pages_4k().contains(p)
        ||| self.mapped_pages_2m().contains(p)
        ||| self.mapped_pages_1g().contains(p)
    }

	#[verifier::external_body]
    pub closed spec fn allocated_pages_4k(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn allocated_pages_2m(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn allocated_pages_1g(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn mapped_pages_4k(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn mapped_pages_2m(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn mapped_pages_1g(&self) -> Set<PagePtr> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn page_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn page_io_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn get_container_owned_pages(&self, c_ptr: ContainerPtr) -> Set<PagePtr>
        recommends
            self.container_map_4k@.dom().contains(c_ptr),
	{
		unimplemented!()
	}

    pub open spec fn page_array_wf(&self) -> bool {
        &&& self.page_array.wf()
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].addr]
            #![trigger page_index2page_ptr(i)]
            0 <= i < NUM_PAGES ==> self.page_array@[i as int].addr == page_index2page_ptr(i)
        &&& forall|i: int|
            #![trigger self.page_array@[i].mappings]
            0 <= i < NUM_PAGES ==> self.page_array@[i].mappings@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].io_mappings]
            0 <= i < NUM_PAGES ==> self.page_array@[i].io_mappings@.finite()
    }

    pub open spec fn free_pages_4k_wf(&self) -> bool {
        &&& self.free_pages_4k.wf()
        &&& self.free_pages_4k.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_4k@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free4k
                ==> self.free_pages_4k@.contains(self.page_array@[i].addr)
                && self.free_pages_4k.get_node_ref(self.page_array@[i].addr) == self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_4k@.contains(page_ptr) ==> page_ptr_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free4k
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free4k && self.page_array@[j].state == PageState::Free4k
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn free_pages_2m_wf(&self) -> bool {
        &&& self.free_pages_2m.wf()
        &&& self.free_pages_2m.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_2m@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                ==> self.free_pages_2m@.contains(self.page_array@[i].addr)
                && self.free_pages_2m.get_node_ref(self.page_array@[i].addr ) == 
                    self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_2m_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_2m@.contains(page_ptr) ==> page_ptr_2m_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free2m
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free2m && self.page_array@[j].state == PageState::Free2m
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn free_pages_1g_wf(&self) -> bool {
        &&& self.free_pages_1g.wf()
        &&& self.free_pages_1g.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_1g@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free1g
                ==> self.free_pages_1g@.contains(self.page_array@[i].addr)
                && self.free_pages_1g.get_node_ref(self.page_array@[i].addr) == self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_1g_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_1g@.contains(page_ptr) ==> page_ptr_1g_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free1g
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free1g && self.page_array@[j].state == PageState::Free1g
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn allocated_pages_4k_wf(&self) -> bool {
        &&& self.allocated_pages_4k@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_4k@.contains(p), page_ptr_valid(p)]
            self.allocated_pages_4k@.contains(p) ==> page_ptr_valid(p)
        &&& forall|i: int|
            #![trigger self.allocated_pages_4k@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated4k
                ==> self.allocated_pages_4k@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_4k@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated4k
    }

    pub open spec fn allocated_pages_2m_wf(&self) -> bool {
        &&& self.allocated_pages_2m@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_2m@.contains(p), page_ptr_2m_valid(p)]
            self.allocated_pages_2m@.contains(p) ==> page_ptr_2m_valid(p)
        &&& forall|i: int|
            #![trigger self.allocated_pages_2m@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated2m
                ==> self.allocated_pages_2m@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_2m@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated2m
    }

    pub open spec fn allocated_pages_1g_wf(&self) -> bool {
        &&& self.allocated_pages_1g@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_1g@.contains(p), page_ptr_1g_valid(p)]
            self.allocated_pages_1g@.contains(p) ==> page_ptr_1g_valid(p)
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated1g
                ==> self.allocated_pages_1g@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_1g@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated1g
    }

    pub open spec fn mapped_pages_4k_wf(&self) -> bool {
        &&& self.mapped_pages_4k@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_4k@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_4k@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_4k@.contains(p) ==> page_ptr_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped4k
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped4k
                ==> self.mapped_pages_4k@.contains(self.page_array@[i].addr)
    }

    pub open spec fn mapped_pages_2m_wf(&self) -> bool {
        &&& self.mapped_pages_2m@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped2m
                ==> self.mapped_pages_2m@.contains(self.page_array@[i].addr)
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_2m@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_2m@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_2m@.contains(p) ==> page_ptr_2m_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped2m
    }

    pub open spec fn mapped_pages_1g_wf(&self) -> bool {
        &&& self.mapped_pages_1g@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped1g
                ==> self.mapped_pages_1g@.contains(self.page_array@[i].addr)
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_1g@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_1g@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_1g@.contains(p) ==> page_ptr_1g_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped1g
    }

    pub open spec fn merged_pages_wf(&self) -> bool {
        &&& forall|i: usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger spec_page_index_truncate_2m(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged2m    
            ==> 
            page_index_2m_valid(i) == false 
            && ( self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Mapped2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Free2m 
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Allocated2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state== PageState::Unavailable2m
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_2m(i) as int].is_io_page
        &&& forall|i: usize|
            #![trigger page_index_1g_valid(i)]
            #![trigger spec_page_index_truncate_1g(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged1g
            ==> 
            page_index_1g_valid(i) == false 
            && (self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Mapped1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Free1g 
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Allocated1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Unavailable1g
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_1g(i) as int].is_io_page
    }

    pub open spec fn hugepages_wf(&self) -> bool {
        &&& forall|i: usize, j: usize|
            #![trigger spec_page_index_merge_2m_vaild(i,j)]
            #![trigger spec_page_index_merge_1g_vaild(i,j)]
            (0 <= i < NUM_PAGES && page_index_2m_valid(i) && 
            (self.page_array@[i as int].state == PageState::Mapped2m 
                || self.page_array@[i as int].state == PageState::Free2m
                || self.page_array@[i as int].state == PageState::Allocated2m
                || self.page_array@[i as int].state == PageState::Unavailable2m)
                && spec_page_index_merge_2m_vaild(i, j) 
            ==> self.page_array@[j as int].state == PageState::Merged2m && self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page) 
            && 
            (0 <= i < NUM_PAGES && page_index_1g_valid(i) && (self.page_array@[i as int].state == PageState::Mapped1g 
                || self.page_array@[i as int].state == PageState::Free1g
                || self.page_array@[i as int].state == PageState::Allocated1g
                || self.page_array@[i as int].state == PageState::Unavailable1g)
                && spec_page_index_merge_1g_vaild(i, j) 
            ==> self.page_array@[j as int].state == PageState::Merged1g && self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page)
    }

    pub open spec fn perm_wf(&self) -> bool {
        &&& self.page_perms_4k@.dom() =~= self.mapped_pages_4k@ + self.free_pages_4k@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_4k@[p].is_init()]
            #![trigger self.page_perms_4k@[p].addr()]
            self.page_perms_4k@.dom().contains(p) ==> self.page_perms_4k@[p].is_init()
                && self.page_perms_4k@[p].addr() == p
        &&& self.page_perms_2m@.dom() =~= self.mapped_pages_2m@ + self.free_pages_2m@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_2m@[p].is_init()]
            #![trigger self.page_perms_2m@[p].addr()]
            self.page_perms_2m@.dom().contains(p) ==> self.page_perms_2m@[p].is_init()
                && self.page_perms_2m@[p].addr() == p
        &&& self.page_perms_1g@.dom() =~= self.mapped_pages_1g@ + self.free_pages_1g@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_1g@[p].is_init()]
            #![trigger self.page_perms_1g@[p].addr()]
            self.page_perms_1g@.dom().contains(p) ==> self.page_perms_1g@[p].is_init()
                && self.page_perms_1g@[p].addr() == p
    }

    pub open spec fn container_wf(&self) -> bool {
        //@Xiangdong Come back for this
        // &&&
        // self.container_map_4k@.dom() == self.container_map_2m@.dom()
        // &&&
        // self.container_map_4k@.dom() == self.container_map_1g@.dom()
        // &&&
        // self.container_map_2m@.dom() == self.container_map_1g@.dom()
        &&& self.container_map_4k@.dom().subset_of(self.allocated_pages_4k@)
        &&& self.container_map_2m@.dom().subset_of(self.allocated_pages_4k@)
        &&& self.container_map_1g@.dom().subset_of(self.allocated_pages_4k@)
        &&& forall|i: int|
            #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
            0 <= i < NUM_PAGES && (self.page_array@[i].state == PageState::Mapped4k
                || self.page_array@[i].state == PageState::Mapped2m || self.page_array@[i].state
                == PageState::Mapped1g) ==> self.page_array@[i].owning_container.is_Some()
        &&& forall|i: int|
            #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
            0 <= i < NUM_PAGES && self.page_array@[i].owning_container.is_Some() ==> (
            self.page_array@[i].state == PageState::Mapped4k || self.page_array@[i].state
                == PageState::Mapped2m || self.page_array@[i].state == PageState::Mapped1g)
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped4k
                ==> self.container_map_4k@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_4k@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped2m
                ==> self.container_map_2m@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_2m@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped1g
                ==> self.container_map_1g@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_1g@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_4k@[c_ptr].contains(page_ptr)]
            self.container_map_4k@.dom().contains(c_ptr) && self.container_map_4k@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped4k && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_2m@[c_ptr].contains(page_ptr)]
            self.container_map_2m@.dom().contains(c_ptr) && self.container_map_2m@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_2m_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped2m && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_1g@[c_ptr].contains(page_ptr)]
            self.container_map_1g@.dom().contains(c_ptr) && self.container_map_1g@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_1g_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped1g && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
    }

    pub open spec fn mapped_pages_have_reference_counter(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.page_array@[i].ref_count]
            #![trigger self.page_array@[i].state]
            #![trigger self.page_array@[i].mappings]
            #![trigger self.page_array@[i].io_mappings]
            0 <= i < NUM_PAGES ==> (self.page_array@[i].ref_count != 0 <==> (
            self.page_array@[i].state == PageState::Mapped4k || self.page_array@[i].state
                == PageState::Mapped2m || self.page_array@[i].state == PageState::Mapped1g))
                && self.page_array@[i].ref_count == self.page_array@[i].mappings@.len()
                + self.page_array@[i].io_mappings@.len()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.page_array_wf()
        &&& self.free_pages_4k_wf()
        &&& self.free_pages_2m_wf()
        &&& self.free_pages_1g_wf()
        &&& self.allocated_pages_4k_wf()
        &&& self.allocated_pages_2m_wf()
        &&& self.allocated_pages_1g_wf()
        &&& self.mapped_pages_4k_wf()
        &&& self.mapped_pages_2m_wf()
        &&& self.mapped_pages_1g_wf()
        &&& self.merged_pages_wf()
        &&& self.hugepages_wf()
        &&& self.perm_wf()
        &&& self.container_wf()
        &&& self.mapped_pages_have_reference_counter()
    }

}



// File: process_manager/container.rs
pub struct Container {
    pub parent: Option<ContainerPtr>,
    pub parent_rev_ptr: Option<SLLIndex>,
    pub children: StaticLinkedList<ContainerPtr, CONTAINER_CHILD_LIST_LEN>,
    pub depth: usize,
    pub uppertree_seq: Ghost<Seq<ContainerPtr>>,
    pub subtree_set: Ghost<Set<ContainerPtr>>,
    pub root_process: Option<ProcPtr>,
    pub owned_procs: StaticLinkedList<ProcPtr, CONTAINER_PROC_LIST_LEN>,
    /// Right now we don't yet have linkedlist with unlimited length, 
    /// so we cannot kill an endpoint and release all the blocked threads.
    /// We we can do now to enable unconditional kill() is to add an invariant to
    /// ensure that each endpoint can ONLY be referenced by threads in the subtree of the container.
    /// So when we kill all the threads, all the endpoints are killed too. 
    pub owned_endpoints: Ghost<Set<EndpointPtr>>,
    pub owned_threads: Ghost<Set<ThreadPtr>>,
    // pub mem_quota: usize,
    // pub mem_quota_2m: usize,
    // pub mem_quota_1g: usize,
    // pub mem_used: usize,
    // pub mem_used_2m: usize,
    // pub mem_used_1g: usize,
    pub quota: Quota,
    pub owned_cpus: ArraySet<NUM_CPUS>,
    pub scheduler: StaticLinkedList<ThreadPtr, MAX_CONTAINER_SCHEDULER_LEN>,
    pub can_have_children: bool,
}


// File: process_manager/process.rs
pub struct Process {
    pub owning_container: ContainerPtr,
    pub rev_ptr: SLLIndex,
    pub pcid: Pcid,
    pub ioid: Option<IOid>,
    pub owned_threads: StaticLinkedList<ThreadPtr, MAX_NUM_THREADS_PER_PROC>,
    pub parent: Option<ProcPtr>,
    pub parent_rev_ptr: Option<SLLIndex>,
    pub children: StaticLinkedList<ProcPtr, PROC_CHILD_LIST_LEN>,
    pub uppertree_seq: Ghost<Seq<ProcPtr>>,
    pub subtree_set: Ghost<Set<ProcPtr>>,
    pub depth: usize,
    pub dmd_paging_mode: DemandPagingMode,
}


// File: process_manager/cpu.rs
#[derive(Clone, Copy, Debug)]
pub struct Cpu {
    pub owning_container: ContainerPtr,
    pub active: bool,
    pub current_thread: Option<ThreadPtr>,
}


// File: process_manager/endpoint.rs
pub struct Endpoint {
    pub queue: StaticLinkedList<ThreadPtr, MAX_NUM_THREADS_PER_ENDPOINT>,
    pub queue_state: EndpointState,
    pub rf_counter: usize,
    pub owning_threads: Ghost<Set<(ThreadPtr, EndpointIdx)>>,
    pub owning_container: ContainerPtr,
}


// File: process_manager/spec_proof.rs
pub struct ProcessManager {
    pub root_container: ContainerPtr,
    pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    pub process_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,
    pub cpu_list: Array<Cpu, NUM_CPUS>,
}

impl ProcessManager {

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.container_perms@.dom() + self.process_perms@.dom() + self.thread_perms@.dom()
            + self.endpoint_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn container_dom(&self) -> Set<ContainerPtr> {
        self.container_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn proc_dom(&self) -> Set<ProcPtr> {
        self.process_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn thread_dom(&self) -> Set<ThreadPtr> {
        self.thread_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn endpoint_dom(&self) -> Set<EndpointPtr> {
        self.endpoint_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn spec_get_container(&self, c_ptr: ContainerPtr) -> &Container {
        &self.container_perms@[c_ptr].value()
    }

	#[verifier::external_body]
    #[verifier(when_used_as_spec(spec_get_container))]
    pub fn get_container(&self, container_ptr: ContainerPtr) -> (ret: &Container)
        requires
            self.container_perms_wf(),
            self.container_dom().contains(container_ptr),
        ensures
            self.get_container(container_ptr) == ret,
	{
		unimplemented!()
	}

    #[verifier(inline)]
    pub open spec fn spec_get_proc(&self, proc_ptr: ProcPtr) -> &Process
        recommends
            self.proc_perms_wf(),
            self.proc_dom().contains(proc_ptr),
    {
        &self.process_perms@[proc_ptr].value()
    }

	#[verifier::external_body]
    #[verifier(when_used_as_spec(spec_get_proc))]
    pub fn get_proc(&self, proc_ptr: ProcPtr) -> (ret: &Process)
        requires
            self.proc_perms_wf(),
            self.process_fields_wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            ret =~= self.get_proc(proc_ptr),
            ret.owned_threads.wf(),
            self.wf() ==> self.container_dom().contains(ret.owning_container),
	{
		unimplemented!()
	}

    #[verifier(inline)]
    pub open spec fn spec_get_thread(&self, thread_ptr: ThreadPtr) -> &Thread
        recommends
            self.threads_perms_wf(),
            self.thread_dom().contains(thread_ptr),
    {
        &self.thread_perms@[thread_ptr].value()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_get_thread))]
    pub fn get_thread(&self, thread_ptr: ThreadPtr) -> (ret: &Thread)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
        ensures
            ret == self.get_thread(thread_ptr),
            self.proc_dom().contains(ret.owning_proc),
            self.container_dom().contains(ret.owning_container),
            self.get_container(ret.owning_container).scheduler.wf(),
            self.get_container(ret.owning_container).owned_procs.wf(),
            self.get_container(ret.owning_container).children.wf(),
    {
        unimplemented!()
    }

    #[verifier(inline)]
    pub open spec fn spec_get_endpoint(&self, endpoint_ptr: EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_perms@.dom().contains(endpoint_ptr),
    {
        &self.endpoint_perms@[endpoint_ptr].value()
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_get_endpoint))]
    pub fn get_endpoint(&self, endpoint_ptr: EndpointPtr) -> (ret: &Endpoint)
        requires
            self.wf(),
            self.endpoint_dom().contains(endpoint_ptr),
        ensures
            ret == self.get_endpoint(endpoint_ptr),
            ret.queue.wf(),
    {
        unimplemented!()
    }


}


impl ProcessManager {

    pub open spec fn container_perms_wf(&self) -> bool {
        &&& container_perms_wf(self.container_perms@)
    }

    pub open spec fn proc_perms_wf(&self) -> bool {
        &&& proc_perms_wf(self.process_perms@)
    }

    pub open spec fn container_fields_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            // #![trigger self.container_dom().contains(c_ptr)]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_cpus]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).scheduler]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_procs]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_endpoints]
        // #![trigger self.get_container(c_ptr)]
        // #![trigger self.container_dom().contains(c_ptr)]
        #![trigger self.get_container(c_ptr).owned_cpus.wf()]
        #![trigger self.get_container(c_ptr).scheduler.wf()]
        #![trigger self.get_container(c_ptr).owned_procs.wf()]
        // #![trigger self.get_container(c_ptr).owned_endpoints.wf()]
        #![trigger self.get_container(c_ptr).scheduler.unique()]
        #![trigger self.get_container(c_ptr).owned_procs.unique()]
        // #![trigger self.get_container(c_ptr).owned_endpoints.unique()]

            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_cpus.wf()
                && self.get_container(c_ptr).scheduler.wf() 
                && self.get_container(c_ptr).scheduler.unique()
                && self.get_container(c_ptr).owned_procs.wf()
                && self.get_container(c_ptr).owned_procs.unique()
    }

    pub open spec fn process_fields_wf(&self) -> bool {
        &&& forall|p_ptr: ProcPtr|
            #![trigger self.get_proc(p_ptr).owned_threads.wf()]
            #![trigger self.get_proc(p_ptr).owned_threads.unique()]
            self.proc_dom().contains(p_ptr)
            ==> self.get_proc(p_ptr).owned_threads.wf()
                && self.get_proc(p_ptr).owned_threads.unique()
    }

    pub open spec fn threads_perms_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
         // #![trigger self.thread_perms@[t_ptr].is_init()]
        // #![trigger self.thread_perms@[t_ptr].addr()]
        // #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors.wf()]
        // #![trigger self.thread_perms@[t_ptr].value().ipc_payload]

            #![trigger self.thread_perms@.dom().contains(t_ptr)]
            self.thread_perms@.dom().contains(t_ptr) ==> 
                self.thread_perms@[t_ptr].is_init()
                && self.thread_perms@[t_ptr].addr() == t_ptr
                && self.thread_perms@[t_ptr].value().endpoint_descriptors.wf() 
                && (self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().is_Some()
                    ==> self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().unwrap().wf())
    }

    pub open spec fn endpoint_perms_wf(&self) -> bool {
        &&& forall|e_ptr: EndpointPtr|
            #![trigger self.endpoint_perms@.dom().contains(e_ptr) ]
            self.endpoint_perms@.dom().contains(e_ptr) ==> 
                self.endpoint_perms@[e_ptr].is_init()
                && self.endpoint_perms@[e_ptr].addr() == e_ptr
                && self.endpoint_perms@[e_ptr].value().queue.wf()
                && self.endpoint_perms@[e_ptr].value().queue.unique()
                && self.endpoint_perms@[e_ptr].value().owning_threads@.finite()
                && self.endpoint_perms@[e_ptr].value().rf_counter
                == self.endpoint_perms@[e_ptr].value().owning_threads@.len()
        // &&
        // self.endpoint_perms@[e_ptr].value().owning_threads@.subset_of(self.thread_perms@.dom())

    }

	#[verifier::external_body]
    pub closed spec fn internal_wf(&self) -> bool {
		unimplemented!()
	}


    pub open spec fn wf(&self) -> bool {
        &&& self.container_perms_wf()
        &&& self.proc_perms_wf()
        &&& self.threads_perms_wf()
        &&& self.endpoint_perms_wf()
        &&& self.container_fields_wf()
        &&& self.process_fields_wf()
        &&& self.internal_wf()
    }

}


impl ProcessManager {

	#[verifier::external_body]
    pub proof fn thread_inv(&self)
        requires
            self.wf(),
        ensures
            forall|t_ptr: ThreadPtr|
                #![trigger self.thread_dom().contains(t_ptr)]
                #![trigger self.get_thread(t_ptr).owning_container]
                #![trigger self.get_thread(t_ptr).owning_proc]
                self.thread_dom().contains(t_ptr) ==> self.container_dom().contains(
                    self.get_thread(t_ptr).owning_container,
                ) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_threads@.contains(t_ptr) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_procs@.contains(self.get_thread(t_ptr).owning_proc)
                    && self.proc_dom().contains(self.get_thread(t_ptr).owning_proc)
                    && self.get_thread(t_ptr).endpoint_descriptors.wf() && (self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().is_Some() ==> self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().unwrap().wf()) && (forall|i: int|
                    #![auto]
                    0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && self.get_thread(
                        t_ptr,
                    ).endpoint_descriptors@[i].is_Some() ==> self.endpoint_dom().contains(
                        self.get_thread(t_ptr).endpoint_descriptors@[i].unwrap(),
                    )) && self.get_proc(self.get_thread(t_ptr).owning_proc).owning_container
                    == self.get_thread(t_ptr).owning_container && (self.get_thread(t_ptr).state
                    == ThreadState::BLOCKED ==> self.get_thread(
                    t_ptr,
                ).blocking_endpoint_ptr.is_Some() && self.endpoint_dom().contains(
                    self.get_thread(t_ptr).blocking_endpoint_ptr.unwrap(),
                )),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub proof fn process_inv(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr: ProcPtr|
                #![trigger self.proc_dom().contains(p_ptr)]
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.container_dom().contains(
                    self.get_proc(p_ptr).owning_container,
                ) && self.get_proc(p_ptr).children.wf(),
	{
		unimplemented!()
	}

}



// File: process_manager/thread.rs
pub struct Thread {
    pub owning_container: ContainerPtr,
    pub owning_proc: ProcPtr,
    pub state: ThreadState,
    pub proc_rev_ptr: SLLIndex,
    pub scheduler_rev_ptr: Option<SLLIndex>,
    pub blocking_endpoint_ptr: Option<EndpointPtr>,
    pub blocking_endpoint_index: Option<EndpointIdx>,
    pub endpoint_rev_ptr: Option<SLLIndex>,
    pub running_cpu: Option<CpuId>,
    pub endpoint_descriptors: Array<Option<EndpointPtr>, MAX_NUM_ENDPOINT_DESCRIPTORS>,
    pub ipc_payload: IPCPayLoad,
    pub error_code: Option<RetValueType>,  //this will only be set when it comes out of endpoint and goes to scheduler.
    pub trap_frame: TrapFrameOption,
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy)]
pub enum IPCPayLoad {
    Message { va: VAddr, len: usize },
    Pages { va_range: VaRange4K },
    Endpoint { endpoint_index: EndpointIdx },
    Pci { bus: u8, dev: u8, fun: u8 },
    PageFault { vaddr: VAddr },
    Empty,
}

impl IPCPayLoad {

    pub open spec fn spec_get_payload_as_va_range(&self) -> Option<VaRange4K> {
        match self {
            IPCPayLoad::Pages { va_range: va_range } => Some(*va_range),
            _ => None,
        }
    }

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_get_payload_as_va_range))]
    pub fn get_payload_as_va_range(&self) -> (ret: Option<VaRange4K>)
        ensures
            ret == self.spec_get_payload_as_va_range(),
    {
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

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.iommu_table_pages@.dom() + self.page_table_pages@.dom()
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

}



// File: kernel/spec.rs
pub struct Kernel {
    pub page_alloc: PageAllocator,
    pub mem_man: MemoryManager,
    pub proc_man: ProcessManager,
    pub page_mapping: Ghost<Map<PagePtr, Set<(ProcPtr, VAddr)>>>,
    /// @Xiangdong fix
    pub page_io_mapping: Ghost<Map<PagePtr, Set<(ProcPtr, VAddr)>>>,
}

impl Kernel {

    pub open spec fn memory_wf(&self) -> bool {
        //Additional safety specs are embedded in page_alloc's specs
        &&& self.mem_man.page_closure().disjoint(
            self.proc_man.page_closure(),
        )
        //Leakage freedom. Internel leakage freedom are embedded recursively in mem_man and proc_man
        &&& self.mem_man.page_closure() + self.proc_man.page_closure()
            == self.page_alloc.allocated_pages_4k()
        //We are not using hugepages for now.
        &&& self.page_alloc.mapped_pages_2m() =~= Set::empty()
        &&& self.page_alloc.mapped_pages_1g() =~= Set::empty()
        &&& self.page_alloc.allocated_pages_2m() =~= Set::empty()
        &&& self.page_alloc.allocated_pages_1g() =~= Set::empty()
        &&& self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom()
        &&& self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom()
        &&& self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom()
    }

    pub open spec fn page_mapping_wf(&self) -> bool {
        &&& self.page_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k())
        &&& self.page_io_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k())
        &&& forall|page_ptr: PagePtr, p_ptr: ProcPtr, va: VAddr|
            #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains(
                (p_ptr, va),
            ) ==> self.page_alloc.page_is_mapped(page_ptr) && self.proc_man.proc_dom().contains(
                p_ptr,
            ) && self.page_alloc.page_mappings(page_ptr).contains(
                (self.proc_man.get_proc(p_ptr).pcid, va),
            )
        &&& forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
            #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> self.page_mapping@.dom().contains(page_ptr)
                && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))
    }

    pub open spec fn mapping_wf(&self) -> bool {
        &&& forall|pcid: Pcid, va: VAddr|
            #![auto]
            #![trigger self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr)]
            #![trigger self.page_alloc.page_mappings(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr).contains((pcid,va))]
            self.mem_man.pcid_active(pcid) && self.mem_man.get_pagetable_mapping_by_pcid(
                pcid,
            ).dom().contains(va) ==> self.page_alloc.page_is_mapped(
                self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr,
            ) && self.page_alloc.page_mappings(
                self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr,
            ).contains((pcid, va))
        &&& forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> va_4k_valid(va) && self.mem_man.pcid_active(pcid)
                && self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
                && self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr == page_ptr
        &&& forall|ioid: IOid, va: VAddr|
            #![trigger self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr)]
            #![trigger self.page_alloc.page_io_mappings(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr).contains((ioid,va))]
            self.mem_man.ioid_active(ioid) && self.mem_man.get_iommu_table_mapping_by_ioid(
                ioid,
            ).dom().contains(va) ==> self.page_alloc.page_is_mapped(
                self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr,
            ) && self.page_alloc.page_io_mappings(
                self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr,
            ).contains((ioid, va))
        &&& forall|page_ptr: PagePtr, ioid: IOid, va: VAddr|
            #![trigger self.page_alloc.page_io_mappings(page_ptr).contains((ioid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_io_mappings(
                page_ptr,
            ).contains((ioid, va)) ==> va_4k_valid(va) && self.mem_man.ioid_active(ioid)
                && self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool {
        &&& forall|proc_ptr: ProcPtr|
            #![trigger self.proc_man.get_proc(proc_ptr).pcid]
            self.proc_man.proc_dom().contains(proc_ptr) ==> self.mem_man.pcid_active(
                self.proc_man.get_proc(proc_ptr).pcid,
            ) && self.mem_man.pcid_to_proc_ptr(self.proc_man.get_proc(proc_ptr).pcid) == proc_ptr
        &&& forall|pcid: Pcid|
            #![trigger self.mem_man.pcid_to_proc_ptr(pcid)]
            self.mem_man.pcid_active(pcid) ==> self.proc_man.proc_dom().contains(
                self.mem_man.pcid_to_proc_ptr(pcid),
            ) && self.proc_man.get_proc(self.mem_man.pcid_to_proc_ptr(pcid)).pcid == pcid
        &&& forall|proc_ptr: ProcPtr|
            #![trigger self.proc_man.get_proc(proc_ptr).ioid]
            self.proc_man.proc_dom().contains(proc_ptr) && self.proc_man.get_proc(
                proc_ptr,
            ).ioid.is_Some() ==> self.mem_man.ioid_active(
                self.proc_man.get_proc(proc_ptr).ioid.unwrap(),
            ) && self.mem_man.ioid_to_proc_ptr(self.proc_man.get_proc(proc_ptr).ioid.unwrap())
                == proc_ptr
        &&& forall|ioid: Pcid|
            #![trigger self.mem_man.ioid_to_proc_ptr(ioid)]
            self.mem_man.ioid_active(ioid) ==> self.proc_man.proc_dom().contains(
                self.mem_man.ioid_to_proc_ptr(ioid),
            ) && self.proc_man.get_proc(self.mem_man.ioid_to_proc_ptr(ioid)).ioid.is_Some()
                && self.proc_man.get_proc(self.mem_man.ioid_to_proc_ptr(ioid)).ioid.unwrap() == ioid
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.mem_man.wf()
        &&& self.page_alloc.wf()
        &&& self.proc_man.wf()
        &&& self.memory_wf()
        &&& self.mapping_wf()
        &&& self.pcid_ioid_wf()
        &&& self.page_mapping_wf()
    }

}



// File: define.rs
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ThreadState {
    SCHEDULED,
    BLOCKED,
    RUNNING,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EndpointState {
    RECEIVE,
    SEND,
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(inconsistent_fields)]
pub enum PageState {
    Unavailable4k,
    Unavailable2m,
    Unavailable1g,
    Pagetable,
    Allocated4k,
    Allocated2m,
    Allocated1g,
    Free4k,
    Free2m,
    Free1g,
    Mapped4k,
    Mapped2m,
    Mapped1g,
    Merged2m,
    Merged1g,
    Io,
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy)]
pub enum RetValueType {
    SuccessUsize { value: usize },
    SuccessSeqUsize { value: Ghost<Seq<usize>> },
    SuccessPairUsize { value1: usize, value2: usize },
    SuccessThreeUsize { value1: usize, value2: usize, value3: usize },
    ErrorNoQuota,
    ErrorVaInUse,
    CpuIdle,
    Error,
    Else,
    NoQuota,
    VaInUse,
}

pub const KERNEL_MEM_END_L4INDEX: usize = 1;

pub const NUM_PAGES: usize = 2 * 1024 * 1024;

pub const PCID_MAX: usize = 4096;

pub const IOID_MAX: usize = 4096;

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const PAGE_ENTRY_WRITE_SHIFT: u64 = 1;

pub const PAGE_ENTRY_USER_SHIFT: u64 = 2;

pub const PAGE_ENTRY_PS_SHIFT: u64 = 7;

pub const PAGE_ENTRY_EXECUTE_SHIFT: u64 = 63;

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << PAGE_ENTRY_WRITE_SHIFT;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << PAGE_ENTRY_USER_SHIFT;

pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << PAGE_ENTRY_PS_SHIFT;

pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << PAGE_ENTRY_EXECUTE_SHIFT;

#[derive(Clone, Copy, Debug)]
pub enum DemandPagingMode {
    NoDMDPG,
    DirectParentPrc,
    AllParentProc,
    AllParentContainer,
}


// File: trap.rs
pub struct TrapFrameOption {
    pub reg: Registers,
    pub exists: bool,
}

#[derive(Clone, Copy, Debug)]
#[repr(C, align(8))]
pub struct Registers {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,
    // Original interrupt stack frame
    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
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



// File: array_set.rs
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub len: usize,

    pub set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

	#[verifier::external_body]
    pub closed spec fn wf(&self) -> bool{
		unimplemented!()
	}


}



// File: array_vec.rs
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T: Copy, const N: usize> ArrayVec<T, N> {

    pub open spec fn spec_len(&self) -> usize {
        self.len
    }

    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

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

    #[verifier::external_body]
    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        unimplemented!()
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

}



// File: va_range.rs
#[derive(Clone, Copy)]
pub struct VaRange4K {
    pub start: VAddr,
    pub len: usize,
    pub view: Ghost<Seq<VAddr>>,
}

impl VaRange4K {

	#[verifier::external_body]
    pub closed spec fn view(&self) -> Seq<VAddr> {
		unimplemented!()
	}


    pub open spec fn wf(&self) -> bool {
        &&& self.start + self.len * 4096 < usize::MAX
        &&& spec_va_4k_valid(self.start)
        &&& self@.len() == self.len
        &&& self@.no_duplicates()
        &&& forall|i: int| #![trigger self@[i]] 0 <= i < self.len ==> spec_va_4k_valid(self@[i])
        &&& self.view_match_spec()
    }

	#[verifier::external_body]
    pub closed spec fn view_match_spec(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub fn index(&self, i: usize) -> (ret: VAddr)
        requires
            self.wf(),
            0 <= i < self.len,
        ensures
            ret == self@[i as int],
	{
		unimplemented!()
	}

}



// File: quota.rs
    #[derive(Clone, Copy, Debug)]
    pub struct Quota{
        pub mem_4k:usize,
        pub mem_2m:usize,
        pub mem_1g:usize,
        pub pcid:usize,
        pub ioid:usize,
    }

    impl Quota{

        pub open spec fn spec_subtract_mem_4k(&self, new:Self, k:usize) -> bool
        {
           &&&
           self.mem_4k - k == new.mem_4k
           &&&
           self.mem_2m == new.mem_2m
           &&&
           self.mem_1g == new.mem_1g
           &&&
           self.pcid == new.pcid
           &&&
           self.ioid == new.ioid
        }

}



// File: process_manager/container_tree.rs
pub open spec fn container_perms_wf(
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].is_init()]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].is_init()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].addr()]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].addr() == c_ptr
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().children.wf()]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children.wf()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().children.unique()]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children.unique()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().uppertree_seq@.no_duplicates()]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().uppertree_seq@.no_duplicates()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().children@.contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children@.contains(
            c_ptr,
        ) == false
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().subtree_set@.finite()]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().subtree_set@.finite()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
    // #![trigger container_perms[c_ptr].value().uppertree_seq@.len(), container_perms[c_ptr].value().depth]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().uppertree_seq@.len()
            == container_perms[c_ptr].value().depth
}


// File: process_manager/process_tree.rs
pub open spec fn proc_perms_wf(proc_perms: Map<ProcPtr, PointsTo<Process>>) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].is_init()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].is_init()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].addr()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].addr() == p_ptr
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children.wf()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children.wf()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children.unique()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children.unique()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.no_duplicates()]

        proc_perms.dom().contains(p_ptr)
            ==> proc_perms[p_ptr].value().uppertree_seq@.no_duplicates()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children@.contains(p_ptr)]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children@.contains(p_ptr)
            == false
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().subtree_set@.finite()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().subtree_set@.finite()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.len(), proc_perms[p_ptr].value().depth]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().uppertree_seq@.len()
            == proc_perms[p_ptr].value().depth
}


// File: kernel/create_and_map_pages.rs
impl Kernel {

	#[verifier::external_body]
    pub fn create_entry_and_alloc_and_map(
        &mut self,
        target_proc_ptr: ProcPtr,
        target_va: VAddr,
    ) -> (ret: (usize, MapEntry))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4,
            old(self).get_num_of_free_pages() >= 4,
            va_4k_valid(target_va),
            old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
        ensures
            ret.0 <= 4,
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|c: ContainerPtr|
                #![auto]
                self.container_dom().contains(c) && old(self).get_proc(
                    target_proc_ptr,
                ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                    self,
                ).get_container_owned_pages(c),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).scheduler,
            old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).quota,
                ret.0,
            ),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
            self.get_address_space(target_proc_ptr).dom() =~= old(self).get_address_space(
                target_proc_ptr,
            ).dom().insert(target_va),
            self.get_address_space(target_proc_ptr) =~= old(self).get_address_space(
                target_proc_ptr,
            ).insert(target_va, ret.1),
            old(self).page_alloc.page_is_mapped(ret.1.addr) == false,
            self.page_alloc.page_is_mapped(ret.1.addr),
            forall|p: PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)]
                p != ret.1.addr ==> self.page_alloc.page_is_mapped(p) == old(
                    self,
                ).page_alloc.page_is_mapped(p),
            self.page_mapping@.dom() == old(self).page_mapping@.dom().insert(ret.1.addr),
            forall|page_ptr: PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                    self,
                ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            self.page_mapping@[ret.1.addr] == Set::empty().insert((target_proc_ptr, target_va)),
	{
		unimplemented!()
	}

    pub fn range_alloc_and_map(&mut self, target_proc_ptr: ProcPtr, va_range: &VaRange4K) -> (ret: (
        usize,
        Ghost<Seq<PagePtr>>,
    ))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            va_range.wf(),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4 * va_range.len,
            old(self).get_num_of_free_pages() >= 4 * va_range.len,
            forall|i: int|
                #![auto]
                0 <= i < va_range.len ==> old(self).get_address_space(
                    target_proc_ptr,
                ).dom().contains(va_range@[i]) == false,
            va_range.len * 4 < usize::MAX,
        ensures
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|c: ContainerPtr|
                #![auto]
                self.container_dom().contains(c) && old(self).get_proc(
                    target_proc_ptr,
                ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                    self,
                ).get_container_owned_pages(c),
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(
                    va_range@[j as int],
                ),
            ret.1@.len() == va_range.len,
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.get_address_space(
                    target_proc_ptr,
                )[va_range@[j as int]].addr == ret.1@[j as int],
            forall|p: PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)]
                ret.1@.contains(p) == false ==> self.page_alloc.page_is_mapped(p) == old(
                    self,
                ).page_alloc.page_is_mapped(p),
            va_range.len == ret.1@.len(),
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> old(self).page_alloc.page_is_mapped(ret.1@[j as int])
                    == false,
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.page_alloc.page_is_mapped(ret.1@[j as int]) == true,
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
            old(self).get_container_quota(
                self.get_proc(target_proc_ptr).owning_container,
            ).spec_subtract_mem_4k(
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container),
                ret.0,
            ),
            forall|va: VAddr|
                #![trigger self.get_address_space(target_proc_ptr).dom().contains(va)]
                #![trigger self.get_address_space(target_proc_ptr)[va]]
            // #![trigger va_4k_valid(va)]
            // va_4k_valid(va)
            // &&

                va_range@.contains(va) == false ==> self.get_address_space(
                    target_proc_ptr,
                ).dom().contains(va) == old(self).get_address_space(target_proc_ptr).dom().contains(
                    va,
                ) && self.get_address_space(target_proc_ptr)[va] == old(self).get_address_space(
                    target_proc_ptr,
                )[va],
            forall|va: VAddr|
                #![trigger self.get_address_space(target_proc_ptr).dom().contains(va)]
            // #![trigger va_4k_valid(va)]
            // va_4k_valid(va)
            // &&

                va_range@.contains(va) ==> self.get_address_space(target_proc_ptr).dom().contains(
                    va,
                ),
            self.page_mapping@.dom() == old(self).page_mapping@.dom() + ret.1@.to_set(),
            forall|page_ptr: PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                    self,
                ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            forall|i: usize|
                #![auto]
                0 <= i < va_range.len ==> self.page_mapping@[ret.1@[i as int]]
                    == Set::empty().insert((target_proc_ptr, va_range@[i as int])),
            forall|va: VAddr|
                #![auto]
                va_range@.contains(va) == false ==> self.get_address_space(target_proc_ptr)[va]
                    =~= old(self).get_address_space(target_proc_ptr)[va],
            forall|i: usize|
                #![auto]
                0 <= i < va_range.len ==> self.get_address_space(
                    target_proc_ptr,
                )[va_range@[i as int]].addr == ret.1@[i as int],
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.process_inv();
        }
        let mut num_page: usize = 0;
        let mut page_diff: Ghost<Seq<PagePtr>> = Ghost(Seq::empty());
        assert(page_diff@.to_set() =~= Set::empty());
        assert(self.page_mapping@.dom() == old(self).page_mapping@.dom() + page_diff@.to_set());
        for i in 0..va_range.len
            invariant
                0 <= i <= va_range.len,
                va_range.len * 4 < usize::MAX,
                old(self).wf(),
                self.wf(),
                self.proc_dom().contains(target_proc_ptr),
                va_range.wf(),
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container).mem_4k
                    >= 4 * (va_range.len - i),
                self.get_num_of_free_pages() >= 4 * (va_range.len - i),
                self.proc_dom() == old(self).proc_dom(),
                self.thread_dom() == old(self).thread_dom(),
                self.endpoint_dom() == old(self).endpoint_dom(),
                self.container_dom() == old(self).container_dom(),
                forall|p_ptr: ProcPtr|
                    #![auto]
                    self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                        ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
                forall|p_ptr: ProcPtr|
                    #![auto]
                    self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                        p_ptr,
                    ),
                forall|t_ptr: ThreadPtr|
                    #![auto]
                    self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                        self,
                    ).get_thread(t_ptr),
                forall|c_ptr: ContainerPtr|
                    #![auto]
                    self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                        target_proc_ptr,
                    ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(
                        c_ptr,
                    ),
                forall|c: ContainerPtr|
                    #![auto]
                    self.container_dom().contains(c) && old(self).get_proc(
                        target_proc_ptr,
                    ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                        self,
                    ).get_container_owned_pages(c),
                forall|e_ptr: EndpointPtr|
                    #![auto]
                    self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                        self,
                    ).get_endpoint(e_ptr),
                forall|j: int|
                    #![auto]
                    i <= j < va_range.len ==> self.get_address_space(
                        target_proc_ptr,
                    ).dom().contains(va_range@[j]) == false,
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> self.get_address_space(target_proc_ptr).dom().contains(
                        va_range@[j as int],
                    ),
                page_diff@.len() == i,
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> self.get_address_space(target_proc_ptr)[va_range@[j as int]].addr
                        == page_diff@[j as int],
                forall|p: PagePtr|
                    #![trigger self.page_alloc.page_is_mapped(p)]
                    page_diff@.contains(p) == false ==> self.page_alloc.page_is_mapped(p) == old(
                        self,
                    ).page_alloc.page_is_mapped(p),
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> old(self).page_alloc.page_is_mapped(page_diff@[j as int])
                        == false,
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> self.page_alloc.page_is_mapped(page_diff@[j as int]) == true,
                num_page <= i * 4,
                self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - num_page,
                old(self).get_container_quota(
                    self.get_proc(target_proc_ptr).owning_container,
                ).spec_subtract_mem_4k(
                    self.get_container_quota(self.get_proc(target_proc_ptr).owning_container),
                    num_page,
                ),
                forall|va: VAddr|
                    #![trigger self.get_address_space(target_proc_ptr).dom().contains(va)]
                    #![trigger self.get_address_space(target_proc_ptr)[va]]
                // #![trigger va_4k_valid(va)]
                // va_4k_valid(va)
                // &&

                    va_range@.contains(va) == false ==> self.get_address_space(
                        target_proc_ptr,
                    ).dom().contains(va) == old(self).get_address_space(
                        target_proc_ptr,
                    ).dom().contains(va) && self.get_address_space(target_proc_ptr)[va] == old(
                        self,
                    ).get_address_space(target_proc_ptr)[va],
                self.page_mapping@.dom() == old(self).page_mapping@.dom() + page_diff@.to_set(),
                forall|page_ptr: PagePtr|
                    #![trigger self.page_mapping@[page_ptr]]
                    old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                        self,
                    ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> self.page_mapping@[page_diff@[j as int]] == Set::empty().insert(
                        (target_proc_ptr, va_range@[j as int]),
                    ),
                forall|va: VAddr|
                    #![auto]
                    va_range@.contains(va) == false ==> self.get_address_space(target_proc_ptr)[va]
                        =~= old(self).get_address_space(target_proc_ptr)[va],
                forall|j: usize|
                    #![auto]
                    0 <= j < i ==> self.get_address_space(target_proc_ptr).dom().contains(
                        va_range@[j as int],
                    ) && self.get_address_space(target_proc_ptr)[va_range@[j as int]].addr
                        == page_diff@[j as int],
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                    =~= old(self).get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).owned_procs,
                self.get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).owned_threads =~= old(self).get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).owned_threads,
                self.get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).owned_endpoints =~= old(self).get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).owned_endpoints,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                    =~= old(self).get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).subtree_set,
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth
                    =~= old(self).get_container(
                    old(self).get_proc(target_proc_ptr).owning_container,
                ).depth,
        {
            proof {
                self.proc_man.thread_inv();
                self.proc_man.process_inv();
                seq_push_lemma::<PagePtr>();
                map_insert_lemma::<VAddr, MapEntry>();
            }
            let ghost_old_quota_mem_4k = Ghost(
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container).mem_4k,
            );
            let ghost_old_quota = Ghost(
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container),
            );
            let old_page_mapping = Ghost(self.page_mapping@);
            let (num, map_entry) = self.create_entry_and_alloc_and_map(
                target_proc_ptr,
                va_range.index(i),
            );

            assert(va_range@.subrange(0, i + 1 as int) == va_range@.subrange(0, i as int).push(
                va_range@[i as int],
            ));
            num_page = num_page + num;
            proof {
                set_lemma::<PagePtr>();
                let old_page_diff = page_diff@.to_set();
                assert(old_page_mapping@.dom().insert(map_entry.addr) == self.page_mapping@.dom());
                assert((old(self).page_mapping@.dom() + page_diff@.to_set()).insert(map_entry.addr)
                    == self.page_mapping@.dom());
                page_diff@ = page_diff@.push(map_entry.addr);
                assert(old_page_diff.insert(map_entry.addr) == page_diff@.to_set());
            }
        }
        (num_page, page_diff)
    }

}



// File: kernel/spec_util.rs
impl Kernel {

    pub open spec fn proc_dom(&self) -> Set<ProcPtr> {
        self.proc_man.proc_dom()
    }

    pub open spec fn thread_dom(&self) -> Set<ThreadPtr> {
        self.proc_man.thread_dom()
    }

    pub open spec fn container_dom(&self) -> Set<ContainerPtr> {
        self.proc_man.container_dom()
    }

    pub open spec fn endpoint_dom(&self) -> Set<EndpointPtr> {
        self.proc_man.endpoint_dom()
    }

    pub open spec fn get_proc(&self, p_ptr: ProcPtr) -> &Process
        recommends
            self.proc_man.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.proc_man.get_proc(p_ptr)
    }

    pub open spec fn get_thread(&self, t_ptr: ThreadPtr) -> &Thread
        recommends
            self.proc_man.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.proc_man.get_thread(t_ptr)
    }

    pub open spec fn get_container(&self, c_ptr: ContainerPtr) -> &Container
        recommends
            self.proc_man.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.proc_man.get_container(c_ptr)
    }

    pub open spec fn get_container_quota(&self, c_ptr: ContainerPtr) -> Quota
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.proc_man.get_container(c_ptr).quota
    }

    pub open spec fn get_endpoint(&self, e_ptr: EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_dom().contains(e_ptr),
    {
        self.proc_man.get_endpoint(e_ptr)
    }

    pub open spec fn get_address_space(&self, p_ptr: ProcPtr) -> Map<VAddr, MapEntry>
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.mem_man.get_pagetable_mapping_by_pcid(self.get_proc(p_ptr).pcid)
    }

    pub open spec fn get_container_owned_pages(&self, c_ptr: ContainerPtr) -> Set<PagePtr>
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.page_alloc.get_container_owned_pages(c_ptr)
    }

    pub open spec fn get_num_of_free_pages(&self) -> usize
        recommends
            self.wf(),
    {
        self.page_alloc.free_pages_4k.len()
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
	{
		unimplemented!()
	}


// File: lemma/lemma_u.rs
	#[verifier::external_body]
pub proof fn seq_push_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            s.contains(x) ==> s.push(v).contains(v) && s.push(v).contains(x),
        forall|s: Seq<A>, v: A| #![auto] s.push(v).contains(v),
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn map_insert_lemma<A, B>()
    ensures
        forall|m: Map<A, B>, x: A, y: A, v: B| x != y ==> m.insert(x, v)[y] == m[y],
	{
		unimplemented!()
	}


// File: util/page_ptr_util_u.rs
pub open spec fn spec_page_index_merge_2m_vaild(i: usize, j: usize) -> bool
    recommends
        page_index_2m_valid(i),
{
    i < j < i + 0x200
}

pub open spec fn spec_page_index_merge_1g_vaild(i: usize, j: usize) -> bool
    recommends
        page_index_1g_valid(i),
{
    i < j < i + 0x40000
}

pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr / 4096usize) as usize
}

pub open spec fn spec_page_index2page_ptr(i: usize) -> usize
    recommends
        page_index_valid(i),
{
    (i * 4096) as usize
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 0x1000 == 0,
    ensures
        ret == spec_page_ptr2page_index(ptr),
{
    unimplemented!()
}

#[verifier::external_body]
#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret: usize)
    requires
        0 <= i < NUM_PAGES,
    ensures
        ret == spec_page_index2page_ptr(i),
{
    unimplemented!()
}


pub open spec fn page_index_2m_valid(i: usize) -> bool {
    &&& i % 512 == 0
    &&& 0 <= i < NUM_PAGES
}

pub open spec fn page_index_1g_valid(i: usize) -> bool {
    &&& i % (512 * 512) as usize == 0
    &&& 0 <= i < NUM_PAGES
}

pub open spec fn page_ptr_valid(ptr: usize) -> bool {
    &&& ptr % 0x1000 == 0
    &&& ptr / 0x1000 < NUM_PAGES
}

pub open spec fn page_index_valid(index: usize) -> bool {
    (0 <= index < NUM_PAGES)
}

pub open spec fn spec_page_index_truncate_2m(index: usize) -> usize {
    (index / 512usize * 512usize) as usize
}

pub open spec fn spec_page_index_truncate_1g(index: usize) -> usize {
    (index / 512usize / 512usize * 512usize * 512usize) as usize
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

}
