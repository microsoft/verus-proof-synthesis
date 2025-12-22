use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type VAddr = usize;
type PagePtr = usize;
type ContainerPtr = usize;
pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;
pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;
pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;
pub type IOid = usize;
pub type SLLIndex = i32;
pub type Pcid = usize;
pub const PAGE_SZ_4k: usize = 1usize << 12;
pub const PAGE_SZ_2m: usize = 1usize << 21;
pub const PAGE_SZ_1g: usize = 1usize << 30;
pub const MAX_USIZE: u64 = 31 * 1024 * 1024 * 1024;

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
        self.value_list_len
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


impl<T: Copy, const N: usize> StaticLinkedList<T, N> {

	#[verifier::external_body]
    pub proof fn wf_to_no_duplicates(&self)
        requires
            self.wf(),
        ensures
            self.spec_seq@.no_duplicates(),
	{
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

    pub closed spec fn allocated_pages_4k(&self) -> Set<PagePtr> {
        self.allocated_pages_4k@
    }

    pub closed spec fn allocated_pages_2m(&self) -> Set<PagePtr> {
        self.allocated_pages_2m@
    }

    pub closed spec fn allocated_pages_1g(&self) -> Set<PagePtr> {
        self.allocated_pages_1g@
    }

    pub closed spec fn mapped_pages_4k(&self) -> Set<PagePtr> {
        self.mapped_pages_4k@
    }

    pub closed spec fn mapped_pages_2m(&self) -> Set<PagePtr> {
        self.mapped_pages_2m@
    }

    pub closed spec fn mapped_pages_1g(&self) -> Set<PagePtr> {
        self.mapped_pages_1g@
    }

    pub closed spec fn page_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
        self.page_array@[page_ptr2page_index(p) as int].mappings@
    }

    pub closed spec fn page_io_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
        self.page_array@[page_ptr2page_index(p) as int].io_mappings@
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


impl PageAllocator {

	#[verifier::external_body]
    fn remove_io_mapping_4k_helper1(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == true,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn remove_io_mapping_4k_helper2(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == false,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    fn remove_io_mapping_4k_helper3(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count != 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
	{
		unimplemented!()
	}

    pub fn remove_io_mapping_4k(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr) -> (ret:
        Option<ContainerPtr>)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            ret.is_None() ==> self.container_map_4k@ =~= old(self).container_map_4k@,
            ret.is_Some() ==> self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                ret.unwrap(),
                old(self).container_map_4k@[ret.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let is_io_page = self.page_array.get(page_ptr2page_index(target_ptr)).is_io_page;
        let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
        if old_ref_count == 1 && is_io_page {
            self.remove_io_mapping_4k_helper1(target_ptr, ioid, va);
            Some(c_ptr)
        } else if old_ref_count == 1 {
            self.remove_io_mapping_4k_helper2(target_ptr, ioid, va);
            Some(c_ptr)
        } else {
            self.remove_io_mapping_4k_helper3(target_ptr, ioid, va);
            None
        }
    }

}



// File: define.rs
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

pub const NUM_PAGES: usize = 2 * 1024 * 1024;


// File: array.rs
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn get(&self, i: usize) -> (out: &A)
        requires
            0 <= i < N,
            self.wf(),
        ensures
            *out == self.seq@[i as int],
	{
		unimplemented!()
	}

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

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

	#[verifier::external_body]
#[verifier(external_body)]
pub proof fn page_ptr_lemma1()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> page_index_valid(page_ptr2page_index(pa)),
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> pa == page_index2page_ptr(page_ptr2page_index(pa)),
        forall|i: usize|
            #![trigger page_index_valid(i)]
            #![trigger page_index2page_ptr(i)]
            page_index_valid(i) ==> i == page_ptr2page_index(page_index2page_ptr(i)),
        forall|pi: usize, pj: usize|
            #![trigger page_ptr_valid(pi), page_ptr_valid(pj), page_ptr2page_index(pi), page_ptr2page_index(pj)]
            page_ptr_valid(pi) && page_ptr_valid(pj) && pi != pj ==> page_ptr2page_index(pi)
                != page_ptr2page_index(pj),
        forall|i: usize, j: usize|
            #![trigger page_index2page_ptr(i), page_index2page_ptr(j)]
            0 < i < NUM_PAGES && 0 < j < NUM_PAGES && i != j ==> page_index2page_ptr(i)
                != page_index2page_ptr(j),
	{
		unimplemented!()
	}


}
