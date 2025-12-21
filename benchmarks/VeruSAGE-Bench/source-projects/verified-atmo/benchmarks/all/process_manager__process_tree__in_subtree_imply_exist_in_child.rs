use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type IOid = usize;

pub type ThreadPtr = usize;

pub type ProcPtr = usize;

pub type ContainerPtr = usize;

pub type Pcid = usize;

pub type SLLIndex = i32;

pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;

pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;

pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;

pub const MAX_NUM_THREADS_PER_PROC: usize = 128;

pub const PROC_CHILD_LIST_LEN: usize = 10;

pub const PAGE_SZ_4k: usize = 1usize << 12;

pub const PAGE_SZ_2m: usize = 1usize << 21;

pub const PAGE_SZ_1g: usize = 1usize << 30;


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


// File: define.rs
#[derive(Clone, Copy, Debug)]
pub enum DemandPagingMode {
    NoDMDPG,
    DirectParentPrc,
    AllParentProc,
    AllParentContainer,
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

pub open spec fn proc_tree_dom_subset_of_proc_dom(
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger proc_perms.dom().contains(p_ptr)]

        proc_tree_dom.contains(p_ptr) ==> proc_perms.dom().contains(p_ptr)
}

pub closed spec fn proc_root_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& proc_tree_dom.contains(root_proc)
    &&& proc_perms[root_proc].value().depth == 0
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc ==> proc_perms[p_ptr].value().depth != 0
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent.is_Some()
}

pub closed spec fn proc_childern_parent_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, child_p_ptr: ProcPtr|
        #![trigger proc_perms[p_ptr].value().children@.contains(child_p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().children@.contains(child_p_ptr)
            ==> proc_tree_dom.contains(child_p_ptr)
            && proc_perms[child_p_ptr].value().parent.unwrap() == p_ptr
            && proc_perms[child_p_ptr].value().depth == proc_perms[p_ptr].value().depth + 1
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().parent.is_Some()
            ==> proc_tree_dom.contains(proc_perms[p_ptr].value().parent.unwrap())
            && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children@.contains(
            p_ptr,
        )
}

pub closed spec fn procs_linkedlist_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(proc_perms[p_ptr].value().parent.unwrap())]
    // #![trigger proc_tree_dom.contains(p_ptr)]

        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent.is_Some() && proc_tree_dom.contains(
            proc_perms[p_ptr].value().parent.unwrap(),
        )
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent_rev_ptr.is_Some()
            && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children@.contains(
            p_ptr,
        ) && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children.get_node_ref(p_ptr) 
        == 
        proc_perms[p_ptr].value().parent_rev_ptr.unwrap()
}

pub closed spec fn proc_childern_depth_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth - 1]]

        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth - 1]
            == proc_perms[p_ptr].value().parent.unwrap()
}

pub closed spec fn proc_subtree_set_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, sub_p_ptr: ProcPtr|
     // //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@.len(), proc_perms[p_ptr].value().depth]
    // //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]]
    // //#![trigger proc_tree_dom.contains(p_ptr), proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_tree_dom.contains(sub_p_ptr)]
    //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)]
    //#![trigger proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]]

        #![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)
            ==> proc_tree_dom.contains(sub_p_ptr)
            && proc_perms[sub_p_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth
            && proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
            == p_ptr
}

pub closed spec fn proc_uppertree_seq_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, u_ptr: ProcPtr|
     //#![trigger proc_tree_dom.contains(p_ptr), proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr), proc_tree_dom.contains(u_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.subrange(0, proc_perms[u_ptr].value().depth as int)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.index_of(u_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)]

        #![trigger proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)
            ==> proc_tree_dom.contains(u_ptr)
            && proc_perms[p_ptr].value().uppertree_seq@[proc_perms[u_ptr].value().depth as int]
            == u_ptr && proc_perms[u_ptr].value().depth
            == proc_perms[p_ptr].value().uppertree_seq@.index_of(u_ptr)
            && proc_perms[u_ptr].value().subtree_set@.contains(p_ptr)
            && proc_perms[u_ptr].value().uppertree_seq@
            =~= proc_perms[p_ptr].value().uppertree_seq@.subrange(
            0,
            proc_perms[u_ptr].value().depth as int,
        )
}

pub closed spec fn proc_subtree_set_exclusive(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, sub_p_ptr: ProcPtr|
        #![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_tree_dom.contains(sub_p_ptr) ==> (
        proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)
            == proc_perms[sub_p_ptr].value().uppertree_seq@.contains(p_ptr))
}

pub open spec fn proc_tree_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    // &&&
    // proc_perms_wf(proc_perms)
    &&& proc_root_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_childern_parent_wf(root_proc, proc_tree_dom, proc_perms)
    &&& procs_linkedlist_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_childern_depth_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_subtree_set_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_uppertree_seq_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_subtree_set_exclusive(root_proc, proc_tree_dom, proc_perms)
}

    #[verifier::spinoff_prover]
pub proof fn in_subtree_imply_exist_in_child(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
    s_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(p_ptr),
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        proc_perms[p_ptr].value().children@.contains(s_ptr) || (exists|child_ptr: ProcPtr|
            #![auto]
            proc_perms[p_ptr].value().children@.contains(child_ptr)
                && proc_perms[child_ptr].value().subtree_set@.contains(s_ptr)),
{
    assert(proc_perms[s_ptr].value().uppertree_seq@.contains(p_ptr));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        proc_perms[p_ptr].value().depth as int,
    ) == proc_perms[p_ptr].value().uppertree_seq@);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> s_ptr != root_proc);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().parent.unwrap() != p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[s_ptr].value().depth - 1] != p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
        == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() != proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> proc_tree_dom.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().depth as int,
    ) =~= proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.no_duplicates());
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.index_of(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ) == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().depth == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@.len() == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int] == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@[proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().depth - 1] == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().parent.unwrap() == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[p_ptr].value().children@.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().subtree_set@.contains(s_ptr));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> (exists|
        child_ptr: ProcPtr,
    |
        #![auto]
        proc_perms[p_ptr].value().children@.contains(child_ptr)
            && proc_perms[child_ptr].value().subtree_set@.contains(s_ptr)));
}


}
