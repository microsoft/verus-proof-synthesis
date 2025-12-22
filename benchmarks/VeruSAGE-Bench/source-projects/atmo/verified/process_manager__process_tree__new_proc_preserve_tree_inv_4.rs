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
pub const PROC_CHILD_LIST_LEN: usize = 10;

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

pub open spec fn new_proc_ensures(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
) -> bool {
    &&& proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms)
    &&& proc_perms_wf(old_proc_perms)
    &&& proc_perms_wf(new_proc_perms)
    &&& proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms)
    &&& proc_tree_dom.contains(proc_ptr)
    &&& proc_tree_dom.contains(new_proc_ptr) == false
    &&& old_proc_perms[proc_ptr].value().children.len() < PROC_CHILD_LIST_LEN
    &&& old_proc_perms[proc_ptr].value().depth < usize::MAX
    &&& new_proc_perms.dom() == old_proc_perms.dom().insert(new_proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().parent =~= Some(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().parent_rev_ptr.is_Some()
    &&& new_proc_perms[new_proc_ptr].value().children@ =~= Seq::empty()
    &&& new_proc_perms[new_proc_ptr].value().uppertree_seq@
        =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().depth as int =~= old_proc_perms[proc_ptr].value().depth
        + 1
    &&& new_proc_perms[new_proc_ptr].value().uppertree_seq@
        =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().subtree_set@ =~= Set::<ProcPtr>::empty()
    &&& forall|p_ptr: ProcPtr|
     //#![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger new_proc_perms[p_ptr].is_init()]
    //#![trigger new_proc_perms[p_ptr].addr()]
    //#![trigger new_proc_perms[p_ptr].value().parent]
    //#![trigger new_proc_perms[p_ptr].value().parent_rev_ptr]
    //#![trigger new_proc_perms[p_ptr].value().children]
    //#![trigger new_proc_perms[p_ptr].value().depth]
    //#![trigger new_proc_perms[p_ptr].value().uppertree_seq]

        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != proc_ptr ==> new_proc_perms[p_ptr].value().parent
            =~= old_proc_perms[p_ptr].value().parent && new_proc_perms[p_ptr].value().parent_rev_ptr
            =~= old_proc_perms[p_ptr].value().parent_rev_ptr
            && new_proc_perms[p_ptr].value().children =~= old_proc_perms[p_ptr].value().children
            && new_proc_perms[p_ptr].value().depth =~= old_proc_perms[p_ptr].value().depth
            && new_proc_perms[p_ptr].value().uppertree_seq
            =~= old_proc_perms[p_ptr].value().uppertree_seq
    &&& forall|p_ptr: ProcPtr|
     //#![trigger new_proc_perms.dom().contains(p_ptr)]
    //#![trigger new_proc_perms[p_ptr].value().subtree_set]

        #![trigger new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)]
        new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)
            ==> new_proc_perms[p_ptr].value().subtree_set@
            =~= old_proc_perms[p_ptr].value().subtree_set@.insert(new_proc_ptr)
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger old_proc_perms[p_ptr].value().subtree_set]
    //#![trigger new_proc_perms[p_ptr].value().subtree_set]

        proc_tree_dom.contains(p_ptr)
            && new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr) == false
            ==> new_proc_perms[p_ptr].value().subtree_set
            =~= old_proc_perms[p_ptr].value().subtree_set
    &&& new_proc_perms[proc_ptr].value().parent =~= old_proc_perms[proc_ptr].value().parent
    &&& new_proc_perms[proc_ptr].value().parent_rev_ptr
        =~= old_proc_perms[proc_ptr].value().parent_rev_ptr
    &&& new_proc_perms[proc_ptr].value().children@
        =~= old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr)
    &&& new_proc_perms[proc_ptr].value().depth =~= old_proc_perms[proc_ptr].value().depth
    &&& new_proc_perms[proc_ptr].value().uppertree_seq
        =~= old_proc_perms[proc_ptr].value().uppertree_seq
    &&& new_proc_perms[proc_ptr].value().children.wf()
    &&& new_proc_perms[proc_ptr].value().children@
        == old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr)
    &&& new_proc_perms[proc_ptr].value().children.len()
        == old_proc_perms[proc_ptr].value().children.len() + 1
    &&&
    forall|v:ProcPtr|
    #![auto]
    old_proc_perms[proc_ptr].value().children@.contains(v) ==> 
        old_proc_perms[proc_ptr].value().children.get_node_ref(v) == 
            new_proc_perms[proc_ptr].value().children.get_node_ref(v)
    &&& new_proc_perms[proc_ptr].value().children.get_node_ref(new_proc_ptr) ==
        new_proc_perms[new_proc_ptr].value().parent_rev_ptr.unwrap()
    &&& new_proc_perms[proc_ptr].value().children.unique()
}

    #[verifier::spinoff_prover]
pub proof fn new_proc_preserve_tree_inv_4(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_subtree_set_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
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
pub proof fn seq_push_unique_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() && s.contains(v) == false ==> s.push(v).no_duplicates() && s.push(
                v,
            ).index_of(v) == s.push(v).len() - 1,
        forall|s: Seq<A>, v: A, y: A|
            #![auto]
            s.no_duplicates() && s.contains(v) && s.contains(y) == false ==> s.push(y).index_of(v)
                == s.index_of(v),
	{
		unimplemented!()
	}


}
