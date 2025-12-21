use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type ProcPtr = usize;
pub type VAddr = usize;
pub type CpuId = usize;
pub type IOid = usize;
pub const PROC_CHILD_LIST_LEN: usize = 10;
pub const MAX_NUM_THREADS_PER_PROC: usize = 128;
pub const MAX_CONTAINER_SCHEDULER_LEN: usize = 10;
pub const CONTAINER_PROC_LIST_LEN: usize = 10;
pub const CONTAINER_CHILD_LIST_LEN: usize = 10;
pub type Pcid = usize;

pub type ThreadPtr = usize;
pub type EndpointPtr = usize;
pub type ContainerPtr = usize;
pub type PagePtr = usize;
pub type EndpointIdx = usize;
pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;
pub const PAGE_SZ_4k: usize = 1usize << 12;
pub type SLLIndex = i32;
pub const MAX_NUM_THREADS_PER_ENDPOINT: usize = 128;


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


	#[verifier::external_body]
    #[verifier::spinoff_prover]
    pub proof fn unique_implys_no_duplicates(&self)
        requires
            self.unique(),
            self.wf(),
        ensures
            self@.no_duplicates(),
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

    pub open spec fn container_tree_wf(&self) -> bool {
        &&& container_tree_wf(self.root_container, self.container_perms@)
    }

    pub open spec fn proc_perms_wf(&self) -> bool {
        &&& proc_perms_wf(self.process_perms@)
    }

    #[verifier(inline)]
    pub open spec fn process_tree_wf(&self, container_ptr: ContainerPtr) -> bool
        recommends
            self.container_dom().contains(container_ptr),
            self.container_perms_wf(),
            self.get_container(container_ptr).root_process.is_Some(),
    {
        proc_tree_wf(
            self.get_container(container_ptr).root_process.unwrap(),
            self.get_container(container_ptr).owned_procs@.to_set(),
            self.process_perms@,
        )
    }

    pub open spec fn process_trees_wf(&self) -> bool
        recommends
            self.container_perms_wf(),
    {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.process_tree_wf(c_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).root_process.is_Some()
                ==> self.process_tree_wf(c_ptr)
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).root_process, self.get_container(c_ptr).owned_procs]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).root_process.is_None()
                ==> self.get_container(c_ptr).owned_procs@.len() == 0
    }

    pub open spec fn cpus_wf(&self) -> bool {
        &&& 
        self.cpu_list.wf()
        &&&
        forall|cpu_i:CpuId|
            // #![trigger self.cpu_list@[cpu_i as int]]
            #![trigger self.cpu_list@[cpu_i as int].active]
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS 
            && self.cpu_list@[cpu_i as int].active == false 
            ==> 
            self.cpu_list@[cpu_i as int].current_thread.is_None()

    }

    pub open spec fn container_cpu_wf(&self) -> bool {
        &&& forall|cpu_i: CpuId|
            #![trigger self.cpu_list@[cpu_i as int]]
            0 <= cpu_i < NUM_CPUS 
            ==> 
            self.container_dom().contains(self.cpu_list@[cpu_i as int].owning_container) 
            && 
            self.get_container(self.cpu_list@[cpu_i as int].owning_container).owned_cpus@.contains(cpu_i)
        &&&
        forall|c_ptr: ContainerPtr, cpu_i: CpuId|
            #![trigger self.get_container(c_ptr).owned_cpus@.contains(cpu_i)]
            #![trigger self.get_container(c_ptr).owned_cpus, self.cpu_list[cpu_i as int].owning_container]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_cpus@.contains(cpu_i)
            ==>
            0 <= cpu_i < NUM_CPUS
            &&
            self.cpu_list[cpu_i as int].owning_container == c_ptr 
    }

    pub open spec fn threads_cpu_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> (
                self.thread_perms@[t_ptr].value().running_cpu.is_Some()
                <==> 
                self.thread_perms@[t_ptr].value().state == ThreadState::RUNNING
            )
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr)
                && self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
                ==> 
                0 <= self.thread_perms@[t_ptr].value().running_cpu.unwrap() < NUM_CPUS
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.is_Some()
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.unwrap()
                    == t_ptr
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].owning_container
                    == self.thread_perms@[t_ptr].value().owning_container
        &&& forall|cpu_i: CpuId|
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS && self.cpu_list@[cpu_i as int].current_thread.is_Some()
                ==> 
                self.thread_perms@.dom().contains(self.cpu_list@[cpu_i as int].current_thread.unwrap())
                && self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.is_Some()
                && self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.unwrap() == cpu_i 
                && self.cpu_list@[cpu_i as int].owning_container
                == self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().owning_container
    }

    pub open spec fn memory_disjoint(&self) -> bool {
        &&& self.container_dom().disjoint(self.process_perms@.dom())
        &&& self.container_dom().disjoint(self.thread_perms@.dom())
        &&& self.container_dom().disjoint(self.endpoint_perms@.dom())
        &&& self.process_perms@.dom().disjoint(self.thread_perms@.dom())
        &&& self.process_perms@.dom().disjoint(self.endpoint_perms@.dom())
        &&& self.thread_perms@.dom().disjoint(self.endpoint_perms@.dom())
    }

    pub open spec fn container_fields_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
        #![trigger self.get_container(c_ptr).owned_cpus.wf()]
        #![trigger self.get_container(c_ptr).scheduler.wf()]
        #![trigger self.get_container(c_ptr).owned_procs.wf()]
        #![trigger self.get_container(c_ptr).scheduler.unique()]
        #![trigger self.get_container(c_ptr).owned_procs.unique()]
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

    pub open spec fn processes_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).owned_procs]
            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&& forall|c_ptr: ContainerPtr, child_p_ptr: ProcPtr|
            #![trigger self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_procs@.contains(child_p_ptr) 
            ==> 
            self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&& forall|p_ptr: ProcPtr|
            #![trigger self.process_perms@[p_ptr].value().owning_container]
            self.process_perms@.dom().contains(p_ptr) 
            ==> 
            self.container_dom().contains(self.process_perms@[p_ptr].value().owning_container) 
            && self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs@.contains(p_ptr) 
            && self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.get_node_ref(p_ptr) 
                == self.process_perms@[p_ptr].value().rev_ptr
    }

    pub open spec fn threads_process_wf(&self) -> bool {
        &&& forall|p_ptr: ProcPtr, child_t_ptr: ThreadPtr|
            #![trigger self.process_perms@.dom().contains(p_ptr), self.thread_perms@[child_t_ptr].value().owning_proc]
            #![trigger self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
            self.process_perms@.dom().contains(p_ptr)
                && self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)
            ==> self.thread_perms@.dom().contains(child_t_ptr)
                && self.thread_perms@[child_t_ptr].value().owning_proc == p_ptr
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().owning_proc]
            #![trigger self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> 
            self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container) 
            && self.process_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_proc)
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.get_node_ref(t_ptr)
                == self.thread_perms@[t_ptr].value().proc_rev_ptr
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owning_container
                == self.thread_perms@[t_ptr].value().owning_container
    }

    pub open spec fn threads_perms_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@.dom().contains(t_ptr)]
            self.thread_perms@.dom().contains(t_ptr) ==> 
                self.thread_perms@[t_ptr].is_init()
                && self.thread_perms@[t_ptr].addr() == t_ptr
                && self.thread_perms@[t_ptr].value().endpoint_descriptors.wf() 
                && (self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().is_Some()
                    ==> self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().unwrap().wf())
    }

    pub open spec fn threads_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).owned_threads]
            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_threads@.subset_of(self.thread_perms@.dom())
        &&& forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
            #![trigger  self.get_container(c_ptr).owned_threads, self.get_thread(t_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_threads@.contains(t_ptr) 
            ==> 
            self.get_thread(t_ptr).owning_container == c_ptr
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> 
            self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container) 
            && self.get_container(self.thread_perms@[t_ptr].value().owning_container).owned_threads@.contains(t_ptr)
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
    }

    pub open spec fn threads_endpoint_descriptors_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr, e_idx: EndpointIdx|
            #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int]]
            self.thread_perms@.dom().contains(t_ptr) 
            && 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS
            && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
            ==> 
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap())
            && self.endpoint_perms@[self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()].value().owning_threads@.contains((t_ptr, e_idx))
        &&& forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr, e_idx: EndpointIdx|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))]
            self.endpoint_perms@.dom().contains(e_ptr)
                && self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))
                ==> 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@.dom().contains(
                t_ptr,
            ) && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
                && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()
                == e_ptr
    }

    pub open spec fn endpoints_queue_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().blocking_endpoint_ptr]
            #![trigger self.thread_perms@[t_ptr].value().endpoint_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr) && self.thread_perms@[t_ptr].value().state
                == ThreadState::BLOCKED
                ==> self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.is_Some()
                && self.thread_perms@[t_ptr].value().blocking_endpoint_index.is_Some() && 0
                <= self.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap()
                < MAX_NUM_ENDPOINT_DESCRIPTORS
                && self.thread_perms@[t_ptr].value().endpoint_descriptors@[self.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap() as int]
                == Some(self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap())
                && self.thread_perms@[t_ptr].value().endpoint_rev_ptr.is_Some()
                && self.endpoint_perms@.dom().contains(
                self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap(),
            )
                && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(
            t_ptr)
                && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.get_node_ref(t_ptr) 
                == self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap()
        &&& forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr|
            #![trigger self.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr), ]
            self.endpoint_perms@.dom().contains(e_ptr) && self.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr)
                ==> 
                self.thread_perms@.dom().contains(t_ptr)
                && self.thread_perms@[t_ptr].value().blocking_endpoint_ptr
                == Some(e_ptr)
                && self.thread_perms@[t_ptr].value().state
                == ThreadState::BLOCKED
    }

    pub open spec fn endpoints_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr, child_e_ptr: EndpointPtr|
            #![trigger self.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(
                c_ptr,
            ).owned_endpoints@.contains(child_e_ptr) ==> self.endpoint_perms@.dom().contains(
                child_e_ptr,
            ) && self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr
        &&& forall|e_ptr: EndpointPtr|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
            self.endpoint_perms@.dom().contains(e_ptr) ==> self.container_dom().contains(
                self.endpoint_perms@[e_ptr].value().owning_container,
            ) && self.get_container(
                self.endpoint_perms@[e_ptr].value().owning_container,
            ).owned_endpoints@.contains(e_ptr) 
    }

    pub open spec fn endpoints_within_subtree(&self) -> bool{
        &&&
        forall|e_ptr:EndpointPtr, t_ptr:ThreadPtr, edp_idx:EndpointIdx|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx))]
            self.endpoint_perms@.dom().contains(e_ptr) && self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx)) 
            ==> 
            (
                self.thread_perms@[t_ptr].value().owning_container == self.endpoint_perms@[e_ptr].value().owning_container
                ||
                self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().subtree_set@.contains(self.thread_perms@[t_ptr].value().owning_container)
            )
    }

    pub open spec fn schedulers_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().scheduler_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr)
            && self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED 
            ==> 
            self.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler@.contains(t_ptr)
            && self.thread_perms@[t_ptr].value().scheduler_rev_ptr.is_Some()
            && self.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler.get_node_ref(t_ptr) 
                == self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap()
        &&& forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
            #![trigger self.get_container(c_ptr).scheduler@.contains(t_ptr)]
            #![trigger self.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().owning_container]
            #![trigger self.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().state]
            self.container_dom().contains(c_ptr) 
            && self.get_container(c_ptr).scheduler@.contains(t_ptr) 
            ==> 
            self.thread_perms@.dom().contains(t_ptr)
            && self.thread_perms@[t_ptr].value().owning_container == c_ptr
            && self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool {
        &&& forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
             #![trigger self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
            self.process_perms@.dom().contains(p_ptr_i) 
            && self.process_perms@.dom().contains(p_ptr_j) 
            && p_ptr_i != p_ptr_j 
            ==> self.process_perms@[p_ptr_i].value().pcid != self.process_perms@[p_ptr_j].value().pcid
        &&& forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
            #![trigger self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
            self.process_perms@.dom().contains(p_ptr_i) 
            && self.process_perms@.dom().contains(p_ptr_j) 
            && p_ptr_i != p_ptr_j 
            && self.process_perms@[p_ptr_i].value().ioid.is_Some()
            && self.process_perms@[p_ptr_j].value().ioid.is_Some()
            ==> 
            self.process_perms@[p_ptr_i].value().ioid.unwrap() != self.process_perms@[p_ptr_j].value().ioid.unwrap()
    }

	#[verifier::external_body]
    pub closed spec fn internal_wf(&self) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
    pub broadcast proof fn reveal_process_manager_wf(&self)
        ensures
            #[trigger] self.internal_wf() <==> {
                &&& self.cpus_wf()
                &&& self.container_cpu_wf()
                &&& self.memory_disjoint()
                &&& self.processes_container_wf()
                &&& self.threads_process_wf()
                &&& self.threads_endpoint_descriptors_wf()
                &&& self.endpoints_queue_wf()
                &&& self.endpoints_container_wf()
                &&& self.schedulers_wf()
                &&& self.pcid_ioid_wf()
                &&& self.threads_cpu_wf()
                &&& self.threads_container_wf()
                &&& self.container_tree_wf()
                &&& self.process_trees_wf()        
                &&& self.endpoints_within_subtree()
    }
	{
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

pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 128;

pub const KERNEL_MEM_END_L4INDEX: usize = 1;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const NUM_CPUS: usize = 32;

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



// File: array_set.rs
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub len: usize,

    pub set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

	#[verifier::external_body]
    pub closed spec fn view(&self) -> Set<usize>{
		unimplemented!()
	}


	#[verifier::external_body]
    pub closed spec fn wf(&self) -> bool{
		unimplemented!()
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

	#[verifier::external_body]
pub closed spec fn container_root_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn container_childern_parent_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn containers_linkedlist_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn container_childern_depth_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn container_subtree_set_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn container_uppertree_seq_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn container_subtree_set_exclusive(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
		unimplemented!()
	}


pub open spec fn container_tree_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    // &&&
    // container_perms_wf(container_perms)
    &&& container_root_wf(root_container, container_perms)
    &&& container_childern_parent_wf(root_container, container_perms)
    &&& containers_linkedlist_wf(root_container, container_perms)
    &&& container_childern_depth_wf(root_container, container_perms)
    &&& container_subtree_set_wf(root_container, container_perms)
    &&& container_uppertree_seq_wf(root_container, container_perms)
    &&& container_subtree_set_exclusive(root_container, container_perms)
}

	#[verifier::external_body]
pub proof fn container_no_change_to_tree_fields_imply_wf(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_tree_wf(root_container, old_container_perms),
        container_perms_wf(new_container_perms),
        old_container_perms.dom() =~= new_container_perms.dom(),
        forall|c_ptr: ContainerPtr|
         //#![trigger old_container_perms[c_ptr]]
        //#![trigger new_container_perms[c_ptr]]

            #![trigger old_container_perms.dom().contains(c_ptr)]
            old_container_perms.dom().contains(c_ptr) ==> new_container_perms[c_ptr].is_init()
                && old_container_perms[c_ptr].value().parent
                =~= new_container_perms[c_ptr].value().parent
                && old_container_perms[c_ptr].value().parent_rev_ptr
                =~= new_container_perms[c_ptr].value().parent_rev_ptr
                && old_container_perms[c_ptr].value().children
                =~= new_container_perms[c_ptr].value().children
                && old_container_perms[c_ptr].value().depth
                =~= new_container_perms[c_ptr].value().depth
                && old_container_perms[c_ptr].value().uppertree_seq
                =~= new_container_perms[c_ptr].value().uppertree_seq
                && old_container_perms[c_ptr].value().subtree_set
                =~= new_container_perms[c_ptr].value().subtree_set,
    ensures
        container_tree_wf(root_container, new_container_perms),
	{
		unimplemented!()
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

	#[verifier::external_body]
pub closed spec fn proc_root_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn proc_childern_parent_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn procs_linkedlist_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn proc_childern_depth_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn proc_subtree_set_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn proc_uppertree_seq_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn proc_subtree_set_exclusive(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
		unimplemented!()
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

	#[verifier::external_body]
pub proof fn process_no_change_to_trees_fields_imply_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms),
        proc_perms_wf(new_proc_perms),
        old_proc_perms.dom() =~= new_proc_perms.dom(),
        forall|p_ptr: ProcPtr|
        //#![trigger old_proc_perms[p_ptr]]
        //#![trigger new_proc_perms[p_ptr]]

            #![trigger old_proc_perms.dom().contains(p_ptr)]
            old_proc_perms.dom().contains(p_ptr) ==> new_proc_perms[p_ptr].is_init()
                && old_proc_perms[p_ptr].value().parent =~= new_proc_perms[p_ptr].value().parent
                && old_proc_perms[p_ptr].value().parent_rev_ptr
                =~= new_proc_perms[p_ptr].value().parent_rev_ptr
                && old_proc_perms[p_ptr].value().children =~= new_proc_perms[p_ptr].value().children
                && old_proc_perms[p_ptr].value().depth =~= new_proc_perms[p_ptr].value().depth
                && old_proc_perms[p_ptr].value().uppertree_seq
                =~= new_proc_perms[p_ptr].value().uppertree_seq
                && old_proc_perms[p_ptr].value().subtree_set
                =~= new_proc_perms[p_ptr].value().subtree_set,
    ensures
        proc_tree_wf(root_proc, proc_tree_dom, new_proc_perms),
	{
		unimplemented!()
	}


// File: process_manager/endpoint_util_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub fn endpoint_push(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    t_ptr: ThreadPtr,
) -> (ret: SLLIndex)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        // endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().queue.wf(),
        endpoint_perm@.value().queue@ == old(endpoint_perm)@.value().queue@.push(t_ptr),
        endpoint_perm@.value().queue.len() == old(endpoint_perm)@.value().queue.len() + 1,
        forall|v:ThreadPtr|
            #![auto]
            old(endpoint_perm)@.value().queue@.contains(v) ==> 
                old(endpoint_perm)@.value().queue.get_node_ref(v) == 
                    endpoint_perm@.value().queue.get_node_ref(v),
        endpoint_perm@.value().queue.get_node_ref(t_ptr) == ret,
        endpoint_perm@.value().queue.unique(),
	{
		unimplemented!()
	}


// File: process_manager/impl_base.rs
impl ProcessManager {

    /// Overview:
    /// yield the given thread
    /// save the payload onto given thread
    /// push given thread onto endpoint queue
    pub fn block_running_thread(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        ipc_payload: IPCPayLoad,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some()
                ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) 
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr 
                ==> 
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) 
                && 
                e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap() 
                ==> old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors 
                =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@ == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@.push(thread_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        proof {
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.unique_implys_no_duplicates();
        }
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let sll = endpoint_push(endpoint_ptr, &mut endpoint_perm, thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            Some(endpoint_ptr),
            Some(sll),
            None,
            ThreadState::BLOCKED,
            ipc_payload,
            Some(endpoint_index),
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }


}



// File: process_manager/thread_util_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub fn thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    blocking_endpoint_ptr: Option<EndpointPtr>,
    endpoint_rev_ptr: Option<SLLIndex>,
    scheduler_rev_ptr: Option<SLLIndex>,
    state: ThreadState,
    ipc_payload: IPCPayLoad,
    blocking_endpoint_index: Option<EndpointIdx>,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        thread_perm@.is_init(),
        thread_perm@.addr() == thread_ptr,
        thread_perm@.value().owning_container == old(thread_perm)@.value().owning_container,
        thread_perm@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        thread_perm@.value().state == state,
        thread_perm@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        thread_perm@.value().scheduler_rev_ptr == scheduler_rev_ptr,
        thread_perm@.value().blocking_endpoint_ptr == blocking_endpoint_ptr,
        thread_perm@.value().endpoint_rev_ptr == endpoint_rev_ptr,
        thread_perm@.value().running_cpu.is_None(),
        thread_perm@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        thread_perm@.value().ipc_payload == ipc_payload,
        thread_perm@.value().error_code == old(thread_perm)@.value().error_code,
        thread_perm@.value().trap_frame == old(thread_perm)@.value().trap_frame,
        thread_perm@.value().blocking_endpoint_index == blocking_endpoint_index,
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


// File: util/page_ptr_util_u.rs
pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4k_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}


}
