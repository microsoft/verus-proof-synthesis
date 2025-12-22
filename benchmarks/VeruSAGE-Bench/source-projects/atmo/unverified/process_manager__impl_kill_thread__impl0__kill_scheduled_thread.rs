use vstd::prelude::*;
use vstd::simple_pptr::*;

fn main() {}

verus!{

pub type IOid = usize;
pub type CpuId = usize;
pub type PagePtr = usize;
pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointPtr = usize;
pub type EndpointIdx = usize;
pub type Pcid = usize;
pub type PAddr = usize;
pub type VAddr = usize;
pub type ContainerPtr = usize;
pub type SLLIndex = i32;
pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;
pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;
pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;
pub const PAGE_SZ_4k: usize = 1usize << 12;
pub const PAGE_SZ_2m: usize = 1usize << 21;
pub const PAGE_SZ_1g: usize = 1usize << 30;
pub const MAX_CONTAINER_SCHEDULER_LEN: usize = 10;
pub const CONTAINER_PROC_LIST_LEN: usize = 10;
pub const CONTAINER_CHILD_LIST_LEN: usize = 10;
pub const MAX_NUM_THREADS_PER_PROC: usize = 128;
pub const MAX_NUM_THREADS_PER_ENDPOINT: usize = 128;
pub const PROC_CHILD_LIST_LEN: usize = 10;

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

    pub open spec fn processes_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).owned_procs]
            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&& forall|c_ptr: ContainerPtr, child_p_ptr: ProcPtr|
         // #![trigger self.container_dom().contains(c_ptr), self.process_perms@[child_p_ptr].value().owning_container]

            #![trigger self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_procs@.contains(child_p_ptr) 
            ==> 
            self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&& forall|p_ptr: ProcPtr|
            #![trigger self.process_perms@[p_ptr].value().owning_container]
        // #![trigger self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs]
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

    pub open spec fn threads_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
         // #![trigger self.container_dom().contains(c_ptr)]

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
        // &&
        // self.endpoint_perms@[e_ptr].value().owning_threads@.subset_of(self.thread_perms@.dom())

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
         // #![trigger self.thread_perms@[t_ptr].value().state]

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
            // #![trigger self.process_perms@.dom().contains(p_ptr_i), self.process_perms@.dom().contains(p_ptr_j), self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
             #![trigger self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
            self.process_perms@.dom().contains(p_ptr_i) 
            && self.process_perms@.dom().contains(p_ptr_j) 
            && p_ptr_i != p_ptr_j 
            ==> self.process_perms@[p_ptr_i].value().pcid != self.process_perms@[p_ptr_j].value().pcid
        &&& forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
            // #![trigger self.process_perms@.dom().contains(p_ptr_i), self.process_perms@.dom().contains(p_ptr_j), self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
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
    },
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


impl ProcessManager {

	#[verifier::external_body]
    pub proof fn proc_owned_threads_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![trigger  self.get_proc(p_ptr_i).owned_threads, self.get_proc(p_ptr_j).owned_threads]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j)
                    && p_ptr_i != p_ptr_j ==> self.get_proc(p_ptr_i).owned_threads@.disjoint(
                    self.get_proc(p_ptr_j).owned_threads@,
                    ),
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


// File: process_manager/container_util_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub fn scheduler_remove_thread(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    rev_ptr: SLLIndex,
    thread_ptr_g: Ghost<ThreadPtr>,
) -> (ret: ThreadPtr)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.get_node_ref(thread_ptr_g@) == rev_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr,
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,
        container_perm@.value().scheduler.wf(),
        container_perm@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() - 1,
        ret == thread_ptr_g@,
        container_perm@.value().scheduler.unique(),
        container_perm@.value().scheduler@ =~= old(container_perm)@.value().scheduler@.remove_value(ret),
        forall|v:ThreadPtr|
            #![auto]
            container_perm@.value().scheduler@.contains(v) ==> 
                old(container_perm)@.value().scheduler.get_node_ref(v) == 
                    container_perm@.value().scheduler.get_node_ref(v),
	{
		unimplemented!()
	}

	#[verifier::external_body]
#[verifier(external_body)]
pub fn container_set_owned_threads(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    owned_threads: Ghost<Set<ThreadPtr>>,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr,
        container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        container_perm@.value().parent =~= old(container_perm)@.value().parent,
        container_perm@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        container_perm@.value().children =~= old(container_perm)@.value().children,
        container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        // container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        container_perm@.value().depth =~= old(container_perm)@.value().depth,
        container_perm@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        container_perm@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        container_perm@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        container_perm@.value().root_process =~= old(container_perm)@.value().root_process,
        container_perm@.value().owned_threads =~= owned_threads,
	{
		unimplemented!()
	}


// File: process_manager/impl_kill_thread.rs
impl ProcessManager {

    pub fn kill_scheduled_thread(
        &mut self,
        thread_ptr: ThreadPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            forall|edp_idx:EndpointIdx|
                #![auto]
                0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS 
                ==>
                old(self).get_thread(thread_ptr).endpoint_descriptors@[edp_idx as int].is_None(),
            old(self).get_thread(thread_ptr).state == ThreadState::SCHEDULED,
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(*old(self), *self, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(*old(self), *self),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr),  
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  
            
            process_mem_unchanged(*old(self), *self),
            self.page_closure() =~= old(self).page_closure().remove(ret.0),
            old(self).page_closure().contains(ret.0),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
            old(self).container_dom().contains(ret.0) == false,
    {
        
        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let proc_rev_ptr = self.get_thread(thread_ptr).proc_rev_ptr;

        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let scheduler_rev_ptr = self.get_thread(thread_ptr).scheduler_rev_ptr.unwrap();
        
        let thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));

        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        proc_remove_thread(proc_ptr, &mut proc_perm, proc_rev_ptr, Ghost(thread_ptr));
       
        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        scheduler_remove_thread(container_ptr, &mut container_perm, scheduler_rev_ptr, Ghost(thread_ptr));
        container_set_owned_threads(container_ptr, &mut container_perm, Ghost(
            old(self).get_container(container_ptr).owned_threads@.remove(thread_ptr)
        ));
      
        thread_to_page(thread_ptr, thread_perm)
    }

}



// File: process_manager/proc_util_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub fn proc_remove_thread(
    proc_ptr: ProcPtr,
    proc_perm: &mut Tracked<PointsTo<Process>>,
    rev_ptr: SLLIndex,
    thread_ptr: Ghost<ThreadPtr>,
) -> (ret: ThreadPtr)
    requires
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().owned_threads.wf(),
        old(proc_perm)@.value().owned_threads@.contains(thread_ptr@),
        old(proc_perm)@.value().owned_threads.get_node_ref(thread_ptr@) == rev_ptr,
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        // proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,
        proc_perm@.value().parent =~= old(proc_perm)@.value().parent,
        proc_perm@.value().parent_rev_ptr =~= old(proc_perm)@.value().parent_rev_ptr,
        proc_perm@.value().children =~= old(proc_perm)@.value().children,
        proc_perm@.value().uppertree_seq =~= old(proc_perm)@.value().uppertree_seq,
        proc_perm@.value().subtree_set =~= old(proc_perm)@.value().subtree_set,
        proc_perm@.value().depth =~= old(proc_perm)@.value().depth,
        proc_perm@.value().dmd_paging_mode =~= old(proc_perm)@.value().dmd_paging_mode,
        proc_perm@.value().owned_threads.wf(),
        proc_perm@.value().owned_threads.len() == old(proc_perm)@.value().owned_threads.len() - 1,
        ret == thread_ptr@,
        forall|v:ThreadPtr|
            #![auto]
            proc_perm@.value().owned_threads@.contains(v) ==> 
                old(proc_perm)@.value().owned_threads.get_node_ref(v) == 
                    proc_perm@.value().owned_threads.get_node_ref(v),
        proc_perm@.value().owned_threads.unique(),
        proc_perm@.value().owned_threads@ =~= old(proc_perm)@.value().owned_threads@.remove_value(ret),
	{
		unimplemented!()
	}


// File: process_manager/spec_util.rs
        pub open spec fn containers_tree_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|container_ptr: ContainerPtr|
                #![trigger old.get_container(container_ptr)]
                new.container_dom().contains(container_ptr) 
                    ==> 
                    {
                        &&& new.get_container(container_ptr).parent =~= old.get_container(container_ptr).parent
                        &&& new.get_container(container_ptr).children =~= old.get_container(container_ptr).children
                        &&& new.get_container(container_ptr).uppertree_seq =~= old.get_container(container_ptr).uppertree_seq
                        &&& new.get_container(container_ptr).subtree_set =~= old.get_container(container_ptr).subtree_set
                        &&& new.get_container(container_ptr).depth =~= old.get_container(container_ptr).depth
                    }
        }

        pub open spec fn process_tree_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|p_ptr: ProcPtr|
                #![trigger old.get_proc(p_ptr)]
                new.proc_dom().contains(p_ptr) 
                    ==> 
                    {
                        &&& new.get_proc(p_ptr).parent =~= old.get_proc(p_ptr).parent
                        &&& new.get_proc(p_ptr).children =~= old.get_proc(p_ptr).children
                        &&& new.get_proc(p_ptr).uppertree_seq =~= old.get_proc(p_ptr).uppertree_seq
                        &&& new.get_proc(p_ptr).subtree_set =~= old.get_proc(p_ptr).subtree_set
                        &&& new.get_proc(p_ptr).depth =~= old.get_proc(p_ptr).depth
                    }
        }

        pub open spec fn process_mem_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|p_ptr: ProcPtr|
                #![trigger old.get_proc(p_ptr)]
                new.proc_dom().contains(p_ptr) 
                    ==> 
                    {
                        &&& new.get_proc(p_ptr).pcid =~= old.get_proc(p_ptr).pcid
                        &&& new.get_proc(p_ptr).ioid =~= old.get_proc(p_ptr).ioid
                    }
        }

        pub open spec fn threads_unchanged_except(old: ProcessManager, new: ProcessManager, changed: Set<ThreadPtr>) -> bool 
        {
            forall|t_ptr: ThreadPtr|
                #![trigger old.get_thread(t_ptr)]
                new.thread_dom().contains(t_ptr) && !changed.contains(t_ptr)
                    ==> new.get_thread(t_ptr) =~= old.get_thread(
                    t_ptr,
                )
        }


// File: process_manager/thread_util_t.rs
	#[verifier::external_body]
#[verifier(external_body)]
pub fn thread_to_page(
    thread_ptr: ThreadPtr,
    thread_perm: Tracked<PointsTo<Thread>>,
) -> (ret: (PagePtr, Tracked<PagePerm4k>))
    requires
        thread_perm@.is_init(),
        thread_perm@.addr() == thread_ptr,
    ensures
        ret.0 == thread_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
	{
		unimplemented!()
	}


// File: lemma/lemma_u.rs
	#[verifier::external_body]
pub proof fn seq_remove_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            0 <= i < s.len() && s.contains(v) && s[i] != v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v),
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.subrange(0,i), s.contains(v)]
            0 <= i < s.len() && s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ).contains(v) == false,
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j]]
            0 <= i < s.len() && 0 <= j < i ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j] == s[j],
        forall|s: Seq<A>, i: int, j: int|
            #![trigger s.subrange(0,i), s[j+1]]
            0 <= i < s.len() && i <= j < s.len() - 1 ==> s.subrange(0, i).add(s.subrange(i + 1, s.len() as int))[j]
                == s[j + 1],
        forall|s: Seq<A>, v: A, i: int|
            #![trigger s.remove_value(v), s.subrange(0,i)]
            0 <= i < s.len() && s.contains(v) && s[i] == v && s.no_duplicates() ==> s.subrange(0, i).add(
                s.subrange(i + 1, s.len() as int),
            ) == s.remove_value(v),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn seq_remove_lemma_2<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A|
            x != v && s.no_duplicates() ==> s.remove_value(x).contains(v) == s.contains(v),
        forall|s: Seq<A>, v: A|
            #![auto]
            s.no_duplicates() ==> s.remove_value(v).contains(v) == false,
	{
		unimplemented!()
	}


// File: util/page_ptr_util_u.rs
pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4k_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}


}
