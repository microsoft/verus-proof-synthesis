use vstd::prelude::*;

verus! {
    pub fn main()
    {
    }


    /*pmem\pmemspec_t*/
    pub open spec fn const_persistence_chunk_size() -> int { 8 }

    pub struct PersistentMemoryByte {
        pub state_at_last_flush: u8,
        pub outstanding_write: Option<u8>,
    }

    impl PersistentMemoryByte {

        pub open spec fn flush_byte(self) -> u8
        {
            match self.outstanding_write {
                None => self.state_at_last_flush,
                Some(b) => b
            }
        }
    }

    pub struct PersistentMemoryRegionView
    {
        pub state: Seq<PersistentMemoryByte>,
    }

    impl PersistentMemoryRegionView
    {

        pub open spec fn len(self) -> nat
        {
            self.state.len()
        }

        pub open spec fn chunk_corresponds_ignoring_outstanding_writes(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].state_at_last_flush
        }

        pub open spec fn chunk_corresponds_after_flush(self, chunk: int, bytes: Seq<u8>) -> bool
        {
            forall |addr: int| {
                &&& 0 <= addr < self.len()
                &&& addr / const_persistence_chunk_size() == chunk
            } ==> #[trigger] bytes[addr] == self.state[addr].flush_byte()
        }

        pub open spec fn can_crash_as(self, bytes: Seq<u8>) -> bool
        {
            &&& bytes.len() == self.len()
            &&& forall |chunk| {
                  ||| self.chunk_corresponds_ignoring_outstanding_writes(chunk, bytes)
                  ||| self.chunk_corresponds_after_flush(chunk, bytes)
              }
        }
    }

    pub struct PersistentMemoryConstants {
        pub impervious_to_corruption: bool
    }

    pub trait PersistentMemoryRegion : Sized {}

/*pmem\subregion_v*/


pub open spec fn memories_differ_only_where_subregion_allows(
    mem1: Seq<u8>,
    mem2: Seq<u8>,                                                         
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
    recommends
        0 <= start,
        0 <= len,
        mem1.len() == mem2.len(),
        start + len <= mem1.len(),
{
    forall |addr: int| {
       ||| 0 <= addr < start
       ||| start + len <= addr < mem1.len()
       ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
    } ==> mem1[addr] == #[trigger] mem2[addr]
}

pub open spec fn views_differ_only_where_subregion_allows(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    start: nat,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool
) -> bool
    recommends
        0 <= start,
        0 <= len,
        start + len <= v1.len(),
        v1.len() == v2.len()
{
    forall |addr: int| {
       ||| 0 <= addr < start
       ||| start + len <= addr < v1.len()
       ||| start <= addr < start + len && !is_writable_absolute_addr_fn(addr)
    } ==> v1.state[addr] == #[trigger] v2.state[addr]
}

pub open spec fn condition_sufficient_to_create_wrpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
) -> bool
    where
        Perm: CheckPermission<Seq<u8>>,
{
    &&& 0 <= len
    &&& start + len <= region_view.len() <= u64::MAX
    &&& forall |crash_state| region_view.can_crash_as(crash_state) ==> condition(crash_state)
    &&& forall |crash_state| condition(crash_state) ==> perm.check_permission(crash_state)
    &&& forall |s1: Seq<u8>, s2: Seq<u8>| {
           &&& condition(s1)
           &&& s1.len() == s2.len() == region_view.len()
           &&& #[trigger] memories_differ_only_where_subregion_allows(s1, s2, start as nat, len,
                                                                    is_writable_absolute_addr_fn)
       } ==> condition(s2)
}

pub proof fn lemma_condition_sufficient_to_create_wrpm_subregion<Perm>(
    region_view: PersistentMemoryRegionView,
    perm: &Perm,
    start: u64,
    len: nat,
    is_writable_absolute_addr_fn: spec_fn(int) -> bool,
    condition: spec_fn(Seq<u8>) -> bool,
)
    where
        Perm: CheckPermission<Seq<u8>>,
    requires
        condition_sufficient_to_create_wrpm_subregion(region_view, perm, start, len, is_writable_absolute_addr_fn,
                                                      condition),
    ensures
        forall |alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>| {
            &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
            &&& region_view.len() == alt_region_view.len()
            &&& views_differ_only_where_subregion_allows(region_view, alt_region_view, start as nat, len,
                                                       is_writable_absolute_addr_fn)
        } ==> perm.check_permission(alt_crash_state),
{
    assert forall |alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>| {
        &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
        &&& region_view.len() == alt_region_view.len()
        &&& views_differ_only_where_subregion_allows(region_view, alt_region_view, start as nat, len,
                                                   is_writable_absolute_addr_fn)
    } implies perm.check_permission(alt_crash_state) by {
        let crash_state = Seq::<u8>::new(
            alt_crash_state.len(),
            |addr| {
                if !(start <= addr < start + len && is_writable_absolute_addr_fn(addr)) {
                    alt_crash_state[addr]
                }
                else {
                    let chunk = addr / const_persistence_chunk_size();
                    if alt_region_view.chunk_corresponds_ignoring_outstanding_writes(chunk, alt_crash_state) {
                        region_view.state[addr].state_at_last_flush
                    }
                    else {
                        region_view.state[addr].flush_byte()
                    }
                }
            }
        );
        assert(memories_differ_only_where_subregion_allows(crash_state, alt_crash_state, start as nat, len,
                                                           is_writable_absolute_addr_fn));
        assert(region_view.can_crash_as(crash_state)) by {
            assert forall |chunk| {
                ||| region_view.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state)
                ||| region_view.chunk_corresponds_after_flush(chunk, crash_state)
            } by {
                if alt_region_view.chunk_corresponds_ignoring_outstanding_writes(chunk, alt_crash_state) {
                    assert(region_view.chunk_corresponds_ignoring_outstanding_writes(chunk, crash_state));
                }
                else {
                    assert(region_view.chunk_corresponds_after_flush(chunk, crash_state));
                }
            }
        }
        assert(condition(crash_state));
    }
}

pub struct WriteRestrictedPersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
}

pub struct WritablePersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}


/*pmem\wrpm_t*/

pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
}

}
