use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

broadcast use pmcopy_axioms;

pub open spec fn get_subregion_view(
    region: PersistentMemoryRegionView,
    start: nat,
    len: nat,
) -> PersistentMemoryRegionView
    recommends
        0 <= start,
        0 <= len,
        start + len <= region.len(),
{
    PersistentMemoryRegionView{ state: region.state.subrange(start as int, (start + len) as int) }
}

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
        assert(region_view.can_crash_as(crash_state));
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

impl WriteRestrictedPersistentMemorySubregion
{
    pub exec fn new<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            0 <= len,
            start + len <= wrpm@.len() <= u64::MAX,
            forall |alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>| {
                &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
                &&& wrpm@.len() == alt_region_view.len()
                &&& views_differ_only_where_subregion_allows(wrpm@, alt_region_view, start as nat, len,
                                                           is_writable_absolute_addr_fn)
            } ==> perm.check_permission(alt_crash_state),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(wrpm.constants()),
            initial_region_view_: Ghost(wrpm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub exec fn new_with_condition<Perm, PMRegion>(
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
        Ghost(condition): Ghost<spec_fn(Seq<u8>) -> bool>,
    ) -> (result: Self)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            wrpm.inv(),
            condition_sufficient_to_create_wrpm_subregion(wrpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                          condition),
        ensures
            result.inv(wrpm, perm),
            result.constants() == wrpm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == wrpm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(wrpm) == result.initial_subregion_view(),
            result.view(wrpm) == get_subregion_view(wrpm@, start as nat, len),
    {
        proof {
            lemma_condition_sufficient_to_create_wrpm_subregion(wrpm@, perm, start, len, is_writable_absolute_addr_fn,
                                                                condition);
        }
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(wrpm.constants()),
            initial_region_view_: Ghost(wrpm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
    {
        self.start() + self.len()
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_view_@
    }

    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool
    {
        self.is_writable_absolute_addr_fn_@
    }

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool
    {
        self.is_writable_absolute_addr_fn()(addr + self.start())
    }

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView
    {
        get_subregion_view(self.initial_region_view(), self.start(), self.len())
    }

    pub closed spec fn view<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>
    ) -> PersistentMemoryRegionView
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        get_subregion_view(wrpm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& wrpm.inv()
        &&& wrpm.constants() == self.constants()
        &&& wrpm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= wrpm@.len()
        &&& self.view(wrpm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
        &&& forall |alt_region_view: PersistentMemoryRegionView, alt_crash_state: Seq<u8>| {
              &&& #[trigger] alt_region_view.can_crash_as(alt_crash_state)
              &&& self.initial_region_view().len() == alt_region_view.len()
              &&& views_differ_only_where_subregion_allows(self.initial_region_view(), alt_region_view,
                                                         self.start(), self.len(),
                                                         self.is_writable_absolute_addr_fn())
           } ==> perm.check_permission(alt_crash_state)
    }

    pub open spec fn inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
    {
        &&& self.view(wrpm).len() == self.len()
        &&& self.opaque_inv(wrpm, perm)
    }

    pub exec fn read_relative_unaligned<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) ->(result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr + num_bytes <= self.len(),
            self.view(wrpm).no_outstanding_writes_in_range(relative_addr as int, relative_addr + num_bytes),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if wrpm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_unaligned(wrpm, relative_addr + self.start_, num_bytes, Tracked(perm))
    }

    pub exec fn read_absolute_unaligned<Perm, PMRegion>(
        self: &Self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        num_bytes: u64,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<Vec<u8>, PmemError>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(wrpm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if wrpm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = wrpm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.get_pm_region_ref().read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            relative_addr < relative_addr + S::spec_size_of() <= self.len(),
            self.view(wrpm).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + S::spec_size_of(),
            ),
            self.view(wrpm).committed().subrange(relative_addr as int, relative_addr + S::spec_size_of()) == true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).committed().subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_aligned(wrpm, relative_addr + self.start_, Ghost(true_val), Tracked(perm))
    }

    pub exec fn read_absolute_aligned<'a, S, Perm, PMRegion>(
        self: &Self,
        wrpm: &'a WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        Ghost(true_val): Ghost<S>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
            self.start() <= absolute_addr,
            absolute_addr < absolute_addr + S::spec_size_of() <= self.end(),
            self.view(wrpm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start(),
            ),
            self.view(wrpm).committed().subrange(absolute_addr - self.start(), absolute_addr + S::spec_size_of() - self.start()) == true_val.spec_to_bytes(),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(wrpm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(wrpm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = wrpm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }

        wrpm.get_pm_region_ref().read_aligned::<S>(absolute_addr)
    }


    pub exec fn write_relative<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + bytes@.len() <= self.view(old::<&mut _>(wrpm)).len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + bytes.len()),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(relative_addr as int, bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(relative_addr as int, bytes@);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger wrpm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + bytes@.len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        assert forall |alt_crash_state| wrpm@.write(relative_addr + self.start_, bytes@).can_crash_as(alt_crash_state)
                   implies perm.check_permission(alt_crash_state) by {
            let alt_region_view = wrpm@.write(relative_addr + self.start_, bytes@);
            assert(alt_region_view.len() == wrpm@.len());
            assert forall |addr: int| {
                       ||| 0 <= addr < self.start()
                       ||| self.start() + self.len() <= addr < alt_region_view.len()
                       ||| self.start() <= addr < self.end() && !self.is_writable_absolute_addr_fn()(addr)
                   } implies self.initial_region_view().state[addr] == #[trigger] alt_region_view.state[addr] by {
                assert(!(relative_addr + self.start_ <= addr < relative_addr + self.start_ + bytes@.len()));
                assert(self.initial_region_view().state[addr] == wrpm@.state[addr]);
            }
        }
        wrpm.write(relative_addr + self.start_, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn write_absolute<Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        bytes: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + bytes@.len() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(absolute_addr - self.start(), bytes@),
    {
        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes@);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + bytes@.len() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.write(absolute_addr, bytes, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_relative<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        relative_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            relative_addr + S::spec_size_of() <= self.view(old::<&mut _>(wrpm)).len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + S::spec_size_of()),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(relative_addr as int, to_write.spec_to_bytes()),
    {
        let ghost bytes = to_write.spec_to_bytes();
        assert(bytes.len() == S::spec_size_of());
        let ghost subregion_view = self.view(wrpm).write(relative_addr as int, bytes);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger wrpm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + S::spec_size_of() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        assert forall |alt_crash_state| wrpm@.write(relative_addr + self.start_, bytes).can_crash_as(alt_crash_state)
                   implies perm.check_permission(alt_crash_state) by {
            let alt_region_view = wrpm@.write(relative_addr + self.start_, bytes);
            assert(alt_region_view.len() == wrpm@.len());
            assert forall |addr: int| {
                       ||| 0 <= addr < self.start()
                       ||| self.start() + self.len() <= addr < alt_region_view.len()
                       ||| self.start() <= addr < self.end() && !self.is_writable_absolute_addr_fn()(addr)
                   } implies self.initial_region_view().state[addr] == #[trigger] alt_region_view.state[addr] by {
                assert(!(relative_addr + self.start_ <= addr < relative_addr + self.start_ + S::spec_size_of()));
                assert(self.initial_region_view().state[addr] == wrpm@.state[addr]);
            }
        }
        wrpm.serialize_and_write(relative_addr + self.start_, to_write, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_absolute<S, Perm, PMRegion>(
        self: &Self,
        wrpm: &mut WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        absolute_addr: u64,
        to_write: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(wrpm), perm),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.len(),
            self.view(old::<&mut _>(wrpm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(wrpm, perm),
            self.view(wrpm) == self.view(old::<&mut _>(wrpm)).write(absolute_addr - self.start(),
                                                                  to_write.spec_to_bytes()),
    {
        let ghost bytes = to_write.spec_to_bytes();
        // assert(bytes.len() == S::spec_size_of()) by {
        //     S::lemma_auto_serialized_len();
        // }
        let ghost subregion_view = self.view(wrpm).write(absolute_addr - self.start(), bytes);
        assert forall |i| #![trigger wrpm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   wrpm@.state[i].outstanding_write.is_none() by {
            assert(wrpm@.state[i] == self.view(wrpm).state[i - self.start()]);
        }
        wrpm.serialize_and_write(absolute_addr, to_write, Tracked(perm));
        assert(self.view(wrpm) =~= subregion_view);
    }

    pub proof fn lemma_reveal_opaque_inv<Perm, PMRegion>(
        self,
        wrpm: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
        perm: &Perm
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(wrpm, perm),
        ensures
            wrpm.inv(),
            wrpm.constants() == self.constants(),
            wrpm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), wrpm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(wrpm) == get_subregion_view(wrpm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(wrpm).state[addr] == wrpm@.state[addr + self.start()],
    {
    }
}


pub struct PersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
}

impl PersistentMemorySubregion
{
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
    ) -> (result: Self)
        requires
            pm.inv(),
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.start() == start,
            result.len() == len,
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
        };
        result
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
    {
        self.start() + self.len()
    }

    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView
    {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& pm.inv()
        &&& pm@.len() <= u64::MAX
        &&& self.view(pm).len() == self.len()
        &&& self.start() + self.len() <= pm@.len()
    }

    pub exec fn read_relative_unaligned<'a, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
        num_bytes: u64,
    ) ->(result: Result<Vec<u8>, PmemError>)
        where
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr + num_bytes <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(relative_addr as int, relative_addr + num_bytes),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_unaligned(pm, relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute_unaligned<'a, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
        num_bytes: u64,
    ) -> (result: Result<Vec<u8>, PmemError>)
        where
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr < relative_addr + S::spec_size_of() <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + S::spec_size_of(),
            ),
            S::bytes_parseable(self.view(pm).committed().subrange(relative_addr as int,
                                                                  relative_addr + S::spec_size_of())),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_aligned(pm, relative_addr + self.start_)
    }

    pub exec fn read_absolute_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr < absolute_addr + S::spec_size_of() <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start(),
            ),
            S::bytes_parseable(
                self.view(pm).committed().subrange(absolute_addr - self.start(),
                                                   absolute_addr + S::spec_size_of() - self.start())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }

        pm.read_aligned::<S>(absolute_addr)
    }
}

/// A `WritablePersistentMemorySubregion` is useful when you have full
/// access to write anything anywhere in a persistent-memory region,
/// but want to reason about what happens when you only read and write
/// within a certain subregion.

pub struct WritablePersistentMemorySubregion
{
    start_: u64,
    len_: Ghost<nat>,
    constants_: Ghost<PersistentMemoryConstants>,
    initial_region_view_: Ghost<PersistentMemoryRegionView>,
    is_writable_absolute_addr_fn_: Ghost<spec_fn(int) -> bool>,
}

impl WritablePersistentMemorySubregion
{
    pub exec fn new<PMRegion: PersistentMemoryRegion>(
        pm: &PMRegion,
        start: u64,
        Ghost(len): Ghost<nat>,
        Ghost(is_writable_absolute_addr_fn): Ghost<spec_fn(int) -> bool>,
    ) -> (result: Self)
        requires
            pm.inv(),
            0 <= len,
            start + len <= pm@.len() <= u64::MAX,
        ensures
            result.inv(pm),
            result.constants() == pm.constants(),
            result.start() == start,
            result.len() == len,
            result.initial_region_view() == pm@,
            result.is_writable_absolute_addr_fn() == is_writable_absolute_addr_fn,
            result.view(pm) == result.initial_subregion_view(),
            result.view(pm) == get_subregion_view(pm@, start as nat, len),
    {
        let result = Self{
            start_: start,
            len_: Ghost(len),
            constants_: Ghost(pm.constants()),
            initial_region_view_: Ghost(pm@),
            is_writable_absolute_addr_fn_: Ghost(is_writable_absolute_addr_fn),
        };
        result
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.constants_@
    }

    pub closed spec fn start(self) -> nat
    {
        self.start_ as nat
    }

    pub closed spec fn len(self) -> nat
    {
        self.len_@
    }

    pub open spec fn end(self) -> nat
    {
        self.start() + self.len()
    }

    pub closed spec fn initial_region_view(self) -> PersistentMemoryRegionView
    {
        self.initial_region_view_@
    }

    pub closed spec fn is_writable_absolute_addr_fn(self) -> spec_fn(int) -> bool
    {
        self.is_writable_absolute_addr_fn_@
    }

    pub open spec fn is_writable_relative_addr(self, addr: int) -> bool
    {
        self.is_writable_absolute_addr_fn()(addr + self.start())
    }

    pub closed spec fn initial_subregion_view(self) -> PersistentMemoryRegionView
    {
        get_subregion_view(self.initial_region_view(), self.start(), self.len())
    }

    pub closed spec fn view<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> PersistentMemoryRegionView
    {
        get_subregion_view(pm@, self.start(), self.len())
    }

    pub closed spec fn opaque_inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& pm.inv()
        &&& pm.constants() == self.constants()
        &&& pm@.len() == self.initial_region_view().len()
        &&& self.initial_region_view().len() <= u64::MAX
        &&& self.start() + self.len() <= pm@.len()
        &&& self.view(pm).len() == self.len()
        &&& views_differ_only_where_subregion_allows(self.initial_region_view(), pm@, self.start(),
                                                   self.len(), self.is_writable_absolute_addr_fn())
    }

    pub open spec fn inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    ) -> bool
    {
        &&& self.view(pm).len() == self.len()
        &&& self.opaque_inv(pm)
    }

    pub exec fn read_relative_unaligned<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        relative_addr: u64,
        num_bytes: u64,
    ) ->(result: Result<Vec<u8>, PmemError>)
        requires
            self.inv(pm),
            relative_addr + num_bytes <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(relative_addr as int, relative_addr + num_bytes),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(relative_addr as int, relative_addr + num_bytes);
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_unaligned(pm, relative_addr + self.start_, num_bytes)
    }

    pub exec fn read_absolute_unaligned<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &PMRegion,
        absolute_addr: u64,
        num_bytes: u64,
    ) -> (result: Result<Vec<u8>, PmemError>)
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr + num_bytes <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + num_bytes - self.start(),
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + num_bytes - self.start()
                    );
                    // If the persistent memory region is impervious
                    // to corruption, read returns the last bytes
                    // written. Otherwise, it returns a
                    // possibly-corrupted version of those bytes.
                    if pm.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    }
                    else {
                        // The addresses in `maybe_corrupted` reflect the fact
                        // that we're reading from a subregion at a certain
                        // start.
                        let absolute_addrs = Seq::<int>::new(num_bytes as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + num_bytes - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + num_bytes
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + num_bytes implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.read_unaligned(absolute_addr, num_bytes)
    }

    pub exec fn read_relative_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        relative_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            relative_addr < relative_addr + S::spec_size_of() <= self.len(),
            self.view(pm).no_outstanding_writes_in_range(
                relative_addr as int,
                relative_addr + S::spec_size_of(),
            ),
            <S as PmCopyHelper>::bytes_parseable(
                self.view(pm).committed().subrange(relative_addr as int, relative_addr + S::spec_size_of())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        relative_addr as int,
                        relative_addr + S::spec_size_of(),
                    );
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat,
                                                           |i: int| relative_addr + self.start() + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        self.read_absolute_aligned(pm, relative_addr + self.start_)
    }

    pub exec fn read_absolute_aligned<'a, S, PMRegion>(
        self: &Self,
        pm: &'a PMRegion,
        absolute_addr: u64,
    ) -> (result: Result<MaybeCorruptedBytes<S>, PmemError>)
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(pm),
            self.start() <= absolute_addr,
            absolute_addr < absolute_addr + S::spec_size_of() <= self.end(),
            self.view(pm).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start(),
            ),
            <S as PmCopyHelper>::bytes_parseable(
                self.view(pm).committed().subrange(absolute_addr - self.start(),
                                                   absolute_addr + S::spec_size_of() - self.start())
            ),
        ensures
            match result {
                Ok(bytes) => {
                    let true_bytes = self.view(pm).committed().subrange(
                        absolute_addr - self.start(),
                        absolute_addr + S::spec_size_of() - self.start()
                    );
                    if self.constants().impervious_to_corruption {
                        bytes@ == true_bytes
                    } else {
                        let absolute_addrs = Seq::<int>::new(S::spec_size_of() as nat, |i: int| absolute_addr + i);
                        maybe_corrupted(bytes@, true_bytes, absolute_addrs)
                    }
                }
                Err(e) => e == PmemError::AccessOutOfRange
            }
    {
        let ghost true_bytes1 = self.view(pm).committed().subrange(
            absolute_addr - self.start(),
            absolute_addr + S::spec_size_of() - self.start(),
        );
        let ghost true_bytes2 = pm@.committed().subrange(
            absolute_addr as int,
            absolute_addr + S::spec_size_of()
        );
        assert(true_bytes1 =~= true_bytes2);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }

        pm.read_aligned::<S>(absolute_addr)
    }

    pub exec fn write_relative<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &mut PMRegion,
        relative_addr: u64,
        bytes: &[u8],
    )
        requires
            self.inv(old::<&mut _>(pm)),
            relative_addr + bytes@.len() <= self.view(old::<&mut _>(pm)).len(),
            self.view(old::<&mut _>(pm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                      relative_addr + bytes.len()),
            forall |i: int| relative_addr <= i < relative_addr + bytes@.len() ==> self.is_writable_relative_addr(i),
        ensures
            self.inv(pm),
            self.view(pm) == self.view(old::<&mut _>(pm)).write(relative_addr as int, bytes@),
    {
        let ghost subregion_view = self.view(pm).write(relative_addr as int, bytes@);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger pm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + bytes@.len() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.write(relative_addr + self.start_, bytes);
        assert(self.view(pm) =~= subregion_view);
    }

    pub exec fn write_absolute<PMRegion: PersistentMemoryRegion>(
        self: &Self,
        pm: &mut PMRegion,
        absolute_addr: u64,
        bytes: &[u8],
    )
        requires
            self.inv(old::<&mut _>(pm)),
            self.start() <= absolute_addr,
            absolute_addr + bytes@.len() <= self.len(),
            self.view(old::<&mut _>(pm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + bytes@.len() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + bytes@.len() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm) == self.view(old::<&mut _>(pm)).write(absolute_addr - self.start(), bytes@),
    {
        let ghost subregion_view = self.view(pm).write(absolute_addr - self.start(), bytes@);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + bytes@.len() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.write(absolute_addr, bytes);
        assert(self.view(pm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_relative<S, PMRegion>(
        self: &Self,
        pm: &mut PMRegion,
        relative_addr: u64,
        to_write: &S,
    )
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(pm)),
            relative_addr + S::spec_size_of() <= self.view(old::<&mut _>(pm)).len(),
            self.view(old::<&mut _>(pm)).no_outstanding_writes_in_range(relative_addr as int,
                                                                        relative_addr + S::spec_size_of()),
            forall |i: int| relative_addr <= i < relative_addr + S::spec_size_of() ==>
                self.is_writable_relative_addr(i),
        ensures
            self.inv(pm),
            self.view(pm) == self.view(old::<&mut _>(pm)).write(relative_addr as int, to_write.spec_to_bytes()),
    {
        let ghost bytes = to_write.spec_to_bytes();
        assert(bytes.len() == S::spec_size_of());
        let ghost subregion_view = self.view(pm).write(relative_addr as int, bytes);
        assert(forall |addr| #![trigger self.is_writable_absolute_addr_fn()(addr)]
                   !self.is_writable_absolute_addr_fn()(addr) ==> !self.is_writable_relative_addr(addr - self.start()));
        assert forall |i| #![trigger pm@.state[i]]
                   relative_addr + self.start_ <= i < relative_addr + self.start_ + S::spec_size_of() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.serialize_and_write(relative_addr + self.start_, to_write);
        assert(self.view(pm) =~= subregion_view);
    }

    pub exec fn serialize_and_write_absolute<S, PMRegion>(
        self: &Self,
        pm: &mut PMRegion,
        absolute_addr: u64,
        to_write: &S,
    )
        where
            S: PmCopy + Sized,
            PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old::<&mut _>(pm)),
            self.start() <= absolute_addr,
            absolute_addr + S::spec_size_of() <= self.len(),
            self.view(old::<&mut _>(pm)).no_outstanding_writes_in_range(
                absolute_addr - self.start(),
                absolute_addr + S::spec_size_of() - self.start()
            ),
            forall |i: int| absolute_addr <= i < absolute_addr + S::spec_size_of() ==>
                #[trigger] self.is_writable_absolute_addr_fn()(i),
        ensures
            self.inv(pm),
            self.view(pm) == self.view(old::<&mut _>(pm)).write(absolute_addr - self.start(),
                                                              to_write.spec_to_bytes()),
    {
        let ghost bytes = to_write.spec_to_bytes();
        // assert(bytes.len() == S::spec_size_of()) by {
        //     S::lemma_auto_serialized_len();
        // }
        let ghost subregion_view = self.view(pm).write(absolute_addr - self.start(), bytes);
        assert forall |i| #![trigger pm@.state[i]]
                   absolute_addr <= i < absolute_addr + S::spec_size_of() implies
                   pm@.state[i].outstanding_write.is_none() by {
            assert(pm@.state[i] == self.view(pm).state[i - self.start()]);
        }
        pm.serialize_and_write(absolute_addr, to_write);
        assert(self.view(pm) =~= subregion_view);
    }

    pub proof fn lemma_reveal_opaque_inv<PMRegion: PersistentMemoryRegion>(
        self,
        pm: &PMRegion,
    )
        requires
            self.inv(pm),
        ensures
            pm.inv(),
            pm.constants() == self.constants(),
            pm@.len() == self.initial_region_view().len(),
            views_differ_only_where_subregion_allows(self.initial_region_view(), pm@, self.start(), self.len(),
                                                     self.is_writable_absolute_addr_fn()),
            self.view(pm) == get_subregion_view(pm@, self.start(), self.len()),
            forall |addr: int| 0 <= addr < self.len() ==>
                #[trigger] self.view(pm).state[addr] == pm@.state[addr + self.start()],
    {
    }
}

}
