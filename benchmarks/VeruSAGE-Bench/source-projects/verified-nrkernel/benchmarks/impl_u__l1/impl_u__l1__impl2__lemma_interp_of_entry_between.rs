use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub struct MemRegion {
    pub base: nat,
    pub size: nat,
}

#[derive(Copy, Clone)]
pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

pub struct PTE {
    pub frame: MemRegion,
    /// The `flags` field on a `PTE` denotes the combined flags of the entire
    /// translation path to the entry. (See page table walk definition in hardware model,
    /// `spec_t::hardware`.) However, because we always set the flags on directories to be
    /// permissive these flags also correspond to the flags that we set for the frame mapping
    /// corresponding to this `PTE`.
    pub flags: Flags,
}

pub ghost struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {

    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers[layer as int].entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers.index(layer as int).num_entries
    }

    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        self.entry_base(layer, base, self.num_entries(layer))
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= X86_NUM_LAYERS
        &&& forall|i: nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i) <= X86_MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= X86_NUM_ENTRIES
                &&& self.entry_size_is_next_layer_size(i)
            }
    }

    pub open spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends
            i < self.layers.len(),
    {
        i + 1 < self.layers.len() ==> self.entry_size(i) == self.entry_size((i + 1) as nat)
            * self.num_entries((i + 1) as nat)
    }

    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + idx * self.entry_size(layer)
        entry_base_from_index(base, idx, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + (idx + 1) * self.entry_size(layer)
        next_entry_base_from_index(base, idx, self.entry_size(layer))
    }

}



// File: impl_u/l1.rs
pub enum NodeEntry {
    Directory(Directory),
    Page(PTE),
    Invalid,
}

pub struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat, // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
}

impl NodeEntry {

    pub open spec fn interp(self, base: nat) -> Map<nat, PTE>
        decreases self, 0nat, 0nat
    {
        match self {
            NodeEntry::Page(p)      => map![base => p],
            NodeEntry::Directory(d) => d.interp_aux(0),
            NodeEntry::Invalid      => map![],
        }
    }

}


impl Directory {

    pub open spec(checked) fn well_formed(&self) -> bool {
        &&& self.arch.inv()
        &&& self.layer < self.arch.layers.len()
        //&&& aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        &&& self.entries.len() == self.num_entries()
    }

    pub open spec(checked) fn entry_size(&self) -> nat
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.entry_size(self.layer)
    }

    pub open spec(checked) fn num_entries(&self) -> nat // number of entries
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.num_entries(self.layer)
    }

    pub open spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| (i < self.entries.len() && self.entries[i as int] is Page)
            ==> (#[trigger] self.entries[i as int]->Page_0.frame.size) == self.entry_size()
    }

    pub open spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.entries.len() && self.entries.index(i as int) is Directory ==> {
            let directory = #[trigger] self.entries[i as int]->Directory_0;
            &&& directory.layer == self.layer + 1
            &&& directory.base_vaddr == self.base_vaddr + i * self.entry_size()
        }
    }

    pub open spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases self.arch.layers.len() - self.layer, 0nat
    {
        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall|i: nat| (i < self.entries.len() && #[trigger] self.entries[i as int] is Directory)
                ==> self.entries[i as int]->Directory_0.inv()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn directories_match_arch(&self) -> bool {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i as int) is Directory)
            ==> (#[trigger] self.entries.index(i as int)->Directory_0.arch) == self.arch
    }

    pub open spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer
    {
        &&& self.well_formed()
        &&& self.pages_match_entry_size()
        &&& self.directories_are_in_next_layer()
        &&& self.directories_match_arch()
        &&& self.directories_obey_invariant()
        //&&& non_empty ==> self.directories_are_nonempty()
        // &&& self.frames_aligned()
    }

    pub open spec(checked) fn upper_vaddr(self) -> nat
        recommends self.well_formed()
    {
        self.arch.upper_vaddr(self.layer, self.base_vaddr)
    }

    pub open spec fn entry_base(self, idx: nat) -> nat {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn next_entry_base(self, idx: nat) -> nat {
        self.arch.next_entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn interp_of_entry(self, entry: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - entry, 1nat
    {
        if entry < self.entries.len() {
            self.entries[entry as int].interp(self.entry_base(entry))
        } else {
            arbitrary()
        }
    }

    pub open spec fn interp_aux(self, i: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - i, 2nat
    {
        if i < self.entries.len() {
            self.interp_aux(i + 1).union_prefer_right(self.interp_of_entry(i))
        } else { // i < self.entries.len()
            map![]
        }
    }

    pub broadcast proof fn lemma_interp_of_entry_between(self, i: nat, va: nat, pte: PTE)
        requires
            i < self.entries.len(),
            #[trigger] self.interp_of_entry(i).contains_pair(va, pte),
            #[trigger] self.inv(),
        ensures
            self.entry_base(i) <= va < self.next_entry_base(i),
            self.entry_base(i) < va + pte.frame.size <= self.next_entry_base(i),
            //i <= self.entries.len() ==> self.interp_aux(i).lower == self.entry_base(i),
            //self.interp_aux(i).upper == self.upper_vaddr(),
            //i == 0 ==> self.interp_aux(0).lower == self.base_vaddr,
        decreases self, self.entries.len() - i, 0nat
    {
        assert(self.interp_of_entry(i).contains_key(va));
        lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        match self.entries[i as int] {
            NodeEntry::Page(p)      => {},
            NodeEntry::Directory(d) => {
                assert(self.next_entry_base(i) == d.upper_vaddr()) by {
                    assert(self.directories_obey_invariant());
                    assert(self.arch.num_entries(self.layer + 1) * self.arch.entry_size(self.layer + 1) == self.arch.entry_size(self.layer)) by (nonlinear_arith)
                        requires
                            self.arch.inv(),
                            self.layer + 1 < self.arch.layers.len();
                };
                d.lemma_interp_aux_between(0, va, pte);
            },
            NodeEntry::Invalid      => {},
        }
    }

	#[verifier::external_body]
    pub broadcast proof fn lemma_interp_aux_between(self, i: nat, va: nat, pte: PTE)
        requires
            #[trigger] self.inv(),
            #[trigger] self.interp_aux(i).contains_pair(va, pte),
        ensures
            self.entry_base(i) <= va < self.upper_vaddr(),
            self.entry_base(i) < va + self.interp_aux(i)[va].frame.size <= self.upper_vaddr(),
        decreases self, self.entries.len() - i, 1nat
	{
		unimplemented!()
	}

}



// File: impl_u/indexing.rs
	#[verifier::external_body]
pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    requires
        0 < entry_size,
    ensures
        entry_base_from_index(base, idx, entry_size) < next_entry_base_from_index(base, idx, entry_size),
        forall|idx2: nat|
            #![trigger entry_base_from_index(base, idx, entry_size), entry_base_from_index(base, idx2, entry_size)]
            idx < idx2 ==> entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size),
                   // // && next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(layer, base, j),
        // TODO: The line above can't be a separate postcondition because it doesn't have any valid triggers.
        // The trigger for it is pretty bad.
        forall|idx2: nat| idx < idx2
            ==> next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size,
        next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n),
        aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size),
        base <= entry_base_from_index(base, idx, entry_size),
	{
		unimplemented!()
	}


}
