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

// Layer 0: 425 Directory ->
// Layer 1: 47  Directory ->
// Layer 2: 5   Page (1K)

// Layer 1: 46  Directory -> (1M)
// Layer 2: 1024 Pages

// Layer 0: 1024 Directories (1T)
// Layer 1: 1024 Directories (1G)
// Layer 2: 1024 Pages

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

    pub open spec(checked) fn interp(self) -> Map<nat, PTE> {
        self.interp_aux(0)
    }

    pub open spec fn entry_base(self, idx: nat) -> nat {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
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

    pub proof fn lemma_entries_interp_equal_implies_interp_equal(self, other: Directory)
        requires
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            forall|j: nat| j < self.entries.len()
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j))
                            == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            self.interp() === other.interp(),
    {
    }

}



}
