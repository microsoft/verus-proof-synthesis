use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
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

}


pub spec const x86_arch_spec: Arch = Arch {
    layers: seq![
        ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
    ],
};

pub proof fn x86_arch_spec_upper_bound()
    ensures
        x86_arch_spec.upper_vaddr(0, 0) == 512 * 512 * 1024 * 1024 * 1024,
        x86_arch_spec.upper_vaddr(0, 0) == MAX_BASE
{
}


}
