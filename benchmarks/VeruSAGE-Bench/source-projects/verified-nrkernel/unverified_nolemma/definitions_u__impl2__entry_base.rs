use vstd::prelude::*;

fn main() {}


verus!{

global size_of usize == 8;

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

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


pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

pub struct ArchExec {
    pub layers: [ArchLayerExec; 4],
}

// File: definitions_u.rs
impl ArchLayerExec {

    pub open spec fn view(self) -> ArchLayer {
        ArchLayer {
            entry_size: self.entry_size as nat,
            num_entries: self.num_entries as nat,
        }
    }

}


impl ArchExec {

    pub open spec fn view(self) -> Arch {
        Arch {
            layers: self.layers@.map(|i: int, l: ArchLayerExec| l@),
        }
    }

	#[verifier::external_body]
    pub fn entry_size(&self, layer: usize) -> (res: usize)
        requires layer < self@.layers.len()
        ensures  res == self@.entry_size(layer as nat)
	{
		unimplemented!()
	}

    pub fn entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= X86_NUM_ENTRIES,
        ensures
            res == self@.entry_base(layer as nat, base as nat, idx as nat)
    {
        base + idx * self.entry_size(layer)
    }

}

}
