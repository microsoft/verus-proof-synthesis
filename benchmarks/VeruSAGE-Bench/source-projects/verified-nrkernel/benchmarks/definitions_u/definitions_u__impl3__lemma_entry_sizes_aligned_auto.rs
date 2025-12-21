use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
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

}



// File: definitions_u.rs
impl Arch {

	#[verifier::external_body]
#[verifier::spinoff_prover]
    pub proof fn lemma_entry_sizes_aligned(self, i: nat, j: nat)
        requires
            self.inv(),
            i <= j,
            j < self.layers.len(),
        ensures
            aligned(self.entry_size(i), self.entry_size(j))
        decreases self.layers.len() - i
	{
		unimplemented!()
	}

#[verifier::spinoff_prover]
    pub proof fn lemma_entry_sizes_aligned_auto(self)
        ensures
            forall|i: nat, j: nat|
                self.inv() && i <= j && j < self.layers.len() ==>
                aligned(self.entry_size(i), self.entry_size(j))
    {
        assert_forall_by(|i: nat, j: nat| {
            requires(self.inv() && i <= j && j < self.layers.len());
            ensures(aligned(self.entry_size(i), self.entry_size(j)));
            self.lemma_entry_sizes_aligned(i, j);
        });
    }

}



}
