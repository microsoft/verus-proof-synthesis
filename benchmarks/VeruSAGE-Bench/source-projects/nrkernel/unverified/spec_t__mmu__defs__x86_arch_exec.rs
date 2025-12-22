use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

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

}

// File: spec_t/mmu/defs.rs
pub const PAGE_SIZE: usize = 4096;

pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

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

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

pub struct ArchExec {
    pub layers: [ArchLayerExec; 4],
}

pub spec const x86_arch_spec: Arch = Arch {
    layers: seq![
        ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
    ],
};

pub fn x86_arch_exec() -> (ret: ArchExec)
    ensures ret@ == x86_arch_spec 
{
    let layers = [
        ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 },
    ];
    let r = ArchExec { layers };
    r
}

}
