use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/translation.rs
pub ghost enum GPDE {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    /// An `Invalid` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
    Invalid,
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table
// MASK_FLAG_* are flags valid for entries at all levels.
pub const MASK_FLAG_P: usize = bit!(0usize);

pub const MASK_FLAG_RW: usize = bit!(1usize);

pub const MASK_FLAG_US: usize = bit!(2usize);

pub const MASK_FLAG_PWT: usize = bit!(3usize);

pub const MASK_FLAG_PCD: usize = bit!(4usize);

pub const MASK_FLAG_XD: usize = bit!(63usize);

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.

pub const MASK_PG_FLAG_G: usize = bit!(8usize);

pub const MASK_PG_FLAG_PAT: usize = bit!(12usize);

pub const MASK_L1_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L2_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L3_PG_FLAG_PAT: usize = bit!(7usize);

// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: usize ensures MASK_ADDR == MASK_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: usize = bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: usize ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1)
}


pub spec const MASK_L2_PG_ADDR_SPEC: usize = bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: usize ensures MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1)
}


pub spec const MASK_L3_PG_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: usize ensures MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PDE {
    pub entry: usize,
    pub layer: Ghost<nat>,
}

// This impl defines everything necessary for the page table walk semantics.
// PDE is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
impl PDE {

    pub open spec fn view(self) -> GPDE {
        let v = self.entry;
        let P   = v & MASK_FLAG_P    == MASK_FLAG_P;
        let RW  = v & MASK_FLAG_RW   == MASK_FLAG_RW;
        let US  = v & MASK_FLAG_US   == MASK_FLAG_US;
        let PWT = v & MASK_FLAG_PWT  == MASK_FLAG_PWT;
        let PCD = v & MASK_FLAG_PCD  == MASK_FLAG_PCD;
        let XD  = v & MASK_FLAG_XD   == MASK_FLAG_XD;
        let G   = v & MASK_PG_FLAG_G == MASK_PG_FLAG_G;
        if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
            if self.layer == 0 {
                let addr = v & MASK_ADDR;
                GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
            } else if self.layer == 1 {
                if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // super page mapping
                    let addr = v & MASK_L1_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 2 {
                if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // huge page mapping
                    let addr = v & MASK_L2_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 3 {
                let addr = v & MASK_L3_PG_ADDR;
                let PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
            } else {
                arbitrary()
            }
        } else {
            GPDE::Invalid
        }
    }

	#[verifier::external_body]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool {
		unimplemented!()
	}
}

// File: spec_t/mmu/defs.rs
// The maximum physical address width is between 32 and 52 bits.
#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: usize = 52;

pub axiom fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;

macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0usize << (($high+1usize)-$low))) << $low
    }
}

pub(crate) use bitmask_inc;


macro_rules! bit {
    ($v:expr) => {
        1usize << $v
    }
}

pub(crate) use bit;


// File: impl_u/l2_impl.rs
pub open spec fn addr_is_zero_padded(layer: nat, addr: usize, is_page: bool) -> bool {
    is_page ==> {
        if layer == 1 {
            addr & MASK_L1_PG_ADDR == addr
        } else if layer == 2 {
            addr & MASK_L2_PG_ADDR == addr
        } else if layer == 3 {
            addr & MASK_L3_PG_ADDR == addr
        } else {
            arbitrary()
        }
    }
}

// PDE is defined in crate::spec_t::mmu::defs to define the page table walk
// semantics. Here we reuse it for the implementation and add exec functions to it.
impl PDE {
    // PAT flag is set to zero for huge pages and super pages
    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@ is Page && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@ is Page && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }

	#[verifier::external_body]
    pub proof fn lemma_addr_mask_when_hp_pat_is_zero(self)
        requires
            self.hp_pat_is_zero(),
            self.all_mb0_bits_are_zero(),
            self@ is Page,
        ensures
            self.layer == 1 ==> self.entry & MASK_L1_PG_ADDR == self.entry & MASK_ADDR,
            self.layer == 2 ==> self.entry & MASK_L2_PG_ADDR == self.entry & MASK_ADDR
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub proof fn lemma_new_entry_mb0_bits_are_zero(
        layer: usize,
        address: usize,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        )
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({ let e = address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS } else { 0 }
                | if is_writable           { MASK_FLAG_RW }       else { 0 }
                | if is_supervisor         { 0 }                  else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }      else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }      else { 0 }
                | if disable_execute       { MASK_FLAG_XD }       else { 0 };
               (PDE { entry: e, layer: Ghost(layer as nat) }).all_mb0_bits_are_zero()
            }),
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub proof fn lemma_new_entry_addr_mask_is_address(
        layer: usize,
        address: usize,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        )
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({ let e = address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { 0 }                   else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 };
               &&& e & MASK_ADDR == address
               &&& e & MASK_FLAG_P == MASK_FLAG_P
               &&& (e & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3)
               &&& (e & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable
               &&& (e & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor
               &&& (e & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough
               &&& (e & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache
               &&& (e & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute
               &&& (is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0)
               &&& (is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0)
               &&& e & bit!(5) == 0
               &&& e & bit!(6) == 0
            }),
	{
		unimplemented!()
	}

    pub fn new_entry(
        layer: usize,
        address: usize,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> (r: PDE)
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            r.all_mb0_bits_are_zero(),
            if is_page { r@ is Page && r@->Page_addr == address } else { r@ is Directory && r@->Directory_addr == address},
            r.hp_pat_is_zero(),
            r.entry & bit!(5) == 0,
            r.entry & bit!(6) == 0,
            r.layer@ == layer,
            r.entry & MASK_ADDR == address,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            (r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3),
            (r.entry & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable,
            (r.entry & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor,
            (r.entry & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough,
            (r.entry & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache,
            (r.entry & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute,
    {
        let e =
        PDE {
            entry: {
                address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { 0 }                   else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 }
            },
            layer: Ghost(layer as nat),
        };

        e
    }

}



}
