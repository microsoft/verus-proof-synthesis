use clap::Args;

pub mod additions;
pub mod benchmark_gen;
pub mod code;
pub mod deghost;
pub mod func;
pub mod unimpl;
pub mod utils;

pub use additions::*;
pub use benchmark_gen::*;
pub use code::*;
pub use deghost::*;
pub use func::*;
pub use unimpl::*;
pub use utils::*;

/// When a flag is set, the corresponding ghost code will not be removed by the
/// deghost functions.
#[derive(Clone)]
#[derive(Args)]
pub struct DeghostMode {
    #[clap(long, help = "Compare requires")]
    pub requires: bool,
    #[clap(long, help = "Compare ensures")]
    pub ensures: bool,
    #[clap(long, help = "Compare invariants")]
    pub invariants: bool,
    #[clap(long, help = "Compare spec functions")]
    pub spec: bool,
    #[clap(long, help = "Compare asserts")]
    pub asserts: bool,
    #[clap(long, help = "Compare asserts with annotations(e.g. #[warn(llm_do_not_change)])")]
    pub asserts_anno: bool,
    #[clap(long, help = "Compare decreases")]
    pub decreases: bool,
    #[clap(long, help = "Compare assumes")]
    pub assumes: bool,
}

impl DeghostMode {
    pub fn replace_with(&mut self, other: &DeghostMode) {
        self.requires = other.requires;
        self.ensures = other.ensures;
        self.invariants = other.invariants;
        self.spec = other.spec;
        self.asserts = other.asserts;
        self.asserts_anno = other.asserts_anno;
        self.decreases = other.decreases;
        self.assumes = other.assumes;
    }
}

/// By default, all flags are set to false so that all ghost code will be removed.
impl Default for DeghostMode {
    fn default() -> Self {
        Self {
            requires: false,
            ensures: false,
            invariants: false,
            spec: false,
            asserts: false,
            asserts_anno: false,
            decreases: false,
            assumes: false,
        }
    }
}
