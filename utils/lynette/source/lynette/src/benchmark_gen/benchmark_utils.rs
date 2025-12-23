use syn_verus::visit_mut::{VisitMut};
use quote::ToTokens;
use crate::{utils::*};

pub fn impl_fn_is_target(f: &syn_verus::ImplItemFn) -> bool {
    is_proof_or_exec(&f.sig) && fn_body_is_target(&f.block)
}

pub fn trait_fn_is_target(f: &syn_verus::TraitItemFn) -> bool {
    is_proof_or_exec(&f.sig) && f.default.is_some() && fn_body_is_target(&f.default.clone().unwrap())
}

pub fn top_level_fn_is_target(f: &syn_verus::ItemFn) -> bool {
    is_proof_or_exec(&f.sig) && fn_body_is_target(&*f.block)
}

pub struct VerusMacroVisitor<V: VisitMut> {
    pub visitor: V
}

impl<V: VisitMut> VisitMut for VerusMacroVisitor<V> {
    fn visit_macro_mut(&mut self, i: &mut syn_verus::Macro) {
        if is_verus_macro(&i) {
            let mut inner = syn_verus::parse_file(&i.tokens.to_string()).expect("error parsing verus macro");
            self.visitor.visit_file_mut(&mut inner);
            i.tokens = inner.to_token_stream();
        }
    }
}
