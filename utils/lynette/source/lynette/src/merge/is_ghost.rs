use crate::merge::types::*;

pub(super) trait IsGhost {
    fn is_ghost(&self) -> bool;
}

impl IsGhost for syn_verus::Item {
    fn is_ghost(&self) -> bool {
        match self {
            syn_verus::Item::Const(i) => i.mode != syn_verus::FnMode::Default,
            syn_verus::Item::Enum(e) => e.mode != syn_verus::DataMode::Default,
            syn_verus::Item::Fn(f) => f.sig.mode != syn_verus::FnMode::Default,
            syn_verus::Item::Struct(s) => s.mode != syn_verus::DataMode::Default,
            _ => false,
        }
    }
}

impl IsGhost for TraitItem {
    fn is_ghost(&self) -> bool {
        match self {
            TraitItem::Const(c) => c.mode != syn_verus::FnMode::Default,
            TraitItem::Fn(m) => m.sig.mode != syn_verus::FnMode::Default,
            TraitItem::Type(_) => false,
            _ => false,
        }
    }
}

impl IsGhost for Stmt {
    fn is_ghost(&self) -> bool {
        match self {
            Stmt::Item(i) => i.is_ghost(),
            Stmt::Expr(e, _) => e.is_ghost(),
            _ => false,
        }
    }
}

impl IsGhost for ImplItem {
    fn is_ghost(&self) -> bool {
        match self {
            ImplItem::Const(c) => c.mode != syn_verus::FnMode::Default,
            ImplItem::Fn(m) => m.sig.mode != syn_verus::FnMode::Default,
            ImplItem::Type(_) => false,
            _ => false,
        }
    }
}

impl IsGhost for syn_verus::Expr {
    fn is_ghost(&self) -> bool {
        match self {
            Expr::Assume(_)
            | Expr::Assert(_)
            | Expr::AssertForall(_)
            | Expr::RevealHide(_)
            | Expr::View(_)
            | Expr::BigAnd(_)
            | Expr::BigOr(_)
            | Expr::Is(_)
            | Expr::Has(_)
            | Expr::Matches(_)
            | Expr::GetField(_) => true,
            _ => false,
        }
    }
}