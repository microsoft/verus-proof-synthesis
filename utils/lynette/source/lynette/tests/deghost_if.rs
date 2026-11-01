//! A ghost-only branch must not hide the executable code in the other branch of an `if`
//! from `compare -t` (AutoVerus) or `additions` (VeruSAGE).

use lynette::{check_allowed_additions_only, fextract_pure_rust, DeghostMode};
use std::fs;
use tempfile::tempdir;

const GHOST: &str = "proof { assert(x == x); }";

fn program(body: &str) -> String {
    format!(
        "use vstd::prelude::*;
verus! {{
fn f(a: u32) -> (r: u32)
    ensures r >= a,
{{
    let mut x = a;
    {body}
    x
}}
fn main() {{}}
}}
"
    )
}

/// Returns whether `compare -t` and `additions` accept the edit from `before` to `after`.
fn accepted(before: &str, after: &str) -> (bool, bool) {
    let dir = tempdir().unwrap();
    let (a, b) = (dir.path().join("a.rs"), dir.path().join("b.rs"));
    fs::write(&a, program(before)).unwrap();
    fs::write(&b, program(after)).unwrap();

    let mode = DeghostMode {
        requires: true,
        ensures: true,
        assumes: true,
        decreases: true,
        ..DeghostMode::default()
    };
    let compare = fextract_pure_rust(a.clone(), &mode).unwrap()
        == fextract_pure_rust(b.clone(), &mode).unwrap();
    (compare, check_allowed_additions_only(a, b).unwrap())
}

#[test]
fn exec_change_beside_a_ghost_else_is_rejected() {
    assert_eq!(
        accepted(
            &format!("if x < 10 {{ x = x + 1; }} else {{ {GHOST} }}"),
            &format!("if x < 10 {{ x = 0; }} else {{ {GHOST} }}"),
        ),
        (false, false),
    );
}

#[test]
fn exec_change_beside_a_ghost_then_is_rejected() {
    assert_eq!(
        accepted(
            &format!("if x < 10 {{ {GHOST} }} else {{ x = x + 1; }}"),
            &format!("if x < 10 {{ {GHOST} }} else {{ x = 0; }}"),
        ),
        (false, false),
    );
}

#[test]
fn deleting_a_ghost_else_is_accepted() {
    assert_eq!(
        accepted(
            &format!("if x < 10 {{ x = x + 1; }} else {{ {GHOST} }}"),
            "if x < 10 { x = x + 1; }",
        ),
        (true, true),
    );
}

#[test]
fn adding_a_fully_ghost_if_is_accepted() {
    assert_eq!(
        accepted("", &format!("if x < 10 {{ {GHOST} }} else {{ {GHOST} }}")),
        (true, true),
    );
}
