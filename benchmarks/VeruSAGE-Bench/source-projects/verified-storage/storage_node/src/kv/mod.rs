//! This module represents key-value store that maps
//! keys to 1) a fixed-size header and 2) a list of fixed-size index
//! pages.
//!
//! This module is in charge of managing both volatile indexes, which
//! actually map keys to values, and the durable structures that store
//! the values themselves.

pub mod durable;
pub mod inv_v;
pub mod kvimpl_t;
pub mod kvimpl_v;
pub mod kvspec_t;
pub mod volatile;
