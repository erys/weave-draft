#![warn(missing_docs)]
#![warn(clippy::pedantic)]

//! # weave-draft
//!
//! `weave-draft` is a crate for representing and manipulating weaving drafts
//!
//! ## Crate features
//!
//! ### `wif`
//!
//! Enable this to convert to the standard `.wif` format

#[doc(inline)]
pub use data::Threading;

mod data;

/// Structure holding all elements of a draft
pub struct Draft {
    threading: Threading,
}
