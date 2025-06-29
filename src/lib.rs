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
pub use data::RiseSink;
#[doc(inline)]
pub use data::Threading;
#[doc(inline)]
pub use data::TieUp;
#[doc(inline)]
pub use data::TieUpCreate;
#[doc(inline)]
pub use data::TieUpKind;
#[doc(inline)]
pub use data::TreadlingInfo;
use std::cmp::Ordering;

mod data;

/// Structure holding all elements of a draft
#[derive(Clone, Debug, PartialEq)]
pub struct Draft {
    threading: Threading,
    treadling: TreadlingInfo,
}

/// An enum representing the axes of a weaving draft
pub enum WeavingAxis {
    /// Threading
    Threading,
    /// Treadling
    Treadling,
}

impl Draft {
    /// Create an empty draft with the given options
    pub fn new(shaft_count: u32, tie_up_create: TieUpCreate, rise_sink: RiseSink) -> Self {
        Self {
            threading: Threading::new(shaft_count, Vec::new()),
            treadling: TreadlingInfo::new(shaft_count, tie_up_create, rise_sink),
        }
    }

    /// Get the threading
    pub fn threading(&self) -> &Threading {
        &self.threading
    }

    /// Get the treadling
    pub fn treadling_info(&self) -> &TreadlingInfo {
        &self.treadling
    }

    /// Get the tie-up
    pub fn tie_up(&self) -> &TieUpKind {
        &self.treadling.tie_up()
    }

    /// Make rising shaft
    pub fn make_rising(&mut self) {
        self.treadling.make_rising();
    }

    /// Make sinking shaft
    pub fn make_sinking(&mut self) {
        self.treadling.make_sinking();
    }

    /// Max shaft used in threading or treadling
    pub fn max_shaft(&self) -> (WeavingAxis, u32) {
        let treadling_max = self.treadling.max_shaft_used();
        let threading_max = self.threading.max_shaft();

        match treadling_max.cmp(&threading_max) {
            Ordering::Less | Ordering::Equal => (WeavingAxis::Threading, threading_max),
            Ordering::Greater => (WeavingAxis::Treadling, treadling_max),
        }
    }

    /// Sets shaft count on threading and treadling. Only succeeds when non-destructive
    ///
    /// # Errors
    /// If shafts greater than the given count are in use, returns an error with the max used shaft
    /// and the axis it's used on
    pub fn set_shaft_count(&mut self, shaft_count: u32) -> Result<(), (WeavingAxis, u32)> {
        let (axis, max) = self.max_shaft();
        if shaft_count >= max {
            self.treadling.set_shaft_count(shaft_count).unwrap();
            self.threading.set_shaft_count(shaft_count).unwrap();
            Ok(())
        } else {
            Err((axis, max))
        }
    }
}
