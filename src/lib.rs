//! # weave-draft
//!
//! `weave-draft` is a crate for representing and manipulating weaving drafts
//!
//! ## Crate features
//!
//! ### `wif`
//!
//! Enable this to convert to the standard `.wif` format

#![warn(missing_docs)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(redundant_imports)]
#![warn(unreachable_pub)]
#![warn(unused_crate_dependencies)]
// clippy groups
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(clippy::nursery)]
// clippy restriction lints
#![warn(clippy::absolute_paths)]
#![warn(clippy::allow_attributes)]
#![warn(clippy::allow_attributes_without_reason)]
#![warn(clippy::as_conversions)]
#![warn(clippy::assertions_on_result_states)]
#![warn(clippy::clone_on_ref_ptr)]
#![warn(clippy::empty_enum_variants_with_brackets)]
#![warn(clippy::empty_structs_with_brackets)]
#![warn(clippy::field_scoped_visibility_modifiers)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::impl_trait_in_params)]
#![warn(clippy::missing_assert_message)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::module_name_repetitions)]
#![warn(clippy::multiple_inherent_impl)]
#![warn(clippy::redundant_test_prefix)]
#![warn(clippy::redundant_type_annotations)]
#![warn(clippy::renamed_function_params)]
#![warn(clippy::rest_pat_in_fully_bound_structs)]
#![warn(clippy::return_and_then)]
#![warn(clippy::same_name_method)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::tests_outside_test_module)]
#![warn(clippy::try_err)]
#![warn(clippy::unneeded_field_pattern)]
#![warn(clippy::unused_result_ok)]
use crate::data::{Shaft, Treadle, YarnSequence};
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
#[doc(inline)]
pub use data::Yarn;
#[doc(inline)]
pub use data::YarnPalette;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::ops::RangeBounds;
use std::rc::Rc;

pub mod data;

/// Structure holding all elements of a draft
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Draft {
    threading: Threading,
    treadling: TreadlingInfo,
    yarn_palette: YarnPalette,
    weft_yarns: YarnSequence,
    warp_yarns: YarnSequence,
}

/// An enum representing the axes of a weaving draft
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum WeavingAxis {
    /// Threading
    Threading,
    /// Treadling
    Treadling,
}

impl Draft {
    /// Create an empty draft with the given options
    #[must_use]
    pub fn new(shaft_count: usize, tie_up_create: TieUpCreate, rise_sink: RiseSink) -> Self {
        Self {
            threading: Threading::new(shaft_count, Vec::new()),
            treadling: TreadlingInfo::new(shaft_count, tie_up_create, rise_sink),
            yarn_palette: YarnPalette::default(),
            weft_yarns: YarnSequence::default(),
            warp_yarns: YarnSequence::default(),
        }
    }

    /// Get the threading
    #[must_use]
    pub const fn threading(&self) -> &Threading {
        &self.threading
    }

    /// Get the treadling
    #[must_use]
    pub const fn treadling_info(&self) -> &TreadlingInfo {
        &self.treadling
    }

    /// Get the tie-up
    #[must_use]
    pub const fn tie_up(&self) -> &TieUpKind {
        self.treadling.tie_up()
    }

    /// Make rising shaft
    pub fn make_rising(&mut self) {
        self.treadling.make_rising();
    }

    /// Make sinking shaft
    pub fn make_sinking(&mut self) {
        self.treadling.make_sinking();
    }

    /// Goes from a treadling to a lift plan. Returns false if already a lift plan,
    /// true if conversion happened
    pub fn make_lift_plan(&mut self) -> bool {
        self.treadling.make_lift_plan()
    }

    /// Max shaft used in threading or treadling
    #[must_use]
    pub fn max_shaft(&self) -> (WeavingAxis, usize) {
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
    ///
    /// # Panics
    /// If shaft count is 0
    pub fn set_shaft_count(&mut self, shaft_count: usize) -> Result<(), (WeavingAxis, usize)> {
        let (axis, max) = self.max_shaft();
        if shaft_count >= max {
            self.treadling.set_shaft_count(shaft_count).unwrap();
            self.threading.set_shaft_count(shaft_count).unwrap();
            Ok(())
        } else {
            Err((axis, max))
        }
    }

    /// Calls [`Threading::splice`]
    ///
    /// # Errors
    /// See [`Threading::splice`]
    pub fn splice_threading<R>(
        &mut self,
        range: R,
        replace_with: &[usize],
    ) -> Result<Vec<usize>, usize>
    where
        R: RangeBounds<usize>,
    {
        self.threading.splice(range, replace_with)
    }

    /// Adds a new thread to teh end of the threading
    ///
    /// # Errors
    /// Returns the shaft if greater than shaft count
    pub fn push_threading(&mut self, shaft: usize) -> Result<(), usize> {
        self.threading.push(shaft)
    }

    /// Insert a thread in the threading at the given index, shifting the later threads
    ///
    /// # Panics
    /// If index is greater than length
    ///
    /// # Errors
    /// If `shaft` is greater than `shaft_count`
    pub fn insert_threading(&mut self, shaft: Shaft, index: usize) -> Result<(), Shaft> {
        self.threading.insert(shaft, index)
    }

    /// Insert a thread at the given index, shifting later threads
    ///
    /// # Errors
    /// Returns the current length if index is greater than length
    pub fn try_insert_threading(
        &mut self,
        shaft: Shaft,
        index: usize,
    ) -> Result<Result<(), Shaft>, usize> {
        self.threading.try_insert(shaft, index)
    }

    /// Remove the thread at the given index, returning it as a [Shaft]
    ///
    /// # Panics
    /// If index is out of bounds
    pub fn remove_threading(&mut self, index: usize) -> Shaft {
        self.threading.remove(index)
    }

    /// Get threading shaft at an index
    #[must_use]
    pub fn get_from_threading(&self, index: usize) -> Option<&usize> {
        self.threading.get(index)
    }

    /// Overwrite thread at given index, returns old thread value
    ///
    /// # Panics
    /// If index is out of bounds
    pub fn put_threading(&mut self, index: usize, shaft: Shaft) -> Shaft {
        self.threading.put(index, shaft)
    }

    /// Overwrite thread at given index. Returns replaced shaft, or none if inserting at the end
    ///
    /// # Errors
    ///
    /// Returns current length if index out of bounds
    pub fn try_put_threading(
        &mut self,
        index: usize,
        shaft: Shaft,
    ) -> Result<Option<Shaft>, usize> {
        self.threading.try_put(index, shaft)
    }

    /// See [`Threading::flip_vertical`]
    pub fn flip_threading_vert(&mut self) {
        self.threading.flip_vertical();
    }

    /// See [`Threading::mirror`]
    pub fn mirror_threading(&mut self) {
        self.threading.mirror();
    }

    /// See [`Threading::reverse`]
    pub fn flip_threading_horiz(&mut self) {
        self.threading.reverse();
    }

    /// Add a new pick at the end using just the given treadle
    ///
    /// # Errors
    /// If treadle is higher than number of shafts, returns treadle
    pub fn push_single_treadling(&mut self, treadle: usize) -> Result<(), usize> {
        self.treadling.push_single(treadle)
    }

    /// Add a new pick at the end using all given treadles/shafts
    ///
    /// # Errors
    /// If any treadle is over the number of treadles/shafts, returns that value
    pub fn push_treadling(&mut self, treadles: HashSet<usize>) -> Result<(), usize> {
        self.treadling.push(treadles)
    }

    /// Toggle treadle at given index. Return `true` if treadle has been toggled on, `false` if toggled off
    ///
    /// # Errors
    /// If treadle is invalid
    /// # Panics
    /// If index is out of bounds
    pub fn toggle_treadle(&mut self, index: usize, treadle: Treadle) -> Result<bool, usize> {
        self.treadling.toggle_treadle(index, treadle)
    }

    /// Inserts treadling at given index
    ///
    /// # Errors
    /// If any treadles are invalid
    /// # Panics
    /// If index is out of bounds
    pub fn insert_treadle(&mut self, index: usize, treadles: HashSet<usize>) -> Result<(), usize> {
        self.treadling.insert(index, treadles)
    }

    /// Based on [`Vec::splice`], it splices the given sequence into the given range. It validates that
    /// the elements in `replace_with` are inside the shaft bounds, and it returns the replaced elements.
    ///
    /// # Errors
    /// If an element in `replace_with` is larger than the shaft count, returns index of first
    /// out-of-bounds element
    pub fn splice_treadling<R>(
        &mut self,
        range: R,
        replace_with: Vec<HashSet<usize>>,
    ) -> Result<Vec<HashSet<usize>>, usize>
    where
        R: RangeBounds<usize>,
    {
        self.treadling.splice(range, replace_with)
    }
    /// Overwrites the treadling at the given index with the new treadles
    ///
    /// # Errors
    /// If treadling is invalid
    ///
    /// # Panics
    /// If index is greater than the length of the treadling
    pub fn put_treadling(
        &mut self,
        index: usize,
        treadles: HashSet<usize>,
    ) -> Result<Option<HashSet<usize>>, usize> {
        self.treadling.put(index, treadles)
    }

    /// Get yarn palette
    #[must_use]
    pub const fn yarn_palette(&self) -> &YarnPalette {
        &self.yarn_palette
    }

    /// Get weft yarns
    #[must_use]
    pub const fn weft_yarns(&self) -> &YarnSequence {
        &self.weft_yarns
    }

    /// Get warp yarns
    #[must_use]
    pub const fn warp_yarns(&self) -> &YarnSequence {
        &self.warp_yarns
    }

    /// Set the repeat of weft yarns
    pub fn set_weft_yarn_repeat<T>(&mut self, yarns: T)
    where
        T: IntoIterator<Item = Yarn>,
    {
        let yarns = self.yarn_palette.use_yarns(yarns);
        self.weft_yarns.set_repeat(&yarns);
    }

    /// set weft yarn repeat offset
    pub const fn set_weft_yarn_offset(&mut self, offset: usize) {
        self.weft_yarns.set_offset(offset);
    }

    /// set weft yarn at index
    pub fn set_weft_yarn(&mut self, index: usize, yarn: Yarn) {
        let yarn = self.yarn_palette.use_yarn(yarn);
        self.weft_yarns.set_yarn(index, yarn);
    }

    /// Get weft yarn at index. Returns `None` if not set via repeat or directly
    #[must_use]
    pub fn try_get_weft_yarn(&self, index: usize) -> Option<&Rc<Yarn>> {
        self.weft_yarns.try_get(index)
    }

    /// Get weft yarn at index
    /// # Panics
    /// If yarn is not set via repeat or directly
    #[must_use]
    pub fn get_weft_yarn(&self, index: usize) -> &Rc<Yarn> {
        self.weft_yarns.get(index)
    }

    /// Set the repeat of weft yarns
    pub fn set_warp_yarn_repeat<T>(&mut self, yarns: T)
    where
        T: IntoIterator<Item = Yarn>,
    {
        let yarns = self.yarn_palette.use_yarns(yarns);
        self.warp_yarns.set_repeat(&yarns);
    }

    /// set warp yarn repeat offset
    pub const fn set_warp_yarn_offset(&mut self, offset: usize) {
        self.warp_yarns.set_offset(offset);
    }

    /// set warp yarn at index
    pub fn set_warp_yarn(&mut self, index: usize, yarn: Yarn) {
        let yarn = self.yarn_palette.use_yarn(yarn);
        self.warp_yarns.set_yarn(index, yarn);
    }

    /// Get warp yarn at index. Returns `None` if not set via repeat or directly
    #[must_use]
    pub fn try_get_warp_yarn(&self, index: usize) -> Option<&Rc<Yarn>> {
        self.warp_yarns.try_get(index)
    }

    /// Get warp yarn at index
    /// # Panics
    /// If yarn is not set via repeat or directly
    #[must_use]
    pub fn get_warp_yarn(&self, index: usize) -> &Rc<Yarn> {
        self.warp_yarns.get(index)
    }
}
