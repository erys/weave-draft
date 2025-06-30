//! data module provides data structures used in the [`crate::Draft`]

use std::cmp::{Ordering, max};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::iter::Extend;
use std::num::FpCategory;
use std::ops::{Add, Index, RangeBounds};
use std::rc::Rc;
use std::slice::SliceIndex;

/// Wrapper for shaft
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Shaft(pub u32);

impl Default for Shaft {
    fn default() -> Shaft {
        Shaft(1)
    }
}

/// Wrapper for Treadle
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Treadle(pub u32);
impl Default for Treadle {
    fn default() -> Treadle {
        Treadle(1)
    }
}

/// Threading in a weaving draft. 1 thread can only be on one shaft
#[derive(Debug, PartialEq, Clone)]
pub struct Threading {
    shaft_count: u32,
    threading: Vec<u32>,
}

impl Default for Threading {
    fn default() -> Threading {
        Threading {
            shaft_count: 2,
            threading: Vec::default(),
        }
    }
}

impl<R> Index<R> for Threading
where
    R: SliceIndex<[u32]>,
{
    type Output = R::Output;

    fn index(&self, index: R) -> &Self::Output {
        &self.threading[index]
    }
}

impl Threading {
    /// Constructs a new threading, verifying that the `shaft_count` is respected.
    ///
    /// # Panics
    /// If there are threads outside the shaft count
    #[must_use]
    pub fn new(shaft_count: u32, threading: Vec<u32>) -> Self {
        for shaft in &threading {
            assert!(
                shaft <= &shaft_count,
                "shaft count is {shaft_count} but found shaft {shaft}"
            );
        }

        Threading {
            shaft_count,
            threading,
        }
    }

    fn validate(&self, other: &[u32]) -> Result<(), usize> {
        let index = other.iter().position(|s| s > &self.shaft_count);
        match index {
            None => Ok(()),
            Some(i) => Err(i),
        }
    }

    /// Based on [`Vec::splice`], it splices the given sequence into the given range. It validates that
    /// the elements in `replace_with` are inside the shaft bounds, and it returns the replaced elements.
    ///
    /// # Examples
    /// ```
    /// # use weave_draft::Threading;
    /// let mut threading = Threading::new(4, vec![1,2,3,4]);
    /// let removed = threading.splice(1..3, &[4,3,4,1]).unwrap();
    /// assert_eq!(threading, Threading::new(4, vec![1,4,3,4,1,4]));
    /// assert_eq!(removed, vec![2,3]);
    ///
    /// let error = threading.splice(1..3, &[5]).unwrap_err();
    /// assert_eq!(error, 0);
    /// assert_eq!(threading.len(), 6); // no removal on failure
    /// ```
    ///
    /// # Errors
    /// If an element in `replace_with` is larger than the shaft count, returns index of first
    /// out-of-bounds element
    pub fn splice<R>(&mut self, range: R, replace_with: &[u32]) -> Result<Vec<u32>, usize>
    where
        R: RangeBounds<usize>,
    {
        self.validate(replace_with)?;
        let replaced: Vec<u32> = self
            .threading
            .splice(range, replace_with.to_owned())
            .collect();

        Ok(replaced)
    }

    /// Number of threads in the threading
    #[must_use]
    pub fn len(&self) -> usize {
        self.threading.len()
    }

    /// Is the threading empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.threading.is_empty()
    }

    /// Get the raw threading
    #[must_use]
    pub fn threading(&self) -> &Vec<u32> {
        &self.threading
    }

    /// Add a new thread at the end of the threading
    /// # Errors
    /// Returns the shaft if greater than shaft count
    pub fn push(&mut self, shaft: u32) -> Result<(), u32> {
        if shaft > self.shaft_count {
            return Err(shaft);
        }
        self.threading.push(shaft);
        Ok(())
    }

    /// Insert a thread at the given index, shifting later threads
    ///
    /// # Panics
    /// If index is greater than the length
    ///
    /// # Errors
    /// If `shaft` is greater than `shaft_count`
    pub fn insert(&mut self, shaft: Shaft, index: usize) -> Result<(), Shaft> {
        if shaft.0 > self.shaft_count {
            return Err(shaft);
        }
        self.threading.insert(index, shaft.0);
        Ok(())
    }

    /// Insert a thread at the given index, shifting later threads
    ///
    /// # Errors
    /// Returns the current length if index is greater than length
    pub fn try_insert(&mut self, shaft: Shaft, index: usize) -> Result<Result<(), Shaft>, usize> {
        let len = self.threading.len();
        if index > len {
            Err(len)
        } else {
            Ok(self.insert(shaft, index))
        }
    }

    /// Remove the thread at the given index, returning it as a [Shaft]
    ///
    /// # Panics
    /// If index is out of bounds
    pub fn remove(&mut self, index: usize) -> Shaft {
        Shaft(self.threading.remove(index))
    }

    /// Get shaft at index
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&u32> {
        self.threading.get(index)
    }

    /// Overwrite thread at given index, returns old thread value
    ///
    /// # Panics
    /// If index is out of bounds
    pub fn put(&mut self, index: usize, shaft: Shaft) -> Shaft {
        let old = self.threading[index];
        self.threading[index] = shaft.0;
        Shaft(old)
    }

    /// Overwrite thread at given index. Returns replaced shaft, or none if inserting at the end
    ///
    /// # Errors
    ///
    /// Returns current length if index out of bounds
    pub fn try_put(&mut self, index: usize, shaft: Shaft) -> Result<Option<Shaft>, usize> {
        let len = self.threading.len();
        match index.cmp(&len) {
            Ordering::Less => Ok(Some(self.put(index, shaft))),
            Ordering::Equal => {
                self.threading.push(shaft.0);
                Ok(None)
            }
            Ordering::Greater => Err(len),
        }
    }

    /// Highest used shaft in threading
    #[must_use]
    pub fn max_shaft(&self) -> u32 {
        let max = self.threading.iter().max();
        *max.unwrap_or(&0)
    }

    /// Non-destructively set shaft count
    ///
    /// # Panics
    /// If `shaft_count` is 0
    ///
    /// # Errors
    /// If `shaft_count` is less than max shaft used
    pub fn set_shaft_count(&mut self, shaft_count: u32) -> Result<(), usize> {
        if shaft_count == 0 {
            panic!("shaft count is 0");
        } else if shaft_count >= self.max_shaft() {
            self.shaft_count = shaft_count;
            Ok(())
        } else {
            // guaranteed to exist because of max shaft check
            let pos = self
                .threading
                .iter()
                .position(|s| s > &shaft_count)
                .unwrap();
            Err(pos)
        }
    }

    /// Shrinks the shaft count to the maximum shaft present in the threading. Returns the old
    /// shaft count if the count changed
    pub fn trim_shafts(&mut self) -> &Self {
        if let Some(&max) = self.threading.iter().max() {
            if max < self.shaft_count {
                self.shaft_count = max;
            }
        }
        self
    }

    /// Returns set of shafts used in the threading
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashSet;
    /// # use weave_draft::Threading;
    /// assert_eq!(HashSet::from([1,2,4]), Threading::new(4, vec![4, 1, 2, 1]).used_shafts());
    /// ```
    #[must_use]
    pub fn used_shafts(&self) -> HashSet<u32> {
        let mut set = HashSet::new();
        for shaft in &self.threading {
            set.insert(*shaft);
        }
        set
    }

    /// Removes any empty shafts, shifting threads down
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::missing_panics_doc)]
    pub fn trim_and_squish_shafts(&mut self) -> &Self {
        let mut used_shafts: Vec<u32> = self.used_shafts().into_iter().collect();
        used_shafts.sort_unstable();
        self.shaft_count = used_shafts.len() as u32;
        let mapping: HashMap<u32, u32> = used_shafts
            .into_iter()
            .enumerate()
            .map(|(i, s)| (s, i as u32 + 1))
            .collect();

        self.threading
            .iter_mut()
            // construction of map guarantees entry exists
            .for_each(|s| *s = *mapping.get(s).unwrap());
        self
    }

    /// Flips the threading vertically. On an 8 shaft threading, this means that shaft 1 becomes shaft 8
    /// shaft 2 becomes shaft 7, and so on.
    pub fn flip_vertical(&mut self) -> &Self {
        for thread in &mut self.threading {
            *thread = self.shaft_count - *thread;
        }
        self
    }

    /// Repeats the threading in reverse, does not repeat the final/center thread
    ///
    /// # Examples
    /// ```
    /// # use weave_draft::Threading;
    /// let mut threading = Threading::new(4, vec![1, 2, 3, 4]);
    /// assert_eq!(threading.mirror().threading(), &vec![1, 2, 3, 4, 3, 2, 1]);
    /// ```
    pub fn mirror(&mut self) -> &Self {
        if self.threading.len() <= 1 {
            return self;
        }
        let mirror_section = self.threading[..(self.threading.len() - 1)].to_vec();
        self.threading.extend(mirror_section.iter().rev());

        self
    }

    /// Reverse threading horizontally
    pub fn reverse(&mut self) -> &Self {
        self.threading.reverse();
        self
    }
}

impl IntoIterator for Threading {
    type Item = u32;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.threading.into_iter()
    }
}

impl Add for &Threading {
    type Output = Threading;

    fn add(self, rhs: Self) -> Self::Output {
        let mut threading = self.threading.clone();
        threading.extend(&rhs.threading);
        Threading {
            shaft_count: max(self.shaft_count, rhs.shaft_count),
            threading,
        }
    }
}

impl Add<Threading> for &Threading {
    type Output = Threading;

    fn add(self, rhs: Threading) -> Self::Output {
        let mut threading = self.threading.clone();
        threading.extend(rhs.threading);
        Threading {
            shaft_count: max(self.shaft_count, rhs.shaft_count),
            threading,
        }
    }
}

impl Add for Threading {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut threading = self.threading;
        threading.extend(rhs.threading);

        Threading {
            shaft_count: max(self.shaft_count, rhs.shaft_count),
            threading,
        }
    }
}

impl Add<&Threading> for Threading {
    type Output = Threading;

    fn add(self, rhs: &Threading) -> Self::Output {
        let mut threading = self.threading;
        threading.extend(&rhs.threading);

        Threading {
            shaft_count: max(self.shaft_count, rhs.shaft_count),
            threading,
        }
    }
}

/// The treadling or lift plan for a draft, also includes the tie-up and whether the loom is rising
/// or sinking shed
#[derive(Debug, PartialEq, Clone)]
pub struct TreadlingInfo {
    shaft_count: u32,
    rise_sink: RiseSink,
    tie_up: TieUpKind,
    treadling: Treadling,
}

impl Default for TreadlingInfo {
    fn default() -> Self {
        TreadlingInfo {
            shaft_count: 2, // 2 shaft is the minimum meaningful shaft count
            rise_sink: RiseSink::default(),
            tie_up: TieUpKind::default(),
            treadling: Treadling::default(),
        }
    }
}

/// Options when creating a new [`TieUpKind`]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TieUpCreate {
    /// Create a direct tie-up
    Direct,
    /// Create an indirect tie-up with given number of treadles
    Indirect(u32),
}

impl TreadlingInfo {
    /// Construct new treadling
    ///
    /// # Panics
    /// If shaft or treadle count is 0
    #[must_use]
    pub fn new(shaft_count: u32, tie_up: TieUpCreate, rise_sink: RiseSink) -> Self {
        assert_ne!(shaft_count, 0, "shaft count is 0");
        let tie_up = match tie_up {
            TieUpCreate::Direct => TieUpKind::Direct,
            TieUpCreate::Indirect(treadles) => {
                assert_ne!(treadles, 0, "treadle count is 0");

                TieUpKind::Indirect(TieUp {
                    treadle_count: treadles,
                    tie_up: vec![HashSet::new(); treadles as usize],
                })
            }
        };

        TreadlingInfo {
            shaft_count,
            tie_up,
            treadling: Treadling::new(),
            rise_sink,
        }
    }

    /// Get the shaft count
    #[must_use]
    pub fn shaft_count(&self) -> u32 {
        self.shaft_count
    }

    /// Returns max shaft used. If this is a direct tie-up, it's the max shaft in the lift plan. If
    /// it's an indirect tie-up, it's the max shaft used in the tie-up, even if no picks use a treadle
    /// tied to that shaft
    #[must_use]
    pub fn max_shaft_used(&self) -> u32 {
        match &self.tie_up {
            TieUpKind::Direct => self.treadling.max_shaft(),
            TieUpKind::Indirect(tie_up) => tie_up.max_shaft(),
        }
    }

    /// Non-destructively sets shaft count
    ///
    /// # Errors
    /// If `shaft_count` is less than the max shaft used, returns max shaft
    pub fn set_shaft_count(&mut self, shaft_count: u32) -> Result<(), u32> {
        let max = self.max_shaft_used();
        if shaft_count >= max {
            self.shaft_count = shaft_count;
            Ok(())
        } else {
            Err(max)
        }
    }

    /// Get the tie-up info
    #[must_use]
    pub fn tie_up(&self) -> &TieUpKind {
        &self.tie_up
    }

    /// Get the treadle count. Returns the shaft count if directly tied up
    #[must_use]
    pub fn treadle_count(&self) -> u32 {
        match self.tie_up {
            TieUpKind::Direct => self.shaft_count,
            TieUpKind::Indirect(TieUp { treadle_count, .. }) => treadle_count,
        }
    }

    /// Whether the treadling is for a rising shaft or sinking shaft loom
    #[must_use]
    pub fn rise_sink(&self) -> RiseSink {
        self.rise_sink
    }

    /// Number of picks in the treadling
    #[must_use]
    pub fn len(&self) -> usize {
        self.treadling.0.len()
    }

    /// Is the treadling empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.treadling.0.len() == 0
    }

    /// Add a new pick at the end using just the given treadle
    ///
    /// # Errors
    /// If treadle is higher than number of shafts, returns treadle
    pub fn push_single(&mut self, treadle: u32) -> Result<(), u32> {
        if treadle > self.treadle_count() {
            return Err(treadle);
        } else if treadle == 0 {
            // tread 0 as no treadle
            self.treadling.0.push(HashSet::new());
        } else {
            self.treadling.0.push(HashSet::from([treadle]));
        }
        Ok(())
    }

    fn validate_treadle(&self, treadle: u32) -> Result<(), u32> {
        if treadle == 0 || treadle > self.treadle_count() {
            Err(treadle)
        } else {
            Ok(())
        }
    }

    fn validate(&self, treadles: &HashSet<u32>) -> Result<(), u32> {
        let t_count = self.treadle_count();
        match treadles.iter().find(|&&t| t == 0 || t > t_count) {
            None => Ok(()),
            Some(&t) => Err(t),
        }
    }

    /// Add a new pick at the end using all given treadles/shafts
    ///
    /// # Errors
    /// If any treadle is over the number of treadles/shafts, returns that value
    pub fn push(&mut self, treadles: HashSet<u32>) -> Result<(), u32> {
        self.validate(&treadles)?;
        self.treadling.0.push(treadles);

        Ok(())
    }

    /// Toggle treadle at given index. Return `true` if treadle has been toggled on, `false` if toggled off
    ///
    /// # Errors
    /// If treadle is invalid
    /// # Panics
    /// If index is out of bounds
    pub fn toggle_treadle(&mut self, index: usize, treadle: Treadle) -> Result<bool, u32> {
        self.validate_treadle(treadle.0)?;
        let pick = &mut self.treadling.0[index];
        if pick.contains(&treadle.0) {
            pick.remove(&treadle.0);
            Ok(false)
        } else {
            pick.insert(treadle.0);
            Ok(true)
        }
    }

    /// Inserts treadling at given index
    ///
    /// # Errors
    /// If any treadles are invalid
    /// # Panics
    /// If index is out of bounds
    pub fn insert(&mut self, index: usize, treadles: HashSet<u32>) -> Result<(), u32> {
        self.validate(&treadles)?;
        self.treadling.0.insert(index, treadles);

        Ok(())
    }

    /// Based on [`Vec::splice`], it splices the given sequence into the given range. It validates that
    /// the elements in `replace_with` are inside the shaft bounds, and it returns the replaced elements.
    ///
    /// # Errors
    /// If an element in `replace_with` is larger than the shaft count, returns index of first
    /// out-of-bounds element
    pub fn splice<R>(
        &mut self,
        range: R,
        replace_with: Vec<HashSet<u32>>,
    ) -> Result<Vec<HashSet<u32>>, u32>
    where
        R: RangeBounds<usize>,
    {
        for pick in &replace_with {
            self.validate(pick)?;
        }

        let replaced: Vec<HashSet<u32>> = self.treadling.0.splice(range, replace_with).collect();

        Ok(replaced)
    }

    /// Overwrites the treadling at the given index with the new treadles
    ///
    /// # Errors
    /// If treadling is invalid
    ///
    /// # Panics
    /// If index is greater than the length of the treadling
    pub fn put(
        &mut self,
        index: usize,
        treadles: HashSet<u32>,
    ) -> Result<Option<HashSet<u32>>, u32> {
        self.validate(&treadles)?;

        match index.cmp(&self.len()) {
            Ordering::Less => {
                let old = self.treadling.0[index].clone();
                self.treadling.0[index] = treadles;
                Ok(Some(old))
            }
            Ordering::Equal => {
                self.treadling.0.push(treadles);
                Ok(None)
            }
            Ordering::Greater => {
                panic!("Index {index} out of bounds")
            }
        }
    }

    /// Convert in place to a rising shaft treadling
    pub fn make_rising(&mut self) {
        match self.rise_sink {
            RiseSink::Rising => (),
            RiseSink::Sinking => self.invert(),
        }
    }

    /// Convert in place to a sinking shaft treadling
    pub fn make_sinking(&mut self) {
        match self.rise_sink {
            RiseSink::Rising => self.invert(),
            RiseSink::Sinking => (),
        }
    }

    /// Goes from a treadling to a lift plan. Returns false if already a lift plan,
    /// true if conversion happened
    pub fn make_lift_plan(&mut self) -> bool {
        match &mut self.tie_up {
            TieUpKind::Direct => false,
            TieUpKind::Indirect(tie_up) => {
                for entry in &mut self.treadling.0 {
                    *entry = tie_up.compute_shafts(entry);
                }
                self.tie_up = TieUpKind::Direct;
                true
            }
        }
    }

    /// Switch from rising to sinking or vice versa
    pub fn invert(&mut self) {
        match &mut self.tie_up {
            TieUpKind::Direct => self.treadling.invert(self.shaft_count),
            TieUpKind::Indirect(tie_up) => tie_up.invert(self.shaft_count),
        }

        self.rise_sink = self.rise_sink.invert();
    }
}

impl Index<usize> for TreadlingInfo {
    type Output = HashSet<u32>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.treadling[index]
    }
}

fn invert(set: &HashSet<u32>, max: u32) -> HashSet<u32> {
    assert_ne!(max, 0, "cannot invert when max is 0");
    let inversion = (1..=max).collect::<HashSet<u32>>();

    &inversion - set
}

/// Whether the loom is a direct tie-up or whether treadles can be tied to multiple shafts
#[derive(Debug, Clone, PartialEq, Default)]
pub enum TieUpKind {
    /// Direct tie up (table loom, some 4 shaft looms, dobby looms)
    #[default]
    Direct,
    /// Indirect tie up (most 4+ shaft manual floor looms)
    Indirect(TieUp),
}

impl TieUpKind {
    /// Get [`TieUp`] if indirect
    #[must_use]
    pub fn tie_up(&self) -> Option<&TieUp> {
        match self {
            TieUpKind::Direct => None,
            TieUpKind::Indirect(tie_up) => Some(tie_up),
        }
    }

    /// Get underlying tie up data if indirect
    #[must_use]
    pub fn raw_tie_up(&self) -> Option<&Vec<HashSet<u32>>> {
        match self {
            TieUpKind::Direct => None,
            TieUpKind::Indirect(tie_up) => Some(&tie_up.tie_up),
        }
    }
}

/// A tie-up of a loom
#[derive(Debug, Clone, PartialEq)]
pub struct TieUp {
    treadle_count: u32,
    /// Each element in the vector corresponds to one treadle, and the hashset is which shafts it's
    /// tied to
    tie_up: Vec<HashSet<u32>>,
}

impl TieUp {
    /// Create an empty tie up for the given treadle count
    #[must_use]
    pub fn new(treadle_count: u32) -> Self {
        TieUp {
            treadle_count,
            tie_up: vec![HashSet::new(); treadle_count as usize],
        }
    }
    fn invert(&mut self, shaft_count: u32) {
        self.tie_up
            .iter_mut()
            .for_each(|t| *t = invert(t, shaft_count));
    }

    fn max_shaft(&self) -> u32 {
        max_vec_hash(&self.tie_up)
    }

    /// Returns the shafts tied up to the given treadle. Returns an empty set if treadle is out of bounds
    ///
    /// Note: treadles (and shafts) are 1-indexed
    #[must_use]
    pub fn get_shafts(&self, treadle: &u32) -> Option<&HashSet<u32>> {
        self.tie_up.get((treadle - 1) as usize)
    }

    /// Computes which shafts are raised when given set of treadles are pressed
    #[must_use]
    pub fn compute_shafts(&self, treadles: &HashSet<u32>) -> HashSet<u32> {
        let mut shafts = HashSet::new();
        for treadle in treadles {
            if let Some(tied_shafts) = self.get_shafts(treadle) {
                for shaft in tied_shafts {
                    shafts.insert(*shaft);
                }
            }
        }
        shafts
    }
}

/// Whether this draft is written for a rising shaft or sinking shaft loom
#[derive(Debug, Clone, PartialEq, Copy, Default)]
pub enum RiseSink {
    /// Rising shaft loom (most US jack looms)
    #[default]
    Rising,
    /// Sinking shaft loom (counterbalance, direct tie up, etc. looms)
    Sinking,
}

impl RiseSink {
    /// Swap to other kind
    #[must_use]
    pub fn invert(self) -> Self {
        match self {
            RiseSink::Rising => Self::Sinking,
            RiseSink::Sinking => Self::Rising,
        }
    }
}

/// Treadling/Lift Plan Sequence
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Treadling(Vec<HashSet<u32>>);

fn max_vec_hash(vec: &[HashSet<u32>]) -> u32 {
    *vec.iter()
        .map(|s| s.iter().max().unwrap_or(&0))
        .max()
        .unwrap_or(&0)
}

impl Treadling {
    fn new() -> Treadling {
        Treadling(Vec::new())
    }

    fn invert(&mut self, shaft_count: u32) {
        self.0.iter_mut().for_each(|t| *t = invert(t, shaft_count));
    }

    fn max_shaft(&self) -> u32 {
        max_vec_hash(&self.0)
    }
}

impl Add for Treadling {
    type Output = Treadling;

    fn add(self, rhs: Self) -> Self::Output {
        let mut new = self.0;
        new.extend(rhs.0);
        Treadling(new)
    }
}

impl Add<&Treadling> for Treadling {
    type Output = Treadling;
    fn add(self, rhs: &Treadling) -> Self::Output {
        let mut new = self.0;
        new.extend_from_slice(&rhs.0);

        Treadling(new)
    }
}

impl Add for &Treadling {
    type Output = Treadling;

    fn add(self, rhs: Self) -> Self::Output {
        let mut new = self.0.clone();
        new.extend_from_slice(&rhs.0);
        Treadling(new)
    }
}

impl Add<Treadling> for &Treadling {
    type Output = Treadling;
    fn add(self, rhs: Treadling) -> Self::Output {
        let mut new = self.0.clone();
        new.extend(rhs.0);
        Treadling(new)
    }
}

impl<S> Index<S> for Treadling
where
    S: SliceIndex<[HashSet<u32>]>,
{
    type Output = S::Output;
    fn index(&self, index: S) -> &Self::Output {
        &self.0[index]
    }
}

/// Palette of yarns to be used in the weaving
#[derive(Debug, Clone, PartialEq, Default)]
pub struct YarnPalette(HashSet<Rc<Yarn>>);

impl YarnPalette {
    /// Construct a new [`YarnPalette`]
    #[must_use]
    pub fn new() -> YarnPalette {
        YarnPalette(HashSet::new())
    }

    /// Adds yarn to palette if not there. Returns reference to yarn owned by palette
    #[allow(clippy::missing_panics_doc)]
    pub fn use_yarn(&mut self, yarn: Yarn) -> Rc<Yarn> {
        if self.0.contains(&yarn) {
            self.0.get(&yarn).unwrap().clone()
        } else {
            let yarn = Rc::new(yarn);
            self.0.insert(yarn.clone());
            yarn
        }
    }
}

/// A yarn that is used in the weaving
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Yarn {
    name: Option<String>,
    color: Color,
    thickness: Thickness, // todo: Other metadata? Like fiber, source, etc
}

/// RGB color
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Color(pub u8, pub u8, pub u8);

impl Color {
    /// retrieve the red value
    #[must_use]
    pub fn r(&self) -> u8 {
        self.0
    }
    /// retrieve the green value
    #[must_use]
    pub fn g(&self) -> u8 {
        self.1
    }
    /// retrieve the blue value
    #[must_use]
    pub fn b(&self) -> u8 {
        self.2
    }
}

/// Thickness of a yarn
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Thickness {
    display_width: ValidDecimal,
    threads_per_unit: ValidDecimal,
    unit: PerUnit,
}

impl Thickness {
    /// The width of the thread in the displayed draft
    #[must_use]
    pub fn display_width(&self) -> ValidDecimal {
        self.display_width
    }

    /// The number of picks/threads per unit
    #[must_use]
    pub fn threads_per_unit(&self) -> ValidDecimal {
        self.threads_per_unit
    }

    /// Unit to be used when calculated picks/thread per inch/centimeter
    #[must_use]
    pub fn unit(&self) -> PerUnit {
        self.unit
    }
}

/// Float wrapper that guarantees the value is `0` or a positive [`Normal`][FpCategory::Normal] float.
/// This allows for a full [`Eq`] and hash
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ValidDecimal(f64);

impl ValidDecimal {
    /// Constructs a [`ValidDecimal`]
    /// # Panics
    /// If the value is infinite, NaN, Negative, or Subnormal
    #[must_use]
    pub fn new(value: f64) -> ValidDecimal {
        match value.classify() {
            FpCategory::Nan | FpCategory::Infinite | FpCategory::Subnormal => {
                panic!("Invalid decimal {value}")
            }
            FpCategory::Normal if value < 0.0 => panic!("Negative decimal {value}"),
            _ => ValidDecimal(value),
        }
    }
}

impl Eq for ValidDecimal {}

impl Hash for ValidDecimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for ValidDecimal {
    fn default() -> Self {
        Self(1.0)
    }
}

/// Unit used in weaving
#[derive(Clone, Debug, PartialEq, Copy, Eq, Hash, Default)]
pub enum PerUnit {
    /// Inches
    #[default]
    Inch,
    /// Centimeters
    Centimeter,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_palette_borrows() {
        let mut palette = YarnPalette::new();
        let yarn = palette.use_yarn(Yarn {
            name: None,
            color: Color(0, 0, 0),
            thickness: Thickness::default(),
        });
        let yarn2 = palette.use_yarn(Yarn {
            name: None,
            color: Color(255, 255, 255),
            thickness: Thickness::default(),
        });
        assert_ne!(yarn, yarn2);
    }

    #[test]
    #[should_panic(expected = "shaft count is 2 but found shaft 3")]
    fn test_validate_threading() {
        let _ = Threading::new(2, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_add_threading() {
        let threading_1 = Threading::new(4, vec![1, 2, 3, 4]);
        let threading_2 = Threading::new(6, vec![3, 4, 5, 6, 1]);
        assert_eq!(
            threading_1 + threading_2,
            Threading::new(6, vec![1, 2, 3, 4, 3, 4, 5, 6, 1])
        );
    }

    #[test]
    fn test_thread_indexing() {
        let threading = Threading::new(4, vec![1, 2, 3, 4]);
        assert_eq!(threading[0], 1);
        assert_eq!(threading[0..1], [1]);
    }

    #[test]
    fn test_treadling_indexing() {
        let treadling = Treadling(vec![
            HashSet::from([1]),
            HashSet::from([2]),
            HashSet::from([3]),
        ]);
        assert_eq!(treadling[0], HashSet::from([1]));
        assert_eq!(treadling[..2], [HashSet::from([1]), HashSet::from([2])]);
    }

    #[test]
    fn test_squish_threading() {
        let mut threading = Threading::new(8, vec![1, 3, 4, 6, 3]);
        assert_eq!(
            threading.trim_and_squish_shafts(),
            &Threading::new(4, vec![1, 2, 3, 4, 2])
        );
    }

    #[test]
    fn test_invert_set() {
        let set = HashSet::from([1, 3, 5, 7]);
        assert_eq!(invert(&set, 8), HashSet::from([2, 4, 6, 8]));
    }

    #[test]
    #[should_panic(expected = "cannot invert when max is 0")]
    fn test_invert_panic() {
        let set = HashSet::from([1, 3, 5, 7]);
        let _ = invert(&set, 0);
    }

    #[test]
    fn test_invert_tie_up() {
        let mut tie_up = TieUp {
            treadle_count: 4,
            tie_up: vec![
                HashSet::from([1, 2]),
                HashSet::from([2, 3]),
                HashSet::from([3, 4]),
                HashSet::from([4, 1]),
            ],
        };
        tie_up.invert(4);
        assert_eq!(
            tie_up,
            TieUp {
                treadle_count: 4,
                tie_up: vec![
                    HashSet::from([3, 4]),
                    HashSet::from([1, 4]),
                    HashSet::from([1, 2]),
                    HashSet::from([2, 3])
                ]
            }
        );
    }
}
