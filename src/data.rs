//! data module provides data structures used in the [crate::Draft]

use std::cmp::max;
use std::collections::{HashMap, HashSet};
use std::iter::Extend;
use std::ops::Add;

/// Threading in a weaving draft. 1 thread can only be on one shaft
#[derive(Debug, PartialEq, Clone)]
pub struct Threading {
    shaft_count: u32,
    threading: Vec<u32>,
}

impl Threading {
    /// Constructs a new threading, verifying that the shaft_count is respected.
    /// # Panics
    /// If there are threads outside the shaft count
    pub fn new(shaft_count: u32, threading: Vec<u32>) -> Self {
        threading.iter().for_each(|shaft| {
            if shaft > &shaft_count {
                panic!("shaft count is {shaft_count} but found shaft {shaft}")
            }
        });

        Threading {
            shaft_count,
            threading,
        }
    }

    /// Get the raw threading
    pub fn threading(&self) -> &Vec<u32> {
        &self.threading
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
    /// ```
    /// # use std::collections::HashSet;
    /// # use weave_draft::Threading;
    /// assert_eq!(HashSet::from([1,2,4]), Threading::new(4, vec![4, 1, 2, 1]).used_shafts());
    /// ```
    pub fn used_shafts(&self) -> HashSet<u32> {
        let mut set = HashSet::new();
        for shaft in &self.threading {
            set.insert(*shaft);
        }
        set
    }

    /// Removes any empty shafts, shifting threads down
    pub fn trim_and_squish_shafts(&mut self) -> &Self {
        let mut used_shafts: Vec<u32> = self.used_shafts().into_iter().collect();
        used_shafts.sort();
        self.shaft_count = used_shafts.len() as u32;
        let mapping: HashMap<u32, u32> = used_shafts
            .into_iter()
            .enumerate()
            .map(|(i, s)| (s, (i + 1) as u32))
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
        for thread in self.threading.iter_mut() {
            *thread = self.shaft_count - *thread
        }
        self
    }

    /// Repeats the threading in reverse, does not repeat the final/center thread
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "shaft count is 2 but found shaft 3")]
    fn test_validate_threading() {
        let _ = Threading::new(2, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_mirror_threading() {
        let mut threading = Threading::new(4, vec![1, 2, 3, 4]);
        threading.mirror();

        assert_eq!(threading.threading, vec![1, 2, 3, 4, 3, 2, 1]);
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
    fn test_squish_threading() {
        let mut threading = Threading::new(8, vec![1, 3, 4, 6, 3]);
        assert_eq!(
            threading.trim_and_squish_shafts(),
            &Threading::new(4, vec![1, 2, 3, 4, 2])
        )
    }
}
