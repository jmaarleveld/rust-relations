use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;


type Pair<U> = (U, U);

/// Struct used to represent a relation.
/// The relation can be defined on any set of types,
/// as long as the type implements
/// `Eq`, `Hash`, `Clone`, and `Debug`.
///
/// Instances of the struct can either be created
/// using the `relation!` macro, or by using the
/// `from_iter` method:
///
/// ```
/// use relations::{relation, Relation};
///
/// let relation_1 = relation!(
///     0 => 1,
///     1 => 2,
///     2 => 3
/// );
///
/// let relation_2 = Relation::from_iter(
///     [(0, 1), (1, 2), (2, 3)]
/// );
///
/// assert_eq!(relation_1, relation_2);
/// ```
#[derive(Debug)]
#[derive(Clone)]
pub struct Relation<U: Eq + Hash + Clone + Debug> {
    forward_map: HashMap<U, u64>,
    backward_map: HashMap<u64, U>,
    relation: HashSet<Pair<u64>>
}

impl<U: Eq + Hash + Clone + Debug> fmt::Display for Relation<U> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let pairs = self.relation
            .iter()
            .map(
                |(x, y)|
                    format!("({:?}, {:?})", self.backward_map[x], self.backward_map[y]));
        let content = pairs.collect::<Vec<String>>().join(", ");
        write!(f, "{{{}}}", content)
    }
}

impl<U: Eq + Hash + Clone + Debug> Relation<U> {
    fn new(forward_map: HashMap<U, u64>,
           backward_map: HashMap<u64, U>,
           relation: HashSet<Pair<u64>>) -> Self {
        Relation{forward_map, backward_map, relation}
    }

    /// Test whether two items x and y are related.
    ///
    /// This is equivalent to checking whether (x, y)
    /// is contained in the relation.
    ///
    /// This also works for x and y not contained in the
    /// relation, as long as x and y have the correct type.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(relation.are_related(&0, &1));
    /// assert!(!relation.are_related(&0, &3));
    /// ```
    pub fn are_related(&self, x: &U, y: &U) -> bool {
        if !self.forward_map.contains_key(x) || !self.forward_map.contains_key(y) {
            return false;
        }
        self.relation.contains(&(self.forward_map[x], self.forward_map[y]))
    }

    /// Test whether the relation is reflexive.
    ///
    /// The relation is reflexive if for every x contained
    /// in any pair (x, y) or (y, x) in the relation, (x, x)
    /// is also contained in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(!relation.is_reflexive());
    /// ```
    pub fn is_reflexive(&self) -> bool {
        self.backward_map
            .iter()
            .all(|(x, _)| self.relation.contains(&(*x, *x)))
    }

    /// Test whether the relation is irreflexive.
    ///
    /// The relation is irreflexive if for every x contained
    /// in any pair (x, y) or (y, x) in the relation, (x, x)
    /// is not contained in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(relation.is_irreflexive());
    /// ```
    pub fn is_irreflexive(&self) -> bool {
        self.backward_map
            .iter()
            .all(|(x, _)| !self.relation.contains(&(*x, *x)))
    }

    /// Test whether the relation is symmetric
    ///
    /// The relation is symmetric if for every pair (x, y)
    /// contained in the relation, (y, x) is also contained
    /// in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(!relation.is_symmetric());
    /// ```
    pub fn is_symmetric(&self) -> bool {
        self.relation
            .iter()
            .copied()
            .all(|(x, y)| self.relation.contains(&(y, x)))
    }

    /// Test whether the relation is transitive.
    ///
    /// The relation is transitive if for every combination
    /// of pairs (x, y) and (y, z) contained in the relation,
    /// (x, z) is also contained in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(!relation.is_transitive());
    /// ```
    pub fn is_transitive(&self) -> bool {
        // TODO: can we make this check more efficient?
        for (x, y) in self.relation.iter().copied() {
            for (u, v) in self.relation.iter().copied() {
                if y != u {
                    continue;
                }
                if !self.relation.contains(&(x, v)) {
                    return false;
                }
            }
        }
        true
    }

    /// Test whether the relation is asymmetric.
    ///
    /// The relation is asymmetric if for every
    /// pair (x, y) contained in the relation,
    /// (y, x) is not contained in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(!relation.is_asymmetric());
    /// ```
    pub fn is_asymmetric(&self) -> bool {
        // Note: this is equivalent to
        //  self.is_irreflexive() && self.is_antisymmetric()
        self.relation
            .iter()
            .copied()
            .all(|(x, y)| !self.relation.contains(&(y, x)))
    }

    /// Test whether the relation is antisymmetric.
    ///
    /// The relation is antisymmetric if for every
    /// pair (x, y) contained in the relation,
    /// either x == y or (y, x) is not contained
    /// in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert!(!relation.is_antisymmetric());
    /// ```
    pub fn is_antisymmetric(&self) -> bool {
        self.relation
            .iter()
            .copied()
            .all(|(x, y)| x == y || !self.relation.contains(&(y, x)))
    }

    /// Test whether the relation is an equivalence relation.
    ///
    /// An equivalence relation is a relation which is
    /// reflexive, symmetric, and transitive.
    pub fn is_equivalence(&self) -> bool {
        self.is_symmetric() && self.is_reflexive() && self.is_transitive()
    }

    /// Test whether the relation is a non-strict partial order.
    ///
    /// A non strict partial order is reflexive, anti-symmetric,
    /// and transitive.
    pub fn is_non_strict_partial_order(&self) -> bool {
        self.is_reflexive() && self.is_antisymmetric() && self.is_transitive()
    }

    /// Test whether the relation is a strict partial order.
    ///
    /// A non strict partial order is reflexive, asymmetric,
    /// and transitive.
    pub fn is_strict_partial_order(&self) -> bool {
        self.is_irreflexive() && self.is_asymmetric() && self.is_asymmetric()
    }

    /// Compute the reflexive closure of the relation.
    ///
    /// The reflexive closure of the relation is the
    /// relation itself, with all missing pairs (x, x)
    /// added to it.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert_eq!(
    ///     relation.reflexive_closure(),
    ///     relation!(0 => 1, 1 => 2, 2 => 3, 0 => 0, 1 => 1, 2 => 2, 3 => 3)
    /// );
    /// ```
    pub fn reflexive_closure(&self) -> Self {
        let mut new_relation = self.relation.clone();
        for (x, _) in self.backward_map.iter() {
            let key = (*x, *x);
            if !new_relation.contains(&key) {
                new_relation.insert(key);
            }
        }
        Self::new(self.forward_map.clone(),
                  self.backward_map.clone(),
                  new_relation)
    }

    /// Compute the symmetric closure of the relation.
    ///
    /// The symmetric closure of the relation is the
    /// relation itself, where for each pair (x, y),
    /// we added the pair (y, x) if it not already
    /// contained in the relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert_eq!(
    ///     relation.symmetric_closure(),
    ///     relation!(0 => 1, 1 => 2, 2 => 3, 3 => 2, 2 => 1, 1 => 0)
    /// );
    /// ```
    pub fn symmetric_closure(&self) -> Self {
        let mut new_relation = self.relation.clone();
        for (x, y) in self.relation.iter().copied() {
            let key = (y, x);
            if !new_relation.contains(&key) {
                new_relation.insert(key);
            }
        }
        Self::new(self.forward_map.clone(),
                  self.backward_map.clone(),
                  new_relation)
    }

    /// Compute the transitive closure of the relation.
    ///
    /// The transitive closure of the relation is the
    /// relation itself, where, for all pairs
    /// (x, y) and (y, z), we added the missing pairs
    /// (x, z).
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3);
    ///
    /// assert_eq!(
    ///     relation.transitive_closure(),
    ///     relation!(
    ///         0 => 1, 0 => 2, 0 => 3,
    ///         1 => 2, 1 => 3,
    ///         2 => 3
    ///     )
    /// );
    /// ```
    pub fn transitive_closure(&self) -> Self {
        let mut new_relation = self.relation.clone();
        for (k, _) in self.backward_map.iter() {
            for (i, _) in self.backward_map.iter() {
                for (j, _) in self.backward_map.iter() {
                    let key_1 = (*i, *k);
                    let key_2 = (*k, *j);
                    if new_relation.contains(&key_1) && new_relation.contains(&key_2) {
                        new_relation.insert((*i, *j));
                    }
                }
            }
        }
        Self::new(self.forward_map.clone(),
                  self.backward_map.clone(),
                  new_relation)
    }

    /// Test whether the relation (self) is a subset of the
    /// other relation.
    ///
    /// This is equivalent to testing that:
    ///     self.are_related(x, y) ==> other.are_related(x, y)
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let a = relation!(1 => 2, 2 => 3);
    /// let b = relation!(1 => 2, 2 => 3);
    /// let c = relation!(1 => 2, 2 => 3, 3 => 4);
    ///
    /// assert!(a.is_subset(&b));
    /// assert!(a.is_subset(&c));
    /// assert!(!c.is_subset(&a));
    /// ```
    pub fn is_subset(&self, other: &Relation<U>) -> bool {
        for (x, y) in self.relation.iter() {
            let u = &self.backward_map[x];
            let v = &self.backward_map[y];
            if !other.are_related(u, v) {
                return false;
            }
        }
        true
    }

    /// Test whether the relation (self) is a proper subset of the
    /// other relation.
    ///
    /// self is a proper subset of other if self.is_subset(other),
    /// and self != other.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let a = relation!(1 => 2, 2 => 3);
    /// let b = relation!(1 => 2, 2 => 3);
    /// let c = relation!(1 => 2, 2 => 3, 3 => 4);
    ///
    /// assert!(!a.is_proper_subset(&b));
    /// assert!(a.is_proper_subset(&c));
    /// assert!(!c.is_proper_subset(&a));
    /// ```
    pub fn is_proper_subset(&self, other: &Relation<U>) -> bool {
        self.is_subset(other) & !other.is_subset(self)
    }
}

impl<U: Eq + Hash + Clone + Debug> FromIterator<Pair<U>> for Relation<U> {
    fn from_iter<T: IntoIterator<Item=Pair<U>>>(iter: T) -> Self {
        let mut forward_map = HashMap::new();
        let mut backward_map = HashMap::new();
        let mut relation = HashSet::new();
        for (x, y) in iter {
            [&x, &y].into_iter().for_each(|z| {
                let item = z.clone();
                if !forward_map.contains_key(&item) {
                    let id = forward_map.len();
                    forward_map.insert(item.clone(), id as u64);
                    backward_map.insert(id as u64, item);
                }
            });
            relation.insert((forward_map[&x], forward_map[&y]));
        }
        Self::new(forward_map, backward_map, relation)
    }
}

impl<U: Eq + Hash + Clone + Debug> PartialEq for Relation<U> {
    fn eq(&self, other: &Self) -> bool {
        self.is_subset(other) && other.is_subset(self)
    }
}

impl<U: Eq + Hash + Clone + Debug> Eq for Relation<U> {}


/// Convenience macro for defining a relation with
/// a static set of pairs.
///
/// Example usage:
/// ```
/// use relations::{relation, Relation};
///
/// let my_relation = relation!(1 => 2, 2 => 3, 3 => 4);
/// ```
#[macro_export]
macro_rules! relation {
    ($($from:expr => $to:expr),*) => {
        {
            Relation::from_iter(
                [
                    $(
                          ($from, $to),
                    )*
                ]
            )
        }
    };
}
