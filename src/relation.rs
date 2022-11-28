use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
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
    forward_map: HashMap<U, usize>,
    backward_map: Vec<U>,
    relation: HashSet<Pair<usize>>
}

impl<U: Eq + Hash + Clone + Debug> fmt::Display for Relation<U> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let pairs = self.relation
            .iter()
            .map(
                |(x, y)|
                    format!("({:?}, {:?})", self.backward_map[*x], self.backward_map[*y]));
        let content = pairs.collect::<Vec<String>>().join(", ");
        write!(f, "{{{}}}", content)
    }
}

impl<U: Eq + Hash + Clone + Debug> Relation<U> {
    fn new(forward_map: HashMap<U, usize>,
           backward_map: Vec<U>,
           relation: HashSet<Pair<usize>>) -> Self {
        Relation{forward_map, backward_map, relation}
    }

    /// Create an empty relation
    pub fn empty() -> Self {
        Self::new(HashMap::new(), Vec::new(), HashSet::new())
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

    /// Test whether the point y is reachable from point x.
    ///
    /// y is reachable from x if there exists
    /// x_1, x_2, ..., x_n such that
    /// (x, x_1), (x_1, x_2), ..., (x_n, y)
    /// are all contained in R.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(
    ///     1 => 2, 2 => 3, 3 => 1,
    ///     4 => 5,
    ///     6 => 7, 7 => 8,
    ///     9 => 9
    /// );
    ///
    /// assert!(rel.reachable_from(&1, &2));
    /// assert!(rel.reachable_from(&1, &3));
    /// assert!(rel.reachable_from(&2, &3));
    /// assert!(rel.reachable_from(&1, &1));
    /// assert!(rel.reachable_from(&4, &5));
    /// assert!(rel.reachable_from(&9, &9));
    /// assert!(!rel.reachable_from(&1, &9));
    /// assert!(!rel.reachable_from(&5, &4));
    /// ```
    pub fn reachable_from(&self, x: &U, y: &U) -> bool {
        let u = self.forward_map[x];
        let v = self.forward_map[y];
        let mut graph = self.as_map();
        let mut stack: Vec<usize> = Vec::with_capacity(self.backward_map.len());
        let mut visited = vec![false; self.backward_map.len()];
        stack.push(u);
        while !stack.is_empty() {
            let current = unsafe { stack.pop().unwrap_unchecked() };
            if visited[current] {
                continue;
            }
            visited[current] = true;
            if current == v {
                return true;
            }
            if let Entry::Occupied(o) = graph.entry(current) {
                stack.extend(o.get());
            }
        }
        false
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
        (0..self.backward_map.len())
            .all(|x| self.relation.contains(&(x, x)))
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
        (0..self.backward_map.len())
            .all(|x| !self.relation.contains(&(x, x)))
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
    /// assert!(relation.is_asymmetric());
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
    /// let relation = relation!(0 => 1, 1 => 2, 2 => 3, 3 => 3);
    ///
    /// assert!(relation.is_antisymmetric());
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
        self.is_irreflexive() && self.is_asymmetric() && self.is_transitive()
    }

    /// Check whether the relation defines a function.
    ///
    /// A function is a relation such that for all y and z
    /// such that (x, y) and (x, z) are both contained in the
    /// relation, y == z.
    /// With other words, a function is a relation where for all
    /// x, there is at most one tuple (x, _).
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel_1 = relation!(1 => 2, 2 => 3, 1 => 3, 3 => 4);
    /// let rel_2 = relation!(1 => 2, 2 => 3, 3 => 4);
    ///
    /// assert!(!rel_1.is_function());
    /// assert!(rel_2.is_function());
    /// ```
    pub fn is_function(&self) -> bool {
        let mut counts = vec![0; self.backward_map.len()];
        for (x, _) in self.relation.iter() {
            counts[*x] += 1;
            if counts[*x] > 1 {
                return false;
            }
        }
        true
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
        for x in 0..self.backward_map.len() {
            let key = (x, x);
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
        for k in 0..self.backward_map.len() {
            for i in 0..self.backward_map.len() {
                for j in 0..self.backward_map.len() {
                    let key_1 = (i, k);
                    let key_2 = (k, j);
                    if new_relation.contains(&key_1) && new_relation.contains(&key_2) {
                        new_relation.insert((i, j));
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
            let u = &self.backward_map[*x];
            let v = &self.backward_map[*y];
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

    /// Compute the relative set for some given element x.
    ///
    /// The relative set of x is the set of all elements
    /// y such that (x, y) is contained in the relation.
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(1 => 2, 1 => 3, 2 => 3);
    ///
    /// assert_eq!(rel.relative_set(&1), HashSet::from([2, 3]));
    /// ```
    pub fn relative_set(&self, x: &U) -> HashSet<U> {
        if !self.forward_map.contains_key(x) {
            return HashSet::new();
        }
        let target = self.forward_map[x];
        let indices = self.relation
            .iter()
            .filter(|(p, _)| p == &target)
            .map(|(_, q)| q);
        HashSet::from_iter(indices.map(|y| self.backward_map[*y].clone()))
    }

    /// Compute the transpose relation of this relation.
    ///
    /// The transposed relation is obtained by taking
    /// the original relation containing pairs (x, y),
    /// and constructing a new relation containing
    /// all pairs (y, x).
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(1 => 2, 1 => 3, 2 => 3);
    ///
    /// assert_eq!(
    ///     rel.transpose(),
    ///     relation!(2 => 1, 3 => 1, 3 => 2)
    /// );
    /// ```
    pub fn transpose(&self) -> Relation<U> {
        Self::new(
            self.forward_map.clone(),
            self.backward_map.clone(),
            self.relation.iter().copied().map(|(x, y)| (y, x)).collect()
        )
    }

    /// Alias for the `transpose` method.
    #[inline(always)]
    pub fn inverse(&self) -> Relation<U> {
        self.transpose()
    }

    /// Compute the complement of the relation.
    ///
    /// The complement contains all pairs (x, y)
    /// such that x and y are not related in the original
    /// relation.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 1);
    ///
    /// assert_eq!(
    ///     rel.complement(),
    ///     relation!(
    ///         1 => 1, 2 => 2, 3 => 3, 4 => 4,
    ///         1 => 3, 1 => 4,
    ///         2 => 1, 2 => 4,
    ///         3 => 1, 3 => 2,
    ///         4 => 2, 4 => 3
    ///     )
    /// );
    /// assert_eq!(rel.complement().complement(), rel);
    /// ```
    pub fn complement(&self) -> Relation<U> {
        let mut pairs: HashSet<Pair<&U>> = HashSet::new();
        for x in self.backward_map.iter() {
            for y in self.backward_map.iter() {
                if !self.are_related(x, y) {
                    pairs.insert((x, y));
                }
            }
        }
        Self::from_iter(pairs)
    }

    /// Compute the equivalence classes of the relation.
    /// This method can only be called if the relation is
    /// an equivalence relation.
    ///
    /// Equivalence classes are sets of elements which
    /// are considered "equal" or equivalent according
    /// to the relation.
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use relations::{relation, Relation};
    ///
    /// let relation = relation!(
    ///     1 => 2, 2 => 1, 1 => 1, 2 => 2,
    ///
    ///     3 => 4, 4 => 5, 3 => 5, 5 => 3, 5 => 4, 4 => 3,
    ///     3 => 3, 4 => 4, 5 => 5,
    ///
    ///     6 => 6
    /// );
    ///
    /// assert_eq!(
    ///     relation.equivalence_classes(),
    ///     vec![
    ///         HashSet::from([1, 2]),
    ///         HashSet::from([3, 4, 5]),
    ///         HashSet::from([6]),
    ///     ]
    /// );
    /// ```
    pub fn equivalence_classes(&self) -> Vec<HashSet<U>> {
        if !self.is_equivalence() {
            panic!(".equivalence_classes() can only be called on an equivalence");
        }
        let mut classes: Vec<HashSet<usize>> = Vec::new();
        let mut class_indices:  HashMap<usize, usize> = HashMap::new();
        let mut pairs = self.relation.iter().copied().collect::<Vec<(usize, usize)>>();
        pairs.sort();
        for (from, to) in pairs {
            if let Entry::Vacant(e) = class_indices.entry(from) {
                e.insert(classes.len());
                classes.push(HashSet::from([from]));
            }
            classes[class_indices[&from]].insert(to);
            class_indices.insert(to, class_indices[&from]);
        }
        classes
            .into_iter()
            .map(|cls|
                cls
                    .into_iter()
                    .map(|x| self.backward_map[x].clone()).collect())
            .collect()
    }

    /// Compute the strongly connected components of the relation.
    ///
    /// Strongly connected components are groups of elements
    /// where there exists a "path" from any element to any
    /// other element.
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use relations::{relation, Relation};
    ///
    /// let rel_2 = relation!(
    ///     1 => 2,
    ///     2 => 3, 2 => 5,
    ///     3 => 4, 3 => 7,
    ///     4 => 3, 4 => 8,
    ///     5 => 6, 5 => 1,
    ///     6 => 7,
    ///     7 => 6,
    ///     8 => 4, 8 => 7
    /// );
    /// assert_eq!(
    ///     rel_2.strongly_connected_components(),
    ///     vec![
    ///         HashSet::from([1, 2, 5]),
    ///         HashSet::from([3, 4, 8]),
    ///         HashSet::from([6, 7]),
    ///     ]
    /// );
    /// ```
    pub fn strongly_connected_components(&self) -> Vec<HashSet<U>> {
        let mut stack: Vec<usize> = Vec::with_capacity(self.forward_map.len());
        // First round of DFS
        let mut visited: Vec<bool> = vec![false; self.forward_map.len()];
        let mut graph = self.as_map();
        for v in 0..self.forward_map.len() {
            Self::dfs_1(v, &mut graph, &mut visited, &mut stack);
        }
        // Second round of DFS
        let mut groups = Vec::new();
        let mut transposed_graph = self.transpose().as_map();
        visited = vec![false; self.forward_map.len()];
        stack.reverse();
        for v in stack.into_iter() {
            let mut current_group: HashSet<U> = HashSet::new();
            self.dfs_2(v, &mut transposed_graph, &mut visited, &mut current_group);
            if !current_group.is_empty() {
                groups.push(current_group);
            }
        }
        groups
    }

    fn dfs_1(v: usize,
             graph: &mut HashMap<usize, Vec<usize>>,
             visited: &mut Vec<bool>,
             stack: &mut Vec<usize>)
    {
        if !visited[v] {
            visited[v] = true;
            let children = graph
                .entry(v)
                .or_insert_with(Vec::new)
                .to_vec();
            for child in children {
                Self::dfs_1(child, graph, visited, stack);
            }
            stack.push(v);
        }
    }

    fn dfs_2(&self,
             v: usize,
             graph: &mut HashMap<usize, Vec<usize>>,
             visited: &mut Vec<bool>,
             group: &mut HashSet<U>)
    {
        if !visited[v] {
            visited[v] = true;
            group.insert(self.backward_map[v].clone());
            let children = graph
                .entry(v)
                .or_insert_with(Vec::new)
                .to_vec();
            for child in children {
                self.dfs_2(child, graph, visited, group);
            }
        }
    }

    /// Build the connectivity relation of the relation.
    ///
    /// The connectivity relation contains all pairs (x, y)
    /// such that there exists a path from x to y in the
    /// original relation.
    /// With other words, the connectivity relation contains
    /// all pairs (x, y) such that for the original relation
    /// `r`, r.reachable_from(&x, &y) == true.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(
    ///     1 => 2, 2 => 3, 3 => 4,
    ///     4 => 2,
    ///     5 => 6, 6 => 5
    /// );
    ///
    /// let conn_rel = rel.connectivity_relation();
    ///
    /// assert_eq!(
    ///     conn_rel,
    ///     relation!(
    ///         1 => 2, 1 => 3, 1 => 4,
    ///         2 => 3, 2 => 4, 2 => 2,
    ///         3 => 4, 3 => 2, 3 => 3,
    ///         4 => 2, 4 => 3, 4 => 4,
    ///         5 => 6, 6 => 5, 5 => 5, 6 => 6
    ///     )
    /// );
    /// ```
    pub fn connectivity_relation(&self) -> Relation<U> {
        let mut connected_pairs: HashSet<Pair<usize>> = HashSet::new();
        let mut graph = self.as_map();
        for start in 0..self.backward_map.len() {
            let mut stack = Vec::with_capacity(self.backward_map.len());
            let mut visited = vec![false; self.backward_map.len()];
            stack.push(start);
            while !stack.is_empty() {
                let current = unsafe { stack.pop().unwrap_unchecked() };
                if visited[current] {
                    continue;
                }
                visited[current] = true;
                let children = graph
                    .entry(current)
                    .or_insert_with(Vec::new)
                    .to_vec();
                for child in children {
                    connected_pairs.insert((start, child));
                    stack.push(child);
                }
            }
        }
        Self::new(
            self.forward_map.clone(),
            self.backward_map.clone(),
            connected_pairs
        )
    }

    /// Multiply two relations.
    ///
    /// The product of two relations is defined in the
    /// following way:
    /// if the LHS contains (x, y) and the RHS contains
    /// (y, z), then the product contains (x, z).
    ///
    /// Note that this is a non-commutative product.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(1 => 2, 2 => 3, 3 => 4);
    ///
    /// assert_eq!(rel.product(&rel), relation!(1 => 3, 2 => 4));
    /// ```
    pub fn product(&self, other: &Relation<U>) -> Relation<U> {
        let mut pairs: HashSet<Pair<U>> = HashSet::new();
        for (x, y) in self.relation.iter().copied() {
            for (u, v) in other.relation.iter().copied() {
                if self.backward_map[y] != other.backward_map[u] {
                    continue;
                }
                let pair = (self.backward_map[x].clone(), other.backward_map[v].clone());
                pairs.insert(pair);
            }
        }
        Relation::from_iter(pairs)
    }

    /// Optimized function for computing R^2.
    fn pow2(&self) -> Relation<U> {
        let graph = self.as_map();
        let mut pairs: HashSet<Pair<usize>> = HashSet::new();
        for (from, targets) in graph.iter() {
            for target in targets.iter() {
                if graph.contains_key(target) {
                    for new_target in graph[target].iter() {
                        pairs.insert((*from, *new_target));
                    }
                }
            }
        }
        Self::new(self.forward_map.clone(),
                  self.backward_map.clone(),
                  pairs)
    }

    /// Compute the n-th power of the relation.
    ///
    /// Here, the n-th power of the relation by multiplying
    /// the relation n times with itself, using the
    /// `.product` function.
    /// Note that R^1 = R, and R^0 is the identity relation.
    ///
    /// We can interpret R^n as the relation of all pairs
    /// (x, y) where we can move in n steps from x to y
    /// in the original relation R.
    ///
    /// ```
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(1 => 2, 2 => 3, 3 => 4);
    ///
    /// assert_eq!(rel.pow(0), relation!(1 => 1, 2 => 2, 3 => 3, 4 => 4));
    /// assert_eq!(rel.pow(1), rel);
    /// assert_eq!(rel.pow(2), relation!(1 => 3, 2 => 4));
    /// assert_eq!(rel.pow(3), relation!(1 => 4));
    /// assert_eq!(rel.pow(4), relation!());
    /// ```
    pub fn pow(&self, n: u64) -> Relation<U> {
        // We can use the well-known divide and conquer
        // algorithm for exponentiation.
        // This is because the product of relations
        // is equivalent/isomorphic to the multiplication
        // of matrices representing the relations.
        if n == 0 {
            let identity = (0..self.backward_map.len()).map(|x| (x, x));
            return Self::new(
                self.forward_map.clone(),
                self.backward_map.clone(),
                    HashSet::from_iter(identity)
            );
        } else if n == 1 {
            return self.clone();
        }
        let half = self.pow(n / 2);
        let prod = half.pow2();
        if n % 2 == 1 {
            return self.product(&prod);
        }
        prod
    }

    fn as_map(&self) -> HashMap<usize, Vec<usize>> {
        let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (x, y) in self.relation.iter().copied() {
            map.entry(x).or_insert_with(Vec::new).push(y);
        }
        map
    }

    /// Convert the relation into a hashmap, where for
    /// every key-value entry, the key is related
    /// to all the items in the value (which is a hashset).
    ///
    /// ```
    /// use std::collections::{HashMap, HashSet};
    /// use relations::{relation, Relation};
    ///
    /// let rel = relation!(
    ///     1 => 2, 1 => 3, 2 => 3,
    ///     4 => 4,
    ///     5 => 6, 6 => 5
    /// );
    ///
    /// let map = HashMap::from_iter(
    ///     [
    ///         (1, HashSet::from([2, 3])),
    ///         (2, HashSet::from([3])),
    ///         (4, HashSet::from([4])),
    ///         (5, HashSet::from([6])),
    ///         (6, HashSet::from([5])),
    ///     ]
    /// );
    ///
    /// assert_eq!(rel.to_hashmap(), map);
    /// ```
    pub fn to_hashmap(&self) -> HashMap<U, HashSet<U>> {
        HashMap::from_iter(
            self.as_map().into_iter().map(|(from, tos)|
                (
                    self.backward_map[from].clone(),
                    HashSet::from_iter(tos.into_iter().map(|x| self.backward_map[x].clone()))
                )
            )
        )
    }

}

impl<U: Eq + Hash + Clone + Debug> FromIterator<Pair<U>> for Relation<U> {
    fn from_iter<T: IntoIterator<Item=Pair<U>>>(iter: T) -> Self {
        let mut forward_map = HashMap::new();
        let mut backward_map = Vec::new();
        let mut relation = HashSet::new();
        for (x, y) in iter {
            [&x, &y].into_iter().for_each(|z| {
                let item = z.clone();
                if !forward_map.contains_key(&item) {
                    let id = forward_map.len();
                    forward_map.insert(item.clone(), id);
                    backward_map.push(item);
                }
            });
            relation.insert((forward_map[&x], forward_map[&y]));
        }
        Self::new(forward_map, backward_map, relation)
    }
}

impl<'a, U: Eq + Hash + Clone + Debug> FromIterator<Pair<&'a U>> for Relation<U> {
    fn from_iter<T: IntoIterator<Item=Pair<&'a U>>>(iter: T) -> Self {
        let mut forward_map = HashMap::new();
        let mut backward_map = Vec::new();
        let mut relation = HashSet::new();
        for (x, y) in iter {
            [&x, &y].into_iter().for_each(|z| {
                let item = *z;
                if !forward_map.contains_key(item) {
                    let id = forward_map.len();
                    forward_map.insert(item.clone(), id);
                    backward_map.push(item.clone());
                }
            });
            relation.insert((forward_map[x], forward_map[y]));
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
    () => {
        {
            Relation::empty()
        }
    };
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
