//! # relations -- A basic crate for working with mathematical relations
//!
//! The goal of this crate is to provide a basic and lightweight
//! library for working with mathematical relations.
//!
//! # Relations
//! Mathematically, relations are sets of 2-tuples.
//! Given a relation R and two items x and y,
//! x and y are said to be R-related if
//! (x, y) is contained in R.
//!
//! Relations can be useful in the implementation of certain
//! algorithms. Additionally, they can be used to model graphs.
//!
//! This crate provides functionality for creating
//! relations and working with them.
//! In particular, there is functionality for testing
//! properties of relations, such as testing whether
//! a relation is transitive.
//! Additionally, there is functionality for computing
//! closures.
//!
//! # Scope of the Crate
//!
//! This crate is not aiming to be feature complete
//! or particularly feature rich.
//! However, features additions of requests are
//! always welcome.
//!
//! # Getting Started
//!
//! There are two main exports in this crate:
//! The `Relation` struct and the `relation!` macro.
//! The former is the central object used to represent
//! relations. The latter provides convenient syntax
//! for denoting static relations.
//!
//! Getting can be as easy as defining a relation using
//! the relation! macro:
//!
//! ```
//! use relations::{relation, Relation};
//!
//! let my_relation = relation!(
//!     0 => 1,
//!     1 => 2,
//!     2 => 3
//! );
//! ```
//!
//! It is then easy to test whether items are related:
//! ```
//! # use relations::{relation, Relation};
//! #
//! # let my_relation = relation!(
//! #     0 => 1,
//! #     1 => 2,
//! #     2 => 3
//! # );
//!
//! assert!(my_relation.are_related(&1, &2));
//! assert!(!my_relation.are_related(&0, &3));
//! assert!(!my_relation.are_related(&3, &4));
//! ```
//!
//! One can then use the provided methods to test things
//! about the relation:
//!
//! ```
//! # use relations::{relation, Relation};
//! #
//! # let my_relation = relation!(
//! #     0 => 1,
//! #     1 => 2,
//! #     2 => 3
//! # );
//! assert!(!my_relation.is_reflexive());
//! assert!(!my_relation.is_symmetric());
//! assert!(!my_relation.is_transitive());
//! assert!(my_relation.is_irreflexive());
//! assert!(my_relation.is_asymmetric());
//! assert!(my_relation.is_antisymmetric());
//! ```
//!
//! You can also compute closures of relations:
//!
//! ```
//! # use relations::{relation, Relation};
//! #
//! # let my_relation = relation!(
//! #     0 => 1,
//! #     1 => 2,
//! #     2 => 3
//! # );
//! assert_eq!(
//!     my_relation.reflexive_closure(),
//!     relation!(0 => 1, 1 => 2, 2 => 3, 0 => 0, 1 => 1, 2 => 2, 3 => 3)
//! );
//! assert_eq!(
//!     my_relation.symmetric_closure(),
//!     relation!(0 => 1, 1 => 2, 2 => 3, 1 => 0, 2 => 1, 3 => 2)
//! );
//! assert_eq!(
//!     my_relation.transitive_closure(),
//!     relation!(0 => 1, 0 => 2, 0 => 3, 1 => 2, 1 => 3, 2 => 3)
//! );
//! ```
//!
//! It is also possible to define relations containing non-numerical items:
//!
//! ```
//! use relations::{relation, Relation};
//!
//! let my_string_relation = relation!(
//!     "a" => "b",
//!     "b" => "c",
//!     "c" => "d"
//! );
//! ```
//!
//! If you need to define relations dynamically, you can create them
//! from iterators:
//!
//! ```
//! use relations::{Relation, relation};
//!
//! let my_relation = Relation::from_iter((1..=10).map(|x| (x, x)));
//!
//! assert_eq!(
//!     my_relation,
//!     relation!(
//!         1 => 1,
//!         2 => 2,
//!         3 => 3,
//!         4 => 4,
//!         5 => 5,
//!         6 => 6,
//!         7 => 7,
//!         8 => 8,
//!         9 => 9,
//!         10 => 10
//!     )
//! );
//! ```

mod relation;

pub use crate::relation::Relation;


#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};
    use crate::Relation;
    use crate::relation;

    #[test]
    fn test_related() {
        let rel = relation!(
            1 => 2,
            5 => 9,
            3 => 0
        );
        assert!(rel.are_related(&1, &2));
        assert!(rel.are_related(&5, &9));
        assert!(rel.are_related(&3, &0));
        assert!(!rel.are_related(&1, &5));
        assert!(!rel.are_related(&1, &9));
        assert!(!rel.are_related(&1, &3));
        assert!(!rel.are_related(&1, &0));
        assert!(!rel.are_related(&5, &2));
        assert!(!rel.are_related(&5, &0));
        assert!(!rel.are_related(&3, &2));
        assert!(!rel.are_related(&2, &1));
        assert!(!rel.are_related(&0, &3));
        assert!(!rel.are_related(&2, &1));
        assert!(!rel.are_related(&4, &7));
    }

    #[test]
    fn test_is_reflexive() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(rel_1.is_reflexive());

        let rel_2 = relation!(
            1 => 2,
            2 => 3,
            3 => 1
        );
        assert!(!rel_2.is_reflexive());

        let rel_3: Relation<i32> = relation!();
        assert!(rel_3.is_reflexive());
    }

    #[test]
    fn test_is_irreflexive() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(!rel_1.is_irreflexive());

        let rel_2 = relation!(
            1 => 2,
            2 => 3,
            3 => 1
        );
        assert!(rel_2.is_irreflexive());

        let rel_3: Relation<i32> = relation!();
        assert!(rel_3.is_irreflexive());
    }

    #[test]
    fn test_is_transitive() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(rel_1.is_transitive());

        let rel_2 = relation!(
            1 => 2,
            2 => 3,
            3 => 1
        );
        assert!(!rel_2.is_transitive());

        let rel_3 = relation!(
            1 => 2,
            2 => 3,
            1 => 3
        );
        assert!(rel_3.is_transitive());

        let rel_4: Relation<i32> = relation!();
        assert!(rel_4.is_transitive());
    }

    #[test]
    fn test_is_symmetric() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(rel_1.is_symmetric());

        let rel_2 = relation!(
            1 => 2,
            2 => 1,
            1 => 3,
            3 => 1
        );
        assert!(rel_2.is_symmetric());

        let rel_3: Relation<i32> = relation!();
        assert!(rel_3.is_symmetric());

        let rel_4 = relation!(
            1 => 2,
            2 => 1,
            1 => 3
        );
        assert!(!rel_4.is_symmetric());
    }

    #[test]
    fn test_is_asymmetric() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(!rel_1.is_asymmetric());

        let rel_2 = relation!(
            1 => 2,
            2 => 1,
            1 => 3,
            3 => 1
        );
        assert!(!rel_2.is_asymmetric());

        let rel_3: Relation<i32> = relation!();
        assert!(rel_3.is_asymmetric());

        let rel_4 = relation!(
            1 => 2,
            2 => 1,
            1 => 3
        );
        assert!(!rel_4.is_asymmetric());

        let rel_5 = relation!(
            1 => 2,
            1 => 3
        );
        assert!(rel_5.is_asymmetric());
    }

    #[test]
    fn test_is_antisymmetric() {
        let rel_1 = relation!(
            1 => 1,
            2 => 2,
            3 => 3
        );
        assert!(rel_1.is_antisymmetric());

        let rel_2 = relation!(
            1 => 2,
            2 => 1,
            1 => 3,
            3 => 1
        );
        assert!(!rel_2.is_antisymmetric());

        let rel_3: Relation<i32> = relation!();
        assert!(rel_3.is_antisymmetric());

        let rel_4 = relation!(
            1 => 1,
            1 => 2,
            1 => 3
        );
        assert!(rel_4.is_antisymmetric());
    }

    #[test]
    fn test_is_subset() {
        let empty: Relation<i32> = relation!();
        assert!(empty.is_subset(&empty));
        assert!(empty.is_subset(&relation!(1 => 2)));
        assert!(!relation!(1 => 2).is_subset(&empty));
        let x = relation!(1 => 2, 2 => 3, 4 => 5);
        let y = relation!(1 => 2, 4 => 5);
        assert!(y.is_subset(&x));
        assert!(!x.is_subset(&y));
        let z = relation!(1 => 2, 4 => 5, 4 => 7);
        assert!(!z.is_subset(&x));
        assert!(!z.is_subset(&y));
        assert!(!x.is_subset(&z));
        assert!(y.is_subset(&z));
        assert!(x.is_subset(&x));
        assert!(y.is_subset(&y));
        assert!(z.is_subset(&z));
    }

    #[test]
    fn test_is_proper_subset() {
        let empty: Relation<i32> = relation!();
        assert!(!empty.is_proper_subset(&empty));
        assert!(empty.is_proper_subset(&relation!(1 => 2)));
        assert!(!relation!(1 => 2).is_proper_subset(&empty));
        let x = relation!(1 => 2, 2 => 3, 4 => 5);
        let y = relation!(1 => 2, 4 => 5);
        assert!(y.is_proper_subset(&x));
        assert!(!x.is_proper_subset(&y));
        let z = relation!(1 => 2, 4 => 5, 4 => 7);
        assert!(!z.is_proper_subset(&x));
        assert!(!z.is_proper_subset(&y));
        assert!(!x.is_proper_subset(&z));
        assert!(y.is_proper_subset(&z));
        assert!(!x.is_proper_subset(&x));
        assert!(!y.is_proper_subset(&y));
        assert!(!z.is_proper_subset(&z));
    }

    #[test]
    fn test_equality() {
        let empty_relation: Relation<i32> = relation!();
        assert_eq!(empty_relation, relation!());
        assert_eq!(relation!(1 => 2), relation!(1 => 2));
        assert_eq!(
            relation!(1 => 2, 1 => 3, 4 => 5, 6 => 6),
            relation!(1 => 2, 1 => 3, 4 => 5, 6 => 6)
        );
        assert_ne!(relation!(), relation!(1 => 2));
        assert_ne!(relation!(1 => 3), relation!(3 => 4));
    }

    #[test]
    fn test_reflexive_closure() {
        let rel_1: Relation<i32> = relation!();
        assert_eq!(rel_1.reflexive_closure(), relation!());
        assert_eq!(
            relation!(1 => 1).reflexive_closure(),
            relation!(1 => 1)
        );
        assert_eq!(
            relation!(1 => 2).reflexive_closure(),
            relation!(1 => 2, 1 => 1, 2 => 2)
        );
        assert_eq!(
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4).reflexive_closure(),
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4, 1 => 1, 3 => 3, 4 => 4)
        );
    }

    #[test]
    fn test_symmetric_closure() {
        let rel_1: Relation<i32> = relation!();
        assert_eq!(rel_1.symmetric_closure(), relation!());
        assert_eq!(
            relation!(1 => 1).symmetric_closure(),
            relation!(1 => 1)
        );
        assert_eq!(
            relation!(1 => 2).symmetric_closure(),
            relation!(1 => 2, 2 => 1)
        );
        assert_eq!(
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4).symmetric_closure(),
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4, 2 => 1, 3 => 1, 4 => 2)
        );
    }

    #[test]
    fn test_transitive_closure() {
        let rel_1: Relation<i32> = relation!();
        assert_eq!(rel_1.transitive_closure(), relation!());
        assert_eq!(
            relation!(1 => 1).transitive_closure(),
            relation!(1 => 1)
        );
        assert_eq!(
            relation!(1 => 2).transitive_closure(),
            relation!(1 => 2)
        );
        assert_eq!(
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4).transitive_closure(),
            relation!(1 => 2, 2 => 2, 1 => 3, 2 => 4, 1 => 4)
        );
        assert_eq!(
            relation!(1 => 2, 2 => 3, 3 => 4, 4 => 5).transitive_closure(),
            relation!(
                1 => 2, 1 => 3, 1 => 4, 1 => 5,
                2 => 3, 2 => 4, 2 => 5,
                3 => 4, 3 => 5,
                4 => 5
            )
        );
    }

    #[test]
    fn test_relative_set() {
        let rel_1 = relation!(1 => 2, 1 => 3, 2 => 3);
        assert_eq!(rel_1.relative_set(&0), HashSet::new());
        assert_eq!(rel_1.relative_set(&1), HashSet::from([2, 3]));
        assert_eq!(rel_1.relative_set(&2), HashSet::from([3]));
        assert_eq!(rel_1.relative_set(&3), HashSet::new());
    }

    #[test]
    fn test_transpose() {
        let rel: Relation<i32> = relation!();
        assert_eq!(rel.transpose(), rel);

        assert_eq!(
            relation!(1 => 2, 2 => 3, 3 => 4).transpose(),
            relation!(4 => 3, 3 => 2, 2 => 1)
        );

        assert_eq!(
            relation!(1 => 1, 1 => 2, 2 => 3, 3 => 1, 5 => 6, 6 => 5).transpose(),
            relation!(1 => 1, 2 => 1, 3 => 2, 1 => 3, 6 => 5, 5 => 6)
        );
    }

    #[test]
    fn test_equivalence_classes() {
        let rel_1: Relation<i32> = relation!();
        assert_eq!(rel_1.equivalence_classes(), Vec::new());

        let rel_2 = relation!(1 => 1, 2 => 2, 3 => 3);
        assert_eq!(
            rel_2.equivalence_classes(),
            vec![HashSet::from([1]), HashSet::from([2]), HashSet::from([3])]
        );

        let rel_3 = relation!(
            1 => 2, 1 => 3, 1 => 4,
            2 => 1, 3 => 1, 4 => 1,
            2 => 4, 2 => 3,
            3 => 2, 3 => 4,
            4 => 2, 4 => 3,
            1 => 1, 2 => 2, 3 => 3, 4 => 4
        );
        assert_eq!(
            rel_3.equivalence_classes(),
            vec![HashSet::from([1, 2, 3, 4])]
        );

        let rel_4 = relation!(
            // Class 1
            1 => 2, 2 => 1, 1 => 1, 2 => 2,

            // Class 2
            3 => 4, 4 => 3, 3 => 3, 4 => 4,

            // Class 3
            5 => 6, 5 => 7, 6 => 5, 7 => 5,
            6 => 7, 7 => 6,
            5 => 5, 6 => 6, 7 => 7
        );
        assert_eq!(
            rel_4.equivalence_classes(),
            vec![
                HashSet::from([1, 2]),
                HashSet::from([3, 4]),
                HashSet::from([5, 6, 7]),
            ]
        );
    }

    #[test]
    fn test_strongly_connected_components() {
        let rel_1: Relation<i32> = relation!();
        assert_eq!(rel_1.strongly_connected_components(), Vec::new());

        let rel_2 = relation!(
            1 => 2,
            2 => 3, 2 => 5,
            3 => 4, 3 => 7,
            4 => 3, 4 => 8,
            5 => 6, 5 => 1,
            6 => 7,
            7 => 6,
            8 => 4, 8 => 7
        );
        assert_eq!(
            rel_2.strongly_connected_components(),
            vec![
                HashSet::from([1, 2, 5]),
                HashSet::from([3, 4, 8]),
                HashSet::from([6, 7]),
            ]
        );
    }

    #[test]
    fn test_is_reachable() {
        let rel = relation!(
             1 => 2, 2 => 3, 3 => 1,
             4 => 5,
             6 => 7, 7 => 8,
             9 => 9
        );

        assert!(rel.reachable_from(&1, &2));
        assert!(rel.reachable_from(&1, &3));
        assert!(rel.reachable_from(&2, &3));
        assert!(rel.reachable_from(&1, &1));
        assert!(rel.reachable_from(&4, &5));
        assert!(rel.reachable_from(&9, &9));
        assert!(!rel.reachable_from(&1, &9));
        assert!(!rel.reachable_from(&5, &4));
    }

    #[test]
    fn test_connectivity_relation() {
         let rel = relation!(
             1 => 2, 2 => 3, 3 => 4,
             4 => 2,
             5 => 6, 6 => 5
         );
         assert_eq!(
             rel.connectivity_relation(),
             relation!(
                 1 => 2, 1 => 3, 1 => 4,
                 2 => 3, 2 => 4, 2 => 2,
                 3 => 4, 3 => 2, 3 => 3,
                 4 => 2, 4 => 3, 4 => 4,
                 5 => 6, 6 => 5, 5 => 5, 6 => 6
             )
         );

        let empty_rel: Relation<i32> = relation!();
        assert_eq!(empty_rel.connectivity_relation(), relation!());
    }

    #[test]
    fn test_to_hashmap() {
         let rel = relation!(
             1 => 2, 1 => 3, 2 => 3,
             4 => 4,
             5 => 6, 6 => 5
         );
         let map = HashMap::from_iter(
             [
                 (1, HashSet::from([2, 3])),
                 (2, HashSet::from([3])),
                 (4, HashSet::from([4])),
                 (5, HashSet::from([6])),
                 (6, HashSet::from([5])),
             ]
         );
         assert_eq!(rel.to_hashmap(), map);

        let empty_rel: Relation<i32> = relation!();
        assert_eq!(empty_rel.to_hashmap(), HashMap::new());
    }

    #[test]
    fn test_product() {
        let empty: Relation<i32> = relation!();
        let rel = relation!(1 => 2, 2 => 3);
        let identity = relation!(1 => 1, 2 => 2, 3 => 3);
        assert_eq!(empty.product(&rel), relation!());
        assert_eq!(rel.product(&empty), relation!());
        assert_eq!(rel.product(&rel), relation!(1 => 3));
        assert_eq!(rel.product(&identity), rel);
        assert_eq!(identity.product(&rel), rel);

        let circular = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 1);
        assert_eq!(
            circular.product(&circular),
            relation!(1 => 3, 2 => 4, 3 => 1, 4 => 2)
        );
        assert_eq!(
            circular.product(&rel),
            relation!(1 => 3, 4 => 2)
        );
        assert_eq!(
            rel.product(&circular),
            relation!(1 => 3, 2 => 4)
        );
    }

    #[test]
    fn test_pow() {
        let empty: Relation<i32> = relation!();
        let rel = relation!(1 => 2, 2 => 3);
        let identity = relation!(1 => 1, 2 => 2, 3 => 3);

        assert_eq!(empty.pow(0), empty);
        assert_eq!(empty.pow(1), empty);
        assert_eq!(empty.pow(2), empty);

        assert_eq!(identity.pow(0), identity);
        assert_eq!(identity.pow(1), identity);
        assert_eq!(identity.pow(2), identity);

        assert_eq!(rel.pow(0), identity);
        assert_eq!(rel.pow(1), rel);
        assert_eq!(rel.pow(2), relation!(1 => 3));
        assert_eq!(rel.pow(3), relation!());
    }

    #[test]
    fn test_complement() {
        let rel = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 1);
        assert_eq!(
            rel.complement(),
            relation!(
                1 => 1, 2 => 2, 3 => 3, 4 => 4,
                1 => 3, 1 => 4,
                2 => 1, 2 => 4,
                3 => 1, 3 => 2,
                4 => 2, 4 => 3
            )
        );
        assert_eq!(rel.complement().complement(), rel);
    }

    #[test]
    fn test_is_function() {
        let rel_1 = relation!(1 => 2, 2 => 3, 1 => 3, 3 => 4);
        let rel_2 = relation!(1 => 2, 2 => 3, 3 => 4);
        assert!(!rel_1.is_function());
        assert!(rel_2.is_function());
    }

    #[test]
    fn test_topological_sort() {
        let linear = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 5);
        let sort = linear.topological_sort();
        assert!(sort.is_some());
        let order = sort.unwrap();
        assert!(
            order == vec![1, 2, 3, 4, 5] ||
                order == vec![5, 4, 3, 2, 1],
            "simple: {:?}", order
        );

        let complex = relation!(1 => 2, 1 => 3, 2 => 5, 2 => 4, 3 => 6, 3 => 4, 4 => 5, 4 => 6);
        let sort = complex.topological_sort();
        assert!(sort.is_some());
        let order = sort.unwrap();
        assert!(
            order == vec![1, 2, 3, 4, 5, 6] ||
                order == vec![1, 3, 2, 4, 5, 6] ||
                order == vec![1, 2, 3, 4, 6, 5] ||
                order == vec![1, 3, 2, 4, 6, 5],
            "complex: {:?}", order
        );

        let cyclic = relation!(1 => 2, 2 => 3, 3 => 1);
        let sort = cyclic.topological_sort();
        assert!(sort.is_none());

        let self_loop = relation!(1 => 2, 2 => 2);
        let sort = self_loop.topological_sort();
        assert!(sort.is_none());
    }

    #[test]
    fn test_is_dag() {
        let loopy = relation!(1 => 2, 2 => 1);
        assert!(!loopy.is_dag());

        let linear = relation!(1 => 2, 2 => 3, 3 => 4);
        assert!(linear.is_dag());

        let tree = relation!(1 => 2, 2 => 3, 2 => 4, 1 => 5, 5 => 6, 5 => 7);
        assert!(tree.is_dag());

        let ring = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 1);
        assert!(!ring.is_dag());

        let self_loop = relation!(1 => 2, 2 => 2);
        assert!(!self_loop.is_dag());
    }

    #[test]
    fn test_find_cycles() {
        let linear = relation!(1 => 2, 2 => 3, 3 => 4);
        assert_eq!(linear.find_cycles(), Vec::<Vec<i32>>::new());

        let loopy = relation!(1 => 2, 2 => 1);
        let cycles = loopy.find_cycles();
        assert!(
            cycles == vec![vec![1, 2]] || cycles == vec![vec![2, 1]],
            "loopy: {:?}", cycles
        );

        let ring = relation!(1 => 2, 2 => 3, 3 => 4, 4 => 1);
        let cycles = ring.find_cycles();
        assert!(
            cycles == vec![vec![1, 2, 3, 4]]
                || cycles == vec![vec![2, 3, 4, 1]]
                || cycles == vec![vec![3, 4, 2, 1]]
                || cycles == vec![vec![4, 1, 2, 3]],
            "ring: {:?}", cycles
        );

        let complex = relation!(
            1 => 2,
            2 => 3, 2 => 6,
            3 => 2, 3 => 4, 4 => 7,
            4 => 2, 4 => 5,
            5 => 5,
            6 => 7
        );
        let cycles = complex.find_cycles();
        assert_eq!(cycles.len(), 3);
        assert!(
            cycles.contains(&vec![5]),
            "complex 1: {:?}", cycles
        );
        assert!(
            cycles.contains(&vec![2, 3]) || cycles.contains(&vec![3, 2]),
            "complex 2: {:?}", cycles
        );
        assert!(
            cycles.contains(&vec![2, 3, 4])
                || cycles.contains(&vec![3, 4, 2])
                || cycles.contains(&vec![4, 2, 3]),
            "complex 3: {:?}", cycles
        );
    }
}