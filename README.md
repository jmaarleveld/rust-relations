# relations -- A lightweight Rust library for working with mathematical relations

![Build](https://github.com/jmaarleveld/rust-relations/actions/workflows/build.yml/badge.svg)
![Tests](https://github.com/jmaarleveld/rust-relations/actions/workflows/test.yml/badge.svg)

The goal of this crate is to provide a basic and lightweight
library for working with mathematical relations.

# Getting Started 
Please refer to the [documentation](https://docs.rs/relations) 
for a guide on how to get started using this crate. 

# Relations
Mathematically, relations are sets of 2-tuples.
Given a relation R and two items x and y,
x and y are said to be R-related if
(x, y) is contained in R.

Relations can be useful in the implementation of certain
algorithms. Additionally, they can be used to model graphs.

This crate provides functionality for creating
relations and working with them.
In particular, there is functionality for testing
properties of relations, such as testing whether
a relation is transitive.
Additionally, there is functionality for computing
closures.

# Scope of the Crate
This crate is not aiming to be feature-complete
or particularly feature rich.
However, features additions of requests are always welcome;
feel free to contribute!
