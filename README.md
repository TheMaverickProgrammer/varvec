# Variable Vectors

The idea behind this repository is to implement a set of "variable vector" types,
built on top of `std::variant` machinery, allowing a user to store heterogenous
types in a `std::vector`-like container, but while using a minimal amount of memory
by contiguously packing data as tightly as possible.

For trivial types, the data is stored in a packed format that completely ignores
alignment requirements (data is re-aligned on-demand during access), and for
non-trivial user defined types, the data is stored on native alignment boundaries,
but each entry only needs the storage required by the current type, not the common
size of all types as would be the case with `std::vector<std::variant<...>>`.

At the moment this repository is rather bare; examples can be seen in the tests directory.
