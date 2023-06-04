# Variable Vectors

[![Build Status](https://app.travis-ci.com/Cfretz244/varvec.svg?branch=master)](https://app.travis-ci.com/Cfretz244/varvec)
[![Coverage Status](https://coveralls.io/repos/github/Cfretz244/varvec/badge.svg?branch=)](https://coveralls.io/github/Cfretz244/varvec?branch=)

The idea behind this repository is to implement a set of "variable vector" types,
built on top of `std::variant` machinery (although extensible to any type that implements
the same API), allowing a user to store heterogenous types in a `std::vector`-like container,
but while also maintaining a minimal memory footprint by contiguously packing data as
tightly as possible.

For trivial types, the data is stored in a packed format that completely ignores
alignment requirements (data is re-aligned on-demand during access), and for
non-trivial user defined types, the data is stored on native alignment boundaries,
but each entry only needs the storage required by the current type, not the common
size of all types as would be the case with `std::vector<std::variant<...>>`.

## Basic Usage

The library customizes into many different types, but at a high level there are only
three types exported, a vector implementation, an iterator, and an overload helper
for composing lambdas (still waiting on a standard option).

A motivating example akin to `std::vector<std::variant<...>>`:
```c++
#include <varvec.hpp>

int main() {
    // A complex vector type.
    using mixed_vector = varvec::static_vector<
        32,   // Total space to use for member storage
        5,    // Max members
        bool, // Types...
        int,
        float,
        double,
        std::unique_ptr<std::string>
    >;

    // Fill it with data of all types.
    mixed_vector vals;
    vals.push_back(true);
    vals.push_back(42);
    vals.push_back(0.5f);
    vals.push_back(3.14159);
    vals.push_back(std::make_unique<std::string>("hello world"));

    // Outputs:
    // Using visit_at syntax: 0.5
    // Using get_at syntax: hello world
    vals.visit_at(2, [] (auto& v) {
        std::cout << "Using visit_at syntax: " << v << std::endl;
    });
    std::cout
        << "Using get_at syntax: "
        << *vals.get_at<std::unique_ptr<std::string>>(4)
        << std::endl;

    // Outputs:
    // Range for: 1
    // Range for: 42
    // Range for: 0.5
    // Range for: 3.14159
    // Range for: hello world
    for (mixed_vector::value_type variant : vals) {
        std::visit(varvec::overload {
            [] <class T> (T* ptr) { std::cout << "Range for: " << **ptr << std::endl; },
            [] (auto& val) { std::cout << "Range for: " << val << std::endl; }
        }, variant);
    }

    // Outputs:
    // 39
    // std::vector<variant<...>> would require ~80 bytes.
    std::cout << vals.used_bytes() << std::endl;
}
```
