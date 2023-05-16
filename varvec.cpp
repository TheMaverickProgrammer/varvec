#include <iostream>
#include <variant>
#include <string>
#include <array>
#include <cassert>
#include <stdexcept>
#include <type_traits>

#define DIRTY_MACRO_DECLARE_OPERATOR(op)                                                  \
  friend bool operator op (vararray_iterator const& lhs, vararray_iterator const& rhs) {  \
    return lhs.idx op rhs.idx;                                                            \
  }

using myvar = std::variant<double, int, float>;

template <class, size_t, size_t>
class variant_array;

namespace detail {

  // Assert that all given variant types are trivial.
  template <template <class...> class Variant, class... Types>
  constexpr bool all_trivial_types(Variant<Types...> const&) {
    return (std::is_trivial_v<Types> && ...);
  }

  // Base case, unimplemented.
  template <class T>
  struct variant_unpacker;

  // Partial specialization to be able to extract the variant's types
  template <template <class...> class Variant, class... Types>
  struct variant_unpacker<Variant<Types...>> {
    using variant_type = Variant<Types...>;

    // Try each type, one after another, peeling one off on each recursion.
    template <class T, class... Ts, size_t Idx, size_t... Idxs>
    static constexpr variant_type unpack_impl(uint8_t type_idx,
        uint8_t const* repr, std::index_sequence<Idx, Idxs...>) {
      constexpr size_t curr_idx = Idx;
      using current_type = std::variant_alternative_t<curr_idx, variant_type>;

      // Is the current index equal to our recorded type index?
      if (type_idx == curr_idx) {
        // Create temporary aligned storage on the stack and return that
        // This allows us to keep the data structure size minimal, without accidentally
        // trying to load misaligned floats, for the low cost of one copy.
        std::aligned_storage_t<sizeof(std::max_align_t), alignof(std::max_align_t)> tmp;
        
        // New is a no-op, as this is a trivial type, but I think it technically makes the
        // std::launder below well defined behavior.
        new(&tmp) current_type();
        memcpy(&tmp, repr, sizeof(current_type));

        // Launder the pointer to get a live object to return.
        return *std::launder(reinterpret_cast<current_type*>(&tmp));
      }

      // If there are types left to try, recurse, otherwise this is unreachable.
      // Clearly tail recursion, the entire call stack should get inlined and be a series
      // of conditional integer comparisons
      if constexpr (sizeof...(Ts)) {
        return unpack_impl<Ts...>(type_idx, repr, std::index_sequence<Idxs...> {});
      } else {
        __builtin_unreachable();
      }
    }

    // Landing function used to start the recursive implementation
    static constexpr variant_type unpack(uint8_t const* data) {
      return unpack_impl<Types...>(*data, data + 1, std::index_sequence_for<Types...> {});
    }
  };

  template <class Container>
  class vararray_iterator {

    public:

      // Member types
      using iterator_category = std::random_access_iterator_tag;
      using value_type = typename Container::value_type;
      using difference_type = std::ptrdiff_t;
      using pointer = value_type*;
      using reference = value_type&;

      // Because default constructibility is useful.
      // Be careful!
      vararray_iterator() noexcept :
        idx(0),
        storage(nullptr)
      {}

      vararray_iterator(vararray_iterator const& other) noexcept :
        idx(other.idx),
        storage(other.storage)
      {}

      // Assignment
      vararray_iterator& operator =(vararray_iterator const& other) noexcept {
        if (&other == this) {
          return *this;
        }
        idx = other.idx;
        storage = other.storage;
        return *this;
      }

      // Dereference
      value_type operator *() const noexcept {
        assert(storage);
        return (*storage)[idx];
      }

      // Increment/decrement operators
      vararray_iterator& operator ++() noexcept {
        ++idx;
        return *this;
      }

      vararray_iterator& operator --() noexcept {
        --idx;
        return *this;
      }

      vararray_iterator operator ++(int) const noexcept {
        auto tmp {*this};
        ++tmp;
        return tmp;
      }

      vararray_iterator operator --(int) const noexcept {
        auto tmp {*this};
        --tmp;
        return tmp;
      }

    private:

      vararray_iterator(size_t idx, Container const* storage) noexcept :
        idx(idx),
        storage(storage)
      {}

      size_t idx;
      Container const* storage;

      // So we can access the private constructor
      friend class variant_array<
        typename Container::value_type,
                 Container::max_items,
                 Container::item_byte_size
      >;

      // Idiomatic implementation of operator == as a free function found by ADL
      friend bool operator ==(vararray_iterator const& lhs, vararray_iterator const& rhs) {
        return lhs.idx == rhs.idx && lhs.storage == rhs.storage;
      }
      friend bool operator !=(vararray_iterator const& lhs, vararray_iterator const& rhs) {
        return !(lhs == rhs);
      }

      // Pointer arithmetic to be a random access iterator.
      friend vararray_iterator operator -(vararray_iterator const& lhs, std::ptrdiff_t rhs) noexcept {
        auto tmp {lhs};
        auto tmpidx = lhs.idx - rhs;
        tmp.idx = tmpidx;
        return tmp;
      }
      friend vararray_iterator operator +(vararray_iterator const& lhs, std::ptrdiff_t rhs) noexcept {
        auto tmp {lhs};
        auto tmpidx = lhs.idx + rhs;
        tmp.idx = tmpidx;
        return tmp;
      }
      friend vararray_iterator operator +(std::ptrdiff_t lhs, vararray_iterator const& rhs) noexcept {
        auto tmp {rhs};
        auto tmpidx = rhs.idx + lhs;
        tmp.idx = tmpidx;
        return tmp;
      }
      DIRTY_MACRO_DECLARE_OPERATOR(<);
      DIRTY_MACRO_DECLARE_OPERATOR(<=);
      DIRTY_MACRO_DECLARE_OPERATOR(>);
      DIRTY_MACRO_DECLARE_OPERATOR(>=);

  };

#undef DIRTY_MACRO_DECLARE_OPERATOR

}

template <class Variant, size_t MaxItems, size_t ItemByteSize>
class variant_array {

  // Enforce static preconditions
  static_assert(detail::all_trivial_types(Variant {}),
      "variant_array uses low-level bitpacking techniques to compress its "
      "memory footprint and can only handle primitive (std::is_trivial) types at this time.");

  public:

    // Useful so our iterator can name us a friend type
    static constexpr size_t max_items = MaxItems;
    static constexpr size_t item_byte_size = ItemByteSize;

    // STL-like member types.
    using iterator_type = detail::vararray_iterator<variant_array>;
    using value_type = Variant;

    // No point in ref-overloads, types are trivial
    void push_back(value_type const& val) noexcept {
      // Copy the data in, packed.
      std::visit([&] (auto&& arg) noexcept {
        // Check invariants
        using stored_type = std::decay_t<decltype(arg)>;
        assert(offset + sizeof(arg) + sizeof(uint8_t) < sizeof(data));

        // Book keeping. Keep track of what type this is.
        offsets[count++] = offset;
        data[offset] = val.index();

        // Increment ongoing offset
        incr_offset(sizeof(uint8_t));

        // Copy
        auto* const data_ptr = &data[offset];
        memcpy(data_ptr, &arg, sizeof(stored_type));
        incr_offset(sizeof(stored_type));
      }, val);
    }

    void pop_back() noexcept {
      // Super cheap. Blink and it's gone!
      assert(!empty());
      if (--count) offset = offsets[count - 1];
    }

    // Throwing variant
    value_type at(size_t const index) const {
      if (index >= count) {
        throw std::out_of_range("Naughty naughty!");
      }
      return (*this)[index];
    }

    // Access
    value_type operator [](size_t const index) const noexcept {
      // Defer to our recursive unpacking.
      assert(index < size());
      return detail::variant_unpacker<value_type>::unpack(&data[offsets[index]]);
    }

    value_type back() const noexcept {
      assert(!empty());
      return (*this)[count - 1];
    }

    value_type front() const noexcept {
      assert(!empty());
      return (*this)[0];
    }

    size_t size() const noexcept { return count;  }

    bool empty() const noexcept { return size() == 0; }

    // Iteration
    iterator_type begin() const noexcept {
      return iterator_type(0, this);
    }

    iterator_type end() const noexcept {
      return iterator_type(count, this);
    }

  private:

    void incr_offset(uint8_t const bytes) noexcept {
      offset += bytes;
    }

    void decr_offset(uint8_t const bytes) noexcept {
      offset -= bytes;
    }

    uint16_t count = 0;
    uint16_t offset = 0;
    std::array<uint8_t, item_byte_size> data = { 0 };
    std::array<uint16_t, max_items> offsets = { 0 };

};


int main() {
  variant_array<myvar, 10, 50> thing;

  thing.push_back(1);
  thing.push_back((float)2.2);
  thing.push_back((double)3.3 );

  for (auto const value : thing) {
    std::visit([](auto const arg) { std::cout << arg << std::endl;  }, value);
  }

  assert(thing.front() == myvar {1});
  assert(thing.back() == myvar {3.3});

  assert(thing.begin() + 3 == thing.end());
  assert(3 + thing.begin() == thing.end());
  assert(thing.begin() == thing.end() - 3);
  assert(thing.begin() < thing.end());
  assert(thing.begin() <= thing.end());
  assert(thing.end() > thing.begin());
  assert(thing.end() >= thing.begin());

  thing.pop_back();
  thing.pop_back();
  thing.pop_back();

  for (auto const value : thing) {
    std::visit([](auto const arg) { assert(false); }, value);
  }
  assert(thing.empty());
}
