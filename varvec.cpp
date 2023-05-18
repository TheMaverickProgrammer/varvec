#include <iostream>
#include <variant>
#include <string>
#include <array>
#include <cassert>
#include <concepts>
#include <stdexcept>
#include <functional>
#include <type_traits>

#define DIRTY_MACRO_DECLARE_OPERATOR(op)                                                  \
  friend bool operator op (vararray_iterator const& lhs, vararray_iterator const& rhs) {  \
    return lhs.idx op rhs.idx;                                                            \
  }

using myvar = std::variant<double, int, float>;

namespace meta {

  template <class T>
  concept trivially_copyable = std::is_trivially_copyable<T>::value;

  template <class T>
  concept trivially_swappable = trivially_copyable<T> && std::default_initializable<T>;

  template <class T>
  struct identity {
    using type = T;
  };
  template <class T>
  using identity_t = identity<T>;

  template <template <class...> class Container, class... Ts>
  constexpr bool max_alignment_of(identity<Container<Ts...>>) {
    return std::max({alignof(Ts)...});
  }

}

template <meta::trivially_swappable, size_t, size_t>
class variant_array;

namespace detail {

  // Base case, unimplemented.
  template <class>
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
                 Container::storage_size
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

  template <class T>
  using aligned_storage_for_t = std::aligned_storage_t<sizeof(T), alignof(T)>;

  template <class T, class Func>
  constexpr auto with_aligned_stack_storage(Func&& callback)
    noexcept(noexcept(std::forward<Func>(callback)(std::declval<aligned_storage_for_t<T>&>())))
  {
    aligned_storage_for_t<T> tmp;
    return std::forward<Func>(callback)(tmp);
  }

  // FIXME: Doing the noexcept generically here sucks. Don't throw
  template <class T, class Func>
  constexpr auto unpack_misaligned_type(uint8_t const* data, Func&& callback)
    noexcept(noexcept(std::forward<Func>(callback)(std::declval<T&>())))
  {
    return with_aligned_stack_storage<T>([&] (auto& storage) {
      T* tmp = new(&storage) T();
      memcpy(tmp, data, sizeof(T));
      return std::forward<Func>(callback)(*tmp);
    });
  }

  template <class Variant, class T, class... Ts, class Func, size_t idx, size_t... idxs>
  constexpr Variant unpack_if_misaligned_impl(uint8_t type_index,
      uint8_t const* data, Func&& callback, std::index_sequence<idx, idxs...>)
    noexcept((noexcept(std::forward<Func>(callback)(std::declval<Ts&>())) && ...))
  {
    if (idx == type_index) {
      if (reinterpret_cast<std::uintptr_t>(data) & (alignof(T) - 1)) {
        // Pointer is misaligned, fix it up
        return unpack_misaligned_type<T>(data, std::forward<Func>(callback));
      } else {
        return std::forward<Func>(callback)(*std::launder(reinterpret_cast<T const*>(data)));
      }
    }

    if constexpr (sizeof...(Ts)) {
      return unpack_if_misaligned_impl<Variant, Ts...>(type_index,
          data, std::forward<Func>(callback), std::index_sequence<idxs...> {});
    } else {
      __builtin_unreachable();
    }
  }

  template <class Variant, class... Ts, class Func>
  constexpr Variant unpack_if_misaligned(uint8_t type_index, uint8_t const* data, Func&& callback)
    noexcept((noexcept(std::forward<Func>(callback)(std::declval<Ts&>())) && ...))
  {
    return unpack_if_misaligned_impl<Variant, Ts...>(type_index, data, std::forward<Func>(callback), std::index_sequence_for<Ts...> {});
  }

  template <template <class...> class Variant, class... Types, class Func>
  constexpr auto variant_unpack(uint8_t type_index, uint8_t const* data, meta::identity<Variant<Types...>>, Func&& callback)
    noexcept((noexcept(std::forward<Func>(callback)(std::declval<Types&>())) && ...))
  {
    return unpack_if_misaligned<Variant<Types...>, Types...>(type_index, data, std::forward<Func>(callback));
  }

  template <class Variant, size_t MaxItems, size_t StorageSize>
  struct trivial_variant_base {
    using offset_array = std::array<uint16_t, MaxItems>;
    using storage_type = std::aligned_storage_t<
      StorageSize,
      max_alignment_of(meta::identity<Variant> {})
    >;

    uint8_t operator [](size_t offset) const noexcept {
      return *(reinterpret_cast<uint8_t const*>(&data) + offset);
    }

    uint8_t* get_data() noexcept {
      return reinterpret_cast<uint8_t*>(&data);
    }

    uint8_t const* get_data() const noexcept {
      return reinterpret_cast<uint8_t const*>(&data);
    }

    void incr_offset(size_t bytes) noexcept {
      offset += bytes;
    }

    void decr_offset(size_t bytes) noexcept {
      offset -= bytes;
    }

    uint8_t type_index_for(size_t offset) const noexcept {
      return (*this)[offset];
    }

    uint16_t count = 0;
    uint16_t offset = 0;
    offset_array offsets {0};
    storage_type data {0};
  };

  template <class Variant, size_t MaxItems, size_t StorageSize>
  struct destructible_variant_base {
    using offset_array = std::array<uint16_t, MaxItems>;
    using storage_type = std::aligned_storage_t<
      StorageSize,
      max_alignment_of(meta::identity<Variant> {})
    >;

    ~destructible_variant_base() noexcept {
      while (count) {
        auto const curr_offset = offsets[--count];
        auto const type_index = static_cast<uint8_t>(data[curr_offset]);
        auto* const curr_data = &data[curr_offset + sizeof(type_index)];
        variant_unpack(type_index, curr_data, meta::identity<Variant> {}, [&] (auto& value) {
          using curr_type = std::decay_t<decltype(value)>;
          value.~curr_type();
        });
      }
    }

    uint8_t operator [](size_t offset) const noexcept {
      return *(reinterpret_cast<uint8_t const*>(&data) + offset);
    }

    uint8_t* get_data() noexcept {
      return reinterpret_cast<uint8_t*>(&data);
    }

    uint8_t const* get_data() const noexcept {
      return reinterpret_cast<uint8_t const*>(&data);
    }

    void incr_offset(size_t bytes) noexcept {
      offset += bytes;
    }

    void decr_offset(size_t bytes) noexcept {
      offset -= bytes;
    }

    uint8_t type_index_for(size_t offset) const {
      return static_cast<uint8_t>(data[offset]);
    }

    uint16_t count = 0;
    uint16_t offset = 0;
    offset_array offsets {0};
    storage_type data {0};
  };

  template <class Variant, size_t MaxItems, size_t StorageSize>
  struct autotrivial_variant_base : std::conditional_t<
    std::is_trivially_destructible_v<Variant>,
    trivial_variant_base<Variant, MaxItems, StorageSize>,
    destructible_variant_base<Variant, MaxItems, StorageSize>
  > {};

}

template <meta::trivially_swappable Variant, size_t MaxItems, size_t StorageSize>
class variant_array : private detail::autotrivial_variant_base<Variant, MaxItems, StorageSize> {

  public:

    // Useful so our iterator can name us a friend type
    static constexpr size_t max_items = MaxItems;
    static constexpr size_t storage_size = StorageSize;

    // STL-like member types.
    using iterator_type = detail::vararray_iterator<variant_array>;
    using value_type = Variant;

    // No point in ref-overloads, types are trivial
    void push_back(value_type const& val) noexcept {
      // Copy the data in, packed.
      std::visit([&] <class T>(T&& arg) noexcept {
        // Indirection here is necessary because we inherit from a template.
        // This makes all of our inherited properties dependendent names, and
        // so we have to disambiguate for the compiler.
        auto& count = this->count;
        auto& offsets = this->offsets;
        auto& offset = this->offset;
        using stored_type = std::decay_t<T>;

        // Check invariants
        assert(offset + sizeof(arg) + sizeof(uint8_t) < sizeof(this->data));

        // Book keeping. Keep track of the type.
        offsets[count++] = offset;
        this->get_data()[offset] = val.index();
        this->incr_offset(sizeof(uint8_t));

        // Copy
        auto* const data_ptr = this->get_data() + offset;
        if (reinterpret_cast<std::uintptr_t>(data_ptr) & (alignof(stored_type) - 1)) {
          memcpy(data_ptr, &arg, sizeof(stored_type));
        } else {
          new(data_ptr) stored_type(std::forward<T>(arg));
        }
        this->incr_offset(sizeof(stored_type));
      }, val);
    }

    void pop_back() noexcept {
      auto& count = this->count;
      auto& offset = this->offset;
      auto& offsets = this->offsets;

      // Super cheap. Blink and it's gone!
      assert(!empty());
      if (--count) offset = offsets[count - 1];
    }

    // Throwing variant
    value_type at(size_t const index) const {
      if (index >= size()) {
        throw std::out_of_range("Naughty naughty!");
      }
      return (*this)[index];
    }

    // Access
    value_type operator [](size_t const index) const noexcept {
      auto& offsets = this->offsets;

      // Defer to our recursive unpacking.
      assert(index < size());
      auto const curr_offset = offsets[index];
      auto* const curr_data = &this->get_data()[curr_offset + sizeof(uint8_t)];
      return detail::variant_unpack(this->type_index_for(curr_offset),
          curr_data, meta::identity<Variant> {}, [] (auto val) { return val; });
    }

    value_type back() const noexcept {
      assert(!empty());
      return (*this)[size() - 1];
    }

    value_type front() const noexcept {
      assert(!empty());
      return (*this)[0];
    }

    size_t size() const noexcept { return this->count; }

    bool empty() const noexcept { return size() == 0; }

    // Iteration
    iterator_type begin() const noexcept {
      return iterator_type(0, this);
    }

    iterator_type end() const noexcept {
      return iterator_type(size(), this);
    }

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
