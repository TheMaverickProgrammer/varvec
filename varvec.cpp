#include <bit>
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

using myvar = std::variant<double, int, float, std::string>;

namespace meta {

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

template <std::copyable, size_t, size_t>
class variant_array;

namespace detail {

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

  template <class T, class Func>
  constexpr auto unpack_misaligned_type(uint8_t const* data, Func&& callback)
    noexcept(noexcept(std::forward<Func>(callback)(std::declval<T&>())))
  {
    return with_aligned_stack_storage<T>([&] (auto& storage) {
      // This is now well defined behavior in C++20
      memcpy(&storage, data, sizeof(T));
      return std::forward<Func>(callback)(*std::launder(reinterpret_cast<T*>(&storage)));
    });
  }

  template <class Variant, class T, class... Ts, class Func, size_t idx, size_t... idxs>
  constexpr std::optional<Variant>
  unpack_if_misaligned_impl(uint8_t type_index,
      uint8_t const* data, Func&& callback, std::index_sequence<idx, idxs...>)
    noexcept((noexcept(std::forward<Func>(callback)(std::declval<Ts&>())) && ...))
  {
    if (idx == type_index) {
      if (std::bit_cast<std::uintptr_t>(data) & (alignof(T) - 1)) {
        // Pointer is misaligned, fix it up
        // This branch technically instantiates for non trivially copyable types,
        // but the alignment logic will guarantee it never gets called.
        assert(std::is_trivially_copyable_v<T>);
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
  constexpr std::optional<Variant>
  unpack_if_misaligned(uint8_t type_index, uint8_t const* data, Func&& callback)
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
    using type_array = std::array<uint8_t, MaxItems>;
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

    uint16_t count = 0;
    uint16_t offset = 0;
    type_array types {0};
    offset_array offsets {0};
    storage_type data {0};
  };

  template <class Variant, size_t MaxItems, size_t StorageSize>
  struct destructible_variant_base {
    using type_array = std::array<uint8_t, MaxItems>;
    using offset_array = std::array<uint16_t, MaxItems>;
    using storage_type = std::aligned_storage_t<
      StorageSize,
      max_alignment_of(meta::identity<Variant> {})
    >;

    ~destructible_variant_base() noexcept {
      while (count) {
        auto const curr_count = --count;
        auto const type_index = types[curr_count];
        auto const curr_offset = offsets[curr_count];
        auto* const curr_data = get_data() + curr_offset + sizeof(type_index);
        variant_unpack(type_index, curr_data, meta::identity<Variant> {}, [&] (auto& value) {
          using curr_type = std::decay_t<decltype(value)>;
          value.~curr_type();
          return std::nullopt;
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

    uint16_t count = 0;
    uint16_t offset = 0;
    type_array types {0};
    offset_array offsets {0};
    storage_type data {0};
  };

  template <class T>
  constexpr bool aligned_for_type(void const* ptr) {
    return !(std::bit_cast<std::uintptr_t>(ptr) & (alignof(T) - 1));
  }

  template <class T, class P>
  constexpr P* realign_for_type(P* ptr) {
    auto const alignment = alignof(T);
    uintptr_t offset = std::bit_cast<std::uintptr_t>(ptr);
    return std::bit_cast<P*>(((offset + (alignment - 1)) & ~(alignment - 1)));
  }

  template <class Variant, size_t MaxItems, size_t StorageSize>
  struct autotrivial_variant_base : std::conditional_t<
    std::is_trivially_destructible_v<Variant>,
    trivial_variant_base<Variant, MaxItems, StorageSize>,
    destructible_variant_base<Variant, MaxItems, StorageSize>
  > {};

}

template <std::copyable Variant, size_t MaxItems, size_t StorageSize>
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
      // Copy the data in, packed if we can.
      std::visit([&] <class T>(T&& arg) noexcept {
        // Indirection here is necessary because we inherit from a template.
        // This makes all of our inherited properties dependendent names, and
        // so we have to disambiguate for the compiler.
        auto& count = this->count;
        auto& types = this->types;
        auto& offsets = this->offsets;
        auto& offset = this->offset;
        using stored_type = std::decay_t<T>;

        // Check invariants
        assert(offset + sizeof(arg) + sizeof(uint8_t) < sizeof(this->data));

        // Copy in.
        auto* base_ptr = this->get_data() + offset;
        auto* data_ptr = base_ptr;
        auto curr_count = count++;
        if constexpr (std::is_trivially_copyable_v<stored_type>) {
          memcpy(data_ptr, &arg, sizeof(stored_type));
        } else {
          data_ptr = detail::realign_for_type<stored_type>(data_ptr);
          new(data_ptr) stored_type(std::forward<T>(arg));
          this->incr_offset(data_ptr - base_ptr);
        }

        offsets[curr_count] = offset;
        types[curr_count] = val.index();
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
      auto& types = this->types;
      auto& offsets = this->offsets;

      // Defer to our recursive unpacking.
      assert(index < size());
      auto const curr_offset = offsets[index];
      auto* const curr_data = this->get_data() + curr_offset;
      return *detail::variant_unpack(types[index],
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
  thing.push_back((float) 2.2);
  thing.push_back((double) 3.3);
  thing.push_back("hello world");

  for (auto const value : thing) {
    std::visit([](auto const arg) { std::cout << arg << std::endl;  }, value);
  }

  assert(thing.front() == myvar {1});
  assert(thing.back() == myvar {"hello world"});

  assert(thing.begin() + 4 == thing.end());
  assert(4 + thing.begin() == thing.end());
  assert(thing.begin() == thing.end() - 4);
  assert(thing.begin() < thing.end());
  assert(thing.begin() <= thing.end());
  assert(thing.end() > thing.begin());
  assert(thing.end() >= thing.begin());

  thing.pop_back();
  thing.pop_back();
  thing.pop_back();
  thing.pop_back();

  for (auto const value : thing) {
    std::visit([](auto const arg) { assert(false); }, value);
  }
  assert(thing.empty());
}
