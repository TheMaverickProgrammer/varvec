#include <bit>
#include <new>
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
  friend bool operator op (variable_iterator const& lhs, variable_iterator const& rhs) {  \
    return lhs.idx op rhs.idx;                                                            \
  }

using myvar = std::variant<bool, int, double, std::string, std::unique_ptr<std::string>>;

namespace varvec::meta {

  template <class T>
  struct identity {
    using type = T;
  };
  template <class T>
  using identity_t = identity<T>;

  template <class... Funcs>
  struct overload : Funcs... {
    using Funcs::operator ()...;
  };
  template <class... Funcs>
  overload(Funcs...) -> overload<Funcs...>;

  template <template <class...> class Container, class... Ts>
  constexpr auto max_alignment_of(identity<Container<Ts...>>) {
    return std::max({alignof(Ts)...});
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto max_size_of(identity<Container<Ts...>>) {
    return std::max({sizeof(Ts)...});
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto min_size_of(identity<Container<Ts...>>) {
    return std::min({sizeof(Ts)...});
  }

  // Base failure case, intentionally unimplemented. The count is the current iteration
  // number, the needle is what we're looking for, and the haystack is the
  // list of types we're searching through.
  template <size_t count, class Needle, class... Haystack>
  struct index_of_impl;

  // Success case! Needle appears next to itself, and we've found it.
  template <size_t match, class Needle, class... Haystack>
  struct index_of_impl<match, Needle, Needle, Haystack...> : std::integral_constant<size_t, match> {};

  // Recursive case. Two unmatched types. Discard the miss, increment the index, and continue.
  template <size_t idx, class Needle, class Other, class... Haystack>
  struct index_of_impl<idx, Needle, Other, Haystack...> : index_of_impl<idx + 1, Needle, Haystack...> {};

  // Meta-function computes the list index of a given type in a list.
  // Precondition: Type must be known to be present in the list
  template <class T, class... Ts>
  struct index_of : index_of_impl<0, T, Ts...> {};

  template <class T, class... Ts>
  constexpr size_t index_of_v = index_of<T, Ts...>::value;

  template <class S, template <class...> class T>
  struct is_specialization_of : std::false_type {};

  template <class... Args, template <class...> class T>
  struct is_specialization_of<T<Args...>, T> : std::true_type {};

  template <class S, template <class...> class T>
  constexpr bool is_specialization_of_v = is_specialization_of<S, T>::value;

}

namespace varvec::storage {

  template <class Variant, size_t bytes>
  using storage_type = std::aligned_storage_t<
    bytes,
    meta::max_alignment_of(meta::identity<Variant> {})
  >;

  template <class T>
  constexpr bool aligned_for_type(void const* ptr) {
    return !(std::bit_cast<std::uintptr_t>(ptr) & (alignof(T) - 1));
  }

  template <class T, class P>
  constexpr P* realign_for_type(P* ptr) {
    auto const alignment = alignof(T);
    auto const offset = std::bit_cast<std::uintptr_t>(ptr);
    return std::bit_cast<P*>(((offset + (alignment - 1)) & ~(alignment - 1)));
  }

  template <class Storage,
           template <std::movable...> class Variant, std::movable... Types, class Func>
  constexpr auto get_typed_ptr_for(uint8_t curr_type,
      Storage* curr_data, size_t curr_idx, meta::identity<Variant<Types...>>, Func&& callback) {
    // Lol. Not sure this is better than the old way
    auto recurse =
      [&] <class T, class... Ts, class Cont, size_t idx, size_t... idxs> (Cont&& cont, std::index_sequence<idx, idxs...>) {
      // If this is the index for our type, cast the pointer into the proper type and call the callback.
      if (idx == curr_type) return std::forward<Func>(callback)(std::bit_cast<T*>(curr_data));

      // Otherwise recurse.
      // Since we're using an index sequence generated off our type list,
      // we're guaranteed to eventually find a match.
      if constexpr (sizeof...(Ts)) {
        // Recursive, generic, explicitly parameterized lambdas are rough to work with.
        return cont.template operator ()<Ts...>(cont, std::index_sequence<idxs...> {});
      } else {
        __builtin_unreachable();
      }
    };
    return recurse.template operator ()<Types...>(recurse, std::index_sequence_for<Types...> {});
  }

  template <class Storage,
           template <std::movable...> class Variant, std::movable... Types, class Func>
  constexpr auto get_aligned_ptr_for(uint8_t curr_type,
      Storage* curr_data, size_t curr_idx, meta::identity<Variant<Types...>> variant, Func&& callback) {
    return get_typed_ptr_for(curr_type,
        curr_data, curr_idx, variant, [&] <class T> (T* ptr) {
      if constexpr (std::copyable<T>) {
        if (!storage::aligned_for_type<T>(ptr)) {
          // Propagates changes back if the user changes anything.
          struct change_forwarder {
            change_forwarder(void* orig, void* tmp) : orig(orig), tmp(tmp) {}
            ~change_forwarder() noexcept {
              if (memcmp(orig, tmp, sizeof(T))) {
                memcpy(orig, tmp, sizeof(T));
              }
            }
            void* orig;
            void* tmp;
          };

          // Only trivially copyable types should ever be misaligned.
          assert(std::is_trivially_copyable_v<T>);

          // Realign and return.
          std::aligned_storage_t<sizeof(T), alignof(T)> tmp;
          change_forwarder forwarder {ptr, &tmp};
          memcpy(&tmp, ptr, sizeof(T));
          (void) forwarder;
          return std::forward<Func>(callback)(std::launder(reinterpret_cast<T*>(&tmp)));
        }
      } else {
        assert(storage::aligned_for_type<T>(ptr));
      }
      return std::forward<Func>(callback)(ptr);
    });
  }

  // FIXME: Make noexcept conditional
  template <class Variant, class Storage, class Metadata>
  constexpr auto move_storage(size_t count, Metadata const& meta, Storage* dest, Storage* src) noexcept {
    for (size_t i = 0; i < count; ++i) {
      auto const type = meta[i].type;
      auto const offset = meta[i].offset;
      get_typed_ptr_for(type, src + offset, i, meta::identity<Variant> {}, [&] <class S> (S* srcptr) {
        get_typed_ptr_for(type, dest + offset, i, meta::identity<Variant> {}, [&] <class D> (D* destptr) {
          if constexpr (std::is_same_v<S, D>) {
            new(destptr) D(std::move(*srcptr));
          } else {
            __builtin_unreachable();
          }
        });
      });
    }
  }

  template <class Variant, class Storage, class Metadata>
  constexpr auto copy_storage(size_t count, Metadata const& meta, Storage* dest, Storage* src) noexcept {
    for (size_t i = 0; i < count; ++i) {
      auto const type = meta[i].type;
      auto const offset = meta[i].offset;
      get_typed_ptr_for(type, src + offset, i, meta::identity<Variant> {}, [&] <class S> (S* srcptr) {
        get_typed_ptr_for(type, dest + offset, i, meta::identity<Variant> {}, [&] <class D> (D* destptr) {
          if constexpr (std::is_same_v<S, D>) {
            new(destptr) D(*srcptr);
          } else {
            __builtin_unreachable();
          }
        });
      });
    }
  }

  template <class OffsetType>
  struct storage_metadata {
    uint8_t type;
    OffsetType offset;
  };

  template <class Variant, size_t bytes, size_t memcount>
  struct static_storage_base {

    using variant_type = Variant;

    static constexpr auto start_size = memcount;
    static constexpr auto max_alignment = meta::max_alignment_of(meta::identity<variant_type> {});

    static_storage_base() noexcept {}

    explicit static_storage_base(size_t start_bytes) {
      if (start_bytes > bytes) {
        throw std::bad_alloc();
      }
    }

    static_storage_base(static_storage_base const&) = delete;
    static_storage_base(static_storage_base&&) = delete;
    ~static_storage_base() = default;

    uint8_t operator [](size_t offset) const noexcept {
      return *(reinterpret_cast<uint8_t const*>(&data) + offset);
    }

    uint8_t* get_data() noexcept {
      return reinterpret_cast<uint8_t*>(&data);
    }

    uint8_t const* get_data() const noexcept {
      return reinterpret_cast<uint8_t const*>(&data);
    }

    void incr_offset(size_t count) noexcept {
      offset += count;
    }

    uint8_t* resize(size_t) {
      throw std::bad_alloc();
    }

    size_t size() const noexcept {
      return bytes;
    }

    bool has_space(size_t more) const noexcept {
      if (count < memcount) return offset + more < bytes;
      else return false;
    }

    // FIXME: Make these sizes configurable
    uint16_t count {0};
    uint16_t offset {0};
    std::array<storage_metadata<uint16_t>, memcount> meta {0};
    storage_type<Variant, bytes> data {0};

  };

  template <class Variant>
  struct dynamic_storage_base {

    using variant_type = Variant;

    static constexpr auto max_alignment = meta::max_alignment_of(meta::identity<variant_type> {});
    static constexpr auto start_size = 8 * meta::max_size_of(meta::identity<variant_type> {});

    dynamic_storage_base() :
      meta(std::ceil(start_size / (double) meta::min_size_of(meta::identity<Variant> {}))),
      data(new (std::align_val_t(max_alignment)) uint8_t[start_size])
    {}

    dynamic_storage_base(dynamic_storage_base const&) = delete;
    dynamic_storage_base(dynamic_storage_base&&) = delete;
    ~dynamic_storage_base() = default;

    uint8_t operator [](size_t offset) const noexcept {
      return data[offset];
    }

    uint8_t* get_data() noexcept {
      return data.get();
    }

    uint8_t const* get_data() const noexcept {
      return data.get();
    }

    void incr_offset(size_t count) noexcept {
      offset += count;
    }

    // FIXME: Propgate noexcept
    uint8_t* resize(size_t newsize) {
      // FIXME: Add logic to fall back on copy constructor if move constructor is throwing
      std::unique_ptr<uint8_t[]> newdata(new (std::align_val_t(max_alignment)) uint8_t[newsize]);
      move_storage<Variant>(count, meta, newdata.get(), data.get());
      data = std::move(newdata);
      bytes = newsize;
      meta.resize(std::ceil(bytes / (double) meta::min_size_of(meta::identity<Variant> {})));
      return get_data() + offset;
    }

    size_t size() const noexcept {
      return bytes;
    }

    bool has_space(size_t more) const noexcept {
      return offset + more < bytes;
    }

    size_t bytes {start_size};
    size_t count {0};
    size_t offset {0};
    std::vector<storage_metadata<size_t>> meta;
    std::unique_ptr<uint8_t[]> data;

  };

  template <class Variant, size_t bytes, size_t memcount>
  struct movable_static_storage_base : static_storage_base<Variant, bytes, memcount> {
    movable_static_storage_base() noexcept {}

    movable_static_storage_base(movable_static_storage_base const&) = delete;

    // FIXME: Make noexcept conditional
    movable_static_storage_base(movable_static_storage_base&& other) noexcept :
      static_storage_base<Variant, bytes, memcount>()
    {
      // Copy state
      this->count = other.count;
      this->offset = other.offset;
      this->meta = other.meta;

      // Move data
      move_storage(this->count, this->meta, this->get_data(), other.get_data());
    }

    ~movable_static_storage_base() noexcept {
      while (this->count) {
        auto const curr_count = --this->count;
        auto const curr_type = this->meta[curr_count].type;
        auto const curr_offset = this->meta[curr_count].offset;
        auto* const curr_ptr = this->get_data() + curr_offset;
        get_typed_ptr_for(curr_type, curr_ptr,
            curr_count, meta::identity<Variant> {}, [&] <class T> (T* value) {
          value->~T();
        });
      }
    }

    using static_storage_base<Variant, bytes, memcount>::operator [];
  };

  template <class Variant, size_t bytes, size_t memcount>
  struct copyable_static_storage_base : movable_static_storage_base<Variant, bytes, memcount> {
    using movable_static_storage_base<Variant, bytes, memcount>::movable_static_storage_base;

    // FIXME: Add conditional noexcept
    copyable_static_storage_base(copyable_static_storage_base const& other) :
      movable_static_storage_base<Variant, bytes, memcount>()
    {
      // Copy state
      this->count = other.count;
      this->offset = other.offset;
      this->meta = other.meta;

      // Copy data
      copy_storage<Variant>(this->count, this->meta, this->get_data(), other.get_data());
    }

    using movable_static_storage_base<Variant, bytes, memcount>::operator [];
  };

  template <class Variant, size_t bytes, size_t memcount>
  using autocopyable_static_storage_base_t = std::conditional_t<
    std::is_copy_constructible_v<Variant>,
    copyable_static_storage_base<Variant, bytes, memcount>,
    movable_static_storage_base<Variant, bytes, memcount>
  >;

  template <class Variant, size_t bytes, size_t memcount>
  using autotrivial_static_storage_base_t = std::conditional_t<
    std::is_trivially_destructible_v<Variant>,
    static_storage_base<Variant, bytes, memcount>,
    autocopyable_static_storage_base_t<Variant, bytes, memcount>
  >;

  // Make sure our trivial destructibility is going to work.
  static_assert(std::is_trivially_destructible_v<autotrivial_static_storage_base_t<std::variant<int>, 8, 2>>);

  template <size_t max_bytes, size_t memcount>
  struct static_storage_context {
    template <class Variant>
    struct static_storage : public autotrivial_static_storage_base_t<Variant, max_bytes, memcount> {
        using autotrivial_static_storage_base_t<Variant, max_bytes, memcount>::autotrivial_static_storage_base_t;
        using autotrivial_static_storage_base_t<Variant, max_bytes, memcount>::operator [];
    };
  };

  template <class Variant>
  struct movable_dynamic_storage_base : dynamic_storage_base<Variant> {
    movable_dynamic_storage_base() = default;
    movable_dynamic_storage_base(movable_dynamic_storage_base const&) = delete;

    // FIXME: Make noexcept conditional
    movable_dynamic_storage_base(movable_dynamic_storage_base&& other) noexcept :
      dynamic_storage_base<Variant>()
    {
      // Copy state
      this->count = other.count;
      this->offset = other.offset;

      // Move data
      this->meta = std::move(other.meta);
      this->data = std::move(other.data);
    }

    ~movable_dynamic_storage_base() noexcept {
      while (this->count) {
        auto const curr_count = --this->count;
        auto const curr_type = this->meta[curr_count].type;
        auto const curr_offset = this->meta[curr_count].offset;
        auto* const curr_ptr = this->get_data() + curr_offset;
        get_typed_ptr_for(curr_type, curr_ptr,
            curr_count, meta::identity<Variant> {}, [&] <class T> (T* value) {
          value->~T();
        });
      }

    }

    using dynamic_storage_base<Variant>::operator [];
  };

  template <class Variant>
  struct copyable_dynamic_storage_base : movable_dynamic_storage_base<Variant> {
    using movable_dynamic_storage_base<Variant>::movable_dynamic_storage_base;

    copyable_dynamic_storage_base(copyable_dynamic_storage_base const& other) :
      movable_dynamic_storage_base<Variant>()
    {
      // Copy state
      this->count = other.count;
      this->offset = other.offset;
      this->meta = other.meta;

      // Copy data
      copy_storage<Variant>(this->count, this->meta, this->get_data(), other.get_data());
    }

    using movable_dynamic_storage_base<Variant>::operator [];
  };

  template <class Variant>
  using autocopyable_dynamic_storage_base_t = std::conditional_t<
    std::is_copy_constructible_v<Variant>,
    copyable_dynamic_storage_base<Variant>,
    movable_dynamic_storage_base<Variant>
  >;

  template <class Variant>
  struct dynamic_storage : public autocopyable_dynamic_storage_base_t<Variant> {
    using autocopyable_dynamic_storage_base_t<Variant>::autocopyable_dynamic_storage_base_t;
    using autocopyable_dynamic_storage_base_t<Variant>::operator [];
  };

  template <class T>
  constexpr auto copyable_type_for() {
    if constexpr (std::copyable<T>) {
      return meta::identity<T> {};
    } else {
      static_assert(std::movable<T>);
      return meta::identity<T*> {};
    }
  }

}

namespace varvec {

  template <template <class> class Storage, template <std::movable...> class Variant, std::movable... Types>
  class basic_variable_vector {

    public:

      using logical_type = Variant<Types...>;
      using value_type = Variant<
        typename decltype(storage::copyable_type_for<Types>())::type...
      >;
      using storage_type = Storage<logical_type>;

      // FIXME: Handle noexcept
      template <class ValueType>
      requires std::is_same_v<std::decay_t<ValueType>, logical_type>
      void push_back(ValueType&& val) {
        std::visit([&] <class T> (T&& arg) { push_back(std::forward<T>(arg)); }, std::forward<ValueType>(val));
      }

      // FIXME: Handle noexcept
      template <class ValueType>
      requires (
          std::is_constructible_v<logical_type, ValueType>
          &&
          !std::is_same_v<std::decay_t<ValueType>, logical_type>
      )
      void push_back(ValueType&& val) {
        using stored_type = std::decay_t<ValueType>;
        auto& offset = impl.offset;
        auto* const base_ptr = impl.get_data() + offset;
        auto* data_ptr = base_ptr;

        // Figure out how much space we'll need.
        auto const required_bytes = sizeof(val);
        if constexpr (!std::is_trivially_copyable_v<stored_type>) {
          data_ptr = storage::realign_for_type<stored_type>(data_ptr);
        }
        auto const alignment_bytes = data_ptr - base_ptr;

        // Check if we have it.
        while (!impl.has_space(required_bytes + alignment_bytes)) {
          // Rethink this
          // Will throw for static vector
          data_ptr = impl.resize(impl.size() * 2);
        }

        impl.incr_offset(alignment_bytes);
        auto const curr_count = impl.count++;
        if constexpr (std::is_trivially_copyable_v<stored_type>) {
          // May copy to a misaligned address
          memcpy(data_ptr, &val, sizeof(stored_type));
        } else {
          new(data_ptr) stored_type(std::forward<ValueType>(val));
        }
        impl.meta[curr_count].type = meta::index_of_v<stored_type, Types...>;
        impl.meta[curr_count].offset = offset;
        impl.incr_offset(required_bytes);
      }

      // FIXME: Handle noexcept
      value_type operator [](size_t index) const {
        assert(index < size());
        auto const& meta = impl.meta[index];
        auto* const curr_ptr = impl.get_data() + meta.offset;
        return storage::get_aligned_ptr_for(meta.type, curr_ptr,
            index, meta::identity<logical_type> {}, [&] <class T> (T* ptr) -> value_type {
          if constexpr (std::copyable<T>) return *ptr;
          else return ptr;
        });
      }

      // FIXME: Handle noexcept
      value_type top() const {
        assert(impl.count);
        return (*this)[impl.count - 1];
      }

      size_t size() const noexcept {
        return impl.count;
      }

    private:

      storage_type impl;

  };

  template <size_t max_bytes, size_t memcount, std::movable... Types>
  using static_variable_vector = basic_variable_vector<
    storage::static_storage_context<max_bytes, memcount>::template static_storage,
    std::variant,
    Types...
  >;

  template <std::movable... Types>
  using dynamic_variable_vector = basic_variable_vector<
    storage::dynamic_storage,
    std::variant,
    Types...
  >;

}

int main() {
  varvec::static_variable_vector<256, 16, bool, int, double, std::string, std::unique_ptr<std::string>> vec;
  //static_assert(std::is_trivially_destructible_v<decltype(vec)>);
  
  vec.push_back(myvar {1}); // 0
  vec.push_back(myvar {std::make_unique<std::string>("hello world")}); // 1

  auto val = vec[1];
  std::visit(varvec::meta::overload {
    [] <class T> (T* ptr) { std::cout << **ptr << std::endl; },
    [] (auto& v) { std::cout << v << std::endl; }
  }, val);
  /*
  vec.push_back(myvar {"hello world"}); // 5
  vec.push_back(myvar {"hello world"}); // 6
  vec.push_back(myvar {"hello world"}); // 7
  vec.push_back(myvar {"hello world"}); // 8
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  vec.push_back(myvar {"hello world"});
  */
  /*
  variable_vector<10, 50, double, int, float, std::string> thing;

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
  */
}
