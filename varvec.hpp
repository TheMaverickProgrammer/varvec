#include <bit>
#include <new>
#include <cmath>
#include <array>
#include <memory>
#include <string>
#include <climits>
#include <cstring>
#include <cassert>
#include <variant>
#include <iostream>
#include <concepts>
#include <stdexcept>
#include <functional>
#include <type_traits>

namespace varvec::meta {

  template <class T>
  struct identity {
    using type = T;
  };
  template <class T>
  using identity_t = typename identity<T>::type;

  // A storable type must be movable, and if it is not nothrow movable, it must also be copyable.
  template <class T>
  concept storable = std::movable<T> && (std::is_nothrow_move_constructible_v<T> || std::copyable<T>);

  template <class Func, storable... Types>
  constexpr bool nothrow_visitor_v = (std::is_nothrow_invocable_v<Func, Types> && ...);

  template <template <class...> class Container, class... Ts>
  constexpr auto max_alignment_of(identity<Container<Ts...>>) noexcept {
    return std::max({alignof(Ts)...});
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto max_size_of(identity<Container<Ts...>>) noexcept {
    return std::max({sizeof(Ts)...});
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto min_size_of(identity<Container<Ts...>>) noexcept {
    return std::min({sizeof(Ts)...});
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto mean_size_of(identity<Container<Ts...>>) noexcept {
    size_t total = 0;
    std::array<size_t, sizeof...(Ts)> sizes {sizeof(Ts)...};
    for (auto size : sizes) total += size;
    return total / sizes.size();
  }

  template <template <class...> class Container, class... Ts>
  constexpr auto num_types_in(identity<Container<Ts...>>) noexcept {
    return sizeof...(Ts);
  }

  template <size_t num>
  constexpr auto smallest_type_for() noexcept {
    if constexpr (num <= std::numeric_limits<uint8_t>::max()) {
      return meta::identity<uint8_t> {};
    } else if constexpr (num <= std::numeric_limits<uint16_t>::max()) {
      return meta::identity<uint16_t> {};
    } else if constexpr (num <= std::numeric_limits<uint32_t>::max()) {
      return meta::identity<uint32_t> {};
    } else {
      static_assert(num <= std::numeric_limits<uint64_t>::max());
      return meta::identity<uint64_t> {};
    }
  }

  template <size_t num>
  using smallest_type_for_t = typename decltype(smallest_type_for<num>())::type;

  template <auto num>
  constexpr auto necessary_bits_for() noexcept {
    if (num == 0) return decltype(num) {1U};
    auto curr = num;
    decltype(num) bits = 0;
    while (curr > 0) {
      ++bits;
      curr >>= 1;
    }
    return bits;
  }

  template <auto num>
  constexpr size_t rounded_bits_for() noexcept {
    auto necessary = necessary_bits_for<num>();
    --necessary;
    necessary |= necessary >> 1;
    necessary |= necessary >> 2;
    necessary |= necessary >> 4;
    if constexpr (sizeof(necessary) >= 2) {
      necessary |= necessary >> 8;
    }
    if constexpr (sizeof(necessary) >= 4) {
      necessary |= necessary >> 16;
    }
    if constexpr (sizeof(necessary) >= 8) {
      necessary |= necessary >> 32;
    }
    return ++necessary;
  }

  constexpr int64_t int_ceil(double val) {
    int64_t casted = static_cast<int64_t>(val);
    return val > casted ? casted + 1 : val;
  }

  template <class... Ts>
  struct simulated_overload_resolution_impl {
    identity<void> operator ()(...) const;
  };

  template <class T, class... Ts>
  struct simulated_overload_resolution_impl<T, Ts...> : simulated_overload_resolution_impl<Ts...> {
    // XXX: I don't really understand why this needs to be here,
    // but clang won't eat it otherwise.
    template <class U>
    using array_type = U[1];

    // XXX: The requires clause here is stupidly non-obvious.
    // Thankfully we don't have to do this as an enable_if SFINAE in C++20
    //
    // We're trying to solve the problem of std::variant<bool, std::string> {"hello"}
    // selecting its type as "bool". This is extremely obnoxious (string converted to 1),
    // and is the behavior in C++17, but in C++20 the wording around the variant converting
    // constructor changed.
    //
    // In C++17 it's supposed to select types as-if performing overload resolution for
    // the same, but this prefers bool over std::string in the above example, which sucks.
    //
    // In C++20 this was changed so that it still runs overload resolution, but first
    // filters out those types for which the expression "U u[] = {std::forward<T>(t)};"
    // isn't valid (assuming T is the incoming type and U is the potential conversion.
    // 
    // Somehow this manages to fix the issue in most cases, and gets std::string chosen.
    template <class U>
    static constexpr bool precisely_convertible_v = requires {
      array_type<T>{std::declval<U>()};
    };

    // Constrained by our precise check above, we declare an overload
    template <class U>
    requires precisely_convertible_v<U>
    identity<T> operator ()(T const&, U const&) const;

    // And inherit all our parent's call operators
    using simulated_overload_resolution_impl<Ts...>::operator ();
  };

  // This type alias, and the struct above, implement the type coversion logic for
  // basic_variable_vector roughly according to the specification for std::variant's
  // converting constructor.
  template <class T, class... Ts>
  using fuzzy_type_match_t =
      typename decltype(simulated_overload_resolution_impl<Ts...> {}(std::declval<T>(), std::declval<T>()))::type;

  // Redirect move-only types to pointers to const
  template <class T>
  constexpr auto copyable_type_for() {
    if constexpr (std::copyable<T>) {
      return meta::identity<T> {};
    } else {
      static_assert(std::movable<T>);
      // XXX: This SUCKS.
      //
      // So here's the problem. The whole point of this library is that the types are stored
      // in a packed format, and so I can't store them inside of variants. However, operator []
      // needs a single consistent return type, and so it works with variants.
      //
      // Since I can't store the types as variants, I have to construct temporary variants as the
      // return of operator []. However, this causes problems for move-only types, since the temporary
      // variant would store it by value and would need a copy.
      //
      // I planned to solve this problem by rewriting movable types into a pointer to the type,
      // and then just return a variant containing a pointer, however, this runs into const-correctness
      // issues. operator [] needs a const overload, as otherwise a const vector is rather worthless,
      // and the const version of the operator is forced to return a const pointer since the moveable
      // type is stored inside of the vector.
      //
      // This puts me in the position of needing to either have the const-qualified operator [] return
      // a different variant type than its mutable counterpart, which seems awful, or always force the
      // pointer to be const, which seems like a usability headache. The only other option is to
      // explicitly discard const for the const overload, which seems like a sin.
      return meta::identity<T const*> {};
    }
  }

  template <class T>
  using copyable_type_for_t = typename decltype(copyable_type_for<T>())::type;

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

}

namespace varvec::storage::offsets {

  // Virtual interface type for offset storage.
  struct virtual_offset_storage {

    using size_type = size_t;

    virtual ~virtual_offset_storage() {}

    virtual size_type operator [](size_type index) const noexcept = 0;

    virtual size_type get(size_type index) const noexcept = 0;
    virtual void set(size_type index, size_type offset) noexcept = 0;

    virtual bool can_handle(size_type offset) const noexcept = 0;
    virtual std::unique_ptr<virtual_offset_storage> clone() const = 0;
    virtual std::unique_ptr<virtual_offset_storage> realloc_for(size_type offset) const = 0;
    virtual void resize(size_type members) = 0;

    virtual size_type size() const noexcept = 0;
    virtual size_type capacity() const noexcept = 0;
    virtual size_type used_bytes() const noexcept = 0;

  };

  // Class implements packed offset storage in the dynamic case.
  //
  // For static vectors, we can pre-compute the minimum integer size that can represent
  // any possible offset we might be asked to store, but for a dynamic vector this is
  // not possible as maximum offset is a runtime property.
  //
  // The offset store is the single-largest data storage requirement we have, other than
  // the data array itself, and so optimizing it to use the minimum integer representation
  // possible is a _significant_ storage win.
  //
  // This class, and the interface above, allows the dynamic vector storage implementation
  // to "hot swap" its offset storage format at runtime, allowing us to use the minimum
  // space necessary based on the runtime conditions of the vector, growing and
  // reforming offsets as the storage offsets grow.
  template <class OffsetType>
  struct concrete_offset_storage final : virtual_offset_storage {

    using size_type = virtual_offset_storage::size_type;

    explicit concrete_offset_storage(size_type members) : storage(members) {}
    concrete_offset_storage(concrete_offset_storage const&) = default;
    concrete_offset_storage(concrete_offset_storage&&) = default;
    ~concrete_offset_storage() = default;

    size_type operator [](size_type index) const noexcept final {
      assert(index < size());
      return storage[index];
    }

    size_type get(size_type index) const noexcept final {
      return (*this)[index];
    }

    void set(size_type index, size_type offset) noexcept final {
      assert(index < capacity());
      storage[index] = offset;
    }

    // Function computes whether the OffsetType of this concrete offset storage
    // can represent the given offset that's about to be stored, or if the offset
    // storage will have to be rebuilt to do so.
    bool can_handle(size_type offset) const noexcept final {
      return offset <= std::numeric_limits<OffsetType>::max();
    }

    std::unique_ptr<virtual_offset_storage> clone() const final {
      return std::make_unique<concrete_offset_storage>(*this);
    }

    // Function handles rebuilding the offset storage in the case that the caller
    // is trying to store an offset that's larger than our current representation type.
    std::unique_ptr<virtual_offset_storage> realloc_for(size_type offset) const final {
      auto realloc_offsets = [this] <class T> (meta::identity<T>) {
        // Copy has to be done while we have full type information
        // so the promotions are handled properly.
        auto ptr = std::make_unique<concrete_offset_storage<T>>(size());
        std::copy(storage.begin(), storage.end(), ptr->storage.begin());
        return ptr;
      };

      if (offset <= std::numeric_limits<uint8_t>::max()) {
        return realloc_offsets(meta::identity<uint8_t> {});
      } else if (offset <= std::numeric_limits<uint16_t>::max()) {
        return realloc_offsets(meta::identity<uint16_t> {});
      } else if (offset <= std::numeric_limits<uint32_t>::max()) {
        return realloc_offsets(meta::identity<uint32_t> {});
      } else {
        assert(offset <= std::numeric_limits<uint64_t>::max());
        return realloc_offsets(meta::identity<uint64_t> {});
      }
    }

    void resize(size_type members) final {
      storage.resize(members);
    }

    size_type size() const noexcept final {
      return storage.size();
    }

    size_type capacity() const noexcept final {
      return storage.capacity();
    }

    size_type used_bytes() const noexcept final {
      return storage.capacity() * sizeof(OffsetType);
    }

    std::vector<OffsetType> storage;

  };

}

namespace varvec::storage {

  // The dynamic storage implementation uses aligned-new to allocate memory,
  // which means it has to be paired with aligned-delete, which means I can't
  // use std::default_delete (the default).
  //
  // If I do the deleter via a function pointer it'll double the size of the
  // unique_ptr, but as an empty class it becomes eligible for EBO, and so
  // it'll be pointer size again. Every byte counts
  template <class T, std::align_val_t alignment>
  struct aligned_deleter {
    void operator ()(T* ptr) const noexcept {
      operator delete[](ptr, alignment);
    }
  };

  template <size_t total_bytes>
  struct static_bitvec_storage {
    static_bitvec_storage() noexcept : storage({0}) {}
    explicit static_bitvec_storage(size_t bytes) {
      if (bytes > total_bytes) {
        throw std::bad_alloc();
      }
    }
    static_bitvec_storage(static_bitvec_storage const&) = default;
    ~static_bitvec_storage() = default;

    void resize(size_t) noexcept {
      // XXX: Not sure if this is the right move.
      // This is so that I can mark push_back noexcept in the static case.
      assert(false);
    }

    constexpr size_t size() const noexcept {
      return total_bytes;
    }

    std::array<uint8_t, total_bytes> storage;
  };

  struct dynamic_bitvec_storage {
    explicit dynamic_bitvec_storage(size_t num_bytes) :
      bytes(num_bytes),
      storage(std::make_unique<uint8_t[]>(bytes))
    {}
    dynamic_bitvec_storage(dynamic_bitvec_storage const& other) : bytes(other.bytes), storage(nullptr) {
      storage = std::make_unique<uint8_t[]>(bytes);
      memcpy(storage.get(), other.storage.get(), bytes);
    }
    dynamic_bitvec_storage(dynamic_bitvec_storage&&) = default;
    ~dynamic_bitvec_storage() = default;

    void resize(size_t new_size) {
      auto tmp = std::make_unique<uint8_t[]>(new_size);
      memcpy(tmp.get(), storage.get(), std::min(size(), new_size));
      bytes = new_size;
      storage = std::move(tmp);
    }

    size_t size() const noexcept {
      return bytes;
    }

    size_t bytes;
    std::unique_ptr<uint8_t[]> storage;
  };

  template <size_t bits_per_entry, class StorageBase>
  struct bitvec_api : StorageBase {

    // XXX: Kind of kludgey, but it means the rest of the code doesn't have to think
    // about this. It's not exposed publicly.
    struct byte_proxy {
      byte_proxy& operator =(uint8_t newval) {
        val = newval;
        container->set_bit(index, val);
        return *this;
      }

      operator uint8_t() const noexcept {
        return val;
      }

      uint8_t val;
      size_t index;
      bitvec_api* container;
    };

    bitvec_api() = default;
    explicit bitvec_api(size_t total_bytes) : StorageBase(total_bytes) {}
    bitvec_api(bitvec_api const&) = default;
    bitvec_api(bitvec_api&&) = default;
    ~bitvec_api() = default;

    static constexpr bool bpe = bits_per_entry;
    static_assert(bpe == 1 || bpe == 2 || bpe == 4 || bpe == 8,
        "varvec bit vectors can only encode representations of up to 1 byte, "
        "and can only handle byte subdivisions that are on even powers of two");

    byte_proxy operator [](size_t index) noexcept {
      auto masked = (const_cast<bitvec_api const&>(*this))[index];
      return byte_proxy {masked, index, this};
    }

    uint8_t operator [](size_t index) const noexcept {
      auto [byte, bit] = calculate_location(index);
      assert(byte < this->size());

      auto data = this->storage[byte];
      return (data >> bit) & ~(~0U << bits_per_entry);
    }

    void set_bit(size_t index, uint8_t val) noexcept {
      assert(val < (1 << bits_per_entry));
      auto [byte, bit] = calculate_location(index);

      assert(byte < this->size());
      auto data = this->storage[byte];

      // Lol ChatGPT gave me this, it's better than what I had before
      uint8_t mask = ((1 << bits_per_entry) - 1) << bit;
      this->storage[byte] = (data & ~mask) | ((val << bit) & mask);
    }

    size_t max_members() const noexcept {
      return (this->size() * CHAR_BIT) / bits_per_entry;
    }

    std::tuple<size_t, size_t> calculate_location(size_t index) const noexcept {
      // Divide by 8 to get the byte index, then mod by 8 to get the bit index.
      // Implemented as a shift and a mask for speed
      auto bit_idx = index * bits_per_entry;
      return {bit_idx >> 3, bit_idx & 7};
    }

  };

  template <size_t bits_per_entry, size_t memcount>
  struct static_bitvec :
    bitvec_api<
      bits_per_entry,
      static_bitvec_storage<meta::int_ceil((bits_per_entry * memcount) / CHAR_BIT)>
    >
  {

    // Unfortunate to have to repeat this, but the language doesn't leave us many options
    using parent_class = bitvec_api<
        bits_per_entry,
        static_bitvec_storage<meta::int_ceil((bits_per_entry * memcount) / CHAR_BIT)>
    >;

    static_bitvec() noexcept : parent_class() {}
    static_bitvec(static_bitvec const&) = default;
    static_bitvec(static_bitvec&&) = default;
    ~static_bitvec() = default;

    using parent_class::operator [];

  };

  template <size_t bits_per_entry>
  struct dynamic_bitvec : bitvec_api<bits_per_entry, dynamic_bitvec_storage> {

    using parent_class = bitvec_api<bits_per_entry, dynamic_bitvec_storage>;

    static constexpr size_t init_size = 8;

    dynamic_bitvec() : parent_class((init_size * bits_per_entry) / CHAR_BIT) {}
    explicit dynamic_bitvec(size_t members) : parent_class((members * bits_per_entry) / CHAR_BIT) {}
    dynamic_bitvec(dynamic_bitvec const&) = default;
    dynamic_bitvec(dynamic_bitvec&&) = default;
    ~dynamic_bitvec() = default;

    using parent_class::operator [];

    void resize(size_t members) {
      parent_class::resize(meta::int_ceil((members * bits_per_entry) / (double) CHAR_BIT));
    }

  };

  struct alignment_record {
    bool needs_align;
    size_t align_of, size_of;
  };

  template <class Variant>
  using align_map = std::array<alignment_record, meta::num_types_in(meta::identity<Variant> {})>;

  template <template <class...> class Variant, class... Types>
  constexpr auto construct_alignment_map(meta::identity<Variant<Types...>>) noexcept {
    return align_map<Variant<Types...>> {
      alignment_record {!std::is_trivially_copyable_v<Types>, alignof(Types), sizeof(Types)}...
    };
  }

  template <class Variant>
  constexpr align_map<Variant> alignment_map_for_v = construct_alignment_map(meta::identity<Variant> {});

  // XXX: I'd like all these alignment functions to all be constexpr, but it's illegal to use
  // reinterpret_cast in a constexpr function, and GCC 10 doesn't have std::bit_cast.
  inline bool aligned_for(void const* ptr, size_t alignment) noexcept {
    return !(reinterpret_cast<std::uintptr_t>(ptr) & (alignment - 1));
  }

  template <class T>
  bool aligned_for_type(void const* ptr) noexcept {
    return aligned_for(ptr, alignof(T));
  }

  template <class Variant>
  bool aligned_for_type_index(void const* ptr, uint8_t type) noexcept {
    auto& align_info = alignment_map_for_v<Variant>;
    return aligned_for(ptr, align_info[type].align_of);
  }

  template <class P>
  P* realign_for(P* ptr, size_t alignment) noexcept {
    auto const offset = reinterpret_cast<std::uintptr_t>(ptr);
    return reinterpret_cast<P*>(((offset + (alignment - 1)) & ~(alignment - 1)));
  }

  template <class P>
  P* realign_backwards_for(P* ptr, size_t alignment) noexcept {
    auto const offset = reinterpret_cast<std::uintptr_t>(ptr);
    return reinterpret_cast<P*>(offset - (offset & (alignment - 1)));
  }

  template <class T, class P>
  P* realign_for_type(P* ptr) noexcept {
    return realign_for(ptr, alignof(T));
  }

  template <class T, class P>
  P* realign_backwards_for_type(P* ptr) noexcept {
    return realign_backwards_for(ptr, alignof(T));
  }

  template <class Variant, class P>
  P* realign_for_type_index(P* ptr, uint8_t type) noexcept {
    auto& align_info = alignment_map_for_v<Variant>;
    return realign_for(ptr, align_info[type].align_of);
  }

  template <class Variant, class P>
  P* realign_backwards_for_type_index(P* ptr, uint8_t type) noexcept {
    auto& align_info = alignment_map_for_v<Variant>;
    return realign_backwards_for(ptr, align_info[type].align_of);
  }

  // Given a type index, an object base pointer, a list of variant types, and a generic callback,
  // function implements a std::visit-esque interface where it unwraps and types the underlying
  // packed object storage, passing through a pointer to the callback function.
  // The passed pointer is NOT guaranteed to be well aligned for the given type.
  template <class Storage,
           template <class...> class Variant, meta::storable... Types, class Func>
  constexpr decltype(auto) get_typed_ptr_for(uint8_t curr_type,
      Storage* curr_data, meta::identity<Variant<Types...>>, Func&& callback)
    noexcept(meta::nothrow_visitor_v<Func, Types...>)
  {
    // Lol. Not sure this is better than the old way
    auto recurse = [&] <class T, class... Ts, class Cont, size_t idx, size_t... idxs>
      (Cont&& cont, std::index_sequence<idx, idxs...>) -> decltype(auto) {
      // Forward const
      using ptr_type = std::conditional_t<
        std::is_const_v<Storage>,
        T const,
        T
      >;

      // If this is the index for our type, cast the pointer into the proper type and call the callback.
      if (idx == curr_type) {
        return std::forward<Func>(callback)(reinterpret_cast<ptr_type*>(curr_data));
      }

      // Otherwise recurse.
      // Since we're using an index sequence generated off our type list,
      // we're guaranteed to eventually find a match.
      if constexpr (sizeof...(Ts)) {
        // Recursive, generic, explicitly parameterized lambdas are obnoxious to work with.
        return cont.template operator ()<Ts...>(cont, std::index_sequence<idxs...> {});
      } else {
        __builtin_unreachable();
      }
    };
    return recurse.template operator ()<Types...>(recurse, std::index_sequence_for<Types...> {});
  }


  // Given a type index, an object base pointer, a list of variant types, and a generic callback,
  // function implements a std::visit-esque interface where it unwraps and types the underlying
  // packed object storage, passing through a pointer to the callback function.
  // The passed pointer IS guaranteed to be well aligned for the given type.
  template <class Storage,
           template <class...> class Variant, meta::storable... Types, class Func>
  constexpr decltype(auto) get_aligned_ptr_for(uint8_t curr_type,
      Storage* curr_data, meta::identity<Variant<Types...>> variant, Func&& callback)
    noexcept(meta::nothrow_visitor_v<Func, Types...>)
  {
    return get_typed_ptr_for(curr_type,
        curr_data, variant, [&] <class T> (T* ptr) {
      using stored_type = std::remove_const_t<T>;

      if constexpr (std::copyable<stored_type>) {
        if (!storage::aligned_for_type<stored_type>(ptr)) {
          // XXX: Kind of janky
          // Propagates changes back if the user changes anything.
          struct change_forwarder {
            using target_type = std::conditional_t<
              std::is_const_v<T>,
              void const,
              void
            >;

            change_forwarder(target_type* orig, void* tmp) : orig(orig), tmp(tmp) {}
            ~change_forwarder() noexcept {
              if constexpr (!std::is_const_v<target_type>) {
                // XXX: Is this worth it? Could just copy
                if (memcmp(orig, tmp, sizeof(stored_type))) {
                  memcpy(orig, tmp, sizeof(stored_type));
                }
              }
            }
            target_type* orig;
            void* tmp;
          };

          // Only trivially copyable types should ever be misaligned.
          assert(std::is_trivially_copyable_v<stored_type>);

          // Realign and return.
          std::aligned_storage_t<sizeof(stored_type), alignof(stored_type)> tmp;
          change_forwarder forwarder {ptr, &tmp};
          memcpy(&tmp, ptr, sizeof(stored_type));
          (void) forwarder;
          return std::forward<Func>(callback)(std::launder(reinterpret_cast<T*>(&tmp)));
        }
      } else {
        assert(storage::aligned_for_type<T>(ptr));
      }
      return std::forward<Func>(callback)(ptr);
    });
  }

  // Takes care of element-wise move operations for a packed buffer.
  template <class Variant, class Storage, class Types, class Offsets>
  constexpr auto move_storage(size_t count,
      Types const& types, Offsets const& offsets, Storage* dest, Storage* src)
    noexcept(std::is_nothrow_move_constructible_v<Variant>)
  {
    static_assert(!std::is_const_v<Storage>);
    for (size_t i = 0; i < count; ++i) {
      uint8_t const type = types[i];
      auto const offset = offsets[i];
      get_typed_ptr_for(type, src + offset, meta::identity<Variant> {}, [&] <class T> (T* srcptr) {
        T* destptr = reinterpret_cast<T*>(dest + offset);
        if constexpr (std::is_trivially_copyable_v<T>) {
          memcpy(destptr, srcptr, sizeof(T));
        } else {
          static_assert(std::is_nothrow_move_constructible_v<T>);
          new(destptr) T(std::move(*srcptr));
        }
      });
    }
  }

  // Takes care of element-wise copy operations for a packed buffer.
  template <class Variant, class Storage, class Types, class Offsets>
  constexpr auto copy_storage(size_t count,
      Types const& types, Offsets const& offsets, Storage* dest, Storage const* src)
    noexcept(std::is_nothrow_copy_constructible_v<Variant>)
  {
    for (size_t i = 0; i < count; ++i) {
      uint8_t const type = types[i];
      auto const offset = offsets[i];
      get_typed_ptr_for(type, src + offset, meta::identity<Variant> {}, [&] <class T> (T const* srcptr) {
        T* destptr = reinterpret_cast<T*>(dest + offset);
        if constexpr (std::is_trivially_copyable_v<T>) {
          memcpy(destptr, srcptr, sizeof(T));
        } else {
          new(destptr) T(*srcptr);
        }
      });
    }
  }

  // Base class for statically sized buffer storage.
  // This class performs the best overall for memory usage.
  template <class Variant, size_t bytes, size_t memcount>
  struct static_storage_base {

    using size_type = size_t;
    using variant_type = Variant;

    // These compute the template parameters for the packed_bitvec used as type storage.
    static constexpr auto num_types = meta::num_types_in(meta::identity<Variant> {});
    static constexpr auto type_bits = meta::rounded_bits_for<num_types - 1>();

    // Need to align the whole struct at an alignment boundary that works for the types.
    static constexpr auto start_size = memcount;
    static constexpr auto max_alignment = meta::max_alignment_of(meta::identity<variant_type> {});

    static constexpr bool has_nothrow_resize = true;

    // Calculate the smallest integer type we can safely use to represent byte offsets
    // and sizes.
    using packed_size_type = meta::smallest_type_for_t<std::max({bytes, memcount})>;

    // This is a fallback case for the extraordinarily unlikely event that the user
    // chooses to parameterize their vector with more than 256 types, in which case
    // static_bitvec can't handle it.
    using unpacked_type_storage = std::array<
      meta::smallest_type_for_t<std::max({num_types})>,
      memcount
    >;

    // Choose to use a bitpacked representation for our type storage if we can
    // Otherwise fall back on std::array.
    using type_storage = std::conditional_t<
      type_bits <= 8,
      static_bitvec<type_bits, memcount>,
      unpacked_type_storage
    >;

    // Aligned in-situ storage for our actual data.
    using storage_type = std::aligned_storage_t<
      bytes,
      meta::max_alignment_of(meta::identity<Variant> {})
    >;

    static_storage_base() noexcept : count(0), offset(0), types(), offsets({0}), data({0}) {}

    explicit static_storage_base(size_type members) {
      if (members > memcount) {
        throw std::bad_alloc();
      }
    }

    static_storage_base(static_storage_base const& other)
      noexcept(std::is_nothrow_copy_constructible_v<Variant>)
      requires std::copyable<Variant>
    :
      count(other.count),
      offset(other.offset),
      types(other.types),
      offsets(other.offsets)
    {
      if constexpr (std::is_trivially_copyable_v<Variant>) {
        data = other.data;
      } else {
        copy_storage<Variant>(count, types, offsets, get_data(), other.get_data());
      }
    }

    static_storage_base(static_storage_base&& other)
      noexcept(std::is_nothrow_move_constructible_v<Variant>)
    :
      count(other.count),
      offset(other.offset),
      types(other.types),
      offsets(other.offsets)
    {
      if constexpr (std::is_trivially_copyable_v<Variant>) {
        data = other.data;
      } else if constexpr (std::is_nothrow_move_constructible_v<Variant>) {
        move_storage<Variant>(count, types, offsets, get_data(), other.get_data());
      } else {
        // Fall back on copies if all the types aren't nothrow move to ensure we don't
        // corrupt the new storage class if something throws.
        copy_storage<Variant>(count, types, offsets, get_data(), other.get_data());
      }
    }

    ~static_storage_base() = default;

    uint8_t operator [](size_type offset) const noexcept {
      return *(reinterpret_cast<uint8_t const*>(&data) + offset);
    }

    static_storage_base& operator =(static_storage_base const& other)
      noexcept(std::is_nothrow_copy_constructible_v<static_storage_base>)
      requires std::copyable<Variant>
    {
      if (this == &other) return *this;
      if constexpr (std::is_nothrow_move_constructible_v<static_storage_base>) {
        auto tmp {other};
        *this = std::move(tmp);
      } else {
        paranoid_assign(other);
      }
      return *this;
    }

    static_storage_base& operator =(static_storage_base&& other)
      noexcept(std::is_nothrow_move_constructible_v<static_storage_base>)
    {
      if (this == &other) return *this;

      // This block makes a best-effort attempt to give sensible semantics even when one of our
      // contained types declares a throwing move constructor.
      if constexpr (std::is_nothrow_move_constructible_v<static_storage_base>) {
        // Easy. Moves don't throw, just do the move
        this->~static_storage_base();
        new(this) static_storage_base(std::move(other));
      } else {
        // This still isn't guaranteed reasonable semantics, but hopefully it works in practice.
        paranoid_assign(std::move(other));
      }
      return *this;
    }

    uint8_t* get_data() noexcept {
      return reinterpret_cast<uint8_t*>(&data);
    }

    uint8_t const* get_data() const noexcept {
      return reinterpret_cast<uint8_t const*>(&data);
    }

    void set_offset(size_type idx, size_type val) noexcept {
      offsets[idx] = val;
    }

    size_type get_offset(size_type idx) const noexcept {
      return offsets[idx];
    }

    void incr_offset(size_type count) noexcept {
      offset += count;
    }

    uint8_t* resize(size_type) noexcept {
      // XXX: Not sure if this is the right move.
      // I was originally throwing std::bad_alloc here, which seems like a nicer solution.
      //
      // This is so that I can mark push_back noexcept in the trivial, static, case.
      // For statically sized vectors with trivial contents (ints, doubles, floats, etc),
      // having this function marked noexcept appears to be a meaningful optimization,
      // (at least on clang 14) allowing the compiler to become _significantly_ more aggressive
      // in inlining and optimizing, potentially allowing the _entire data structure_ to
      // get optimized out.
      //
      // If the user builds with -DNDEBUG we also still need to return something here or we'll
      // get a compile warning. It's a logical error to call this function, and would mean
      // the caller tried to overflow a statically sized vector. We could return the proper
      // pointer and let the caller overflow, but this would likely result in much harder
      // to track down bugs stemming from memory corruption.
      //
      // Returning a nullptr here almost guarantees an immediate crash in push_back, where it
      // should hopefully be more obvious what's gone wrong.
      assert(false);
      return nullptr;
    }

    size_type buffer_size() const noexcept {
      return bytes;
    }

    size_type size() const noexcept {
      return sizeof(types) + sizeof(offsets) + sizeof(data);
    }

    constexpr size_type max_members() const noexcept {
      return memcount;
    }

    bool has_space(size_type more) const noexcept {
      if (count < memcount) return offset + more <= bytes;
      else return false;
    }

    template <class Storage>
    void paranoid_assign(Storage&& other) {
      // Move could throw. This still isn't guaranteed sensible semantics, but hopefully it
      // should work well enough in practice. Don't throw from moves and none of this will matter.
      auto backup {*this};
      this->~static_storage_base();
      try {
        // First try to construct ourselves off of the incoming object.
        new(this) static_storage_base(std::forward<Storage>(other));
      } catch (...) {
        try {
          // First pass threw. Unfortunate. Try to restore ourselves to our backup
          new(this) static_storage_base(std::move(backup));
        } catch (...) {
          // Restoration ALSO threw, bad news.
          // Final escape clause is to reset ourselves to an empty container (sucks, but won't throw)
          // to ensure that we don't allow a destroyed object to escape into the rest of the program.
          new(this) static_storage_base();
        }
        throw;
      }
    }

    packed_size_type count;
    packed_size_type offset;

    type_storage types;
    std::array<packed_size_type, memcount> offsets;
    storage_type data;

  };

  // Class used for statically sized storage that has at least one non-trivial destructor.
  template <class Variant, size_t bytes, size_t memcount>
  struct destructible_static_storage_base : static_storage_base<Variant, bytes, memcount> {

    static constexpr bool has_nothrow_resize = true;

    using static_storage_base<Variant, bytes, memcount>::static_storage_base;

    destructible_static_storage_base(destructible_static_storage_base const&) = default;
    destructible_static_storage_base(destructible_static_storage_base&&) = default;

    ~destructible_static_storage_base() noexcept {
      while (this->count) {
        auto const curr_count = --this->count;
        uint8_t const curr_type = this->types[curr_count];
        auto const curr_offset = this->offsets[curr_count];
        auto* const curr_ptr = this->get_data() + curr_offset;
        get_typed_ptr_for(curr_type, curr_ptr, meta::identity<Variant> {}, [&] <class T> (T* value) {
          value->~T();
        });
      }
    }

    using static_storage_base<Variant, bytes, memcount>::operator =;
    using static_storage_base<Variant, bytes, memcount>::operator [];
  };

  // Base class for dynamically sized buffer storage.
  template <class Variant>
  struct dynamic_storage {

    using size_type = size_t;
    using variant_type = Variant;

    static constexpr auto start_members = 8;
    static constexpr auto start_size = start_members * meta::mean_size_of(meta::identity<variant_type> {});
    static constexpr auto max_alignment = meta::max_alignment_of(meta::identity<variant_type> {});

    static constexpr auto num_types = meta::num_types_in(meta::identity<Variant> {});
    static constexpr auto type_bits = meta::rounded_bits_for<num_types - 1>();

    static constexpr bool has_nothrow_resize = false;

    // This is a fallback case for the extraordinarily unlikely event that the user
    // chooses to parameterize their vector with more than 256 types, in which case
    // dynamic_bitvec can't handle it.
    using unpacked_type_storage = std::vector<
      meta::smallest_type_for_t<std::max({num_types})>
    >;

    // Choose to use a bitpacked representation for our type storage if we can
    // Otherwise fall back on std::vector.
    using type_storage = std::conditional_t<
      type_bits <= 8,
      dynamic_bitvec<type_bits>,
      unpacked_type_storage
    >;

    // Interface type with which to access rebuildable offset storage.
    using offset_storage = std::unique_ptr<offsets::virtual_offset_storage>;

    // Make the optimistic choice that the user will store smaller things,
    // will rebuild if wrong
    using initial_offset_storage = offsets::concrete_offset_storage<
      meta::smallest_type_for_t<meta::min_size_of(meta::identity<variant_type> {})>
    >;

    using deleter = aligned_deleter<uint8_t, std::align_val_t(max_alignment)>;

    using data_storage = std::unique_ptr<uint8_t[], deleter>;

    dynamic_storage() :
      bytes(start_size),
      count(0),
      offset(0),
      types(start_members),
      offsets(std::make_unique<initial_offset_storage>(start_members)),
      data(new(std::align_val_t(max_alignment)) uint8_t[bytes])
    {}

    explicit dynamic_storage(size_type members) :
      bytes(members * meta::mean_size_of(meta::identity<variant_type> {})),
      count(0),
      offset(0),
      types(members),
      offsets(std::make_unique<initial_offset_storage>(members)),
      data(new(std::align_val_t(max_alignment)) uint8_t[bytes])
    {}

    dynamic_storage(dynamic_storage const& other)
      requires std::copyable<Variant>
    :
      bytes(other.bytes),
      count(other.count),
      offset(other.offset),
      types(other.types),
      offsets(other.offsets->clone()),
      data(new (std::align_val_t(max_alignment)) uint8_t[bytes])
    {
      if constexpr (std::is_trivially_copyable_v<Variant>) {
        memcpy(get_data(), other.get_data(), bytes);
      } else {
        copy_storage<Variant>(count, types, *offsets, get_data(), other.get_data());
      }
    }

    dynamic_storage(dynamic_storage&& other) noexcept :
      bytes(other.bytes),
      count(other.count),
      offset(other.offset),
      types(std::move(other.types)),
      offsets(std::move(other.offsets)),
      data(std::move(other.data))
    {
      other.bytes = 0;
      other.count = 0;
      other.offset = 0;
    }

    ~dynamic_storage() noexcept {
      while (count) {
        auto const curr_count = --count;
        uint8_t const curr_type = types[curr_count];
        auto const curr_offset = offsets->get(curr_count);
        auto* const curr_ptr = get_data() + curr_offset;
        get_typed_ptr_for(curr_type, curr_ptr, meta::identity<Variant> {}, [&] <class T> (T* value) {
          value->~T();
        });
      }
    }

    uint8_t operator [](size_type offset) const noexcept {
      return data[offset];
    }

    dynamic_storage& operator =(dynamic_storage const& other) requires std::copyable<Variant> {
      if (this == &other) return *this;
      auto tmp {other};
      *this = std::move(tmp);
      return *this;
    }

    dynamic_storage& operator =(dynamic_storage&& other) noexcept {
      if (this == &other) return *this;
      this->~dynamic_storage();
      new(this) dynamic_storage(std::move(other));
      return *this;
    }

    uint8_t* get_data() noexcept {
      return data.get();
    }

    uint8_t const* get_data() const noexcept {
      return data.get();
    }

    void set_offset(size_type idx, size_type val) noexcept {
      // Potentially reallocate our offset storage if its runtime
      // type can't represent the offset value we need to store.
      if (!offsets->can_handle(val)) offsets = offsets->realloc_for(val);
      offsets->set(idx, val);
    }

    size_type get_offset(size_type idx) const noexcept {
      return offsets->get(idx);
    }

    void incr_offset(size_type count) noexcept {
      offset += count;
    }

    static void aligned_delete(uint8_t* ptr) noexcept {
      operator delete[] (ptr, std::align_val_t(max_alignment));
    }

    uint8_t* resize(size_type scale) {
      // Update
      data = realloc(bytes * scale);
      bytes *= scale;
      if (types.max_members() < count * scale) {
        types.resize(count * scale);
      }
      if (offsets->size() < count * scale) {
        offsets->resize(count * scale);
      }
      return get_data() + offset;
    }

    void shrink_to_fit() {
      // Reallocate the storage region
      data = realloc(offset);

      // Update all the book keeping
      bytes = offset;
      types.resize(count);
      offsets->resize(count);
    }

    size_type buffer_size() const noexcept {
      return bytes;
    }

    size_type size() const noexcept {
      return buffer_size() + (sizeof(uint8_t) * types.size()) + offsets->used_bytes();
    }

    size_type max_members() const noexcept {
      return offsets->capacity();
    }

    bool has_space(size_type more) const noexcept {
      return count < max_members() && offset + more < bytes;
    }

    std::unique_ptr<uint8_t[], deleter> realloc(size_type new_size) {
      // Align some storage.
      std::unique_ptr<uint8_t[], deleter> newdata {
        new(std::align_val_t(max_alignment)) uint8_t[new_size]
      };

      // Strong exception guarantee. Don't throw from moves
      if constexpr (std::is_trivially_copyable_v<Variant>) {
        memcpy(newdata.get(), data.get(), bytes);
      } else if constexpr (std::is_nothrow_move_constructible_v<Variant>) {
        move_storage<Variant>(count, types, *offsets, newdata.get(), data.get());
      } else {
        copy_storage<Variant>(count, types, *offsets, newdata.get(), data.get());
      }
      return newdata;
    }

    size_type bytes;
    size_type count;
    size_type offset;

    type_storage types;
    offset_storage offsets;
    data_storage data;

  };

  // Surrounding "context" type is necessary to adapt the template signature
  // of the static storage types to get a consistent arity.
  template <size_t max_bytes, size_t memcount>
  struct static_storage_context {
    template <class Variant>
    using static_storage = std::conditional_t<
      std::is_trivially_destructible_v<Variant>,
      static_storage_base<Variant, max_bytes, memcount>,
      destructible_static_storage_base<Variant, max_bytes, memcount>
    >;
  };

}

namespace varvec {

  template <template <class> class, template <class...> class, meta::storable...>
  class basic_variable_vector;

  template <template <class> class Storage,
           template <class...> class Variant, meta::storable... Types>
  class basic_variable_iterator {

    public:

      using container_type = basic_variable_vector<Storage, Variant, Types...>;

      using iterator_category = std::random_access_iterator_tag;
      using value_type = typename container_type::value_type;
      using difference_type = typename container_type::difference_type;
      using reference = value_type&;
      using size_type = typename container_type::size_type;

      // Because default construction is useful.
      // Be careful!
      basic_variable_iterator() noexcept :
        idx(0),
        storage(nullptr)
      {}

      basic_variable_iterator(basic_variable_iterator const& other) noexcept :
        idx(other.idx),
        storage(other.storage)
      {}

      basic_variable_iterator& operator =(basic_variable_iterator const& other) noexcept {
        if (&other == this) {
          return *this;
        }
        idx = other.idx;
        storage = other.storage;
        return *this;
      }

      value_type operator *() const
        noexcept(std::is_nothrow_copy_constructible_v<value_type>)
      {
        return (*storage)[idx];
      }

      basic_variable_iterator& operator ++() noexcept {
        ++idx;
        return *this;
      }

      basic_variable_iterator& operator --() noexcept {
        --idx;
        return *this;
      }

      basic_variable_iterator operator ++(int) noexcept {
        auto tmp {*this};
        ++idx;
        return tmp;
      }

      basic_variable_iterator operator --(int) noexcept {
        auto tmp {*this};
        --idx;
        return tmp;
      }

    private:

      basic_variable_iterator(size_type idx, container_type const* storage) noexcept :
        idx(idx),
        storage(storage)
      {}

      friend class basic_variable_vector<Storage, Variant, Types...>;

      size_type idx;
      container_type const* storage;

      friend bool operator ==(basic_variable_iterator const& lhs, basic_variable_iterator const& rhs) noexcept {
        return lhs.idx == rhs.idx && lhs.storage == rhs.storage;
      }

      friend bool operator !=(basic_variable_iterator const& lhs, basic_variable_iterator const& rhs) noexcept {
        return !(lhs == rhs);
      }

      friend auto operator <=>(basic_variable_iterator const& lhs, basic_variable_iterator const& rhs) noexcept {
        return lhs.idx <=> rhs.idx;
      }

      friend basic_variable_iterator operator -(basic_variable_iterator const& lhs, std::ptrdiff_t rhs) noexcept {
        auto tmp {lhs};
        auto tmpidx = lhs.idx - rhs;
        tmp.idx = tmpidx;
        return tmp;
      }

      friend basic_variable_iterator operator +(basic_variable_iterator const& lhs, std::ptrdiff_t rhs) noexcept {
        auto tmp {lhs};
        auto tmpidx = lhs.idx + rhs;
        tmp.idx = tmpidx;
        return tmp;
      }

      friend basic_variable_iterator operator +(std::ptrdiff_t lhs, basic_variable_iterator const& rhs) noexcept {
        return rhs + lhs;
      }

  };

  template <template <class> class Storage,
           template <class...> class Variant, meta::storable... Types>
  class basic_variable_vector {

    public:

      using value_type = Variant<meta::copyable_type_for_t<Types>...>;
      using size_type = size_t;
      using difference_type = std::ptrdiff_t;
      using iterator = basic_variable_iterator<Storage, Variant, Types...>;
      using const_iterator = iterator;

      using logical_type = Variant<Types...>;
      using storage_type = Storage<logical_type>;

    private:

      static constexpr bool nothrow_value_copyable =
        std::is_nothrow_copy_constructible_v<value_type>;
      static constexpr bool nothrow_logical_copyable =
        std::is_nothrow_copy_constructible_v<logical_type>;

      static constexpr bool nothrow_value_movable =
        std::is_nothrow_move_constructible_v<value_type>;
      static constexpr bool nothrow_logical_movable =
        std::is_nothrow_move_constructible_v<logical_type>;

      template <class T>
      static constexpr bool contained_type_v = (std::is_same_v<T, Types> || ...);

      template <class T>
      static constexpr bool trivial_get_reqs_v =
          contained_type_v<T> && std::is_trivially_constructible_v<T>;

      template <class T>
      static constexpr bool nontrivial_get_reqs_v =
          contained_type_v<T> && !std::is_trivially_constructible_v<T>;

      template <class Func>
      static constexpr bool exhaustive_visitor_v = (std::is_invocable_v<Func, Types&> && ...);

      template <class Func>
      static constexpr bool nothrow_exhaustive_visitor_v = (std::is_nothrow_invocable_v<Func, Types&> && ...);

      template <class T>
      static constexpr bool nothrow_insertable_v =
          storage_type::has_nothrow_resize && std::is_nothrow_constructible_v<logical_type, T>;

      template <class T>
      static constexpr bool variant_is_insertable_v =
          nothrow_logical_movable && std::is_same_v<std::decay_t<T>, logical_type>;

      template <class T>
      static constexpr bool type_is_insertable_v = nothrow_logical_movable
          && std::is_constructible_v<logical_type, T> && !std::is_same_v<std::decay_t<T>, logical_type>;

    public:

      basic_variable_vector()
        noexcept(std::is_nothrow_constructible_v<storage_type>)
      {}

      explicit basic_variable_vector(size_type start_members) :
        impl(start_members)
      {}

      basic_variable_vector(basic_variable_vector const& other)
        noexcept(nothrow_logical_copyable)
        requires (std::copyable<Types> && ...)
      :
        impl(other.impl)
      {}

      basic_variable_vector(basic_variable_vector&& other)
        noexcept(nothrow_logical_movable)
      :
        impl(std::move(other.impl))
      {}

      ~basic_variable_vector() = default;

      // Subscript operator. Creates a temporary variant to return.
      value_type operator [](size_type index) const noexcept(nothrow_value_copyable) {
        assert(index < size());
        uint8_t const type = impl.types[index];
        auto const offset = impl.get_offset(index);
        auto* const curr_ptr = impl.get_data() + offset;
        return storage::get_aligned_ptr_for(type, curr_ptr, meta::identity<logical_type> {},
            [] <class T> (T const* ptr) noexcept(nothrow_value_copyable) -> value_type {
          if constexpr (std::copyable<T>) return *ptr;
          else return ptr;
        });
      }

      basic_variable_vector& operator =(basic_variable_vector const& other)
        noexcept(std::is_nothrow_copy_assignable_v<storage_type>)
        requires (std::copyable<Types> && ...)
      {
        if (&other == this) return *this;
        impl = other.impl;
        return *this;
      }

      basic_variable_vector& operator =(basic_variable_vector&& other)
        noexcept(std::is_nothrow_move_assignable_v<storage_type>)
      {
        if (&other == this) return *this;
        impl = std::move(other.impl);
        return *this;
      }

      // Function handles forwarding in a std::variant of the right types.
      template <class ValueType>
      requires std::is_same_v<std::decay_t<ValueType>, logical_type>
      void push_back(ValueType&& val)
        noexcept(std::is_nothrow_constructible_v<std::decay_t<ValueType>, ValueType>)
      {
        std::visit([&] <class T> (T&& arg) { push_back(std::forward<T>(arg)); }, std::forward<ValueType>(val));
      }

      // Function handles forwarding in any type that's convertible to our variant type.
      template <class ValueType>
      requires (
        std::is_constructible_v<logical_type, ValueType>
        &&
        !std::is_same_v<std::decay_t<ValueType>, logical_type>
      )
      void push_back(ValueType&& val)
        noexcept(
          storage_type::has_nothrow_resize
          &&
          std::is_nothrow_constructible_v<logical_type, ValueType>
        )
      {
        // XXX: It's REALLY difficult to get overload resolution here to work
        // the way we'd want. This implementation is based on the converting constructor
        // constraint rules added to the standard for std::variant in C++20.
        // For details, check paper P0608R3.
        using stored_type = meta::fuzzy_type_match_t<ValueType, Types...>;

        // Figure out where we'll store this thing, taking into account
        // whether it needs to be aligned.
        auto [data_ptr, alignment_bytes] = find_storage_base<stored_type, false>(impl.offset);

        // Check if we have it.
        while (!impl.has_space(sizeof(stored_type) + alignment_bytes) && data_ptr) {
          // FIXME: Rethink grow strategy
          // Static vector returns null on overflow if assertions are disabled. Will crash below.
          data_ptr = impl.resize(2);
        }

        impl.incr_offset(alignment_bytes);
        auto const curr_count = impl.count++;
        if constexpr (std::is_trivially_copyable_v<stored_type>) {
          // May copy to a misaligned address
          // If you crash here you overflowed a static vector.
          memcpy(data_ptr, &val, sizeof(stored_type));
        } else {
          // Will align at native requirements
          // If you crash here you overflowed a static vector.
          new(data_ptr) stored_type(std::forward<ValueType>(val));
        }
        impl.types[curr_count] = meta::index_of_v<stored_type, Types...>;
        impl.set_offset(curr_count, impl.offset);
        impl.incr_offset(sizeof(stored_type));
      }

      void pop_back() {
        destroy_at(--impl.count);
      }

      value_type front() const noexcept(nothrow_value_copyable) {
        return (*this)[0];
      }

      value_type back() const noexcept(nothrow_value_copyable) {
        return (*this)[size() - 1];
      }

      value_type at(size_t index) {
        bounds_check(index);
        return (*this)[index];
      }

      value_type at(size_t index) const {
        bounds_check(index);
        return (*this)[index];
      }

      // Function allows std::visit style visitation syntax at a given index.
      // Useful because it's the only call that allows universal mutation.
      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit(size_type index, Func&& callback)
        noexcept(nothrow_exhaustive_visitor_v<Func>)
      {
        // Very carefully forwarding noexcept here because it seems to make a difference.
        constexpr bool is_noexcept = noexcept(nothrow_exhaustive_visitor_v<Func>);

        uint8_t const type = impl.types[index];
        auto const offset = impl.get_offset(index);
        auto* const curr_ptr = impl.get_data() + offset;
        storage::get_aligned_ptr_for(type, curr_ptr,
            meta::identity<logical_type> {}, [&] <class T> (T* ptr) noexcept(is_noexcept) {
          std::forward<Func>(callback)(*ptr);
        });
      }

      // Function allows std::visit style visitation syntax at a given index.
      // Useful because it's the only call that allows universal mutation.
      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit(size_type index, Func&& callback) const
        noexcept(nothrow_exhaustive_visitor_v<Func>)
      {
        // Very carefully forwarding noexcept here because it seems to make a difference.
        constexpr bool is_noexcept = noexcept(nothrow_exhaustive_visitor_v<Func>);

        const_cast<basic_variable_vector*>(this)->visit(index, [&] <class T> (T& val) noexcept(is_noexcept) {
          std::forward<Func>(callback)(const_cast<T const&>(val));
        });
      }

      // Function allows std::visit style visitation syntax at a given index.
      // Useful because it's the only call that allows universal mutation.
      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit(iterator it, Func&& callback)
        noexcept(nothrow_exhaustive_visitor_v<Func>)
      {
        visit(it.idx, std::forward<Func>(callback));
      }

      // Function allows std::visit style visitation syntax at a given index.
      // Useful because it's the only call that allows universal mutation.
      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit(iterator it, Func&& callback) const
        noexcept(nothrow_exhaustive_visitor_v<Func>)
      {
        visit(it.idx, std::forward<Func>(callback));
      }

      // Function allows std::visit style visitation syntax at a given index.
      // Useful because it's the only call that allows universal mutation.
      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit_at(size_type index, Func&& callback) {
        bounds_check(index);
        visit(index, std::forward<Func>(callback));
      }

      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit_at(size_type index, Func&& callback) const {
        const_cast<basic_variable_vector*>(this)->visit_at(index, [&] <class T> (T& val) {
          std::forward<Func>(callback)(const_cast<T const&>(val));
        });
      }

      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit_at(iterator it, Func&& callback) {
        visit_at(it.idx, std::forward<Func>(callback));
      }

      template <class Func>
      requires exhaustive_visitor_v<Func>
      void visit_at(iterator it, Func&& callback) const {
        visit_at(it.idx, std::forward<Func>(callback));
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T& get(size_type index) & noexcept {
        // Trust the user and grab it.
        // Obviously this is UB if you call it with the wrong type
        // If you want exceptions, call get_at.
        return *reinterpret_cast<T*>(impl.get_data() + impl.get_offset(index));
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T const& get(size_type index) const& noexcept {
        return const_cast<basic_variable_vector*>(this)->get<T>(index);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T&& get(size_type index) && noexcept {
        return std::move(get<T>());
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T& get(iterator it) & noexcept {
        return get<T>(it.idx);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T const& get(iterator it) const& noexcept {
        return get<T>(it.idx);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T&& get(iterator it) && noexcept {
        return std::move(*this).template get<T>(it.idx);
      }

      template <class T>
      requires trivial_get_reqs_v<T>
      T get(size_type index) const noexcept {
        // Trust the user and grab it.
        // Obviously this is UB if you call it with the wrong type
        // If you want exceptions, call get_at.
        auto* const data_ptr = reinterpret_cast<T const*>(impl.get_data() + impl.get_offset(index));

        // Since this overload is only for trivial types, the address
        // could be misaligned, and so we copy into a temporary if so.
        if (storage::aligned_for_type<T>(data_ptr)) {
          return *data_ptr;
        } else {
          T retval;
          memcpy(&retval, impl.get_data() + impl.get_offset(index), sizeof(T));
          return retval;
        }
      }

      template <class T>
      requires trivial_get_reqs_v<T>
      T get(iterator it) const noexcept {
        return get<T>(it.idx);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T& get_at(size_type index) & {
        // Bounds and type checks.
        bounds_check(index);
        if (impl.types[index] != meta::index_of_v<T, Types...>) {
          throw std::bad_cast();
        }
        return get<T>(index);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T const& get_at(size_type index) const& {
        return const_cast<basic_variable_vector*>(this)->get_at<T>(index);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T&& get_at(size_type index) && {
        return std::move(get_at<T>());
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T& get_at(iterator it) & {
        return get_at<T>(it.idx);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T const& get_at(iterator it) const& {
        return get_at<T>(it.idx);
      }

      template <class T>
      requires nontrivial_get_reqs_v<T>
      T&& get_at(iterator it) && {
        return std::move(*this).template get_at<T>(it.idx);
      }

      template <class T>
      requires trivial_get_reqs_v<T>
      T get_at(size_type index) const {
        // Bounds and type checks.
        bounds_check(index);
        if (impl.types[index] != meta::index_of_v<T, Types...>) {
          throw std::bad_cast();
        }
        return get<T>(index);
      }

      template <class T>
      requires trivial_get_reqs_v<T>
      T get_at(iterator it) const {
        return get_at<T>(it.idx);
      }

      template <class ValueType>
      requires variant_is_insertable_v<ValueType>
      void insert(size_type idx, ValueType&& val)
        noexcept(
          storage_type::has_nothrow_resize
          &&
          std::is_nothrow_constructible_v<logical_type, ValueType>
        )
      {
        std::visit([&] <class T> (T&& arg) { insert(idx, std::forward<T>(arg)); }, std::forward<ValueType>(val));
      }

      template <class ValueType>
      requires variant_is_insertable_v<ValueType>
      void insert(iterator it, ValueType&& val) noexcept(nothrow_insertable_v<ValueType>) {
        insert(it.idx, std::forward<ValueType>(val));
      }

      template <class ValueType>
      requires type_is_insertable_v<ValueType>
      void insert(size_type idx, ValueType&& val) noexcept(nothrow_insertable_v<ValueType>) {
        using stored_type = meta::fuzzy_type_match_t<ValueType, Types...>;
        assert(idx <= size());

        // If this is equivalent to a push_back, just call that.
        if (idx == size()) {
          push_back(std::forward<ValueType>(val));
          return;
        }

        // Find the insert point and how much additional space we'll need
        auto [additional_space, move_point] = find_insert_move_point<stored_type>(idx);

        // Make sure we have space.
        // FIXME: Rethink grow strategy
        // Static vector returns null on overflow if assertions are disabled.
        while (!impl.has_space(additional_space) && impl.resize(2));

        // Move everything forwards by the necessary offset, walking backwards from the end.
        walk_backward_move_forward(idx, move_point);

        // Perform the actual insert.
        auto curr_offset = impl.get_offset(idx);
        auto [insert_ptr, alignment_bytes] = find_storage_base<stored_type, false>(curr_offset);
        if constexpr (std::is_trivially_copyable_v<stored_type>) {
          memcpy(insert_ptr, &val, sizeof(stored_type));
        } else {
          new(insert_ptr) stored_type(std::forward<ValueType>(val));
        }

        // Update all bookkeeping
        impl.types[idx] = meta::index_of_v<stored_type, Types...>;
        impl.set_offset(idx, curr_offset + alignment_bytes);
        impl.incr_offset(additional_space);
        ++impl.count;
      }

      template <class ValueType>
      requires type_is_insertable_v<ValueType>
      void insert(iterator it, ValueType&& val) noexcept(nothrow_insertable_v<ValueType>) {
        insert(it.idx, std::forward<ValueType>(val));
      }

      iterator erase(size_type idx) noexcept requires nothrow_logical_movable {
        assert(idx < size());

        // Knock out the requested index and shift everything backwards
        impl.offset = walk_forward_move_backward(idx);
        --impl.count;
        return begin() + idx;
      }

      iterator erase(iterator it) noexcept requires nothrow_logical_movable {
        return erase(it.idx);
      }

      size_type size() const noexcept {
        return impl.count;
      }

      size_type capacity() const noexcept {
        return impl.max_members();
      }

      bool empty() const noexcept {
        return size() == 0;
      }

      template <class ValueType>
      requires std::is_same_v<std::decay_t<ValueType>, logical_type>
      bool has_space(ValueType const& val) const noexcept {
        return std::visit([&] (auto& arg) { return has_space(arg); });
      }

      template <class ValueType>
      requires (
          std::is_constructible_v<logical_type, ValueType>
          &&
          !std::is_same_v<std::decay_t<ValueType>, logical_type>
      )
      bool has_space(ValueType const&) const noexcept {
        // Compute the type we would store for this argument
        using stored_type = meta::fuzzy_type_match_t<ValueType, Types...>;

        // Figure out if we need space for alignment
        auto [_, alignment_bytes] = find_storage_base<stored_type>(impl.offset);

        // Check if we have it.
        return impl.has_space(sizeof(stored_type) + alignment_bytes);
      }

      size_type used_bytes() const noexcept {
        return impl.size();
      }

      iterator begin() const noexcept {
        return iterator {0, this};
      }

      iterator end() const noexcept {
        return iterator {size(), this};
      }

    private:

      template <class ValueType, bool is_const = true>
      auto find_storage_base(size_type offset) const noexcept {
        auto* const base_ptr = impl.get_data() + offset;
        auto* data_ptr = base_ptr;

        // Figure out how much space we'll need.
        auto const required_bytes = sizeof(ValueType);
        if constexpr (!std::is_trivially_copyable_v<ValueType>) {
          data_ptr = storage::realign_for_type<ValueType>(data_ptr);
        }
        auto const alignment_bytes = data_ptr - base_ptr;

        if constexpr (is_const) {
          return std::tuple {data_ptr, alignment_bytes};
        } else {
          return std::tuple {const_cast<uint8_t*>(data_ptr), alignment_bytes};
        }
      }

      template <class InsertType>
      auto find_insert_move_point(size_type index) const noexcept {
        // Pre-compute all metadata for the type we're inserting
        uint8_t prev_type_of = meta::index_of_v<InsertType, Types...>;
        auto& align_info = storage::alignment_map_for_v<value_type>;
        auto prev = align_info[prev_type_of];

        // Walk index by index and compute how much space we'll need to perform the insert.
        auto curr_idx = index;
        auto curr_offset = impl.get_offset(curr_idx);
        while (curr_idx <= size()) {
          // Prospective address of the current index.
          auto* const curr_ptr = impl.get_data() + curr_offset;

          // If the previous storage index were to be relocated based on this pointer,
          // would it also need to be realigned?
          if (prev.needs_align) {
            auto* const aligned_ptr =
                storage::realign_for_type_index<value_type>(curr_ptr, prev_type_of);
            curr_offset += aligned_ptr - curr_ptr;
          }
          curr_offset += prev.size_of;

          // Update
          if (curr_idx < size()) {
            prev_type_of = impl.types[curr_idx];
            prev = align_info[prev_type_of];
          }
          ++curr_idx;
        }

        // curr_offset is now pushed all the way to the end of the bytes needed for the insert.
        // From this, compute the first destination address for the move routine (offset minus size
        // of final element), along with the number of additional bytes we'll need to use in total.
        auto move_point = curr_offset - align_info[impl.types[size() - 1]].size_of;
        return std::tuple {curr_offset - impl.offset, move_point};
      }

      void walk_backward_move_forward(size_type insert_index, size_type move_point) noexcept {
        static_assert(nothrow_logical_movable);

        auto curr_idx = size();
        auto& align_info = storage::alignment_map_for_v<value_type>;
        do {
          // do-while and start with decrement
          // to handle counting down to zero with an unsigned type.
          --curr_idx;

          // Get current metadata
          uint8_t const type_index = impl.types[curr_idx];
          auto const& curr = align_info[type_index];

          // Compute from/to
          uint8_t* const move_dst = impl.get_data() + move_point;
          uint8_t* const move_src = impl.get_data() + impl.get_offset(curr_idx);

          // Sanity checks
          auto const well_aligned =
              storage::aligned_for_type_index<value_type>(move_src, type_index)
              &&
              storage::aligned_for_type_index<value_type>(move_dst, type_index);
          assert(well_aligned || !curr.needs_align);

          // Perform the move, conditional on if the type is trivially copyable (needs alignment)
          if (move_src != move_dst) {
            if (curr.needs_align) {
              // Handles carefully calling a move constructor on pointers that may overlap.
              move_overlapping_pointers(curr, move_src, move_dst, type_index);
            } else {
              // Regions can overlap, so we can't memcpy
              memmove(move_dst, move_src, curr.size_of);
            }
          }

          // Update type and offset
          impl.types[curr_idx + 1] = type_index;
          impl.set_offset(curr_idx + 1, move_point);

          // Compute next move target
          if (curr_idx > insert_index) {
            // Get the type of the next thing to be moved.
            uint8_t const next_type = impl.types[curr_idx - 1];
            auto const& next = align_info[next_type];

            // Compute the offset for the next object
            uint8_t* next_dst;
            if (next.needs_align) {
              next_dst = storage::realign_backwards_for(move_dst - next.size_of, next.align_of);
            } else {
              next_dst = move_dst - next.size_of;
            }
            move_point = next_dst - impl.get_data();
          }
        } while (curr_idx != insert_index);
      }

      size_type walk_forward_move_backward(size_type erase_point) noexcept {
        // Walk forward and shift each object back one index
        auto curr_idx = erase_point;
        auto curr_offset = impl.get_offset(curr_idx);
        auto& align_info = storage::alignment_map_for_v<value_type>;
        while (true) {
          // Destroy the current index and break if it's the final element.
          destroy_at(curr_idx);
          if (curr_idx == size() - 1) break;

          // Get type and alignment info for the index we're moving
          uint8_t const type_index = impl.types[curr_idx + 1];
          auto const& curr = align_info[type_index];

          // Compute the new storage location
          auto* move_dst = impl.get_data() + curr_offset;
          if (curr.needs_align) {
            move_dst = storage::realign_for_type_index<value_type>(move_dst, type_index);
            curr_offset = move_dst - impl.get_data();
          }

          // Compute the current storage location
          auto const src_offset = impl.get_offset(curr_idx + 1);
          auto* move_src = impl.get_data() + src_offset;

          // Sanity checks
          auto const well_aligned =
              storage::aligned_for_type_index<value_type>(move_src, type_index)
              &&
              storage::aligned_for_type_index<value_type>(move_dst, type_index);
          assert(well_aligned || !curr.needs_align);

          // Perform the move, conditional on if the type is trivially copyable (needs alignment)
          if (move_src != move_dst) {
            if (curr.needs_align) {
              move_overlapping_pointers(curr, move_src, move_dst, type_index);
            } else {
              memmove(move_dst, move_src, curr.size_of);
            }
          }

          // Update bookkeeping
          impl.types[curr_idx] = type_index;
          impl.set_offset(curr_idx, move_dst - impl.get_data());

          curr_offset += curr.size_of;
          ++curr_idx;
        }
        return curr_offset;
      }

      void move_overlapping_pointers(auto const& align,
          uint8_t* move_src, uint8_t* move_dst, uint8_t type_index) noexcept
        requires nothrow_logical_movable
      {
        storage::get_typed_ptr_for(type_index, move_src,
            meta::identity<logical_type> {}, [&] <class T> (T* srcptr) noexcept {
          static_assert(!std::is_const_v<T>);

          // XXX: Have to be very careful here.
          //
          // The move_src and move_dst can potentially overlap in memory, and if they do
          // we have to move through an intermediate object to prevent accidentally corrupting
          // the object while we move from it.
          //
          // The check is formulated as it is so it'll work regardless of which is first in memory.
          auto const srcintptr = reinterpret_cast<std::uintptr_t>(srcptr);
          auto const destintptr = reinterpret_cast<std::uintptr_t>(move_dst);
          if (std::max(srcintptr, destintptr) <
              std::min(srcintptr + align.size_of, destintptr + align.size_of)) {
            T tmp(std::move(*srcptr));
            srcptr->~T();

            // We call placement-new here on an untyped pointer.
            // The idea is hopefully encourage the compiler to realize that it might alias
            new(move_dst) T(std::move(tmp));
          } else {
            new(move_dst) T(std::move(*srcptr));
            srcptr->~T();
          }
        });
      }

      void destroy_at(size_type index) noexcept {
        uint8_t const type = impl.types[index];
        auto const offset = impl.get_offset(index);
        auto* const curr_ptr = impl.get_data() + offset;
        storage::get_aligned_ptr_for(type, curr_ptr,
            meta::identity<logical_type> {}, [] <class T> (T* ptr) noexcept {
          ptr->~T();
        });
      }

      void bounds_check(size_t index) const {
        if (index >= size()) {
          std::string msg = "varvec::vector was indexed out of bounds. ";
          msg += "Index was: " + std::to_string(index);
          msg += ", size was: " + std::to_string(size());
          throw std::out_of_range(msg);
        }
      }

      storage_type impl;

      // FIXME: We can do better performance wise
      friend bool operator ==(basic_variable_vector const& lhs, basic_variable_vector const& rhs)
        noexcept(noexcept(*lhs.begin() != *rhs.begin()))
      {
        auto lhs_it = lhs.begin();
        auto rhs_it = rhs.begin();
        while (lhs_it != lhs.end() && rhs_it != rhs.end()) {
          if (*lhs_it++ != *rhs_it++) return false;
        }
        return lhs_it == lhs.end() && rhs_it == rhs.end();
      }

  };

  // One of the two main types of the library.
  // A statically sized, packed, variant vector.
  template <size_t max_bytes, size_t memcount, meta::storable... Types>
  using static_vector = basic_variable_vector<
    storage::static_storage_context<max_bytes, memcount>::template static_storage,
    std::variant,
    Types...
  >;

  // One of the two main types of the library.
  // A dynamically sized, packed, variant vector.
  template <meta::storable... Types>
  using vector = basic_variable_vector<
    storage::dynamic_storage,
    std::variant,
    Types...
  >;

  // XXX: Feels like this should really be in varvec::meta, but it's so useful for
  // visitation that I want it to be easier to type, and it can't be a type alias
  // here because CTAD doesn't work for type aliases...
  template <class... Funcs>
  struct overload : Funcs... {
    using Funcs::operator ()...;
  };
  template <class... Funcs>
  overload(Funcs...) -> overload<Funcs...>;

}
