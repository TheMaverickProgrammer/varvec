#include <catch2/catch_test_macros.hpp>
#include "../varvec.hpp"

using trivial_vector = varvec::static_vector<64, 16, bool, int, float>;

static_assert(
  std::is_trivially_destructible_v<trivial_vector>
);

using copyable_vector = varvec::static_vector<128, 4, bool, int, float, std::string>;

static_assert(
  !std::is_trivially_destructible_v<copyable_vector>
  &&
  std::copyable<copyable_vector>
  &&
  std::movable<copyable_vector>
);

using movable_vector = varvec::static_vector<128, 4, bool, int, float, std::string, std::unique_ptr<double>>;

static_assert(
  !std::is_trivially_destructible_v<movable_vector>
  &&
  !std::copyable<movable_vector>
  &&
  std::movable<movable_vector>
);

using dynamic_vector = varvec::vector<bool, int, float, std::string>;

static_assert(
  !std::is_trivially_destructible_v<dynamic_vector>
  &&
  std::copyable<dynamic_vector>
  &&
  std::movable<dynamic_vector>
);

using dynamic_movable_vector = varvec::vector<bool, int, float, std::string, std::unique_ptr<double>>;

static_assert(
  !std::is_trivially_destructible_v<dynamic_movable_vector>
  &&
  !std::copyable<dynamic_movable_vector>
  &&
  std::movable<dynamic_movable_vector>
);

TEST_CASE("basic properties", "[varvec tests]") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    V vec;
    REQUIRE(vec.size() == 0);
    REQUIRE(vec.empty());
    REQUIRE(vec.used_bytes() > 0);
    REQUIRE(vec.begin() == vec.end());

    if constexpr (std::copyable<V>) {
      auto copy = vec;
      REQUIRE(copy.size() == 0);
      REQUIRE(copy.empty());
      REQUIRE(copy.used_bytes() > 0);
      REQUIRE(copy.begin() == copy.end());
      REQUIRE(copy == vec);
    }
  };
  asserts(varvec::meta::identity<trivial_vector> {});
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

TEST_CASE("container properties", "[varvec tests]") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    using val = typename V::value_type;
    V vec;
    vec.push_back(true);
    vec.push_back(5);
    vec.push_back((float) 3.5);
    vec.push_back("hello world");

    auto validate = [] (auto& v) {
      REQUIRE(v[0] == val {true});
      v.visit_at(0, varvec::meta::overload {
        [] (bool& val) { REQUIRE(val == true); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[1] == val {5});
      v.visit_at(1, varvec::meta::overload {
        [] (int& val) { REQUIRE(val == 5); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[2] == val {(float) 3.5});
      v.visit_at(2, varvec::meta::overload {
        [] (float& val) { REQUIRE(val == 3.5); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[3] == val {"hello world"});
      v.visit_at(3, varvec::meta::overload {
        [] (std::string& val) { REQUIRE(val == "hello world"); },
        [] (auto&) { REQUIRE(false); }
      });
    };

    validate(vec);
    if constexpr (std::copyable<V>) {
      auto copy = vec;
      validate(copy);
    }
  };
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}
