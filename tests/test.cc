#include <catch2/catch_test_macros.hpp>
#include <catch2/benchmark/catch_benchmark_all.hpp>

#include "../varvec.hpp"

using trivial_vector = varvec::static_vector<32, 8, bool, int, float>;

static_assert(
  sizeof(trivial_vector) == 32 + 8 + 2 + 2
);

static_assert(
  noexcept(std::declval<trivial_vector>()[0])
);
static_assert(
  noexcept(std::declval<trivial_vector>().get<bool>(0))
);
static_assert(
  noexcept(std::declval<trivial_vector>().visit(0, [] (auto&) noexcept {}))
);
static_assert(
  !noexcept(std::declval<trivial_vector>().visit(0, [] (auto&) {}))
);

static_assert(
  std::is_trivially_destructible_v<trivial_vector>
);

using copyable_vector = varvec::static_vector<128, 8, bool, int, float, std::string>;

static_assert(
  !std::is_trivially_destructible_v<copyable_vector>
  &&
  std::copyable<copyable_vector>
  &&
  std::movable<copyable_vector>
);
static_assert(
  noexcept(std::declval<copyable_vector>().get<bool>(0))
);
static_assert(
  noexcept(std::declval<copyable_vector>().visit(0, [] (auto&) noexcept {}))
);
static_assert(
  !noexcept(std::declval<copyable_vector>().visit(0, [] (auto&) {}))
);

using movable_vector = varvec::static_vector<128, 8, bool, int, float, std::string, std::unique_ptr<double>>;

static_assert(
  !std::is_trivially_destructible_v<movable_vector>
  &&
  !std::copyable<movable_vector>
  &&
  std::movable<movable_vector>
);
static_assert(
  noexcept(std::declval<movable_vector>().get<bool>(0))
);
static_assert(
  noexcept(std::declval<movable_vector>().visit(0, [] (auto&) noexcept {}))
);
static_assert(
  !noexcept(std::declval<movable_vector>().visit(0, [] (auto&) {}))
);

using dynamic_copyable_vector = varvec::vector<bool, int, float, std::string>;

static_assert(
  !std::is_trivially_destructible_v<dynamic_copyable_vector>
  &&
  std::copyable<dynamic_copyable_vector>
  &&
  std::movable<dynamic_copyable_vector>
);

using dynamic_movable_vector = varvec::vector<bool, int, float, std::string, std::unique_ptr<double>>;

static_assert(
  !std::is_trivially_destructible_v<dynamic_movable_vector>
  &&
  !std::copyable<dynamic_movable_vector>
  &&
  std::movable<dynamic_movable_vector>
);

TEST_CASE("construction properties", "[varvec tests]") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    V vec;
    typename V::iterator vecit = vec.begin();
    REQUIRE(vec.size() == 0);
    REQUIRE(vec.empty());
    REQUIRE(vec.used_bytes() > 0);
    REQUIRE(vec.begin() == vec.end());

    REQUIRE_THROWS_AS(vec.at(0), std::out_of_range);

    if constexpr (std::copyable<V>) {
      auto copy = vec;
      vecit = copy.begin();
      REQUIRE(copy.size() == 0);
      REQUIRE(copy.empty());
      REQUIRE(copy.used_bytes() > 0);
      REQUIRE(copy.begin() == copy.end());
      REQUIRE(copy == vec);

      REQUIRE_THROWS_AS(copy.at(0), std::out_of_range);
    }
  };
  asserts(varvec::meta::identity<trivial_vector> {});
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_copyable_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

TEST_CASE("container properties", "[varvec tests]") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    using val = typename V::value_type;
    V vec;
    REQUIRE(vec.has_space(true));
    vec.push_back(true);
    REQUIRE(vec.has_space(5));
    vec.push_back(5);
    REQUIRE(vec.has_space((float) 3.5));
    vec.push_back((float) 3.5);
    REQUIRE(vec.has_space("hello world"));
    vec.push_back("hello world");

    auto validate = [] (auto& v) {
      auto it = v.begin();
      REQUIRE(v[0] == val {true});
      REQUIRE(*it++ == val {true});
      v.visit(0, varvec::overload {
        [] (bool& val) { REQUIRE(val == true); },
        [] (auto&) { REQUIRE(false); }
      });
      v.visit_at(0, varvec::overload {
        [] (bool& val) { REQUIRE(val == true); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[1] == val {5});
      REQUIRE(*it++ == val {5});
      v.visit(v.begin() + 1, varvec::overload {
        [] (int& val) { REQUIRE(val == 5); },
        [] (auto&) { REQUIRE(false); }
      });
      v.visit_at(v.begin() + 1, varvec::overload {
        [] (int& val) { REQUIRE(val == 5); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[2] == val {(float) 3.5});
      REQUIRE(*it++ == val {(float) 3.5});
      v.visit(2, varvec::overload {
        [] (float& val) { REQUIRE(val == 3.5); },
        [] (auto&) { REQUIRE(false); }
      });
      v.visit_at(2, varvec::overload {
        [] (float& val) { REQUIRE(val == 3.5); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(v[3] == val {"hello world"});
      REQUIRE(*it++ == val {"hello world"});
      v.visit(v.end() - 1, varvec::overload {
        [] (std::string& val) { REQUIRE(val == "hello world"); },
        [] (auto&) { REQUIRE(false); }
      });
      v.visit_at(v.end() - 1, varvec::overload {
        [] (std::string& val) { REQUIRE(val == "hello world"); },
        [] (auto&) { REQUIRE(false); }
      });
      REQUIRE(it == v.end());

      REQUIRE(v.begin() + 4 == v.end());
      REQUIRE(4 + v.begin() == v.end());
      REQUIRE(v.begin() == v.end() - 4);
      REQUIRE(v.begin() < v.end());
      REQUIRE(v.begin() <= v.end());
      REQUIRE(v.end() > v.begin());
      REQUIRE(v.end() >= v.begin());
    };

    validate(vec);
    if constexpr (std::copyable<V>) {
      auto copy = vec;
      validate(copy);

      copy.pop_back();
      copy.pop_back();
      copy.pop_back();
      copy.pop_back();
      REQUIRE(copy.empty());
      REQUIRE(copy.begin() == copy.end());
    }
  };
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_copyable_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

TEST_CASE("move-only properties", "varvec tests") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    using val = typename V::value_type;

    V vec;
    REQUIRE(vec.has_space(true));
    vec.push_back(true);
    REQUIRE(vec.has_space(1337));
    vec.push_back(1337);
    REQUIRE(vec.has_space("hello world"));
    vec.push_back("hello world");
    REQUIRE(vec.has_space(std::make_unique<double>(3.14159)));
    vec.push_back(std::make_unique<double>(3.14159));

    auto validate = [] (auto& v) {
      auto it = v.begin();
      REQUIRE(v[0] == val {true});
      REQUIRE(*it++ == val {true});
      REQUIRE(v[1] == val {1337});
      REQUIRE(*it++ == val {1337});
      REQUIRE(v[2] == val {"hello world"});
      REQUIRE(*it++ == val {"hello world"});

      std::visit(varvec::overload {
        [] (std::unique_ptr<double> const* doubleptr) { REQUIRE(**doubleptr == 3.14159); },
        [] (auto&&) { REQUIRE(false); }
      }, v[3]);
      std::visit(varvec::overload {
        [] (std::unique_ptr<double> const* doubleptr) { REQUIRE(**doubleptr == 3.14159); },
        [] (auto&&) { REQUIRE(false); }
      }, *it++);

      v.visit(3, varvec::overload {
        [] (std::unique_ptr<double>& ptr) { REQUIRE(*ptr == 3.14159); },
        [] (auto&&) { REQUIRE(false); }
      });
      v.visit_at(3, varvec::overload {
        [] (std::unique_ptr<double>& ptr) { REQUIRE(*ptr == 3.14159); },
        [] (auto&&) { REQUIRE(false); }
      });
      REQUIRE(it == v.end());
    };
    validate(vec);

    auto moved = std::move(vec);
    validate(moved);
    moved.pop_back();
    moved.pop_back();
    moved.pop_back();
    moved.pop_back();
    REQUIRE(moved.empty());
    REQUIRE(moved.begin() == moved.end());
  };
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

TEST_CASE("mutation", "varvec tests") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    using val = typename V::value_type;
    V vec;
    vec.push_back(true);
    vec.push_back(5);
    vec.push_back((float) 3.5);
    vec.push_back("hello world");

    vec.visit(3, varvec::overload {
      [] (std::string& msg) { msg = "hello life"; },
      [] (auto&) { REQUIRE(false); }
    });
    vec.visit_at(3, varvec::overload {
      [] (std::string& msg) { msg = "hello life"; },
      [] (auto&) { REQUIRE(false); }
    });
    REQUIRE(std::get<std::string>(vec[3]) == "hello life");
    REQUIRE(vec.template get<std::string>(3) == "hello life");
    REQUIRE(vec.template get_at<std::string>(3) == "hello life");

    if constexpr (std::copyable<V>) {
      auto const copy = vec;
      REQUIRE(copy.template get<std::string>(3) == "hello life");
      REQUIRE(copy.template get_at<std::string>(3) == "hello life");
    }

    vec.visit(2, varvec::overload {
      [] (float& msg) { msg = 42.0; },
      [] (auto&) { REQUIRE(false); }
    });
    vec.visit_at(2, varvec::overload {
      [] (float& msg) { msg = 42.0; },
      [] (auto&) { REQUIRE(false); }
    });
    REQUIRE(std::get<float>(vec[2]) == 42.0);
    REQUIRE(vec.template get<float>(2) == 42.0);
    REQUIRE(vec.template get_at<float>(2) == 42.0);

    if constexpr (std::copyable<V>) {
      auto const copy = vec;
      REQUIRE(copy.template get<float>(2) == 42.0);
      REQUIRE(copy.template get_at<float>(2) == 42.0);
    }

    vec.visit(1, varvec::overload {
      [] (int& msg) { msg = 1337; },
      [] (auto&) { REQUIRE(false); }
    });
    vec.visit_at(1, varvec::overload {
      [] (int& msg) { msg = 1337; },
      [] (auto&) { REQUIRE(false); }
    });
    REQUIRE(std::get<int>(vec[1]) == 1337);
    REQUIRE(vec.template get<int>(1) == 1337);
    REQUIRE(vec.template get_at<int>(1) == 1337);

    vec.visit(0, varvec::overload {
      [] (bool& msg) { msg = false; },
      [] (auto&) { REQUIRE(false); }
    });
    vec.visit_at(0, varvec::overload {
      [] (bool& msg) { msg = false; },
      [] (auto&) { REQUIRE(false); }
    });
    REQUIRE(std::get<bool>(vec[0]) == 0);
    REQUIRE(vec.template get<bool>(0) == 0);
    REQUIRE(vec.template get_at<bool>(0) == 0);

    vec.template get<std::string>(3) = "hello c++";
    REQUIRE(vec.template get<std::string>(3) == "hello c++");
    REQUIRE(vec.template get_at<std::string>(3) == "hello c++");
  };
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_copyable_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

TEST_CASE("resize", "varvec tests") {
  struct big_data {
    big_data() : big_dumb_data {0} {}
    bool operator ==(big_data const&) const = default;
    std::array<char, 4096> big_dumb_data;
  };
  using value = std::variant<bool, int, float, std::string, big_data>;
  using big_data_vector = varvec::vector<bool, int, float, std::string, big_data>;

  big_data_vector vec(4);
  REQUIRE(vec.capacity() == 4);

  for (int i = 0; i < 5; i++) {
    vec.push_back(i);
  }
  REQUIRE(vec.size() == 5);
  REQUIRE(vec.capacity() == 8);

  int count = 0;
  for (auto val : vec) {
    REQUIRE(val == value {count++});
  }

  for (int i = 0; i < 5; i++) {
    vec.push_back(big_data {});
  }
  REQUIRE(vec.size() == 10);

  for (int i = 5; i < 10; i++) {
    REQUIRE(vec[i] == value {big_data {}});
  }
}

TEST_CASE("insert", "varvec tests") {
  auto asserts = [] <class V> (varvec::meta::identity<V>) {
    using val = typename V::value_type;

    V vec;
    vec.push_back("a long enough string that the small string optimization won't apply");
    vec.push_back("a long enough string that the small string optimization won't apply");
    vec.insert(0, true);
    vec.insert(1, false);
    vec.push_back("a long enough string that the small string optimization won't apply");
    vec.insert(3, 3.5f);
    vec.insert(6, "a final value");

    REQUIRE(vec.size() == 7);
    REQUIRE(vec[0] == val {true});
    REQUIRE(vec[1] == val {false});
    REQUIRE(vec[2] == val {"a long enough string that the small string optimization won't apply"});
    REQUIRE(vec[3] == val {3.5f});
    REQUIRE(vec[4] == val {"a long enough string that the small string optimization won't apply"});
    REQUIRE(vec[5] == val {"a long enough string that the small string optimization won't apply"});
    REQUIRE(vec[6] == val {"a final value"});
  };
  asserts(varvec::meta::identity<copyable_vector> {});
  asserts(varvec::meta::identity<movable_vector> {});
  asserts(varvec::meta::identity<dynamic_copyable_vector> {});
  asserts(varvec::meta::identity<dynamic_movable_vector> {});
}

#ifdef VARVEC_BENCHMARK
TEST_CASE("performance", "varvec benchmarks") {
  copyable_vector vec;
  dynamic_copyable_vector dvec;
  std::vector<std::variant<bool, int, float, std::string>> stdvec;

  vec.push_back(bool(rand() % 2));
  vec.push_back(rand());
  vec.push_back(0.5f + rand());
  vec.push_back("hello world" + std::to_string(rand()));

  dvec.push_back(bool(rand() % 2));
  dvec.push_back(rand());
  dvec.push_back(0.5f + rand());
  dvec.push_back("hello world" + std::to_string(rand()));

  stdvec.push_back(bool(rand() % 2));
  stdvec.push_back(rand());
  stdvec.push_back(0.5f + rand());
  stdvec.push_back("hello world" + std::to_string(rand()));

  BENCHMARK("static vector bool subscript operator") {
    return vec[0];
  };
  BENCHMARK("static vector int subscript operator") {
    return vec[1];
  };
  BENCHMARK("static vector float subscript operator") {
    return vec[2];
  };
  BENCHMARK("static vector std::string subscript operator") {
    return vec[3];
  };

  BENCHMARK("dynamic vector bool subscript operator") {
    return dvec[0];
  };
  BENCHMARK("dynamic vector int subscript operator") {
    return dvec[1];
  };
  BENCHMARK("dynamic vector float subscript operator") {
    return dvec[2];
  };
  BENCHMARK("dynamic vector std::string subscript operator") {
    return dvec[3];
  };

  BENCHMARK("std::vector<std::variant> bool subscript operator") {
    return stdvec[0];
  };
  BENCHMARK("std::vector<std::variant> int subscript operator") {
    return stdvec[1];
  };
  BENCHMARK("std::vector<std::variant> float subscript operator") {
    return stdvec[2];
  };
  BENCHMARK("std::vector<std::variant> std::string subscript operator") {
    return stdvec[3];
  };

  BENCHMARK("static vector bool get") {
    return vec.get<bool>(0);
  };
  BENCHMARK("static vector int get") {
    return vec.get<int>(1);
  };
  BENCHMARK("static vector float get") {
    return vec.get<float>(2);
  };
  BENCHMARK("static vector std::string get") {
    return vec.get<std::string>(3);
  };

  BENCHMARK("dynamic vector bool get") {
    return dvec.get<bool>(0);
  };
  BENCHMARK("dynamic vector int get") {
    return dvec.get<int>(1);
  };
  BENCHMARK("dynamic vector float get") {
    return dvec.get<float>(2);
  };
  BENCHMARK("dynamic vector std::string get") {
    return dvec.get<std::string>(3);
  };

  BENCHMARK("std::vector<std::variant> bool std::get") {
    return std::get<bool>(vec[0]);
  };
  BENCHMARK("std::vector<std::variant> int std::get") {
    return std::get<int>(vec[1]);
  };
  BENCHMARK("std::vector<std::variant> float std::get") {
    return std::get<float>(vec[2]);
  };
  BENCHMARK("std::vector<std::variant> std::string std::get") {
    return std::get<std::string>(vec[3]);
  };
}
#endif
