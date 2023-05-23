#include <catch2/catch_test_macros.hpp>
#include "../varvec.hpp"

TEST_CASE("basic test", "[varvec tests]") {
  varvec::static_vector<32, 8, bool, int, float> vec;
  REQUIRE(vec.size() == 0);
}
