find_package(Catch2 3 REQUIRED)

option(benchmark "Whether to enable benchmarks" OFF)

add_executable(tests test.cc)
target_link_libraries(tests PRIVATE Catch2::Catch2WithMain)
if (${benchmark})
  target_compile_definitions(tests PRIVATE VARVEC_BENCHMARK)
else ()
  target_compile_options(tests PRIVATE -fsanitize=address,undefined)
  target_link_options(tests PRIVATE -fsanitize=address,undefined)
endif ()
set_property(TARGET tests PROPERTY CXX_STANDARD 20)
add_test(NAME varvec_tests COMMAND tests)
