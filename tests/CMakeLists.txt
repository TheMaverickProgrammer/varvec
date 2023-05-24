find_package(Catch2 3 REQUIRED)

add_executable(tests test.cc)
target_link_libraries(tests PRIVATE Catch2::Catch2WithMain)
target_compile_options(tests PRIVATE -fsanitize=address,undefined -stdlib=libc++)
target_link_options(tests PRIVATE -fsanitize=address,undefined -stdlib=libc++)
set_property(TARGET tests PROPERTY CXX_STANDARD 20)
add_test(NAME varvec_tests COMMAND tests)
