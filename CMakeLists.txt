cmake_minimum_required(VERSION 3.23)

project(varvec LANGUAGES CXX)

set(HEADER_FILE varvec.hpp)
add_library(${PROJECT_NAME} INTERFACE)

target_sources(
  ${PROJECT_NAME}
  PUBLIC FILE_SET HEADERS
  BASE_DIRS ${PROJECT_SOURCE_DIR}
  FILES ${HEADER_FILE}
)

install(TARGETS ${PROJECT_NAME} FILE_SET HEADERS)

enable_testing()

add_subdirectory(tests)
