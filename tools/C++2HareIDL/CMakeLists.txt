set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

set(HARE_IDL_DIR "../../../../../Hare-IDL")

add_clang_executable(C++2HareIDL
  C++2HareIDL.cpp
  debug.h
  debug.cpp
  )

target_include_directories(C++2HareIDL PRIVATE ${HARE_IDL_DIR}/src)

add_subdirectory(${HARE_IDL_DIR}/3rdparty/cppformat cppformat)

target_link_libraries(C++2HareIDL
  cppformat
  clangAST
  clangBasic
  clangDriver
  clangFrontend
  clangRewriteFrontend
  clangStaticAnalyzerFrontend
  clangTooling
  )

install(TARGETS C++2HareIDL
  RUNTIME DESTINATION bin)
