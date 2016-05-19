set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

add_clang_executable(C++2HareIDL
  C++2HareIDL.cpp
  )

target_link_libraries(C++2HareIDL
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
