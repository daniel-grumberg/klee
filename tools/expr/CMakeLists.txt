#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
klee_add_shared_component(expr
  expr.cpp
)

set(LLVM_COMPONENTS
  support
)

klee_get_llvm_libs(LLVM_LIBS ${LLVM_COMPONENTS})
target_link_libraries(expr PUBLIC ${LLVM_LIBS})
target_link_libraries(expr PRIVATE  kleaverSolver)
