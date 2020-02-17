//===-- expr.c --------------------------------------------------*- C -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the klee expression library, in particular the C
// bindings for use in non C++ applications.
//
//===----------------------------------------------------------------------===//

#include "klee-c/expr.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/ExprBuilder.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Solver.h"

#include "llvm/Support/CBindingWrapping.h"

using namespace klee;

namespace {
// Encapsulate a builder and the associated array cache to tie lifetime of
// arrays to that of builder.
struct LibExprBuilder {
  explicit LibExprBuilder(ExprBuilder *TheBuilder,
                          registration_fn_t TheRegistrationFn)
      : Builder(TheBuilder), RegistrationFn(TheRegistrationFn) {}
  std::unique_ptr<ExprBuilder> Builder;
  registration_fn_t RegistrationFn;
};

} // namespace

DEFINE_SIMPLE_CONVERSION_FUNCTIONS(ref<Expr>, klee_expr_t)
DEFINE_SIMPLE_CONVERSION_FUNCTIONS(ref<Array>, klee_array_t)
DEFINE_SIMPLE_CONVERSION_FUNCTIONS(UpdateList, klee_update_list_t)
DEFINE_SIMPLE_CONVERSION_FUNCTIONS(LibExprBuilder, klee_expr_builder_t)
DEFINE_SIMPLE_CONVERSION_FUNCTIONS(ConstraintManager,
                                   klee_constraint_manager_t);

// Conceptually passing ref<Expr> around the ABI boundary is a bit trickier than
// it looks. Effectively, we cannot pass it out by value, so we have to copy
// constructed into a new'd ref<Expr>. It might seem like the reference count
// will be one too high, but this is not the case, as the original ref<Expr>
// returned by the C++ API will be destroyed via stack-unwinding before crossing
// the boundary. the underlying object will live on as it is captured by the
// newly allocated ref<Expr>.
// TODO: If this pattern winds up being useful (probably for passing ref<T>
// around) consider merging this generically into CBindingWrapping.h
static klee_expr_t allocating_wrap(const LibExprBuilder *Builder,
                                   const ref<Expr> &RefExpr) {
  ref<Expr> *TheCopiedRef = new ref<Expr>(RefExpr);
  klee_expr_t TheExpr = wrap(TheCopiedRef);
  if (Builder->RegistrationFn != nullptr)
    Builder->RegistrationFn(TheExpr);
  return TheExpr;
}

klee_expr_builder_t
klee_expr_builder_create(registration_fn_t registration_fn) {
  ExprBuilder *DefaultBuilder = createDefaultExprBuilder();
  LibExprBuilder *TheBuilder =
      new LibExprBuilder(DefaultBuilder, registration_fn);
  return wrap(TheBuilder);
}

void klee_expr_builder_dispose(klee_expr_builder_t builder) {
  LibExprBuilder *TheBuilder = unwrap(builder);
  delete TheBuilder;
}

klee_constraint_manager_t klee_expr_constraint_manager_create(void) {
  ConstraintManager *TheManager = new ConstraintManager();
  return wrap(TheManager);
}

void klee_expr_constraint_manager_dispose(klee_constraint_manager_t manager) {
  ConstraintManager *TheManager = unwrap(manager);
  delete TheManager;
}

void klee_expr_constraint_manager_add(klee_constraint_manager_t manager,
                                      klee_expr_t constraint) {
  ConstraintManager *TheManager = unwrap(manager);
  ref<Expr> *TheConstraint = unwrap(constraint);
  TheManager->addConstraint(*TheConstraint);
}

size_t klee_expr_constraint_manager_size(klee_constraint_manager_t manager) {
  ConstraintManager *TheManager = unwrap(manager);
  return TheManager->size();
}

void klee_expr_constraint_manager_dump(klee_constraint_manager_t manager) {
  ConstraintManager *TheManager = unwrap(manager);
  for (auto i = TheManager->begin(), e = TheManager->end(); i != e; ++i) {
    ref<Expr> TheConstraint = *i;
    TheConstraint->dump();
    llvm::errs() << " \n";
  }
}

const char *
klee_expr_constraint_manager_get_smtlibv2(klee_constraint_manager_t manager) {
  ConstraintManager *TheManager = unwrap(manager);

  Solver *TheZ3Solver = klee::createCoreSolver(klee::CoreSolverType::Z3_SOLVER);
  TheZ3Solver->setCoreSolverTimeout(klee::time::Span("30s"));

  Query TheQuery(*TheManager, ConstantExpr::alloc(0, klee::Expr::Bool));
  const char *result = TheZ3Solver->getConstraintLog(TheQuery);
  delete TheZ3Solver;
  return result;
}

int klee_expr_constraint_manager_get_ktest(klee_constraint_manager_t manager,
                                           size_t num_arrays,
                                           klee_array_t *arrays,
                                           const char *path) {
  std::vector<const Array *> Objects;
  Objects.reserve(num_arrays);

  std::vector<std::vector<unsigned char>> Values;
  Values.reserve(num_arrays);

  KTest Test;
  int retval;

  ConstraintManager *TheManager = unwrap(manager);

  Solver *TheZ3Solver = klee::createCoreSolver(klee::CoreSolverType::Z3_SOLVER);
  TheZ3Solver->setCoreSolverTimeout(klee::time::Span("30s"));

  Query TheQuery(*TheManager, ConstantExpr::alloc(0, klee::Expr::Bool));

  for (auto arr = arrays, arr_end = arrays + num_arrays; arr != arr_end; ++arr)
    Objects.push_back(unwrap(*arr)->get());

  if (!TheZ3Solver->getInitialValues(TheQuery, Objects, Values)) {
    retval = 1;
    goto cleanup;
  }

  Test.numArgs = 0;
  Test.args = NULL;
  Test.symArgvs = 0;
  Test.symArgvLen = 0;
  Test.numObjects = num_arrays;
  Test.objects = new KTestObject[num_arrays];
  assert(Test.objects);
  for (unsigned i = 0; i < num_arrays; ++i) {
    KTestObject *Obj = &Test.objects[i];
    Obj->name = const_cast<char *>(Objects[i]->getName().c_str());
    Obj->numBytes = Values[i].size();
    Obj->bytes = new unsigned char[Obj->numBytes];
    assert(Obj->bytes);
    std::copy(Values[i].begin(), Values[i].end(), Obj->bytes);
  }

  if (!kTest_toFile(&Test, path)) {
    retval = 1;
    goto cleanup1;
  }

  retval = 0;

cleanup1:
  for (unsigned i = 0; i < num_arrays; ++i) {
    delete[] Test.objects[i].bytes;
  }
  delete[] Test.objects;
cleanup:
  delete TheZ3Solver;
  return retval;
}

void klee_expr_set_mem_from_ktest(void *mem, size_t length, const char *name,
                                  const char *path, void **cookie) {
  if (name == NULL)
    name = "unnamed";

  KTest *testData = NULL;

  if (*cookie == NULL) {
    testData = kTest_fromFile(path);
    if (testData == NULL) {
      llvm::errs() << "Cannot replay, no KTEST_FILE!\n";
      exit(1);
    }
    *cookie = static_cast<void *>(testData);
  } else {
    testData = static_cast<KTest *>(*cookie);
  }

  for (size_t testPosition = 0;; ++testPosition) {
    if (testPosition >= testData->numObjects) {
      llvm::errs() << "Could not find a matching object in the test data... "
                      "continuing with zero!\n";
      memset(mem, 0, length);
      break;
    } else {
      KTestObject *Obj = &testData->objects[testPosition];
      if (strcmp(name, Obj->name) == 0) {
        memcpy(mem, Obj->bytes,
               length < Obj->numBytes ? length : Obj->numBytes);
        if (length != Obj->numBytes) {
          llvm::errs() << "object sizes differ. Expected " << length
                       << "but got " << Obj->numBytes << "\n";
          if (Obj->numBytes < length)
            memset((char *) mem + Obj->numBytes, 0, length - Obj->numBytes);
        }
      }
      break;
    }
  }
}

klee_expr_width_t klee_expr_get_width(klee_expr_t expr) {
  ref<Expr> *TheExpr = unwrap(expr);
  return (*TheExpr)->getWidth();
}

bool klee_expr_is_constant(klee_expr_t expr) {
  ref<Expr> *TheExpr = unwrap(expr);
  return llvm::isa<ConstantExpr>(TheExpr->get());
}

int klee_expr_compare(klee_expr_t lhs, klee_expr_t rhs) {
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  return Lhs->compare(*Rhs);
}

// Clients need to make sure they
// call this to ensure Exprs aren't
// held on forever
void klee_expr_dispose(klee_expr_t expr) {
  ref<Expr> *TheRefExpr = unwrap(expr);
  delete TheRefExpr;
}

klee_expr_t klee_expr_copy(klee_expr_t expr) {
  ref<Expr> *TheRefExpr = unwrap(expr);
  ref<Expr> *TheCopiedRef = new ref<Expr>(*TheRefExpr);
  return wrap(TheCopiedRef);
}

void klee_expr_dump(klee_expr_t expr) {
  ref<Expr> *TheRefExpr = unwrap(expr);
  (*TheRefExpr)->dump();
}

klee_array_t klee_array_create(const char *name, uint64_t size,
                               const uint64_t *constants, bool is_signed,
                               klee_expr_width_t domain,
                               klee_expr_width_t range) {
  std::string TheName(name);
  Array *TheNakedArray = nullptr;

  if (!constants) {
    TheNakedArray = new Array(TheName, size, nullptr, nullptr, domain, range);
  } else {
    std::vector<ref<ConstantExpr>> Constants;
    Constants.reserve(size);
    for (size_t I = 0; I < size; ++I) {
      llvm::APInt TheValue(range, constants[I], is_signed);
      ref<ConstantExpr> TheConstant = ConstantExpr::alloc(TheValue);
      Constants.push_back(TheConstant);
    }
    TheNakedArray = new Array(TheName, size, &Constants[0],
                              &Constants[0] + size, domain, range);
  }

  auto TheArray = new ref<Array>(TheNakedArray);
  return wrap(TheArray);
}

klee_array_t klee_array_copy(klee_array_t array) {
  auto *TheArray = unwrap(array);
  auto *TheCopiedArray = new ref<Array>(*TheArray);
  return wrap(TheCopiedArray);
}

void klee_array_dispose(klee_array_t array) {
  auto *TheArray = unwrap(array);
  delete TheArray;
}

klee_update_list_t klee_update_list_create(const klee_array_t array) {
  auto *TheArray = unwrap(array);
  // Bump the reference count of the
  // array so that it lives on when
  // disposed of
  UpdateList *TheUpdateList = new UpdateList(TheArray->get(), nullptr);
  return wrap(TheUpdateList);
}

void klee_update_list_extend(klee_update_list_t updates, klee_expr_t idx,
                             klee_expr_t value) {

  UpdateList *TheUpdateList = unwrap(updates);
  ref<Expr> *TheIndex = unwrap(idx);
  ref<Expr> *TheValue = unwrap(value);
  TheUpdateList->extend(*TheIndex, *TheValue);
}

klee_update_list_t klee_update_list_copy(klee_update_list_t list) {
  auto *TheUpdateList = unwrap(list);
  auto *TheCopiedUpdateList = new UpdateList(*TheUpdateList);
  return wrap(TheCopiedUpdateList);
}

void klee_update_list_dispose(klee_update_list_t list) {
  UpdateList *TheUpdateList = unwrap(list);
  // This should automatically at
  // the end of the scope decrement
  // the reference count of the
  // underlying array and delete it
  // if necessary
  // XXX: This is disgusting but we
  // need this to support
  // ref-counted array's here
  auto *TheDirtyArray = const_cast<Array *>(TheUpdateList->root);
  ref<Array> TheRefArray(TheDirtyArray);
  delete TheUpdateList;
}

klee_expr_t klee_build_constant_expr(klee_expr_builder_t builder, uint64_t val,
                                     klee_expr_width_t width, bool is_signed) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  llvm::APInt TheValue(width, val, is_signed);
  ref<Expr> ConstantExpr = LibBuilder->Builder->Constant(TheValue);
  return allocating_wrap(LibBuilder, ConstantExpr);
}

klee_expr_t klee_build_read_expr(const klee_expr_builder_t builder,
                                 const klee_update_list_t updates,
                                 const klee_expr_t index) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  UpdateList *Updates = unwrap(updates);
  ref<Expr> *Index = unwrap(index);
  ref<Expr> ReadExpr = LibBuilder->Builder->Read(*Updates, *Index);
  return allocating_wrap(LibBuilder, ReadExpr);
}

klee_expr_t klee_build_select_expr(const klee_expr_builder_t builder,
                                   const klee_expr_t cond,
                                   const klee_expr_t lhs,
                                   const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Cond = unwrap(cond);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SelectExpr = LibBuilder->Builder->Select(*Cond, *Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SelectExpr);
}

klee_expr_t klee_build_concat_expr(const klee_expr_builder_t builder,
                                   const klee_expr_t lhs,
                                   const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> ConcatExpr = LibBuilder->Builder->Concat(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, ConcatExpr);
}

klee_expr_t klee_build_extract_expr(const klee_expr_builder_t builder,
                                    const klee_expr_t lhs, unsigned offset,
                                    klee_expr_width_t width) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> ExtractExpr = LibBuilder->Builder->Extract(*Lhs, offset, width);
  return allocating_wrap(LibBuilder, ExtractExpr);
}

klee_expr_t klee_build_zext_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs,
                                 klee_expr_width_t width) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> ZExtExpr = LibBuilder->Builder->ZExt(*Lhs, width);
  return allocating_wrap(LibBuilder, ZExtExpr);
}

klee_expr_t klee_build_sext_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs,
                                 klee_expr_width_t width) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> SExtExpr = LibBuilder->Builder->SExt(*Lhs, width);
  return allocating_wrap(LibBuilder, SExtExpr);
}

klee_expr_t klee_build_add_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> AddExpr = LibBuilder->Builder->Add(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, AddExpr);
}

klee_expr_t klee_build_sub_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SubExpr = LibBuilder->Builder->Sub(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SubExpr);
}

klee_expr_t klee_build_mul_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> MulExpr = LibBuilder->Builder->Mul(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, MulExpr);
}

klee_expr_t klee_build_udiv_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> UDivExpr = LibBuilder->Builder->UDiv(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, UDivExpr);
}

klee_expr_t klee_build_sdiv_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SDivExpr = LibBuilder->Builder->SDiv(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SDivExpr);
}

klee_expr_t klee_build_urem_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> URemExpr = LibBuilder->Builder->URem(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, URemExpr);
}

klee_expr_t klee_build_srem_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SRemExpr = LibBuilder->Builder->SRem(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SRemExpr);
}

klee_expr_t klee_build_not_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> NotExpr = LibBuilder->Builder->Not(*Lhs);
  return allocating_wrap(LibBuilder, NotExpr);
}

klee_expr_t klee_build_and_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> AndExpr = LibBuilder->Builder->And(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, AndExpr);
}

klee_expr_t klee_build_or_expr(const klee_expr_builder_t builder,
                               const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> OrExpr = LibBuilder->Builder->Or(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, OrExpr);
}

klee_expr_t klee_build_xor_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> XorExpr = LibBuilder->Builder->Xor(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, XorExpr);
}

klee_expr_t klee_build_shl_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> ShlExpr = LibBuilder->Builder->Shl(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, ShlExpr);
}

klee_expr_t klee_build_lshr_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> LShrExpr = LibBuilder->Builder->LShr(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, LShrExpr);
}

klee_expr_t klee_build_ashr_expr(const klee_expr_builder_t builder,
                                 const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> AShrExpr = LibBuilder->Builder->AShr(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, AShrExpr);
}

klee_expr_t klee_build_eq_expr(const klee_expr_builder_t builder,
                               const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> EqExpr = LibBuilder->Builder->Eq(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, EqExpr);
}

klee_expr_t klee_build_ne_expr(const klee_expr_builder_t builder,
                               const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> NeExpr = LibBuilder->Builder->Ne(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, NeExpr);
}

klee_expr_t klee_build_ult_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> UltExpr = LibBuilder->Builder->Ult(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, UltExpr);
}

klee_expr_t klee_build_ule_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> UleExpr = LibBuilder->Builder->Ule(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, UleExpr);
}

klee_expr_t klee_build_ugt_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> UgtExpr = LibBuilder->Builder->Ugt(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, UgtExpr);
}

klee_expr_t klee_build_uge_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> UgeExpr = LibBuilder->Builder->Uge(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, UgeExpr);
}

klee_expr_t klee_build_slt_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SltExpr = LibBuilder->Builder->Slt(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SltExpr);
}

klee_expr_t klee_build_sle_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SleExpr = LibBuilder->Builder->Sle(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SleExpr);
}

klee_expr_t klee_build_sgt_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SgtExpr = LibBuilder->Builder->Sgt(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SgtExpr);
}

klee_expr_t klee_build_sge_expr(const klee_expr_builder_t builder,
                                const klee_expr_t lhs, const klee_expr_t rhs) {
  LibExprBuilder *LibBuilder = unwrap(builder);
  ref<Expr> *Lhs = unwrap(lhs);
  ref<Expr> *Rhs = unwrap(rhs);
  ref<Expr> SgeExpr = LibBuilder->Builder->Sge(*Lhs, *Rhs);
  return allocating_wrap(LibBuilder, SgeExpr);
}
