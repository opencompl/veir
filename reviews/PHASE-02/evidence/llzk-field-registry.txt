//===-- Field.cpp -----------------------------------------------*- C++ -*-===//
//
// Part of the LLZK Project, under the Apache License v2.0.
// See LICENSE.txt for license information.
// Copyright 2025 Veridise Inc.
// SPDX-License-Identifier: Apache-2.0
//
//===----------------------------------------------------------------------===//

#include "llzk/Util/Field.h"

#include "llzk/Dialect/Array/IR/Types.h"
#include "llzk/Dialect/Felt/IR/Types.h"
#include "llzk/Dialect/POD/IR/Attrs.h"
#include "llzk/Dialect/POD/IR/Types.h"
#include "llzk/Dialect/Polymorphic/IR/Types.h"
#include "llzk/Dialect/String/IR/Types.h"
#include "llzk/Dialect/Struct/IR/Types.h"
#include "llzk/Util/Constants.h"
#include "llzk/Util/Debug.h"
#include "llzk/Util/DynamicAPIntHelper.h"

#include <mlir/IR/Attributes.h>
#include <mlir/IR/BuiltinAttributes.h>
#include <mlir/IR/Operation.h>

#include <llvm/ADT/APSInt.h>
#include <llvm/ADT/SlowDynamicAPInt.h>
#include <llvm/ADT/Twine.h>
#include <llvm/ADT/TypeSwitch.h>
#include <llvm/Support/LogicalResult.h>

#include <algorithm>
#include <mutex>

using namespace mlir;

namespace llzk {

// Having `knownFields` as a static local object ensures it is initialized when
// `getKnownFields` is called, rather than relying on non-local static initialization
// order (https://en.cppreference.com/cpp/language/initialization).
static DenseMap<StringRef, Field> &getKnownFields() {
  static DenseMap<StringRef, Field> knownFields;
  return knownFields;
}

Field::Field(std::string_view primeStr, StringRef name) : Field(APSInt(primeStr), name) {}

Field::Field(const APInt &prime, StringRef name) : primeName(name) {
  primeMod = toDynamicAPInt(prime);
  halfPrime = (primeMod + felt(1)) / felt(2);
  bitwidth = prime.getBitWidth();
}

FailureOr<std::reference_wrapper<const Field>> Field::tryGetField(StringRef fieldName) {
  static std::once_flag fieldsInit;
  std::call_once(fieldsInit, initKnownFields);

  auto &knownFields = getKnownFields();
  if (auto it = knownFields.find(fieldName); it != knownFields.end()) {
    return {it->second};
  }
  return failure();
}

LogicalResult Field::verifyFieldDefined(StringRef fieldName, EmitErrorFn errFn) {
  if (failed(Field::tryGetField(fieldName))) {
    return errFn().append("field '", fieldName, "' is not defined");
  }
  return success();
}

const Field &Field::getField(StringRef fieldName, EmitErrorFn errFn) {
  auto res = tryGetField(fieldName);
  if (succeeded(res)) {
    return res.value().get();
  }
  std::string msg = "field \"" + fieldName.str() + "\" is unsupported";
  if (errFn) {
    errFn().append(msg).report();
  }
  llvm::report_fatal_error(msg.c_str());
}

void Field::addField(Field &&f, EmitErrorFn errFn) {
  // Use `tryGetField()` to ensure knownFields is initialized before checking for conflicts.
  auto existing = Field::tryGetField(f.name());
  if (succeeded(existing)) {
    // Field exists and conflicts with existing definition.
    std::string msg;
    debug::Appender(msg) << "Definition of \"" << f.name()
                         << "\" conflicts with prior definition: prior="
                         << existing.value().get().prime() << ", new=" << f.prime();
    if (errFn) {
      errFn().append(msg).report();
    } else {
      llvm::report_fatal_error(msg.c_str());
    }
    return;
  }
  // Field does not exist, add it.
  getKnownFields().try_emplace(f.name(), f);
}

void Field::initKnownFields() {
  static constexpr const char BN128[] = "bn128", BN254[] = "bn254", GRUMPKIN[] = "grumpkin",
                              BABYBEAR[] = "babybear", GOLDILOCKS[] = "goldilocks",
                              MERSENNE31[] = "mersenne31", KOALABEAR[] = "koalabear";

  auto insert = [](const char *name, const char *primeStr) {
    getKnownFields().try_emplace(name, Field(primeStr, name));
  };

  // Reference: https://github.com/iden3/circom/blob/master/program_structure/src/utils/constants.rs
  // bn128/254, default for circom
  insert(BN128, "21888242871839275222246405745257275088548364400416034343698204186575808495617");
  insert(BN254, "21888242871839275222246405745257275088548364400416034343698204186575808495617");
  // Grumpkin scalar field
  insert(GRUMPKIN, "21888242871839275222246405745257275088696311157297823662689037894645226208583");
  // 15 * 2^27 + 1, default for zirgen
  insert(BABYBEAR, "2013265921");
  // 2^64 - 2^32 + 1, used for plonky2
  insert(GOLDILOCKS, "18446744069414584321");
  // 2^31 - 1, used for Plonky3
  insert(MERSENNE31, "2147483647");
  // 2^31 - 2^24 + 1, also for Plonky3
  insert(KOALABEAR, "2130706433");
}

DynamicAPInt Field::reduce(const DynamicAPInt &i) const {
  DynamicAPInt m = i % prime();
  if (m < 0) {
    return prime() + m;
  }
  return m;
}

DynamicAPInt Field::reduce(const APInt &i) const { return reduce(toDynamicAPInt(i)); }

DynamicAPInt Field::toSigned(const DynamicAPInt &i) const { return i < half() ? i : i - prime(); }

DynamicAPInt Field::inv(const DynamicAPInt &i) const { return modInversePrime(i, prime()); }

DynamicAPInt Field::inv(const APInt &i) const {
  return modInversePrime(toDynamicAPInt(i), prime());
}

IntegerAttr Field::getPrimeAttr(MLIRContext *context, unsigned bitWidth) const {
  return IntegerAttr::get(
      IntegerType::get(context, bitWidth), toExactWidthAPInt(prime(), bitWidth)
  );
}

// Parses Fields from the given attribute, if able.
static LogicalResult parseFields(Attribute a) {
  // clang-format off
  return TypeSwitch<
             Attribute, FailureOr<SmallVector<std::reference_wrapper<const Field>>>>(a)
      .Case<UnitAttr>(
          [](auto) {
            return success();
          })
      .Case<StringAttr>(
          [](auto s) -> FailureOr<SmallVector<std::reference_wrapper<const Field>>> {
            auto fieldRes = Field::tryGetField(s);
            if (failed(fieldRes)) {
              return failure();
            }
            return SmallVector<std::reference_wrapper<const Field>> {fieldRes.value()};
          })
      .Case<ArrayAttr>(
          [](auto arr) -> FailureOr<SmallVector<std::reference_wrapper<const Field>>> {
            // An ArrayAttr may only contain inner StringAttr
            SmallVector<std::reference_wrapper<const Field>> res;
            for (Attribute elem : arr) {
              if (auto s = llvm::dyn_cast<StringAttr>(elem)) {
                auto fieldRes = Field::tryGetField(s);
                if (failed(fieldRes)) {
                  return failure();
                }
                res.push_back(fieldRes.value());
              } else {
                return failure();
              }
            }
            return res;
          })
      .Default([](auto) { return failure(); });
  // clang-format on
}

LogicalResult addSpecifiedFields(ModuleOp modOp) {
  if (Attribute a = modOp->getAttr(FIELD_ATTR_NAME)) {
    return parseFields(a);
  }
  // Always recurse.
  if (ModuleOp parentMod = modOp->getParentOfType<ModuleOp>()) {
    return addSpecifiedFields(parentMod);
  }
  return success();
}

} // namespace llzk

namespace {

struct FieldsCtx {
  llzk::FieldSet &fields;
  LogicalResult &status;
  mlir::Operation *scope;
};

} // namespace

static void handleAttribute(mlir::Attribute, FieldsCtx &);

static void handleType(mlir::Type type, FieldsCtx &ctx) {
  TypeSwitch<mlir::Type> ts(type);
  ts.Case([&ctx](llzk::felt::FeltType felt) {
    if (felt.hasField()) {
      ctx.fields.insert(felt.getField());
    } else {
      ctx.status = failure();
      if (ctx.scope) {
        ctx.scope->emitWarning() << "felt type is unspecified, which may cause some passes to fail";
      }
    }
  })
      .Case([&ctx](llzk::array::ArrayType array) { handleType(array.getElementType(), ctx); })
      .Case([&ctx](llzk::pod::PodType pod) {
    for (auto record : pod.getRecords()) {
      handleAttribute(record, ctx);
    }
  }).Case([&ctx](mlir::FunctionType funcType) {
    for (auto i : funcType.getInputs()) {
      handleType(i, ctx);
    }
    for (auto o : funcType.getResults()) {
      handleType(o, ctx);
    }
  });
  // Do nothing by default for any other type
  ts.Default([](auto) {});
}

static void handleAttribute(mlir::Attribute attr, FieldsCtx &ctx) {
  TypeSwitch<mlir::Attribute> ts(attr);
  ts.Case([&ctx](mlir::TypeAttr typeAttr) { handleType(typeAttr.getValue(), ctx); })
      .Case([&ctx](mlir::ArrayAttr arrayAttr) {
    for (auto a : arrayAttr) {
      handleAttribute(a, ctx);
    }
  })
      .Case([&ctx](mlir::DictionaryAttr dictAttr) {
    for (auto a : dictAttr.getValue()) {
      handleAttribute(a.getValue(), ctx);
    }
  }).Case([&ctx](llzk::pod::RecordAttr recordAttr) {
    handleType(recordAttr.getType(), ctx);
  }).Default([](auto) {});
}

LogicalResult llzk::collectFields(mlir::Operation *root, llzk::FieldSet &fields, bool silent) {
  if (!root) {
    return success(); // Nothing to do
  }
  LogicalResult status = success();
  root->walk([&fields, &status, silent](mlir::Operation *op) {
    FieldsCtx ctx = {.fields = fields, .status = status, .scope = silent ? nullptr : op};
    // Crawl for types in the results,
    for (auto result : op->getOpResults()) {
      handleType(result.getType(), ctx);
    }
    // the attributes,
    for (auto attr : op->getAttrs()) {
      handleAttribute(attr.getValue(), ctx);
    }
    // block arguments (if any)
    for (auto &region : op->getRegions()) {
      for (auto &block : region) {
        for (auto &arg : block.getArguments()) {
          handleType(arg.getType(), ctx);
        }
      }
    }
  });

  return status;
}

std::optional<std::reference_wrapper<const llzk::Field>>
llzk::tryDetectSpecifiedField(Operation *root) {
  if (!root) {
    return std::nullopt;
  }

  ModuleOp modOp = dyn_cast<ModuleOp>(root);
  if (!modOp) {
    modOp = root->getParentOfType<ModuleOp>();
  }

  if (!modOp) {
    return std::nullopt;
  }

  FieldSet fields;
  if (failed(collectFields(modOp, fields)) || fields.size() != 1) {
    return std::nullopt;
  }
  return *fields.begin();
}
