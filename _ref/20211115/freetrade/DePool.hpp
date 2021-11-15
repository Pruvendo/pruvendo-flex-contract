#pragma once

#include <tvm/contract_handle.hpp>

namespace tvm { inline namespace schema {

__interface IDePool {
  [[internal, noaccept]]
  void transferStake(address destination, uint64 amount) = 0x6810bf4e; // = hash_v<"transferStake(address,uint64)()v2">
};
using IDePoolPtr = handle<IDePool>;

}} // namespace tvm::schema

