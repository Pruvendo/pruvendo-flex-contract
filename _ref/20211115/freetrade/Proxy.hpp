#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>

namespace tvm {

static constexpr unsigned PROXY_TIMESTAMP_DELAY = 1800;
using proxy_replay_protection_t = replay_attack_protection::timestamp<PROXY_TIMESTAMP_DELAY>;

__interface IProxy {

  [[external]]
  void constructor(uint256 pubkey) = 1;

  [[external, noaccept]]
  void sendMessage(cell msg, uint8 flags) = 2;

  // For noop-deploy
  [[external, noaccept]]
  void onDeploy() = 3;
};
using IProxyPtr = handle<IProxy>;

struct DProxy {
  uint256 owner_;
};

__interface EProxy {
};

__always_inline
std::pair<StateInit, address> prepare_proxy_state_init_and_addr(int8 wch, cell proxy_code, DProxy proxy_data) {
  cell data_cl = prepare_persistent_data<IProxy, proxy_replay_protection_t, DProxy>(
    proxy_replay_protection_t::init(), proxy_data);
  StateInit st_init {
    /*split_depth*/{}, /*special*/{},
    proxy_code, data_cl, /*library*/{}
  };
  cell init_cl = build(st_init).make_cell();
  return { st_init, address::make_std(wch, uint256(tvm_hash(init_cl))) };
}

} // namespace tvm

