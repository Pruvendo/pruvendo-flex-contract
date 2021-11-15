#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

#include "Price.hpp"
#include "PriceXchg.hpp"

namespace tvm {

// Helper contract to test forbidden direct deploy of listing contracts (Wrapper/TradingPair/XchgPair)
__interface IWrongListingMock {

  [[external]]
  void constructor(uint256 pubkey, cell trading_pair_code, cell xchg_pair_code) = 10;

  // === additional configuration necessary for deploy wrapper === //

  [[external, noaccept]]
  void setFlexWrapperCode(cell flex_wrapper_code) = 14;
  // === ===================================================== === //

  [[external, noaccept]]
  address deployWrapper(
    uint256 wrapper_pubkey,
    uint128 wrapper_deploy_value,
    uint128 wrapper_keep_balance,
    Tip3Config tip3cfg) = 15;

  [[external, noaccept]]
  address deployWrapperWithWrongCall(
    uint256 wrapper_pubkey,
    uint128 wrapper_deploy_value,
    uint128 wrapper_keep_balance,
    Tip3Config tip3cfg) = 16;

  [[external, noaccept]]
  address deployTradingPair(
    address tip3_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount,
    address notify_addr
  ) = 17;

  [[external, noaccept]]
  address deployTradingPairWithWrongCall(
    address tip3_root,
    uint128 deploy_value
  ) = 18;

  [[external, noaccept]]
  address deployXchgPair(
    address tip3_major_root,
    address tip3_minor_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount,
    address notify_addr
  ) = 19;

  [[external, noaccept]]
  address deployXchgPairWithWrongCall(
    address tip3_major_root,
    address tip3_minor_root,
    uint128 deploy_value
  ) = 20;
};
using IWrongListingMockPtr = handle<IWrongListingMock>;

struct DWrongListingMock {
  uint256 owner_;
  cell trading_pair_code_;
  cell xchg_pair_code_;
  int8 workchain_id_;
  address flex_;
  optcell flex_wrapper_code_;
};

__interface EWrongListingMock {
};

}

