#pragma once

#include <tvm/contract_handle.hpp>

/** \file
 *  \brief Subpart of DePool imported interface
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

namespace tvm {

/** \interface IDePool
 * \brief Subset of DePool interface
 */
__interface IDePool {
  /// Transfer participant's stake to destination contract
  [[internal, noaccept]]
  void transferStake(address destination, uint64 amount) = 0x6810bf4e;
};
using IDePoolPtr = handle<IDePool>;

/** \interface IParticipant
 * \brief Subset of DePool IParticipant interface
 */
__interface IParticipant {
  [[internal, noaccept]]
  void onTransfer(address source, uint128 amount) = 0x23c4771d; ///< Notification about stake transfer

  [[internal, noaccept]]
  void receiveAnswer(uint32 errcode, uint64 comment) = 0x3f109e44; ///< Error or success notification for last command
};
using IParticipantPtr = handle<IParticipant>;

} // namespace tvm

