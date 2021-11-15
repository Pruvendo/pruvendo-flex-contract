# stTONs - TON Labs DePool stake tokens contract

## Contract interfaces:
* tvm::IstTONs
* tvm::IstTONsNotify

## Expected working sequence:
* Create personal instance of stTONs contract. Using deploy message with prepared persistent data and noop call (tvm::IstTONs::onDeploy()).
  stTONs contract should be created for one specific DePool address.
* Call DePool -> tvm::IDePool::transferStake() to transfer stake at stTONs contract address.
* stTONs contract will receive tvm::IParticipant::onTransfer() notification and will increase token balance at the stake value.
* Call stTONs -> tvm::IstTONs::lendOwnership() to lend ownership for specific tokens amount to service contract (mintofarm or other).
  stTONs contract sends tvm::IstTONsNotify::onLendOwnership() to the service contract.
* Service contract should verify stTONs to be a correct version by sender address, comparing it with the expected deploy address.
* When all lend ownership is expired or terminated by service contracts (using tvm::IstTONs::returnOwnership()), stTONs owner may request tvm::IstTONs::returnStake() to transfer stake back to some other contract.
* stTONs contract when receive returnStake, will send tvm::IDePool::transferStake() with amount = 0 to send full stake.
* DePool will send notification with error code to stTONs, stTONs will save it to `last_depool_error_`.
* stTONs owner may request tvm::IstTONs::returnStake() more times (if there is some error in `last_depool_error_`).
* stTONs owner will call tvm::IstTONs::finalize() to terminate contract and send all remaining crystals to dst address. If there is some error in `last_depool_error_`, distinct from `STATUS_SUCCESS`/`STATUS_DEPOOL_CLOSED`/`STATUS_NO_PARTICIPANT` and `ignore_errors` flag is not set,
 the call will be failed.
 
