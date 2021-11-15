const assert = require('assert');
const {TonClient, abiJson, abiContract, signerKeys, signerNone} = require('@tonclient/core');
const {libNode} = require("@tonclient/lib-node");
const contract = require('./common.js');
const { hexToUtf8, utf8ToHex, stringToArray, arrayToString, delay, fixLeadingZero } = require('./utils.js')
const conf = contract.readConfig();

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}
function zeroFill( number, width ) {
    width -= number.toString().length;
    if ( width > 0 ) {
        return new Array( width + (/\./.test( number ) ? 2 : 1) ).join( '0' ) + number;
    }
    return number + ""; // always return a string
}
function addMinutes(date, minutes) {
    return new Date(date.getTime() + minutes*60000);
}

describe('Flex Contracts test', function () {
    this.timeout(540000);
    let ton;
    const null_addr = '0:0000000000000000000000000000000000000000000000000000000000000000';
    before(async function () {
        const config = {
            network: {
                endpoints: [conf.url]
            },
            defaultWorkchain: 0,
            log_verbose: false,
            messageExpirationTimeout: 220000000,
            messageProcessingTimeout: 220000000,
            waitForTimeout: 220000000
        }
        TonClient.useBinaryLibrary(libNode);
        ton = new TonClient(config);
    });
    describe('stTONs test', function () {
        let sttons_tip3cfg = {
            name:            "stTONs",
            symbol:          "STTON",
            decimals:        0
        };
        let client_mock;
<<<<<<< HEAD
        let mywallet;
        let flexWalletCode;
        let flex_tip3_root;
        let depool_mock;
        let stTONs;
        let stTONskeys;
        let stTONsFwd;
        const stTONcosts = {
            receive_stake_transfer_costs: 1e9, // full costs of receiveStakeTransfer processing
            store_crystals_costs: 0.1e9, // costs of storeCrystalls processing
            mint_costs: 0.1e9, // costs of `mint` call
            process_receive_stake_costs: 0.1e9, // costs of receiveStakeTransfer function processing itself
            deploy_wallet_costs: 0.2e9, // costs of deployWallet (without crystals stored in the wallet)
            min_transfer_tokens: 10000,
            transfer_stake_costs: 0.1e9
        };
        const src_client1 = '0:0000000000000000000000000000000000000000000000000000000000000001';
        before(async function () {
            flexWalletCode = await contract.getCodeFromImage(ton, contract.flexWalletPackage.imageBase64);
=======
        let depool_mock;
        let stTONs;
        let stTONsCode;
        let stTONskeys;
        before(async function () {
            stTONsCode = await contract.getCodeFromImage(ton, contract.stTONsPackage.imageBase64);
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
            stTONskeys = await ton.crypto.generate_random_sign_keys();
            console.log(`[Test] stTONs keys:`, stTONskeys);
        });
        it("Deploying stTONsClientMock", async function () {
            client_mock = await contract.deployStTONsClientMock(ton, conf);
<<<<<<< HEAD
=======
            console.log('[Test]: stTONsClientMock addr =', client_mock.addr);
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
            const balance = await contract.getBalance(ton, client_mock.addr);
            console.log('[Test]: stTONsClientMock balance =', balance);
            assert(balance > 0);
        });
<<<<<<< HEAD
        it("stTONs deploy flex token root", async function () {
            const stTONsFwdOptions = {
              owner_pubkey: '0x' + stTONskeys.public,
              tip3cfg: { name: "", symbol: "", decimals: 0, root_public_key: "0x0", root_address: null_addr },
              depool: null_addr,
              costs: stTONcosts,
              tip3code: flexWalletCode
              };
            stTONsFwd = await contract.calcDeployAddress(ton, conf, contract.stTONsPackage, stTONskeys,
              stTONsFwdOptions);
            console.log('[Test]: stTONsFwd =', stTONsFwd);
            flex_tip3_root = await contract.deployFlexTip3Root(ton, conf,
              sttons_tip3cfg.name, sttons_tip3cfg.symbol, sttons_tip3cfg.decimals, flexWalletCode, 0, stTONsFwd);
            sttons_tip3cfg.root_public_key = "0x" + flex_tip3_root.keys.public;
            sttons_tip3cfg.root_address = flex_tip3_root.addr;

            const balance = await contract.getBalance(ton, flex_tip3_root.addr);
            console.log('[Test]: stTONs tip3 root balance =', balance);
            assert(balance > 0);
        });
=======
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
        it("stTONs deploy DePool mock", async function () {
            depool_mock = await contract.deployDePoolMock(ton, conf);
            const balance = await contract.getBalance(ton, depool_mock.addr);
            console.log('[Test]: DePool mock balance =', balance);
            assert(balance > 0);
        });
<<<<<<< HEAD
        it("stTONs deploy itself", async function () {
            stTONs = await contract.deployStTONs(ton, conf, stTONskeys, sttons_tip3cfg, depool_mock.addr, stTONcosts, flexWalletCode);
            const balance = await contract.getBalance(ton, stTONs.addr);
            console.log('[Test]: stTONs balance =', balance);
            assert(balance > 0);
            assert.equal(stTONsFwd, stTONs.addr);
        });
        it("stTONsClientMock storeCrystalls", async function () {
            await contract.stTONsClientMock_storeCrystalls(ton, client_mock, client_mock.addr, stTONs.addr, 3e9);
            const details = await contract.stTONs_getDetails(ton, stTONs.addr);
            console.log('[Test] details: ', details);
            assert.equal(details.accounts.length, 1);
            // assert.equal(details.accounts[0].std_addr, 0x1);
            assert(details.accounts[0].account > 2e9);
        });
        it("DePoolMock sendOnTransfer", async function () {
            await contract.DePoolMock_sendOnTransfer(ton, depool_mock, stTONs.addr, client_mock.addr, 10e9);
            const details = await contract.DePoolMock_getDetails(ton, depool_mock.addr);
            console.log('[Test] details: ', details);
            assert.equal(details.fwd_records.length, 1);
            assert.equal(details.fwd_records[0].dst, stTONs.addr);
            assert.equal(details.fwd_records[0].src, client_mock.addr);
            assert.equal(details.fwd_records[0].amount, 10e9);

            mywallet = await contract.FlexTip3Root_getWalletAddress(ton, flex_tip3_root.addr, 0x0, client_mock.addr);
            console.log('[Test] mywallet addr: ', mywallet);
            const balance = await contract.getBalance(ton, mywallet);
            console.log('[Test]: mywallet crystals balance =', balance);
            assert(balance > 0);

            const token_balance = await contract.Tip3Wallet_getBalance(ton, mywallet);
            console.log('[Test]: mywallet token balance =', token_balance);
            assert.equal(token_balance, 10e9);
        });
        it("Transferring back from tip3", async function () {
            await contract.stTONsClientMock_sendTransferBack(ton, client_mock,
                stTONs.addr, mywallet, 1e9, 10e9);
                
            const details = await contract.DePoolMock_getDetails(ton, depool_mock.addr);
            console.log('[Test] details: ', details);
            assert.equal(details.fwd_records.length, 1);
            assert.equal(details.fwd_records[0].dst, stTONs.addr);
            assert.equal(details.fwd_records[0].src, client_mock.addr);
            assert.equal(details.fwd_records[0].amount, 10e9);
            
            assert.equal(details.bck_records.length, 1);
            assert.equal(details.bck_records[0].dst, client_mock.addr);
            assert.equal(details.bck_records[0].src, stTONs.addr);
            assert.equal(details.bck_records[0].amount, 10e9);
        });
=======
        it("Deploying stTONs", async function () {
            stTONs = await contract.stTONsClientMock_deployStTONs(ton, client_mock,
              5e9, stTONsCode, "0x" + stTONskeys.public, client_mock.addr, depool_mock.addr,
              "0x" + depool_mock.keys.public);
            console.log('[Test]: stTONs addr =', stTONs);
            const balance = await contract.getBalance(ton, stTONs);
            console.log('[Test]: stTONs balance =', balance);
            assert(balance > 0);
        });
        it("DePoolMock sendOnTransfer", async function () {
            await contract.DePoolMock_sendOnTransfer(ton, depool_mock, stTONs, client_mock.addr, 10e9);
            const details = await contract.DePoolMock_getDetails(ton, depool_mock.addr);
            console.log('[Test] details: ', details);
            assert.equal(details.fwd_records.length, 1);
            assert.equal(details.fwd_records[0].dst, stTONs);
            assert.equal(details.fwd_records[0].src, client_mock.addr);
            assert.equal(details.fwd_records[0].amount, 10e9);

            const token_balance = await (await contract.stTONs_getDetails(ton, stTONs)).balance;
            console.log('[Test]: stTONs token balance =', token_balance);
            assert.equal(token_balance, 10e9);
        });
        it("Transferring stake back", async function () {
            await contract.stTONsClientMock_returnStake(ton, client_mock,
                stTONs, client_mock.addr, 1e9, 0.2e9);

            const details = await contract.DePoolMock_getDetails(ton, depool_mock.addr);
            console.log('[Test] details: ', details);
            assert.equal(details.fwd_records.length, 1);
            assert.equal(details.fwd_records[0].dst, stTONs);
            assert.equal(details.fwd_records[0].src, client_mock.addr);
            assert.equal(details.fwd_records[0].amount, 10e9);

            assert.equal(details.bck_records.length, 1);
            assert.equal(details.bck_records[0].dst, client_mock.addr);
            assert.equal(details.bck_records[0].src, stTONs);
            assert.equal(details.bck_records[0].amount, 0); // back transfer is called with zero amount

            const st_details = await contract.stTONs_getDetails(ton, stTONs);
            assert(st_details.transferring_stake_back);
            assert.equal(st_details.last_depool_error, 0);
        });
        it("Transferring stake back", async function () {
            await contract.stTONsClientMock_finalize(ton, client_mock,
                stTONs, client_mock.addr, 0.2e9, false);
            const balance = await contract.getBalance(ton, client_mock.addr);
            console.log('[Test]: client_mock balance =', balance);
            assert(balance > 0);
        });
        // it("End", async function () { assert(false); });
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
    });
    describe('Flex deploy', function () {
        let deployForSolidityStyleDebots = true;

        let flex;
        let proxy1;
        let proxy2;

        let pairCode;
        let xchgPairCode;
        let extWalletCode;
        let flexWalletCode;
        let flexWrapperCode;
        let client1;
        let client2;

        let nuka_root;
        let nuka_wrapper;
        let nuka_wrapper_keys;
        let nuka_wrapper_wallet;
        let nuka_wallet1;
        let nuka_wallet2;
        let nuka_wallet1_intern;
        let nuka_wallet2_intern;

        let funtics_root;
        let funtics_wrapper;
        let funtics_wrapper_keys;
        let funtics_wrapper_wallet;
        let funtics_wallet1;
        let funtics_wallet2;
        let funtics_wallet1_intern;
        let funtics_wallet2_intern;

        let nuka_funtics_xchg_pair;

        const notify_addr = "0:48e6891227df6a7e29e342e5ebced85ccefec9d0f842031c922a38c691d61af9";
        const deals_limit = 20;
        const tons_cfg = {
            transfer_tip3: 2e8,
            return_ownership: 2e8,
            trading_pair_deploy: 1e9,
            order_answer: 1e8,
            process_queue: 4e8,
            send_notify: 1e8
        };
        const listing_cfg = {
            // Funds requirement (from client) to deploy wrapper
            register_wrapper_cost: 10e9,
            // Funds to be taken in case of rejected wrapper
            // rest will be returned to client
            reject_wrapper_cost: 1e9,
            // Funds to send in wrapper deploy message
            wrapper_deploy_value: 1.2e9,
            // Wrapper will try to keep this balance (should be less then wrapper_deploy_value)
            wrapper_keep_balance: 1e9,
            // Funds to send in external wallet deploy message
            ext_wallet_balance: 1e9,
            // Funds to send with Wrapper::setInternalWalletCode message
            set_internal_wallet_value: 0.2e9,
            // Funds requirement (from client) to deploy xchg/trading pair
            register_pair_cost: 10e9,
            // Funds to be taken in case of rejected xchg/trading pair
            // rest will be returned to client
            reject_pair_cost: 1e9,
            // Funds to send in pair deploy message
            pair_deploy_value: 1.2e9,
            // Pair will try to keep this balance
            pair_keep_balance: 1e9,
            // Value for answer
            register_return_value: 0.1e9
        };
        let nuka_tip3cfg;
        let funtics_tip3cfg;
        let nuka_wrapper_tip3cfg;
        let funtics_wrapper_tip3cfg;

        before(async function () {
            proxy1 = await contract.deployProxy(ton, conf);
            console.log('[Test]: proxy1 balance =', await contract.getBalance(ton, proxy1.addr));
            proxy2 = await contract.deployProxy(ton, conf);
            console.log('[Test]: proxy2 balance =', await contract.getBalance(ton, proxy2.addr));

            pairCode = await contract.getCodeFromImage(ton, contract.pairPackage.imageBase64);
            priceCode = await contract.getCodeFromImage(ton, contract.pricePackage.imageBase64);
            xchgPairCode = await contract.getCodeFromImage(ton, contract.xchgPairPackage.imageBase64);
            xchgPriceCode = await contract.getCodeFromImage(ton, contract.xchgPricePackage.imageBase64);
            clientCode = await contract.getCodeFromImage(ton, contract.clientPackage.imageBase64);
            extWalletCode = await contract.getCodeFromImage(ton, contract.tip3WalletPackage.imageBase64);
            flexWalletCode = await contract.getCodeFromImage(ton, contract.flexWalletPackage.imageBase64);
            flexWrapperCode = await contract.getCodeFromImage(ton, contract.flexWrapperPackage.imageBase64);

            flex = await contract.deployFlex(
              ton, conf, "TON Labs", null,
              pairCode, priceCode,
              xchgPairCode, xchgPriceCode,
              flexWrapperCode, extWalletCode, flexWalletCode,
              tons_cfg,
              deals_limit,
              listing_cfg
              );
            console.log('[Test]: flex balance =', await contract.getBalance(ton, flex.addr));
            pairCode = await contract.Flex_getTradingPairCode(ton, flex);
            xchgPairCode = await contract.Flex_getXchgPairCode(ton, flex);
        });
        it("Flex isFullyInitialized", async function () {
            assert(await contract.Flex_isFullyInitialized(ton, flex));
        });
        it("Flex getOwnershipInfo", async function () {
            const info = await contract.Flex_getOwnershipInfo(ton, flex);
            console.log("Flex getOwnershipInfo = ", info);
            assert.equal(info.deployer_pubkey, "0x" + flex.keys.public);
            assert.equal(info.ownership_description, "TON Labs");
            assert.equal(info.owner_contract, null);
        });
        it("Flex getWrapperListingRequests", async function () {
            const requests = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);
        });
        it("Deploy client1", async function () {
            if (deployForSolidityStyleDebots) {
              client1 = await contract.deployFlexClient(ton, conf, pairCode, xchgPairCode);
              console.log('[Test]: client1 addr =', client1.addr);
              await contract.FlexClient_setFlexCfg(ton, client1, tons_cfg, flex.addr);
              await contract.FlexClient_setExtWalletCode(ton, client1, extWalletCode);
              await contract.FlexClient_setFlexWalletCode(ton, client1, flexWalletCode);
              await contract.FlexClient_setFlexWrapperCode(ton, client1, flexWrapperCode);
              console.log('[Test]: client1 balance =', await contract.getBalance(ton, client1.addr));
            }
        });
        it("Deploy client2", async function () {
            if (deployForSolidityStyleDebots) {
              client2 = await contract.deployFlexClient(ton, conf, pairCode, xchgPairCode);
              await contract.FlexClient_setFlexCfg(ton, client2, tons_cfg, flex.addr);
              await contract.FlexClient_setExtWalletCode(ton, client2, extWalletCode);
              await contract.FlexClient_setFlexWalletCode(ton, client2, flexWalletCode);
              await contract.FlexClient_setFlexWrapperCode(ton, client2, flexWrapperCode);
              console.log('[Test]: client2 balance =', await contract.getBalance(ton, client2.addr));
            }
        });
        it("Nuka Tip3 root deploy", async function () {
            nuka_root = await contract.deployTip3Root(ton, conf, "NUKA caps", "NUKA", 0, extWalletCode, 2000);
            console.log('[Test]: nuka tip3 root balance =', await contract.getBalance(ton, nuka_root.addr));
            const walletCodeHash = await contract.Tip3Root_getWalletCodeHash(ton, nuka_root);
            console.log('[Test]: tip3 wallet code hash =', walletCodeHash);

            nuka_tip3cfg = {
                name:            "NUKA caps",
                symbol:          "NUKA",
                decimals:        0,
                root_public_key: "0x" + nuka_root.keys.public,
                root_address:    nuka_root.addr
            };
        });
        it("Nuka wallet1 deploy", async function () {
            nuka_wallet1 = await contract.Tip3Root_deployWallet(ton, conf, nuka_root, null_addr, 1000, 5e9);
            console.log('nuka_wallet1 address = ', nuka_wallet1.addr);
            console.log('[Test]: nuka_wallet1 balance =', await contract.getBalance(ton, nuka_wallet1.addr));
            const nuka_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet1.addr);
            console.log('[Test]: nuka_wallet1 tokens balance =', nuka_wallet1_balance);
            assert.equal(nuka_wallet1_balance, 1000);
        });
        it("Nuka wallet2 deploy", async function () {
            nuka_wallet2 = await contract.Tip3Root_deployWallet(ton, conf, nuka_root, null_addr, 100, 5e9);
            console.log('nuka_wallet2 address = ', nuka_wallet2.addr);
            console.log('[Test]: nuka_wallet2 balance =', await contract.getBalance(ton, nuka_wallet2.addr));
            const nuka_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet2.addr);
            console.log('[Test]: nuka_wallet2 tokens balance =', nuka_wallet2_balance);
            assert.equal(nuka_wallet2_balance, 100);
        });
        it("Funtics Tip3 root deploy", async function () {
            funtics_root = await contract.deployTip3Root(ton, conf, "Funtics", "FUNT", 0, extWalletCode, 200000);
            console.log('[Test]: tip3 funtics root balance =', await contract.getBalance(ton, funtics_root.addr));
            const walletCodeHash = await contract.Tip3Root_getWalletCodeHash(ton, funtics_root);
            console.log('[Test]: tip3 funtics wallet code hash =', walletCodeHash);

            funtics_tip3cfg = {
                name:            "Funtics",
                symbol:          "FUNT",
                decimals:        0,
                root_public_key: "0x" + funtics_root.keys.public,
                root_address:    funtics_root.addr
            };
        });
        it("funtics wallet1 deploy", async function () {
            funtics_wallet1 = await contract.Tip3Root_deployWallet(ton, conf, funtics_root, null_addr, 100, 5000000000);
            console.log('FUNT wallet1 address = ', funtics_wallet1.addr);
            console.log('[Test]: FUNT wallet1 balance =', await contract.getBalance(ton, funtics_wallet1.addr));
            const funtics_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet1.addr);
            console.log('[Test]: FUNT wallet1 tokens balance =', funtics_wallet1_balance);
            assert.equal(funtics_wallet1_balance, 100);
        });
        it("funtics wallet2 deploy", async function () {
            funtics_wallet2 = await contract.Tip3Root_deployWallet(ton, conf, funtics_root, null_addr, 20000, 5000000000);
            console.log('FUNT wallet2 address = ', funtics_wallet2.addr);
            console.log('[Test]: FUNT wallet2 balance =', await contract.getBalance(ton, funtics_wallet2.addr));
            const funtics_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet2.addr);
            console.log('[Test]: FUNT wallet2 tokens balance =', funtics_wallet2_balance);
            assert.equal(funtics_wallet2_balance, 20000);
        });
        // nuka wrapper
        it("FlexClient registerWrapper for nuka", async function () {
            const requests = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);
            nuka_wrapper_keys = await ton.crypto.generate_random_sign_keys();
            await contract.FlexClient_registerWrapper(ton, client1,
              "0x" + nuka_wrapper_keys.public, listing_cfg.register_wrapper_cost + 2e9, nuka_tip3cfg
              );
            const requestsAfter = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests (after) = ", requestsAfter);
            assert.equal(requestsAfter.length, 1);
        });
        it("Flex approveWrapper for nuka", async function () {
            nuka_wrapper = await contract.Flex_approveWrapper(ton, flex, "0x" + nuka_wrapper_keys.public);
            console.log("[Test]: Approved NUKA wrapper = ", nuka_wrapper);
            console.log('[Test]: NUKA wrapper balance =', await contract.getBalance(ton, nuka_wrapper));
            const requests = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);

            // nuka_wrapper_tip3cfg has the same parameters (as nuka_tip3cfg) except for root address and root pubkey
            nuka_wrapper_tip3cfg = nuka_tip3cfg;
            nuka_wrapper_tip3cfg.root_address = nuka_wrapper;
            nuka_wrapper_tip3cfg.root_public_key = "0x" + nuka_wrapper_keys.public;

            assert(await contract.Wrapper_hasInternalWalletCode(ton, nuka_wrapper));
            nuka_wrapper_wallet = await contract.Wrapper_getExternalWallet(ton, nuka_wrapper);
            console.log('[Test]: NUKA wrapper wallet address = ', nuka_wrapper_wallet);
            console.log('[Test]: NUKA wrapper wallet balance =', await contract.getBalance(ton, nuka_wrapper_wallet));

            const internal_wallet_code = await contract.Wrapper_getInternalWalletCode(ton, nuka_wrapper);
            const internal_wallet_code_hash = (await contract.getHashCode(ton, internal_wallet_code)).hash;
            console.log('[Test]: internal wallet code hash: ', internal_wallet_code_hash);    
        });
        // funtics wrapper
        it("FlexClient registerWrapper for funtics", async function () {
            const requests = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);
            funtics_wrapper_keys = await ton.crypto.generate_random_sign_keys();
            await contract.FlexClient_registerWrapper(ton, client1,
              "0x" + funtics_wrapper_keys.public, listing_cfg.register_wrapper_cost + 2e9, funtics_tip3cfg
              );
            const requestsAfter = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests (after) = ", requestsAfter);
            assert.equal(requestsAfter.length, 1);
        });
        it("Flex approveWrapper for nuka", async function () {
            funtics_wrapper = await contract.Flex_approveWrapper(ton, flex, "0x" + funtics_wrapper_keys.public);
            console.log("[Test] Approved FUNT wrapper = ", funtics_wrapper);
            console.log('[Test]: FUNT wrapper balance =', await contract.getBalance(ton, funtics_wrapper));
            const requests = await contract.Flex_getWrapperListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);

            // funtics_wrapper_tip3cfg has the same parameters (as funtics_tip3cfg) except for root address and root pubkey
            funtics_wrapper_tip3cfg = funtics_tip3cfg;
            funtics_wrapper_tip3cfg.root_address = funtics_wrapper;
            funtics_wrapper_tip3cfg.root_public_key = "0x" + funtics_wrapper_keys.public;

            assert(await contract.Wrapper_hasInternalWalletCode(ton, funtics_wrapper));
            funtics_wrapper_wallet = await contract.Wrapper_getExternalWallet(ton, funtics_wrapper);
            console.log('[Test]: FUNT wrapper wallet address = ', funtics_wrapper_wallet);
            console.log('[Test]: FUNT wrapper wallet balance =', await contract.getBalance(ton, funtics_wrapper_wallet));

            const internal_wallet_code = await contract.Wrapper_getInternalWalletCode(ton, funtics_wrapper);
            const internal_wallet_code_hash = (await contract.getHashCode(ton, internal_wallet_code)).hash;
            console.log('[Test]: internal wallet code hash: ', internal_wallet_code_hash);
        });
        it("Transfers for nuka external->internal", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const owner_pubkey = "0x" + client1.keys.public;
            const payload = await contract.FlexClient_getPayloadForDeployInternalWallet(ton, client1,
                owner_pubkey, client1.addr, 1e9);
            const wallet1_details = await contract.Tip3Wallet_getDetails(ton, nuka_wallet1.addr);
            const nuka_wrapper_wallet_details = await contract.Tip3Wallet_getDetails(ton, nuka_wrapper_wallet);

            assert.equal((await contract.getHashCode(ton, wallet1_details.code)).hash,
                         (await contract.getHashCode(ton, nuka_wrapper_wallet_details.code)).hash);

            await contract.Tip3Wallet_transferWithNotify(ton, nuka_wallet1,
                nuka_wallet1.addr, nuka_wrapper_wallet, 500, 1.5e9, false, payload
                );
            nuka_wallet1_intern = await contract.Wrapper_getWalletAddress(ton, nuka_wrapper, owner_pubkey, client1.addr);
            const nuka_wallet1_int_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet1_intern);
            console.log('[Test]: nuka_wallet1 internal tokens balance =', nuka_wallet1_int_balance);
            console.log('[Test]: nuka_wallet1 internal address =', nuka_wallet1_intern);
            assert.equal(nuka_wallet1_int_balance, 500);
        });
        it("Transfers for funtics external->internal", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const owner_pubkey = "0x" + client2.keys.public;
            const payload = await contract.FlexClient_getPayloadForDeployInternalWallet(ton, client2,
                owner_pubkey, client2.addr, 1e9);
            await contract.Tip3Wallet_transferWithNotify(ton, funtics_wallet2,
                funtics_wallet2.addr, funtics_wrapper_wallet, 10000, 1.5e9, false, payload
                );
            funtics_wallet2_intern = await contract.Wrapper_getWalletAddress(ton, funtics_wrapper, owner_pubkey, client2.addr);
            const funtics_wallet2_int_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet2_intern);
            assert.equal(funtics_wallet2_int_balance, 10000);
        });
        // nuka/funtics exchange pair
        it("FlexClient registerXchgPair for nuka", async function () {
            const requests = await contract.Flex_getXchgPairListingRequests(ton, flex);
            console.log("Flex listing getXchgPairListingRequests = ", requests);
            assert.equal(requests.length, 0);
            xchg_pair_keys = await ton.crypto.generate_random_sign_keys();
            await contract.FlexClient_registerXchgPair(ton, client1,
              "0x" + xchg_pair_keys.public, listing_cfg.register_pair_cost + 2e9,
              nuka_root.addr, funtics_root.addr, 1, notify_addr
              );
            const requestsAfter = await contract.Flex_getXchgPairListingRequests(ton, flex);
            console.log("Flex getXchgPairListingRequests (after) = ", requestsAfter);
            assert.equal(requestsAfter.length, 1);
        });
        it("Flex approveXchgPair for nuka", async function () {
            nuka_funtics_xchg_pair = await contract.Flex_approveXchgPair(ton, flex, "0x" + xchg_pair_keys.public);
            console.log("[Test] Approved NUKA/FUNT xchg pair = ", nuka_funtics_xchg_pair);
            console.log('[Test]: Xchg pair balance =', await contract.getBalance(ton, nuka_funtics_xchg_pair));
            const requests = await contract.Flex_getXchgPairListingRequests(ton, flex);
            console.log("Flex getWrapperListingRequests = ", requests);
            assert.equal(requests.length, 0);

            const requested_pair = await contract.Flex_getXchgTradingPair(ton, flex, nuka_root.addr, funtics_root.addr);
            assert.equal(requested_pair, nuka_funtics_xchg_pair);
        });
        it("Deploying empty funtics internal wallet for client1", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const wallet_keys = await ton.crypto.generate_random_sign_keys();
            const wallet_pubkey = "0x" + wallet_keys.public;
            funtics_wallet1_intern = await contract.FlexClient_deployEmptyFlexWallet(ton, client1,
                wallet_pubkey, 1e9, funtics_wrapper_tip3cfg);
            console.log('[Test]: funtics_wallet1_intern address =', funtics_wallet1_intern);
            console.log('[Test]: funtics_wallet1_intern balance =', await contract.getBalance(ton, funtics_wallet1_intern));
        });
        it("Deploying empty nuka internal wallet for client2", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const wallet_keys = await ton.crypto.generate_random_sign_keys();
            const wallet_pubkey = "0x" + wallet_keys.public;
            nuka_wallet2_intern = await contract.FlexClient_deployEmptyFlexWallet(ton, client2,
                wallet_pubkey, 1e9, nuka_wrapper_tip3cfg);
            console.log('[Test]: nuka_wallet2_intern address =', nuka_wallet2_intern);
            console.log('[Test]: nuka_wallet2_intern balance =', await contract.getBalance(ton, nuka_wallet2_intern));
        });
        it("Client1 selling 50 nuka tokens at price 72.60", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const deals_limit = await contract.Flex_getDealsLimit(ton, flex);
            const lend_finish_time = Math.floor(addMinutes(new Date(), 10) / 1000);
            const tons_value = 3e9;
            const price_xchg = await contract.FlexClient_deployPriceXchg(ton, client1,
                true, 72.60e9, 1e9, 50, 50, lend_finish_time, 1, deals_limit,
                tons_value, xchgPriceCode, nuka_wallet1_intern, funtics_wallet1_intern,
                nuka_wrapper_tip3cfg, funtics_wrapper_tip3cfg, notify_addr
            );
            console.log('[Test]: price_xchg: ', price_xchg);
            console.log('[Test]: price_xchg balance =', await contract.getBalance(ton, price_xchg));
        });
        it("Client2 buying 50 nuka tokens at price 72.60", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const deals_limit = await contract.Flex_getDealsLimit(ton, flex);
            const lend_finish_time = Math.floor(addMinutes(new Date(), 10) / 1000);
            const tons_value = 3e9;
            const price_xchg = await contract.FlexClient_deployPriceXchg(ton, client2,
                false, 72.60e9, 1e9, 50, 3630, lend_finish_time, 1, deals_limit,
                tons_value, xchgPriceCode, funtics_wallet2_intern, nuka_wallet2_intern,
                nuka_wrapper_tip3cfg, funtics_wrapper_tip3cfg, notify_addr
            );
            console.log('[Test]: price_xchg: ', price_xchg);
            console.log('[Test]: price_xchg balance =', await contract.getBalance(ton, price_xchg));

            const nuka1_details = await contract.Tip3Wallet_getDetails(ton, nuka_wallet1_intern);
            const funtics2_details = await contract.Tip3Wallet_getDetails(ton, funtics_wallet2_intern);
            console.log('[Test]: nuka1_details.lend_ownership: ', nuka1_details.lend_ownership);
            console.log('[Test]: funtics2_details.lend_ownership: ', funtics2_details.lend_ownership);
            assert.equal(nuka1_details.lend_ownership.length, 0);
            assert.equal(funtics2_details.lend_ownership.length, 0);
        });
        it("Client1 selling additional 50 nuka tokens at price 124.56", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            nuka1_details = await contract.Tip3Wallet_getDetails(ton, nuka_wallet1_intern);
            console.log('[Test]: nuka1_details.lend_ownership: ', nuka1_details.lend_ownership);
            assert.equal(nuka1_details.lend_ownership.length, 0);
            console.log('[Test]: notify_addr: ', notify_addr);
            const deals_limit = await contract.Flex_getDealsLimit(ton, flex);
            const lend_finish_time = Math.floor(addMinutes(new Date(), 10) / 1000);
            const tons_value = 3e9;
            const price_xchg = await contract.FlexClient_deployPriceXchg(ton, client1,
                true, 124.56e9, 1e9, 50, 50, lend_finish_time, 1, deals_limit,
                tons_value, xchgPriceCode, nuka_wallet1_intern, funtics_wallet1_intern,
                nuka_wrapper_tip3cfg, funtics_wrapper_tip3cfg, notify_addr
            );
            console.log('[Test]: price_xchg (124.56): ', price_xchg);
            console.log('[Test]: price_xchg (124.56) balance =', await contract.getBalance(ton, price_xchg));

            nuka1_details = await contract.Tip3Wallet_getDetails(ton, nuka_wallet1_intern);
            console.log('[Test]: nuka1_details.lend_ownership: ', nuka1_details.lend_ownership);
            assert.equal(nuka1_details.lend_ownership.length, 1);
        });
        it("Client1 cancelling additional sell", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const deals_limit = await contract.Flex_getDealsLimit(ton, flex);
            const lend_finish_time = Math.floor(addMinutes(new Date(), 10) / 1000);
            const tons_value = 3e9;
            await contract.FlexClient_cancelXchgOrder(ton, client1,
                true, 124.56e9, 1e9, /*min_amount*/1, deals_limit, tons_value, xchgPriceCode,
                nuka_wrapper_tip3cfg, funtics_wrapper_tip3cfg, notify_addr
            );
            const nuka1_details = await contract.Tip3Wallet_getDetails(ton, nuka_wallet1_intern);
            console.log('[Test]: nuka1_details.lend_ownership: ', nuka1_details.lend_ownership);
            assert.equal(nuka1_details.lend_ownership.length, 0);
        });
        it("Check internal wallet balances after deal", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const nuka_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet1_intern);
            console.log('internal NUKA wallet1 tokens: ', nuka_wallet1_balance);
            const nuka_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet2_intern);
            console.log('internal NUKA wallet2 tokens: ', nuka_wallet2_balance);
            const funtics_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet1_intern);
            console.log('internal FUNT wallet1 tokens: ', funtics_wallet1_balance);
            const funtics_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet2_intern);
            console.log('internal FUNT wallet2 tokens: ', funtics_wallet2_balance);

            assert.equal(nuka_wallet1_balance, 500 - 50);
            assert.equal(nuka_wallet2_balance, 50);
            assert.equal(funtics_wallet1_balance, 3630);
            assert.equal(funtics_wallet2_balance, 10000 - 3630);
        });
        it("Transferring internal tokens back to external", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            await contract.FlexClient_burnWallet(ton, client1, 1e9, "0x" + nuka_wallet1.keys.public, null_addr, nuka_wallet1_intern);
            const nuka_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet1.addr);
            console.log('external NUKA wallet1 tokens: ', nuka_wallet1_balance);
            
            await contract.FlexClient_burnWallet(ton, client1, 1e9, "0x" + funtics_wallet1.keys.public, null_addr, funtics_wallet1_intern);
            const funtics_wallet1_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet1.addr);
            console.log('external FUNT wallet1 tokens: ', funtics_wallet1_balance);
            
            await contract.FlexClient_burnWallet(ton, client2, 1e9, "0x" + nuka_wallet2.keys.public, null_addr, nuka_wallet2_intern);
            const nuka_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, nuka_wallet2.addr);
            console.log('external NUKA wallet2 tokens: ', nuka_wallet2_balance);
            
            await contract.FlexClient_burnWallet(ton, client2, 1e9, "0x" + funtics_wallet2.keys.public, null_addr, funtics_wallet2_intern);
            const funtics_wallet2_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet2.addr);
            console.log('external FUNT wallet2 tokens: ', funtics_wallet2_balance);

            assert.equal(nuka_wallet1_balance, 1000 - 50);
            assert.equal(nuka_wallet2_balance, 100 + 50);
            assert.equal(funtics_wallet1_balance, 100 + 3630);
            assert.equal(funtics_wallet2_balance, 20000 - 3630);
        });
        it("Transferring extra tons from Flex root to client 1", async function () {
            if (!deployForSolidityStyleDebots)
                return;
            const flex_balance = await contract.getBalance(ton, flex.addr);
            console.log('Flex root tons balance: ', flex_balance);
            assert(flex_balance > 1);
            await contract.Flex_transfer(ton, flex, client1.addr, Math.round(flex_balance * 1e9 - 1e9));
            const new_flex_balance = await contract.getBalance(ton, flex.addr);
            console.log('Flex root tons balance after transfer: ', new_flex_balance);
            assert(new_flex_balance <= 1);
            console.log('client1 tons balance after transfer: ', await contract.getBalance(ton, client1.addr));
        });
        it("Print env variables for testing", async function () {
            console.log('export FLEX_ADDR=%s', flex.addr.trim());

            if (deployForSolidityStyleDebots) {
                console.log('export CLIENT1_ADDR=%s', client1.addr.trim());
                console.log('export CLIENT2_ADDR=%s', client2.addr.trim());
            } else {
                console.log('export PROXY1_ADDR=%s', proxy1.addr.trim());
                console.log('export PROXY2_ADDR=%s', proxy2.addr.trim());
            }
            console.log('export NUKA1_ADDR=%s', nuka_wallet1.addr.trim());
            console.log('export NUKA2_ADDR=%s', nuka_wallet2.addr.trim());
            console.log('export FUNT1_ADDR=%s', funtics_wallet1.addr.trim());
            console.log('export FUNT2_ADDR=%s', funtics_wallet2.addr.trim());
        });
    });
});

