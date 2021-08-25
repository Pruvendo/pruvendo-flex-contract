const assert = require('assert');
const {TONClient} = require('ton-client-node-js');
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

describe('FLeX Contracts test', function () {
    this.timeout(540000);
    let ton;
    before(async function () {
        const config = {
            defaultWorkchain: 0,
            servers: [conf.url],
            log_verbose: false,
            messageExpirationTimeout: 220000000,
            messageProcessingTimeout: 220000000,
            waitForTimeout: 220000000
        }
        ton = await TONClient.create(config);
    });
    describe('FLeX deploy', function () {
        let deployForSolidityStyleDebots = false;

        let flex;
        let proxy1;
        let proxy2;

        let pairCode;
        let client1;
        let client2;

        let root;
        let wallet1;
        let wallet2;

        let funtics_wallet1;
        let funtics_wallet2;

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

            flex = await contract.deployFLeX(
              ton, conf,
              pairCode.codeBase64, priceCode.codeBase64,
              xchgPairCode.codeBase64, xchgPriceCode.codeBase64,
              { transfer_tip3: 2e8,
                return_ownership: 2e8,
                trading_pair_deploy: 1e9,
                order_answer: 1e8,
                process_queue: 4e8,
                send_notify: 1e8
              },
              1, // min_amount
              20, // deals_limit
              "0:48e6891227df6a7e29e342e5ebced85ccefec9d0f842031c922a38c691d61af9" // notify addr
              );
            console.log('[Test]: flex balance =', await contract.getBalance(ton, flex.addr));
            pairCode = await contract.FLeX_getTradingPairCode(ton, flex);
        });
        it("FLeX isFullyInitialized", async function () {
            assert(await contract.FLeX_isFullyInitialized(ton, flex));
        });
        it("Deploy client1", async function () {
            if (deployForSolidityStyleDebots) {
              client1 = await contract.deployFLeXClient(ton, conf, pairCode);
              console.log('[Test]: client1 balance =', await contract.getBalance(ton, client1.addr));
            }
        });
        it("Deploy client2", async function () {
            if (deployForSolidityStyleDebots) {
              client2 = await contract.deployFLeXClient(ton, conf, pairCode);
              console.log('[Test]: client2 balance =', await contract.getBalance(ton, client2.addr));
            }
        });
        it("Tip3 deploy", async function () {
            walletCode = await contract.getCodeFromImage(ton, contract.tip3WalletPackage.imageBase64);
            root = await contract.deployTip3Root(ton, conf, "NUKA caps", "NUKA", 0, walletCode.codeBase64, 2000);
            console.log('[Test]: tip3 root balance =', await contract.getBalance(ton, root.addr));
            const walletCodeHash = await contract.Tip3Root_getWalletCodeHash(ton, root);
            console.log('[Test]: tip3 wallet code hash =', walletCodeHash);
        });
        it("wallet1 deploy", async function () {
            const owner_addr = deployForSolidityStyleDebots ? client1.addr : proxy1.addr;
            const internal_owner = owner_addr.replace(/^(0\:)/,"0x");
            console.log('[Test]: wallet1 internal_owner =', internal_owner);
            wallet1 = await contract.Tip3Root_deployWallet(ton, conf, root, 0, internal_owner, 1000, 5000000000);
            console.log('wallet1 address = ', wallet1.addr);
            console.log('[Test]: wallet1 balance =', await contract.getBalance(ton, wallet1.addr));
            const wallet1_balance = await contract.Tip3Wallet_getBalance(ton, wallet1);
            console.log('[Test]: wallet1 tokens balance =', wallet1_balance);
            assert.equal(wallet1_balance, 1000);
        });
        it("wallet2 deploy", async function () {
            const owner_addr = deployForSolidityStyleDebots ? client2.addr : proxy2.addr;
            const internal_owner = owner_addr.replace(/^(0\:)/,"0x");
            console.log('[Test]: wallet2 internal_owner =', internal_owner);
            wallet2 = await contract.Tip3Root_deployWallet(ton, conf, root, 0, internal_owner, 100, 5000000000);
            console.log('wallet2 address = ', wallet2.addr);
            console.log('[Test]: wallet2 balance =', await contract.getBalance(ton, wallet2.addr));
            const wallet2_balance = await contract.Tip3Wallet_getBalance(ton, wallet2);
            console.log('[Test]: wallet2 tokens balance =', wallet2_balance);
            assert.equal(wallet2_balance, 100);
        });
        it("Tip3 funtics deploy", async function () {
            walletCode = await contract.getCodeFromImage(ton, contract.tip3WalletPackage.imageBase64);
            root = await contract.deployTip3Root(ton, conf, "Funtics", "FUNT", 0, walletCode.codeBase64, 20000);
            console.log('[Test]: tip3 funtics root balance =', await contract.getBalance(ton, root.addr));
            const walletCodeHash = await contract.Tip3Root_getWalletCodeHash(ton, root);
            console.log('[Test]: tip3 funtics wallet code hash =', walletCodeHash);
        });
        it("funtics wallet1 deploy", async function () {
            const owner_addr = deployForSolidityStyleDebots ? client1.addr : proxy1.addr;
            const internal_owner = owner_addr.replace(/^(0\:)/,"0x");
            // console.log('[Test]: FUNT wallet1 internal_owner =', internal_owner);
            funtics_wallet1 = await contract.Tip3Root_deployWallet(ton, conf, root, 0, internal_owner, 100, 5000000000);
            console.log('FUNT wallet1 address = ', funtics_wallet1.addr);
            console.log('[Test]: FUNT wallet1 balance =', await contract.getBalance(ton, funtics_wallet1.addr));
            const wallet1_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet1);
            console.log('[Test]: FUNT wallet1 tokens balance =', wallet1_balance);
            assert.equal(wallet1_balance, 100);
        });
        it("funtics wallet2 deploy", async function () {
            const owner_addr = deployForSolidityStyleDebots ? client2.addr : proxy2.addr;
            const internal_owner = owner_addr.replace(/^(0\:)/,"0x");
            // console.log('[Test]: FUNT wallet2 internal_owner =', internal_owner);
            funtics_wallet2 = await contract.Tip3Root_deployWallet(ton, conf, root, 0, internal_owner, 10000, 5000000000);
            console.log('FUNT wallet2 address = ', funtics_wallet2.addr);
            console.log('[Test]: FUNT wallet2 balance =', await contract.getBalance(ton, funtics_wallet2.addr));
            const wallet2_balance = await contract.Tip3Wallet_getBalance(ton, funtics_wallet2);
            console.log('[Test]: FUNT wallet2 tokens balance =', wallet2_balance);
            assert.equal(wallet2_balance, 10000);
        });
    });
});

