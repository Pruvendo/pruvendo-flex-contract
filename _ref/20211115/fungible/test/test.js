const assert = require('assert');
const {TonClient, abiJson, abiContract, signerKeys, signerNone} = require('@tonclient/core');
const {libNode} = require("@tonclient/lib-node");
const contract = require('./common.js');
const { hexToUtf8, utf8ToHex, stringToArray, arrayToString, delay, fixLeadingZero } = require('./utils.js')
const conf = contract.readConfig();

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

describe('RootTokenContract test', function () {
    this.timeout(240000);
    let ton;
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
        };
        TonClient.useBinaryLibrary(libNode);
        ton = new TonClient(config);
    });

    // Proxy-contract TestRootOwner managing RootTokenContract by internal messages.
    // While providing external interface (by user pubkey)
    describe('Root internal ownership check', function () {
        let rootCode;
        let walletCode;
        let rootOwner;
        let root;

        before(async function () {
            rootCode = await contract.getCodeFromImage(ton, contract.rootPackage.imageBase64);
            walletCode = await contract.getCodeFromImage(ton, contract.walletPackage.imageBase64);
            rootOwner = await contract.deployRootOwner(ton, conf,
              1e9, rootCode, walletCode, 'pepsi', 'pep', 0);
            console.log('[Test]: rootOwner balance =', await contract.getBalance(ton, rootOwner.addr));

            wallet1 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet1 keys:`, wallet1.keys);
        });
        it("check getTokenRoot", async function () {
            console.log('[Test]: get token root address...');
            let rootAddress = await contract.TestRootOwner_getTokenRoot(ton, rootOwner);
            console.log('response: rootAddress = ', rootAddress);
            root = { addr: rootAddress, keys: "" };
        });
        it("check getWalletCodeHash", async function () {
            console.log('[Test]: getWalletCodeHash...');
            let hash = await contract.getWalletCodeHash(ton, root);
            console.log('response: hash = ', hash);
        });
        it("check name", async function () {
            console.log('[Test]: get name...');
            let name = await contract.getName(ton, root);
            console.log('response: name = ', name);
            assert.equal(name, "pepsi");
        });
        it("check symbol", async function () {
            console.log('[Test]: get symbol...');
            let symbol = await contract.getSymbol(ton, root);
            console.log('response: symbol = ', symbol);
            assert.equal(symbol, "pep");
        });
        it("check decimals", async function () {
            console.log('[Test]: get decimals...');
            let decimals = await contract.getDecimals(ton, root);
            console.log('response: decimals = ', decimals);
            assert.equal(decimals, 0);
        });
        it("check total supply", async function () {
            console.log('[Test]: get total supply...');
            let count = await contract.getTotalSupply(ton, root);
            console.log('response: total supply = ', count);
            assert.equal(count, 0);
        });
        it("check mint", async function () {
            console.log('[Test]: minting 1000 tokens...');
            await contract.TestRootOwner_mint(ton, rootOwner, 2e8, 1000);
            let count = await contract.getTotalSupply(ton, root);
            console.log('response: total supply = ', count);
            assert.equal(count, 1000);
        });
        it("check deployWallet", async function () {
            console.log('[Test]: deploying wallet through TestRootOwner...');
            let deploy1 = await contract.TestRootOwner_deployWallet(ton, rootOwner,
              4e8, "0x" + wallet1.keys.public, null, 15, 2e8);
            console.log('[Test]: deploy1 =', deploy1);
            wallet1.addr = deploy1;

            let wallet_tokens = await contract.Wallet_getBalance(ton, wallet1.addr);
            console.log('[Test]: wallet_tokens =', wallet_tokens);
            assert.equal(wallet_tokens, 15);
        });
        it("check total granted", async function () {
            console.log('[Test]: get total granted...');
            let count = await contract.getTotalGranted(ton, root);
            console.log('response: total granted = ', count);
            assert.equal(count, 15);
        });
        it("check grant", async function () {
            console.log('[Test]: granting 85 tokens...');
            await contract.TestRootOwner_grant(ton, rootOwner, 2e8, wallet1.addr, 85, 1e8);
            let count = await contract.getTotalGranted(ton, root);
            console.log('response: total granted = ', count);
            assert.equal(count, 100);
        });
    });

    describe('RootTokenContract construct', function () {
        let walletCode;
        let pepsi_root;
        let wallet1;
        let wallet2;
        let wallet3;
        let wallet4;

        before(async function () {
            walletCode = await contract.getCodeFromImage(ton, contract.walletPackage.imageBase64);
            pepsi_root = await contract.deployRoot(ton, conf, 'pepsi', 'pep', 0, walletCode, 777);
            console.log('[Test]: pepsi_root balance =', await contract.getBalance(ton, pepsi_root.addr));
            
            wallet1 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet1 keys:`, wallet1.keys);
            
            wallet2 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet2 keys:`, wallet2.keys);
            
            wallet3 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet3 keys:`, wallet3.keys);

            wallet4 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet4 keys:`, wallet4.keys);
        });
        it("check getWalletCodeHash", async function () {
            console.log('[Test]: getWalletCodeHash...');
            let hash = await contract.getWalletCodeHash(ton, pepsi_root);
            console.log('response: hash = ', hash);
        });
        it("check name", async function () {
            console.log('[Test]: get name...');
            let name = await contract.getName(ton, pepsi_root);
            console.log('response: name = ', name);
            assert.equal(name, "pepsi");
        });
        it("check symbol", async function () {
            console.log('[Test]: get symbol...');
            let symbol = await contract.getSymbol(ton, pepsi_root);
            console.log('response: symbol = ', symbol);
            assert.equal(symbol, "pep");
        });
        it("check decimals", async function () {
            console.log('[Test]: get decimals...');
            let decimals = await contract.getDecimals(ton, pepsi_root);
            console.log('response: decimals = ', decimals);
            assert.equal(decimals, 0);
        });
        it("check root key", async function () {
            console.log('[Test]: get root key...');
            let root_key = await contract.getRootKey(ton, pepsi_root);
            console.log('response: root key = ', root_key);
            assert.equal(fixLeadingZero(root_key), "0x" + pepsi_root.keys.public);
        });
        it("check total supply", async function () {
            console.log('[Test]: get total supply...');
            let count = await contract.getTotalSupply(ton, pepsi_root);
            console.log('response: total supply = ', count);
            assert.equal(count, 777);
        });
        it("check total granted", async function () {
            console.log('[Test]: get total granted...');
            let count = await contract.getTotalGranted(ton, pepsi_root);
            console.log('response: total granted = ', count);
            assert.equal(count, 0);
        });
        it("check wallet code", async function () {
            console.log('[Test]: get wallet code...');
            let code = await contract.getWalletCode(ton, pepsi_root);
            hashCodeRequested = await contract.getHashCode(ton, code);
            hashCodeOriginal = await contract.getHashCode(ton, walletCode);
            assert.equal(hashCodeRequested.hash, hashCodeOriginal.hash);
        });
        it("check wallet deploy and address", async function () {
            console.log('[Test]: get wallet address for pubkey =', wallet1.keys.public);
            let address = await contract.getWalletAddress(ton, pepsi_root, "0x" + wallet1.keys.public, null);
            console.log('response: wallet calculated address = ', address);
            let deployedAddress = await contract.deployWallet(ton, pepsi_root, "0x" + wallet1.keys.public, null, 77, 1000000000);
            console.log('response: wallet deployed address = ', deployedAddress);
            assert.equal(address, deployedAddress);
            wallet1.addr = deployedAddress;
            
            //await sleep(10000);

            let count = await contract.getTotalGranted(ton, pepsi_root);
            assert.equal(count, 77);

            console.log('[Test]: pepsi_root gas balance =', await contract.getBalance(ton, pepsi_root.addr));
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));

            let name = await contract.Wallet_getName(ton, wallet1.addr);
            assert.equal(name, "pepsi");
            let symbol = await contract.Wallet_getSymbol(ton, wallet1.addr);
            assert.equal(symbol, "pep");
            let decimals = await contract.Wallet_getDecimals(ton, wallet1.addr);
            assert.equal(decimals, 0);
            let wallet_tokens = await contract.Wallet_getBalance(ton, wallet1.addr);
            assert.equal(wallet_tokens, 77);
            let wallet_key = await contract.Wallet_getWalletKey(ton, wallet1.addr);
            assert.equal(fixLeadingZero(wallet_key), "0x" + wallet1.keys.public);
            let root_addr = await contract.Wallet_getRootAddress(ton, wallet1.addr);
            assert.equal(root_addr, pepsi_root.addr);
            let allowance = await contract.Wallet_allowance(ton, wallet1.addr);
            console.log('response: allowance = ', allowance);
            assert.equal(allowance.spender, '0:0000000000000000000000000000000000000000000000000000000000000000');
            assert.equal(allowance.remainingTokens, 0);

            const wallet_code_hash = await contract.Wallet_getCodeHash(ton, wallet1.addr);
            console.log('response: wallet.code_hash = ', wallet_code_hash);
            const hashCodeOriginal = await contract.getHashCode(ton, walletCode);
            assert.equal(wallet_code_hash, "0x" + hashCodeOriginal.hash);

            console.log('[Test]: Now granting 23 pepsi tokens to wallet1...');
            await contract.grant(ton, pepsi_root, wallet1.addr, 23, 40000000);
            //await sleep(10000);

            console.log('[Test]: pepsi_root gas balance =', await contract.getBalance(ton, pepsi_root.addr));
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));

            assert.equal(await contract.getTotalGranted(ton, pepsi_root), 100);
            assert.equal(await contract.getTotalSupply(ton, pepsi_root), 777);
            assert.equal(await contract.Wallet_getBalance(ton, wallet1.addr), 100);

            console.log('[Test]: Now minting 1000');
            await contract.mint(ton, pepsi_root, 1000);
            //await sleep(10000);
            assert.equal(await contract.getTotalGranted(ton, pepsi_root), 100);
            assert.equal(await contract.getTotalSupply(ton, pepsi_root), 1777);
        });
        it("Deploy empty wallet2", async function () {
            console.log('[Test]: get wallet2 address for pubkey =', wallet2.keys.public);
            let address = await contract.getWalletAddress(ton, pepsi_root, "0x" + wallet2.keys.public, null);
            console.log('response: wallet2 calculated address = ', address);
            let deployedAddress =
              await contract.deployWallet(ton, pepsi_root, "0x" + wallet2.keys.public, null, 0, 1000000000);
            console.log('response: wallet2 deployed address = ', deployedAddress);
            //await sleep(10000);
            wallet2.addr = deployedAddress;
            assert.equal(address, deployedAddress);
            assert.equal(await contract.Wallet_getBalance(ton, deployedAddress), 0);
            console.log('[Test]: wallet2 balance =', await contract.getBalance(ton, deployedAddress));
        });
        it("check wallet1 -> wallet2 transfer", async function () {
            let wallet2_address = await contract.getWalletAddress(ton, pepsi_root, "0x" + wallet2.keys.public, null);
            console.log('response: wallet2 calculated address = ', wallet2_address);
            assert.equal(wallet2_address, wallet2.addr);
            await contract.Wallet_transfer(ton, wallet1, wallet1.addr, wallet2_address, 5, 160000000, false);
            //await sleep(10000);
            console.log('transfer ok');
            let wallet1_balance = await contract.Wallet_getBalance(ton, wallet1.addr);
            console.log('wallet1 token balance = ', wallet1_balance);
            let wallet2_balance = await contract.Wallet_getBalance(ton, wallet2.addr);
            console.log('wallet2 token balance = ', wallet2_balance);
            
            assert.equal(wallet1_balance, 77 + 23 - 5);
            assert.equal(wallet2_balance, 5);
            
            console.log('[Test]: pepsi_root gas balance =', await contract.getBalance(ton, pepsi_root.addr));
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 gas balance =', await contract.getBalance(ton, wallet2.addr));
        });
        it("Deploy empty wallet3", async function () {
            console.log('[Test]: get wallet3 address for pubkey =', wallet3.keys.public);
            let address = await contract.getWalletAddress(ton, pepsi_root, "0x" + wallet3.keys.public, null);
            console.log('response: wallet3 calculated address = ', address);
            let deployedAddress =
              await contract.deployWallet(ton, pepsi_root, "0x" + wallet3.keys.public, null, 0, 1000000000);
            console.log('response: wallet3 deployed address = ', deployedAddress);
            //await sleep(10000);
            wallet3.addr = deployedAddress;
            assert.equal(address, deployedAddress);
            assert.equal(await contract.Wallet_getBalance(ton, deployedAddress), 0);
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, deployedAddress));
        });
        it("Test allowance for wallet3 from wallet1", async function () {
            console.log('[Test]: approving allowance for wallet3.addr =', wallet3.addr);
            await contract.Wallet_approve(ton, wallet1, wallet3.addr, 0, 15);
            let allowance = await contract.Wallet_allowance(ton, wallet1.addr);
            console.log('response: allowance = ', allowance);
            assert.equal(allowance.spender, wallet3.addr);
            assert.equal(allowance.remainingTokens, 15);
            
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
            
            console.log('[Test]: requesting transferFrom from wallet1 into wallet3');
            await contract.Wallet_transferFrom(ton, wallet3, wallet3.addr, wallet1.addr, wallet3.addr, 7, 200000000);
            // await sleep(20000);
            allowance = await contract.Wallet_allowance(ton, wallet1.addr);
            console.log('response: allowance = ', allowance);
            assert.equal(allowance.spender, wallet3.addr);
            assert.equal(allowance.remainingTokens, 15 - 7);
            assert.equal(await contract.Wallet_getBalance(ton, wallet1.addr), 77 + 23 - 5 - 7);
            assert.equal(await contract.Wallet_getBalance(ton, wallet3.addr), 7);
            
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
            
            console.log('[Test]: requesting additional transferFrom from wallet1 into wallet3');
            await contract.Wallet_transferFrom(ton, wallet3, wallet3.addr, wallet1.addr, wallet3.addr, 8, 200000000);
            //await sleep(20000);
            allowance = await contract.Wallet_allowance(ton, wallet1.addr);
            console.log('response: allowance = ', allowance);
            assert.equal(allowance.spender, wallet3.addr);
            assert.equal(allowance.remainingTokens, 0);
            assert.equal(await contract.Wallet_getBalance(ton, wallet3.addr), 15);
            
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
        });
        it("transferToRecipient to wallet4", async function () {
            let wallet4_address = await contract.getWalletAddress(ton, pepsi_root, "0x" + wallet4.keys.public, null);
            console.log('response: wallet4 calculated address = ', wallet4_address);
            wallet4.addr = wallet4_address;

            let wallet4_pub = "0x" + wallet4.keys.public;
            await contract.Wallet_transferToRecipient(
              ton, wallet1, wallet1.addr, wallet4_pub, null,
              await contract.Wallet_getBalance(ton, wallet1.addr),
              200000000, true, false);
            await contract.Wallet_transferToRecipient(
              ton, wallet2, wallet2.addr, wallet4_pub, null,
              await contract.Wallet_getBalance(ton, wallet2.addr),
              200000000, true, false);
            await contract.Wallet_transferToRecipient(
              ton, wallet3, wallet3.addr, wallet4_pub, null,
              await contract.Wallet_getBalance(ton, wallet3.addr),
              200000000, true, false);
              
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 gas balance =', await contract.getBalance(ton, wallet2.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
            console.log('[Test]: wallet4 gas balance =', await contract.getBalance(ton, wallet4.addr));
            
            console.log('[Test]: wallet1 token balance =', await contract.Wallet_getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 token balance =', await contract.Wallet_getBalance(ton, wallet2.addr));
            console.log('[Test]: wallet3 token balance =', await contract.Wallet_getBalance(ton, wallet3.addr));
            console.log('[Test]: wallet4 token balance =', await contract.Wallet_getBalance(ton, wallet4.addr));
        });
        it("Destroy wallets", async function () {
            console.log('[Test]: pepsi_root gas balance =', await contract.getBalance(ton, pepsi_root.addr));
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 gas balance =', await contract.getBalance(ton, wallet2.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
            
            console.log('[Test]: wallet1 token balance =', await contract.Wallet_getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 token balance =', await contract.Wallet_getBalance(ton, wallet2.addr));
            console.log('[Test]: wallet3 token balance =', await contract.Wallet_getBalance(ton, wallet3.addr));
            
            // Destroy wallets and send remaining native funds to the root
            await contract.Wallet_destroy(ton, wallet1, pepsi_root.addr);
            await contract.Wallet_destroy(ton, wallet2, pepsi_root.addr);
            await contract.Wallet_destroy(ton, wallet3, pepsi_root.addr);

            console.log('[Test]: pepsi_root gas balance =', await contract.getBalance(ton, pepsi_root.addr));
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            console.log('[Test]: wallet2 gas balance =', await contract.getBalance(ton, wallet2.addr));
            console.log('[Test]: wallet3 gas balance =', await contract.getBalance(ton, wallet3.addr));
        });
        /*
        it("Grant to non-existent wallet (bounced message check)", async function () {
            let wallet_unknown = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet_unknown keys:`, wallet_unknown.keys);
            wallet_unknown.addr = await contract.getWalletAddress(ton, pepsi_root, 0, "0x" + wallet_unknown.keys.public);
            console.log('response: wallet_unknown calculated address = ', wallet_unknown.addr);

            // TotalGranted should not be changed by `grant` call to inactive address
            assert.equal(await contract.getTotalGranted(ton, pepsi_root), 100);
            await contract.grant(ton, pepsi_root, wallet_unknown.addr, 250, 40000000);
            await sleep(20000);
            assert.equal(await contract.getTotalGranted(ton, pepsi_root), 100);
        });
        it("Transfer to non-existent wallet (bounced message check)", async function () {
            let wallet_unknown2 = { addr: "", keys: await ton.crypto.generate_random_sign_keys() };
            console.log(`[Test] wallet_unknown2 keys:`, wallet_unknown2.keys);
            wallet_unknown2.addr = await contract.getWalletAddress(ton, pepsi_root, 0, "0x" + wallet_unknown2.keys.public);
            console.log('response: wallet_unknown2 calculated address = ', wallet_unknown2.addr);
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            // We must see equal wallet1 token balance before and after failed transfer
            assert.equal(await contract.Wallet_getBalance(ton, wallet1.addr), 77 + 23 - 5 - 7 - 8);
            await contract.Wallet_transfer(ton, wallet1, wallet1.addr, wallet_unknown2.addr, 5, 40000000, false);
            console.log('[Test]: wallet1 gas balance =', await contract.getBalance(ton, wallet1.addr));
            await sleep(20000);
            assert.equal(await contract.Wallet_getBalance(ton, wallet1.addr), 77 + 23 - 5 - 7 - 8);
        });*/
    });
});

