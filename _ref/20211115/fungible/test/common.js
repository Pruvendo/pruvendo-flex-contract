var fs = require('fs');
const os = require('os');
const path = require('path');
const {abiJson, abiContract, signerKeys, signerNone} = require('@tonclient/core');

const { hexToUtf8, utf8ToHex, stringToArray, arrayToString, delay, fixLeadingZero } = require('./utils.js')

const ContractError = {
    message_sender_is_not_my_owner: 100,
    not_enough_balance            : 101,
    wrong_bounced_header          : 102,
    wrong_bounced_args            : 103
}
const nodeSeGiverAddress = '0:841288ed3b55d9cdafa806807f02a0ae0c169aa5edfe88a789a6482429756a94';
const nodeSeGiverAbi =
    {
        "ABI version": 1,
        "functions": [
            {
                "name": "constructor",
                "inputs": [],
                "outputs": []
            },
            {
                "name": "sendGrams",
                "inputs": [
                    {"name": "dest", "type": "address"},
                    {"name": "amount", "type": "uint64"}
                ],
                "outputs": []
            }
        ],
        "events": [],
        "data": []
    };

const readGiverKeys = () => {
    let keysPath = path.resolve(os.homedir(), 'giver_keys.json');
    return JSON.parse(fs.readFileSync(keysPath));
}

const readConfig = () => {
    var conf = JSON.parse(fs.readFileSync("./config.json"));
    if (!conf.localNode) {
        conf.url = conf.urlWeb;
        conf.giverKeys = readGiverKeys();
    }
    return conf;
}

const testnetGiverAddress = '0:653b9a6452c7a982c6dc92b2da9eba832ade1c467699ebb3b43dca6d77b780dd';
const testnetGiverAbi =
    {
        "ABI version": 2,
        "header": ["time"],
        "functions": [
            {
                "name": "grant",
                "inputs": [
                    {"name":"addr","type":"address"}
                ],
                "outputs": []
            },
            {
                "name": "constructor",
                "inputs": [],
                "outputs": []
            }
        ],
        "data": [],
        "events": []
    };

const loadPackage = (name) => {
    var contract = {};
    contract.abi = JSON.parse(fs.readFileSync('../' + name + '.abi', 'utf8'));
    contract.imageBase64 = fs.readFileSync('../' + name + '.tvc').toString('base64');
    return contract;
};

const rootPackage = loadPackage('RootTokenContract');
const walletPackage = loadPackage('TONTokenWallet');
const walletOwnerPackage = loadPackage('TestWalletOwner');
const rootOwnerPackage = loadPackage('TestRootOwner');

const emptyParams = {};

async function waitForResultXN(ton, result) {
  await ton.net.query_transaction_tree({in_msg: result.transaction.in_msg, timeout: 60000 * 5});
}

async function waitForFinalExternalAnswer(ton, result, abi, function_name, N) {
    let orig_addr = result.transaction.account_addr;
    let externalMessages = [];
    const tree = await ton.net.query_transaction_tree({
        in_msg: result.transaction.in_msg,
        abi_registry: [ abiContract(abi) ],
        timeout: 60000 * 5
    });
    for (const msg of tree.messages) {
      //console.log('cur msg = ', msg);
      if ((msg.src == orig_addr) && (msg.dst.length === 0)) {
        externalMessages.push(msg);
      }
    }
    return externalMessages[0].decoded_body.value;
}

async function deploy(ton, conf, contract, keys, options = {}) {
    const msg = await ton.abi.encode_message({
        abi: abiContract(contract.abi),
        call_set: { function_name: "constructor", input: options },
        deploy_set: { tvc: contract.imageBase64 },
        signer: keys ? signerKeys(keys) : signerNone(),
    });
    const futureAddress = msg.address;

    if (conf.localNode) {
        const result = await ton.processing.process_message({
            send_events: false,
            message_encode_params: {
                address: nodeSeGiverAddress,
                abi: abiContract(nodeSeGiverAbi),
                call_set: {
                    function_name: 'sendGrams',
                    input: {dest: futureAddress, amount: 20_000_000_000}
                },
                signer: signerNone()
            }
        });
        await waitForResultXN(ton, result);
    } else {
        const result = await ton.processing.process_message({
            send_events: false,
            message_encode_params: {
                address: testnetGiverAddress,
                abi: abiContract(testnetGiverAbi),
                call_set: {
                    function_name: 'grant',
                    input: {addr: futureAddress}
                },
                signer: signerNone()
            }
        });
        await waitForResultXN(ton, result);
    }
    console.log("[Test] giver sent crystals to ", futureAddress);
    const txn = await ton.processing.send_message({
        abi: abiContract(contract.abi),
        message: msg.message,
        send_events: false
    });
    await ton.processing.wait_for_transaction({
        message: msg.message,
        send_events: false,
        shard_block_id: txn.shard_block_id
    });
    return futureAddress;
}

async function Root_setWalletCode(ton, root, wallet_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: root.addr,
            abi: abiContract(rootPackage.abi),
            call_set: {
                function_name: 'setWalletCode',
                input: {_answer_id: "0x0", wallet_code: wallet_code}
            },
            signer: signerKeys(root.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = parseInt(result.transaction.compute.gas_used);
    console.log('[set_root_code] gas used:', gas);
}
async function deployRoot(ton, conf, name, symbol, decimals, walletCode, totalSupply) {
    const rootKeys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] root keys:`, rootKeys);

    let ctorParams = {
        name: utf8ToHex(name), symbol: utf8ToHex(symbol), decimals: decimals,
        root_pubkey: '0x' + rootKeys.public, root_owner: null,
        total_supply: totalSupply,
    };

    const rootAddress = await deploy(ton, conf, rootPackage, rootKeys, ctorParams);
    console.log('[Test]: root address', rootAddress);

    let root = {addr: rootAddress, keys: rootKeys};

    await Root_setWalletCode(ton, root, walletCode);
    return root;
}

async function TestRootOwner_set_root_code(ton, rootOwner, root_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'set_root_code',
                input: {root_code: root_code}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[set_root_code] gas used:', gas);
}
async function TestRootOwner_set_wallet_code(ton, rootOwner, wallet_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'set_wallet_code',
                input: {wallet_code: wallet_code}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[set_wallet_code] gas used:', gas);
}
async function TestRootOwner_deployRoot(ton, rootOwner, name, symbol, decimals, crystalsToRoot) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'deployRoot',
                input: {name: utf8ToHex(name), symbol: utf8ToHex(symbol), decimals: decimals,
                        crystalsToRoot: crystalsToRoot}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[deployRoot] gas used:', gas);
}

async function deployRootOwner(ton, conf, crystalsToRoot, rootCode, walletCode, name, symbol, decimals) {
    const rootKeys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] root keys:`, rootKeys);

    let ctorParams = {
        owner_key: '0x' + rootKeys.public
    };

    const rootOwnerAddress = await deploy(ton, conf, rootOwnerPackage, rootKeys, ctorParams);
    console.log('[Test]: root owner address', rootOwnerAddress);
    let root_owner = {addr: rootOwnerAddress, keys: rootKeys};

    await TestRootOwner_set_root_code(ton, root_owner, rootCode);
    await TestRootOwner_set_wallet_code(ton, root_owner, walletCode);
    await TestRootOwner_deployRoot(ton, root_owner, name, symbol, decimals, crystalsToRoot);
    return root_owner;
}

async function deployWalletIndependent(ton, conf, name, symbol, decimals, root_public_key, root_address, code) {
    const walletKeys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] independent wallet keys:`, walletKeys);
    
    let ctorParams = {
        name: utf8ToHex(name), symbol: utf8ToHex(symbol), decimals: decimals,
        root_public_key: root_public_key, wallet_public_key: "0x" + walletKeys.public,
        root_address: root_address, code: code,
    };

    const walletAddress = await deploy(ton, conf, walletPackage, walletKeys, ctorParams);
    console.log('[Test]: independent wallet address', walletAddress);

    return {addr: walletAddress, keys: walletKeys};
}

async function getGas(ton, transId) {
    const result = (await ton.net.query_collection({
        collection: 'transactions',
        filter: {id: {eq: transId}},
        result: 'compute { gas_used }'
    })).result;
    if (result.length) {
        return parseInt(result[0].compute.gas_used);
    }
    return null;
}

async function getBalance(ton, addr) {
    const queryResult = (await ton.net.query_collection({
        collection: 'accounts',
        filter: {id: {eq: addr}},
        result: 'id balance'
    })).result;

    if (queryResult.length) {
        const accountData = queryResult[0]
        if (accountData.id !== addr) {
            console.debug(`Something wrong: requested addr = ${addr}, received addr = ${accountData.id}`)
            return null
        }
        return accountData.balance / 1e9
    }
    return null
}

async function getHashCode(ton, bocBase64) {
    return await ton.boc.get_boc_hash({boc: bocBase64});
}

async function getCodeFromImage(ton, imageBase64) {
    const result = await ton.boc.get_code_from_tvc({tvc: imageBase64});
    return result.code;
}

// ===================  RootTokenContract methods  ======================================
async function deployWallet(ton, root, pubkey, owner, tokens, crystals) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: root.addr,
            abi: abiContract(rootPackage.abi),
            call_set: {
                function_name: 'deployWallet',
                input: {_answer_id: "0x0", pubkey: pubkey,
                        owner: owner, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(root.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[deployWallet] gas used:', gas);
    await waitForResultXN(ton, result);
    return result.decoded.output.value0;
}

async function grant(ton, root, dest, tokens, crystals) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: root.addr,
            abi: abiContract(rootPackage.abi),
            call_set: {
                function_name: 'grant',
                input: {_answer_id: "0x0", dest: dest, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(root.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[grant] gas used:', gas);
    await waitForResultXN(ton, result);
}

async function mint(ton, root, tokens) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: root.addr,
            abi: abiContract(rootPackage.abi),
            call_set: {
                function_name: 'mint',
                input: {_answer_id: "0x0", tokens: tokens}
            },
            signer: signerKeys(root.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[mint] gas used:', gas);
}

async function tvm_run_local(ton, address, abi, function_name, input = {}) {
    const msg = await ton.abi.encode_message({
      abi: abiContract(abi),
      address,
      call_set: {
          function_name: function_name,
          input: input
      },
      signer: signerNone()
    });
    const account = (await ton.net.query_collection({
        collection: 'accounts',
        filter: { id: { eq: address } },
        result: 'boc'
    })).result[0].boc;
    return (await ton.tvm.run_tvm({ message: msg.message, account, abi: abiContract(abi) })).decoded;
}

async function getName(ton, root) {
    return hexToUtf8(
        (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getName')).output.value0
        );
}

async function getSymbol(ton, root) {
    return hexToUtf8(
        (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getSymbol')).output.value0
        );
}

async function getDecimals(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getDecimals')).output.value0;
}

async function getRootKey(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getRootKey')).output.value0;
}

async function getTotalSupply(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getTotalSupply')).output.value0;
}

async function getTotalGranted(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getTotalGranted')).output.value0;
}

async function getWalletCode(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getWalletCode')).output.value0;
}

async function getWalletAddress(ton, root, walletKey, owner) {
    return (
        await tvm_run_local(ton, root.addr, rootPackage.abi, 'getWalletAddress',
                            { pubkey: walletKey, owner: owner })
    ).output.value0;
}

async function getWalletCodeHash(ton, root) {
    return (await tvm_run_local(ton, root.addr, rootPackage.abi, 'getWalletCodeHash')).output.value0;
}

// ===================  TONTokenWallet methods  ======================================
async function Wallet_transfer(ton, wallet, answer_addr, to, tokens, crystals, return_ownership) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'transfer',
                input: {answer_addr: answer_addr, to: to, tokens: tokens, crystals: crystals, return_ownership: return_ownership}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet transfer] gas used:', gas);
    await waitForResultXN(ton, result);
}

async function Wallet_transferToRecipient(ton, wallet, answer_addr, recipient_pubkey, recipient_owner,
                                          tokens, crystals, deploy, return_ownership) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'transferToRecipient',
                input: {answer_addr: answer_addr, recipient_pubkey: recipient_pubkey,
                        recipient_owner: recipient_owner, tokens: tokens, crystals: crystals,
                        deploy: deploy, return_ownership: return_ownership}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet transferToRecipient] gas used:', gas);
    await waitForResultXN(ton, result);
}

async function Wallet_getName(ton, wallet_address) {
    return hexToUtf8((await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.name);
}

async function Wallet_getSymbol(ton, wallet_address) {
    return hexToUtf8((await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.symbol);
}

async function Wallet_getDecimals(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.decimals;
}

async function Wallet_getBalance(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.balance;
}

async function Wallet_getWalletKey(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.wallet_public_key;
}

async function Wallet_getRootAddress(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.root_address;
}

async function Wallet_allowance(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.allowance;
}
async function Wallet_getCodeHash(ton, wallet_address) {
    return (await tvm_run_local(ton, wallet_address, walletPackage.abi, 'getDetails')).output.code_hash;
}

async function Wallet_destroy(ton, wallet, dest) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'destroy',
                input: {dest: dest}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet transfer] gas used:', gas);
    await waitForResultXN(ton, result);
}

async function Wallet_approve(ton, wallet, spender, remainingTokens, tokens) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'approve',
                input: {spender: spender, remainingTokens: remainingTokens, tokens: tokens}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet approve] gas used:', gas);
}

async function Wallet_transferFrom(ton, wallet, answer_addr, from, to, tokens, crystals) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'transferFrom',
                input: {answer_addr: answer_addr, from: from, to: to, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet transferFrom] gas used:', gas);
    await waitForResultXN(ton, result);
}

async function Wallet_disapprove(ton, wallet) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(walletPackage.abi),
            call_set: {
                function_name: 'disapprove',
                input: {},
            },
            signer: signerKeys(wallet.keys)
        }
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[wallet disapprove] gas used:', gas);
}

// ===================  TestRootOwner methods  ======================================
async function TestRootOwner_getTokenRoot(ton, rootOwner) {
    return (await tvm_run_local(ton, rootOwner.addr, rootOwnerPackage.abi, 'getTokenRoot')).output.value0;
}

async function TestRootOwner_mint(ton, rootOwner, processingCrystals, tokens) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'mint',
                input: {processingCrystals: processingCrystals, tokens: tokens}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[mint] gas used:', gas);
}

async function TestRootOwner_grant(ton, rootOwner, processingCrystals, dest, tokens, crystals) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'grant',
                input: {processingCrystals: processingCrystals, dest: dest, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[grant] gas used:', gas);
}

async function TestRootOwner_deployWallet(ton, rootOwner, processingCrystals, pubkey, owner, tokens, crystals) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: rootOwner.addr,
            abi: abiContract(rootOwnerPackage.abi),
            call_set: {
                function_name: 'deployWallet',
                input: {processingCrystals: processingCrystals,
                        pubkey: pubkey, owner: owner, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(rootOwner.keys)
        }
    });
    //console.log('[deployWallet] initial result:', result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[deployWallet] gas used:', gas);
    const answer = await waitForFinalExternalAnswer(ton, result, rootOwnerPackage.abi, 'deployWallet', 10);
    console.log('[deployWallet] answer = ', answer);
    return answer.value0;
}

module.exports = {
    rootPackage,
    walletPackage,
    getBalance,
    deploy,
    deployRoot,
    deployWalletIndependent,
    readConfig,
    getHashCode,
    getCodeFromImage,
    deployWallet,
    deployRootOwner,
    grant,
    mint,
    getName,
    getSymbol,
    getDecimals,
    getRootKey,
    getTotalSupply,
    getTotalGranted,
    getWalletCode,
    getWalletAddress,
    getWalletCodeHash,
    Wallet_transfer,
    Wallet_transferToRecipient,
    Wallet_destroy,
    Wallet_getName,
    Wallet_getSymbol,
    Wallet_getDecimals,
    Wallet_getBalance,
    Wallet_getWalletKey,
    Wallet_getRootAddress,
    Wallet_allowance,
    Wallet_getCodeHash,
    Wallet_approve,
    Wallet_transferFrom,
    Wallet_disapprove,
    TestRootOwner_getTokenRoot,
    TestRootOwner_mint,
    TestRootOwner_grant,
    TestRootOwner_deployWallet,
    ContractError
}
