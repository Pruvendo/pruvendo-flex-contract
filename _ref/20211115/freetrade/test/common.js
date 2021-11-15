var fs = require('fs');
const os = require('os');
const path = require('path');
const assert = require('assert');
const {abiContract, signerKeys, signerNone} = require('@tonclient/core');

const { hexToUtf8, utf8ToHex, stringToArray, arrayToString, delay, fixLeadingZero } = require('./utils.js')

const VotingWalletContractError = {
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

const readOSGiverKeys = () => {
    let keysPath = path.resolve(os.homedir(), 'giver_keys_os.json');
    return JSON.parse(fs.readFileSync(keysPath));
}

const readConfig = () => {
    var conf = JSON.parse(fs.readFileSync("./config.json"));
    if (!conf.localNode) {
        conf.url = conf.urlWeb;
        conf.giverKeys = readGiverKeys();
        //conf.giverKeys = readOSGiverKeys();
    }
    return conf;
}

// for dev-net
const testnetGiverAddressDev = '0:653b9a6452c7a982c6dc92b2da9eba832ade1c467699ebb3b43dca6d77b780dd';
// for ci-net
//const testnetGiverAddress = '0:2bb4a0e8391e7ea8877f4825064924bd41ce110fce97e939d3323999e1efbb13';
// for OS or dev-net2
//const testnetGiverAddressOS = '-1:7777777777777777777777777777777777777777777777777777777777777777';

// for dev-net
const testnetGiverAbiDev =
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

// for ci-net
const testnetGiverAbi =
{
	"ABI version": 2,
	"header": ["time", "expire"],
	"functions": [
		{
			"name": "sendTransaction",
			"inputs": [
				{"name":"dest","type":"address"},
				{"name":"value","type":"uint128"},
				{"name":"bounce","type":"bool"}
			],
			"outputs": [
			]
		},
		{
			"name": "getMessages",
			"inputs": [
			],
			"outputs": [
				{"components":[{"name":"hash","type":"uint256"},{"name":"expireAt","type":"uint64"}],"name":"messages","type":"tuple[]"}
			]
		},
		{
			"name": "upgrade",
			"inputs": [
				{"name":"newcode","type":"cell"}
			],
			"outputs": [
			]
		},
		{
			"name": "constructor",
			"inputs": [
			],
			"outputs": [
			]
		}
	],
	"data": [
	],
	"events": [
	]
};

const msigGiverAbi = {
	"ABI version": 2,
	"header": ["pubkey", "time", "expire"],
	"functions": [
		{
			"name": "constructor",
			"inputs": [
				{"name":"owners","type":"uint256[]"},
				{"name":"reqConfirms","type":"uint8"}
			],
			"outputs": [
			]
		},
		{
			"name": "acceptTransfer",
			"inputs": [
				{"name":"payload","type":"bytes"}
			],
			"outputs": [
			]
		},
		{
			"name": "sendTransaction",
			"inputs": [
				{"name":"dest","type":"address"},
				{"name":"value","type":"uint128"},
				{"name":"bounce","type":"bool"},
				{"name":"flags","type":"uint8"},
				{"name":"payload","type":"cell"}
			],
			"outputs": [
			]
		},
		{
			"name": "submitTransaction",
			"inputs": [
				{"name":"dest","type":"address"},
				{"name":"value","type":"uint128"},
				{"name":"bounce","type":"bool"},
				{"name":"allBalance","type":"bool"},
				{"name":"payload","type":"cell"}
			],
			"outputs": [
				{"name":"transId","type":"uint64"}
			]
		},
		{
			"name": "confirmTransaction",
			"inputs": [
				{"name":"transactionId","type":"uint64"}
			],
			"outputs": [
			]
		},
		{
			"name": "isConfirmed",
			"inputs": [
				{"name":"mask","type":"uint32"},
				{"name":"index","type":"uint8"}
			],
			"outputs": [
				{"name":"confirmed","type":"bool"}
			]
		},
		{
			"name": "getParameters",
			"inputs": [
			],
			"outputs": [
				{"name":"maxQueuedTransactions","type":"uint8"},
				{"name":"maxCustodianCount","type":"uint8"},
				{"name":"expirationTime","type":"uint64"},
				{"name":"minValue","type":"uint128"},
				{"name":"requiredTxnConfirms","type":"uint8"}
			]
		},
		{
			"name": "getTransaction",
			"inputs": [
				{"name":"transactionId","type":"uint64"}
			],
			"outputs": [
				{"components":[{"name":"id","type":"uint64"},{"name":"confirmationsMask","type":"uint32"},{"name":"signsRequired","type":"uint8"},{"name":"signsReceived","type":"uint8"},{"name":"creator","type":"uint256"},{"name":"index","type":"uint8"},{"name":"dest","type":"address"},{"name":"value","type":"uint128"},{"name":"sendFlags","type":"uint16"},{"name":"payload","type":"cell"},{"name":"bounce","type":"bool"}],"name":"trans","type":"tuple"}
			]
		},
		{
			"name": "getTransactions",
			"inputs": [
			],
			"outputs": [
				{"components":[{"name":"id","type":"uint64"},{"name":"confirmationsMask","type":"uint32"},{"name":"signsRequired","type":"uint8"},{"name":"signsReceived","type":"uint8"},{"name":"creator","type":"uint256"},{"name":"index","type":"uint8"},{"name":"dest","type":"address"},{"name":"value","type":"uint128"},{"name":"sendFlags","type":"uint16"},{"name":"payload","type":"cell"},{"name":"bounce","type":"bool"}],"name":"transactions","type":"tuple[]"}
			]
		},
		{
			"name": "getTransactionIds",
			"inputs": [
			],
			"outputs": [
				{"name":"ids","type":"uint64[]"}
			]
		},
		{
			"name": "getCustodians",
			"inputs": [
			],
			"outputs": [
				{"components":[{"name":"index","type":"uint8"},{"name":"pubkey","type":"uint256"}],"name":"custodians","type":"tuple[]"}
			]
		}
	],
	"data": [
	],
	"events": [
		{
			"name": "TransferAccepted",
			"inputs": [
				{"name":"payload","type":"bytes"}
			],
			"outputs": [
			]
		}
	]
};

const loadPackage = (name) => {
    var contract = {};
    contract.abi = JSON.parse(fs.readFileSync('../' + name + '.abi', 'utf8'));
    contract.imageBase64 = fs.readFileSync('../' + name + '.tvc').toString('base64');
    return contract;
};
const loadPackageFix = (name) => {
    var contract = {};
    contract.abi = JSON.parse(fs.readFileSync('../' + name + '.abi', 'utf8'));
    contract.abi_fixed = JSON.parse(fs.readFileSync('../' + name + '.abi.fixed', 'utf8'));
    contract.imageBase64 = fs.readFileSync('../' + name + '.tvc').toString('base64');
    return contract;
};

const proxyPackage = loadPackage('Proxy');
const clientPackage = loadPackage('FlexClient');
const flexPackage = loadPackage('Flex');
const pairPackage = loadPackage('TradingPair');
const pricePackage = loadPackage('Price');
const xchgPairPackage = loadPackage('XchgPair');
const xchgPricePackage = loadPackage('PriceXchg');
const depoolMockPackage = loadPackage('DePoolMock');
const stTONsPackage = loadPackage('stTONs');
const stTONsClientMockPackage = loadPackage('stTONsClientMock');
const WrongListingMockPackage = loadPackage('WrongListingMock');

const tip3RootPackage = loadPackage('../tokens/fungible/RootTokenContract');
const flexTip3RootPackage = loadPackage('../tokens/fungible/FlexTokenRoot');
const tip3WalletPackage = loadPackage('../tokens/fungible/TONTokenWallet');
const flexWalletPackage = loadPackage('../tokens/fungible/FlexWallet');
const flexWrapperPackage = loadPackage('../tokens/fungible/Wrapper');

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
      console.log('cur msg = ', msg);
      if ((msg.src == orig_addr) && (msg.dst.length === 0)) {
        externalMessages.push(msg);
      }
    }
    return externalMessages[0].decoded_body.value;
}

async function calcDeployAddress(ton, conf, contract, keys, options) {
    const msg = await ton.abi.encode_message({
        abi: abiContract(contract.abi),
        call_set: { function_name: "constructor", input: options },
        deploy_set: { tvc: contract.imageBase64 },
        signer: keys ? signerKeys(keys) : signerNone(),
    });
    return msg.address;
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
        // For dev-net:
        const result = await ton.processing.process_message({
            send_events: false,
            message_encode_params: {
                address: testnetGiverAddressDev,
                abi: abiContract(testnetGiverAbiDev),
                call_set: {
                    function_name: 'grant',
                    input: {addr: futureAddress}
                },
                signer: signerNone()
            }
        });
        await waitForResultXN(ton, result);
        // For ci-net:
        //await ton.contracts.run({
        //    address: testnetGiverAddress,
        //    abi: testnetGiverAbi,
        //    functionName: 'sendTransaction',
        //    input: {dest: futureAddress, value: 100_000_000_000, bounce:false},
        //    keyPair: conf.giverKeys
        //});
        // For OS or net2.ton.dev
        //await ton.contracts.run({
        //    address: testnetGiverAddressOS,
        //    abi: msigGiverAbi,
        //    functionName: 'submitTransaction',
        //    input: {dest: futureAddress, value: 100_000_000_000, bounce:false, allBalance:false, payload:""},
        //    keyPair: conf.giverKeys
        //});
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

async function deployProxy(ton, conf) {
    const proxyKeys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] proxy keys:`, proxyKeys);
    }
    let ctorParams = {
        pubkey: "0x" + proxyKeys.public,
    };
    const proxyAddress = await deploy(ton, conf, proxyPackage, proxyKeys, ctorParams);
    if (conf.verbose) {
        console.log('[Test]: proxy address', proxyAddress);
    }

    let proxy = {addr: proxyAddress, keys: proxyKeys};
    return proxy;
}

async function deployStTONsClientMock(ton, conf) {
    const keys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] stTONsClientMock keys:`, keys);
    }
    let ctorParams = {
        owner_pubkey: "0x" + keys.public,
    };
    const addr = await deploy(ton, conf, stTONsClientMockPackage, keys, ctorParams);
    if (conf.verbose) {
        console.log('[Test]: stTONsClientMock addr', addr);
    }

    return {addr: addr, keys: keys};
}

// ====== FlexClient functions ========
async function deployFlexClient(ton, conf, tradingPairCode, xchgPairCode) {
    const clientKeys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] client keys:`, clientKeys);
    }
    let ctorParams = {
        pubkey: "0x" + clientKeys.public,
        trading_pair_code: tradingPairCode,
        xchg_pair_code: xchgPairCode
    };
    const clientAddress = await deploy(ton, conf, clientPackage, clientKeys, ctorParams);
    if (conf.verbose) {
        console.log('[Test]: client address', clientAddress);
    }

    let client = {addr: clientAddress, keys: clientKeys};
    return client;
}

async function FlexClient_setFlexCfg(ton, flexClient, tons_cfg, flex) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'setFlexCfg',
                input: {tons_cfg: tons_cfg, flex: flex}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient setExtWalletCode] gas used:', gas);
}

async function FlexClient_setExtWalletCode(ton, flexClient, ext_wallet_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'setExtWalletCode',
                input: {ext_wallet_code: ext_wallet_code}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient setExtWalletCode] gas used:', gas);
}

async function FlexClient_setFlexWalletCode(ton, flexClient, flex_wallet_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'setFlexWalletCode',
                input: {flex_wallet_code: flex_wallet_code}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient setFlexWalletCode] gas used:', gas);
}

async function FlexClient_setFlexWrapperCode(ton, flexClient, flex_wrapper_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'setFlexWrapperCode',
                input: {flex_wrapper_code: flex_wrapper_code}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient setFlexWrapperCode] gas used:', gas);
}

async function FlexClient_deployTradingPair(ton, flexClient,
    tip3_root, deploy_min_value, deploy_value, min_trade_amount
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployTradingPair',
                input: {tip3_root: tip3_root, deploy_min_value: deploy_min_value,
                        deploy_value: deploy_value, min_trade_amount: min_trade_amount}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployTradingPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_deployXchgPair(ton, flexClient,
    tip3_major_root, tip3_minor_root, deploy_min_value, deploy_value, min_trade_amount, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployXchgPair',
                input: {tip3_major_root: tip3_major_root, tip3_minor_root: tip3_minor_root,
                        deploy_min_value: deploy_min_value, deploy_value: deploy_value,
                        min_trade_amount: min_trade_amount, notify_addr: notify_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployXchgPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_deployPriceWithSell(ton, flexClient,
    price, amount, lend_finish_time, min_amount, deals_limit, tons_value, price_code,
    my_tip3_addr, receive_wallet, tip3_code,
    name, symbol, decimals, root_public_key, root_address
) {
    const tip3cfg = {
        name:            name,
        symbol:          symbol,
        decimals:        decimals,
        root_public_key: root_public_key,
        root_address:    root_address
    };
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployPriceWithSell',
                input: {price: price, amount: amount, lend_finish_time: lend_finish_time,
                        min_amount: min_amount, deals_limit: deals_limit, tons_value: tons_value,
                        price_code: price_code, my_tip3_addr: my_tip3_addr,
                        receive_wallet: receive_wallet, tip3_code: tip3_code, tip3cfg: tip3cfg}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployPriceWithSell] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_deployPriceWithBuy(ton, flexClient,
    price, amount, order_finish_time, min_amount, deals_limit, deploy_value, price_code, my_tip3_addr,
    tip3_code, name, symbol, decimals, root_public_key, root_address
) {
    const tip3cfg = {
        name:            name,
        symbol:          symbol,
        decimals:        decimals,
        root_public_key: root_public_key,
        root_address:    root_address
    };
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployPriceWithBuy',
                input: {price: price, amount: amount, order_finish_time: order_finish_time,
                        min_amount: min_amount, deals_limit: deals_limit, deploy_value: deploy_value,
                        price_code: price_code, my_tip3_addr: my_tip3_addr, tip3_code: tip3_code,
                        tip3cfg: tip3cfg}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployPriceWithBuy] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_deployPriceXchg(ton, flexClient,
    sell, price_num, price_denum, amount, lend_amount, lend_finish_time, min_amount, deals_limit,
    tons_value, xchg_price_code, my_tip3_addr, receive_wallet,
    major_tip3cfg, minor_tip3cfg, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployPriceXchg',
                input: {sell: sell, price_num: price_num, price_denum: price_denum, amount: amount,
                        lend_amount: lend_amount, lend_finish_time: lend_finish_time, min_amount: min_amount,
                        deals_limit: deals_limit, tons_value: tons_value, xchg_price_code: xchg_price_code,
                        my_tip3_addr: my_tip3_addr, receive_wallet: receive_wallet,
                        major_tip3cfg: major_tip3cfg, minor_tip3cfg: minor_tip3cfg, notify_addr: notify_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployPriceXchg] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_cancelSellOrder(ton, flexClient,
    price, min_amount, deals_limit, value, price_code, tip3_code,
    name, symbol, decimals, root_public_key, root_address, notify_addr
) {
    const tip3cfg = {
        name:            name,
        symbol:          symbol,
        decimals:        decimals,
        root_public_key: root_public_key,
        root_address:    root_address
    };
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'cancelSellOrder',
                input: {price: price, min_amount: min_amount, deals_limit: deals_limit, value: value,
                price_code: price_code, tip3_code: tip3_code, tip3cfg: tip3cfg, notify_addr: notify_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient cancelSellOrder] gas used:', gas);
}

async function FlexClient_cancelBuyOrder(ton, flexClient,
    price, min_amount, deals_limit, value, price_code, tip3_code,
    name, symbol, decimals, root_public_key, root_address, notify_addr
) {
    const tip3cfg = {
        name:            name,
        symbol:          symbol,
        decimals:        decimals,
        root_public_key: root_public_key,
        root_address:    root_address
    };
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'cancelSellOrder',
                input: {price: price, min_amount: min_amount, deals_limit: deals_limit, value: value,
                price_code: price_code, tip3_code: tip3_code, tip3cfg: tip3cfg, notify_addr: notify_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient cancelSellOrder] gas used:', gas);
}

async function FlexClient_cancelXchgOrder(ton, flexClient,
    sell, price_num, price_denum, min_amount, deals_limit, value, xchg_price_code,
    major_tip3cfg, minor_tip3cfg, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'cancelXchgOrder',
                input: {sell: sell, price_num: price_num, price_denum: price_denum, min_amount: min_amount,
                        deals_limit: deals_limit, value: value, xchg_price_code: xchg_price_code,
                        major_tip3cfg: major_tip3cfg, minor_tip3cfg: minor_tip3cfg, notify_addr: notify_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient cancelXchgOrder] gas used:', gas);
}

async function FlexClient_transfer(ton, flexClient,
    dest, value, bounce
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'transfer',
                input: {dest: dest, value: value, bounce: bounce}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient transfer] gas used:', gas);
}

async function WrongListingMock_setFlexWrapperCode(ton, wrongListingMock, flex_wrapper_code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'setFlexWrapperCode',
                input: {flex_wrapper_code: flex_wrapper_code}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock setFlexWrapperCode] gas used:', gas);
}

async function WrongListingMock_deployWrapper(ton, wrongListingMock, wrapper_pubkey,
    wrapper_deploy_value, wrapper_keep_balance, tip3cfg
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployWrapper',
                input: {wrapper_pubkey: wrapper_pubkey,
                        wrapper_deploy_value: wrapper_deploy_value,
                        wrapper_keep_balance: wrapper_keep_balance,
                        tip3cfg: tip3cfg}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployWrapper] gas used:', gas);
    return result.decoded.output.value0;
}

async function WrongListingMock_deployWrapperWithWrongCall(ton, wrongListingMock, wrapper_pubkey,
    wrapper_deploy_value, wrapper_keep_balance, tip3cfg
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployWrapperWithWrongCall',
                input: {wrapper_pubkey: wrapper_pubkey,
                        wrapper_deploy_value: wrapper_deploy_value,
                        wrapper_keep_balance: wrapper_keep_balance,
                        tip3cfg: tip3cfg}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployWrapperWithWrongCall] gas used:', gas);
    return result.decoded.output.value0;
}

async function WrongListingMock_deployTradingPair(ton, wrongListingMock,
    tip3_root, deploy_min_value, deploy_value, min_trade_amount, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployTradingPair',
                input: {tip3_root: tip3_root, deploy_min_value: deploy_min_value,
                        deploy_value: deploy_value, min_trade_amount: min_trade_amount,
                        notify_addr: notify_addr}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployTradingPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function WrongListingMock_deployTradingPairWithWrongCall(ton, wrongListingMock,
    tip3_root, deploy_value
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployTradingPairWithWrongCall',
                input: {tip3_root: tip3_root,
                        deploy_value: deploy_value}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployTradingPairWithWrongCall] gas used:', gas);
    return result.decoded.output.value0;
}

async function WrongListingMock_deployXchgPair(ton, wrongListingMock,
    tip3_major_root, tip3_minor_root, deploy_min_value, deploy_value, min_trade_amount, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployXchgPair',
                input: {tip3_major_root: tip3_major_root, tip3_minor_root: tip3_minor_root,
                        deploy_min_value: deploy_min_value, deploy_value: deploy_value,
                        min_trade_amount: min_trade_amount, notify_addr: notify_addr}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployXchgPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function WrongListingMock_deployXchgPairWithWrongCall(ton, wrongListingMock,
    tip3_major_root, tip3_minor_root, deploy_value
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wrongListingMock.addr,
            abi: abiContract(WrongListingMockPackage.abi),
            call_set: {
                function_name: 'deployXchgPairWithWrongCall',
                input: {tip3_major_root: tip3_major_root, tip3_minor_root: tip3_minor_root,
                        deploy_value: deploy_value}
            },
            signer: signerKeys(wrongListingMock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[WrongListingMock deployXchgPairWithWrongCall] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_deployEmptyFlexWallet(ton, flexClient,
    pubkey, tons_to_wallet, tip3cfg
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'deployEmptyFlexWallet',
                input: {pubkey: pubkey,
                        tons_to_wallet: tons_to_wallet,
                        tip3cfg: tip3cfg}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient deployEmptyFlexWallet] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_burnWallet(ton, flexClient,
    crystals_value, out_pubkey, out_owner, my_tip3_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flexClient.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'burnWallet',
                input: {crystals_value: crystals_value, out_pubkey: out_pubkey,
                        out_owner: out_owner, my_tip3_addr: my_tip3_addr}
            },
            signer: signerKeys(flexClient.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient burnWallet] gas used:', gas);
}

async function FlexClient_getPayloadForDeployInternalWallet(ton, flexClient,
    owner_pubkey, owner_addr, crystals
) {
    return (await tvm_run_local(ton, flexClient.addr, clientPackage.abi, 'getPayloadForDeployInternalWallet', {
        owner_pubkey: owner_pubkey,
        owner_addr: owner_addr,
        crystals: crystals
    })).output.value0;
}

async function deployWrongListingMock(ton, conf, tradingPairCode, xchgPairCode) {
    const mockKeys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] WrongListingMock keys:`, mockKeys);
    }
    let ctorParams = {
        pubkey: "0x" + mockKeys.public,
        trading_pair_code: tradingPairCode,
        xchg_pair_code: xchgPairCode
    };
    const address = await deploy(ton, conf, WrongListingMockPackage, mockKeys, ctorParams);
    if (conf.verbose) {
        console.log('[Test]: WrongListingMock address', address);
    }

    return {addr: address, keys: mockKeys};
}

async function DePoolMock_sendOnTransfer(ton, depool_mock,
    dst, src, amount
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: depool_mock.addr,
            abi: abiContract(depoolMockPackage.abi),
            call_set: {
                function_name: 'sendOnTransfer',
                input: {dst: dst, src: src, amount: amount}
            },
            signer: signerKeys(depool_mock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[DePoolMock sendOnTransfer] gas used:', gas);
}

async function stTONsClientMock_deployStTONs(ton, client_mock,
    crystals, code, owner_pubkey, owner_address, depool, depool_pubkey
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client_mock.addr,
            abi: abiContract(stTONsClientMockPackage.abi),
            call_set: {
                function_name: 'deployStTONs',
                input: { crystals: crystals, code: code,
                         owner_pubkey: owner_pubkey, owner_address: owner_address,
                         depool: depool, depool_pubkey: depool_pubkey }
            },
            signer: signerKeys(client_mock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[stTONsClientMock deployStTONs] gas used:', gas);
    return result.decoded.output.value0;
}

async function stTONsClientMock_returnStake(ton, client_mock,
    stTONsAddr, dst, processing_crystals, depool_processing_crystals
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client_mock.addr,
            abi: abiContract(stTONsClientMockPackage.abi),
            call_set: {
                function_name: 'returnStake',
                input: { stTONsAddr: stTONsAddr, dst: dst,
                         processing_crystals: processing_crystals,
                         depool_processing_crystals: depool_processing_crystals }
            },
            signer: signerKeys(client_mock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[stTONsClientMock returnStake] gas used:', gas);
}

async function stTONsClientMock_finalize(ton, client_mock,
    stTONsAddr, dst, processing_crystals, ignore_errors
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client_mock.addr,
            abi: abiContract(stTONsClientMockPackage.abi),
            call_set: {
                function_name: 'finalize',
                input: { stTONsAddr: stTONsAddr, dst: dst,
                         processing_crystals: processing_crystals, ignore_errors: ignore_errors }
            },
            signer: signerKeys(client_mock.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[stTONsClientMock finalize] gas used:', gas);
}

// ======== Tip3 root methods ========

async function Tip3Root_setWalletCode(ton, tip3Root, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: tip3Root.addr,
            abi: abiContract(tip3RootPackage.abi),
            call_set: {
                function_name: 'setWalletCode',
                input: {_answer_id: "0x0", wallet_code: code}
            },
            signer: signerKeys(tip3Root.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[SuperRoot setWalletCode] gas used:', gas);
}

// utf8ToHex
async function deployTip3Root(ton, conf, name, symbol, decimals, walletCode, totalSupply) {
    const rootKeys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] root keys:`, rootKeys);

    let ctorParams = {
        name: name, symbol: symbol, decimals: decimals,
        root_pubkey: '0x' + rootKeys.public,
        root_owner: null,
        total_supply: totalSupply,
    };

    const rootAddress = await deploy(ton, conf, tip3RootPackage, rootKeys, ctorParams);
    console.log('[Test]: root address', rootAddress);
    let root = {addr: rootAddress, keys: rootKeys};
    await Tip3Root_setWalletCode(ton, root, walletCode);
    console.log(`[Test] setWalletCode ok`);
    return root;
}

async function deployFlexTip3Root(ton, conf, name, symbol, decimals, walletCode, totalSupply, root_owner) {
    const rootKeys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] flex token root keys:`, rootKeys);

    let ctorParams = {
        name: name, symbol: symbol, decimals: decimals,
        root_public_key: '0x' + rootKeys.public,
        root_owner: root_owner,
        total_supply: totalSupply,
    };

    const rootAddress = await deploy(ton, conf, flexTip3RootPackage, rootKeys, ctorParams);
    console.log('[Test]: flex token root address', rootAddress);
    let root = {addr: rootAddress, keys: rootKeys};
    await Tip3Root_setWalletCode(ton, root, walletCode);
    console.log(`[Test] setWalletCode ok`);
    return root;
}

async function deployDePoolMock(ton, conf) {
    const keys = await ton.crypto.generate_random_sign_keys();
    console.log(`[Test] DePool mock keys:`, keys);

    let ctorParams = {
        owner_pubkey: '0x' + keys.public
    };

    const mockAddress = await deploy(ton, conf, depoolMockPackage, keys, ctorParams);
    console.log('[Test]: DePool mock address', mockAddress);
    return {addr: mockAddress, keys: keys};
}

const trade_pair_code = 1;
const xchg_pair_code = 2;
const wrapper_code = 3;
const ext_wallet_code = 4;
const flex_wallet_code = 5;
const price_code = 6;
const xchg_price_code = 7;

async function Flex_setPairCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: trade_pair_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setPairCode] gas used:', gas);
}

async function Flex_setPriceCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: price_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setPriceCode] gas used:', gas);
}

async function Flex_setXchgPairCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: xchg_pair_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setXchgPairCode] gas used:', gas);
}

async function Flex_setXchgPriceCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: xchg_price_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setXchgPriceCode] gas used:', gas);
}

async function Flex_setWrapperCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: wrapper_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setWrapperCode] gas used:', gas);
}

async function Flex_setExtWalletCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: ext_wallet_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setExtWalletCode] gas used:', gas);
}

async function Flex_setFlexWalletCode(ton, flex, code) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'setSpecificCode',
                input: {type: flex_wallet_code, code: code}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex setFlexWalletCode] gas used:', gas);
}

async function Flex_transfer(ton, flex, to, tons) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'transfer',
                input: {to: to, tons: tons}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex transfer] gas used:', gas);
}

async function Flex_approveWrapper(ton, flex, pubkey) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'approveWrapper',
                input: {_answer_id: "0x0", pubkey: pubkey}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex approveWrapper] gas used:', gas);
    return result.decoded.output.value0;
}

async function Flex_approveTradingPair(ton, flex, pubkey) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'approveTradingPair',
                input: {_answer_id: "0x0", pubkey: pubkey}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex approveTradingPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function Flex_approveXchgPair(ton, flex, pubkey) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: flex.addr,
            abi: abiContract(flexPackage.abi),
            call_set: {
                function_name: 'approveXchgPair',
                input: {_answer_id: "0x0", pubkey: pubkey}
            },
            signer: signerKeys(flex.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[Flex approveXchgPair] gas used:', gas);
    return result.decoded.output.value0;
}

async function FlexClient_registerWrapper(ton, client,
    wrapper_pubkey, value, tip3cfg) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'registerWrapper',
                input: {wrapper_pubkey: wrapper_pubkey, value: value, tip3cfg: tip3cfg}
            },
            signer: signerKeys(client.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient registerWrapper] gas used:', gas);
}

async function FlexClient_registerTradingPair(ton, client,
    request_pubkey, value, tip3_root, min_amount, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'registerTradingPair',
                input: {request_pubkey: request_pubkey, value: value,
                        tip3_root: tip3_root,
                        min_amount: min_amount, notify_addr: notify_addr}
            },
            signer: signerKeys(client.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient registerTradingPair] gas used:', gas);
}

async function FlexClient_registerXchgPair(ton, client,
    request_pubkey, value, tip3_major_root, tip3_minor_root, min_amount, notify_addr
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: client.addr,
            abi: abiContract(clientPackage.abi),
            call_set: {
                function_name: 'registerXchgPair',
                input: {request_pubkey: request_pubkey, value: value,
                        tip3_major_root: tip3_major_root, tip3_minor_root: tip3_minor_root,
                        min_amount: min_amount, notify_addr: notify_addr}
            },
            signer: signerKeys(client.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FlexClient registerXchgPair] gas used:', gas);
}

async function deployFlex(ton, conf, ownershipDescription, ownerAddress,
                          pairCode, priceCode, xchgPairCode, xchgPriceCode,
                          wrapperCode, extWalletCode, flexWalletCode,
                          tonsCfg, dealsLimit, listingCfg) {
    const flexKeys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] flex keys:`, flexKeys);
    }
    let ctorParams = {
        deployer_pubkey: "0x" + flexKeys.public,
        ownership_description: ownershipDescription,
        owner_address: ownerAddress,
        tons_cfg: tonsCfg,
        deals_limit: dealsLimit,
        listing_cfg: listingCfg
    };
    const flexAddress = await deploy(ton, conf, flexPackage, flexKeys, ctorParams);
    if (conf.verbose) {
        console.log('[Test]: Flex address', flexAddress);
    }

    let flex = {addr: flexAddress, keys: flexKeys};
    await Flex_setPairCode(ton, flex, pairCode);
    await Flex_setPriceCode(ton, flex, priceCode);
    await Flex_setXchgPairCode(ton, flex, xchgPairCode);
    await Flex_setXchgPriceCode(ton, flex, xchgPriceCode);

    await Flex_setWrapperCode(ton, flex, wrapperCode);
    await Flex_setExtWalletCode(ton, flex, extWalletCode);
    await Flex_setFlexWalletCode(ton, flex, flexWalletCode);

    return flex;
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

async function Flex_isFullyInitialized(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'isFullyInitialized')).output.value0;
}

async function Flex_getOwnershipInfo(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.ownership;
}

async function Flex_getTradingPairCode(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.trading_pair_code;
}

async function Flex_getXchgPairCode(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.xchg_pair_code;
}

async function Flex_getXchgTradingPair(ton, flex, tip3_major_root, tip3_minor_root) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getXchgTradingPair',
        {tip3_major_root: tip3_major_root, tip3_minor_root: tip3_minor_root})).output.value0;
}

async function Flex_getDealsLimit(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.deals_limit;
}

async function Flex_getWrapperListingRequests(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.wrapper_listing_requests;
}

async function Flex_getTradePairListingRequests(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.trade_pair_listing_requests;
}

async function Flex_getXchgPairListingRequests(ton, flex) {
    return (await tvm_run_local(ton, flex.addr, flexPackage.abi, 'getDetails')).output.xchg_pair_listing_requests;
}


// ===================  RootTokenContract methods  ======================================
async function Tip3Root_deployWallet(ton, conf, root, owner, tokens, crystals) {
    const walletKeys = await ton.crypto.generate_random_sign_keys();
    if (conf.verbose) {
        console.log(`[Test] tip3 wallet keys:`, walletKeys);
    }
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: root.addr,
            abi: abiContract(tip3RootPackage.abi),
            call_set: {
                function_name: 'deployWallet',
                input: {_answer_id: "0x0", pubkey: "0x" + walletKeys.public,
                owner: owner, tokens: tokens, crystals: crystals}
            },
            signer: signerKeys(root.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[deployWallet] gas used:', gas);
    return {addr: result.decoded.output.value0, keys: walletKeys};
}

async function Tip3Root_getWalletCodeHash(ton, root) {
    return (await tvm_run_local(ton, root.addr, tip3RootPackage.abi, 'getWalletCodeHash')).output.value0;
}

// Tip3 wallet methods
async function Tip3Wallet_transferWithNotify(ton, wallet,
    answer_addr, to, tokens, crystals, return_ownership, payload
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(tip3WalletPackage.abi),
            call_set: {
                function_name: 'transferWithNotify',
                input: {_answer_id: "0x0", answer_addr: answer_addr, to: to, tokens: tokens, crystals: crystals,
                        return_ownership: return_ownership, payload: payload}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[transferWithNotify] gas used:', gas);
}

async function Tip3Wallet_transfer(ton, wallet,
    answer_addr, to, tokens, crystals, return_ownership
) {
    const result = await ton.processing.process_message({
        send_events: false,
        message_encode_params: {
            address: wallet.addr,
            abi: abiContract(tip3WalletPackage.abi),
            call_set: {
                function_name: 'transfer',
                input: {_answer_id: "0x0", answer_addr: answer_addr, to: to, tokens: tokens, crystals: crystals,
                        return_ownership: return_ownership}
            },
            signer: signerKeys(wallet.keys)
        }
    });
    await waitForResultXN(ton, result);
    const gas = await getGas(ton, result.transaction.id);
    console.log('[transfer] gas used:', gas);
}

async function Tip3Wallet_getBalance(ton, wallet_addr) {
    return (await tvm_run_local(ton, wallet_addr, tip3WalletPackage.abi, 'getDetails')).output.balance;
}

async function Tip3Wallet_getDetails(ton, wallet_addr) {
    return (await tvm_run_local(ton, wallet_addr, tip3WalletPackage.abi, 'getDetails')).output;
}

//
async function DePoolMock_getDetails(ton, depool_mock_addr) {
    return (await tvm_run_local(ton, depool_mock_addr, depoolMockPackage.abi, 'getDetails')).output;
}

//
async function stTONs_getDetails(ton, stTONs_addr) {
    return (await tvm_run_local(ton, stTONs_addr, stTONsPackage.abi, 'getDetails')).output;
}

// Wrapper methods
async function Wrapper_getWalletAddress(ton, wrapper_addr, pubkey, owner) {
    return (await tvm_run_local(ton, wrapper_addr, flexWrapperPackage.abi, 'getWalletAddress', {
        pubkey: pubkey, owner: owner
    })).output.value0;
}

async function Wrapper_getExternalWallet(ton, wrapper_addr) {
    return (await tvm_run_local(ton, wrapper_addr, flexWrapperPackage.abi, 'getDetails')).output.external_wallet;
}

async function Wrapper_hasInternalWalletCode(ton, wrapper_addr) {
    return (await tvm_run_local(ton, wrapper_addr, flexWrapperPackage.abi, 'hasInternalWalletCode')).output.value0;
}

async function Wrapper_getInternalWalletCode(ton, wrapper_addr) {
    return (await tvm_run_local(ton, wrapper_addr, flexWrapperPackage.abi, 'getDetails')).output.wallet_code;
}

//
async function FlexTip3Root_getWalletAddress(ton, addr, pubkey, owner) {
    return (await tvm_run_local(ton, addr, flexTip3RootPackage.abi, 'getWalletAddress', {
        pubkey: pubkey, owner: owner
    })).output.value0;
}


/*
async function createDeployContestMessage(ton, conf, keys,
                                          title, link, hash, juryAddr, juryKeys,
                                          startsIn, lastsFor, votingWindow, sendApprovalGrams) {
    const deployParams = {
        package: ContestPackage,
        constructorParams: {
            title: title, link: link, hash: hash, juryAddr: juryAddr, juryKeys: juryKeys,
            startsIn: startsIn, lastsFor: lastsFor, votingWindow: votingWindow,
            sendApprovalGrams: sendApprovalGrams },
        keyPair: keys ? keys : contract.keys,
    };
    return await ton.contracts.createDeployMessage(deployParams);
}
*/

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
            console.log(`Something wrong: requested addr = ${addr}, received addr = ${accountData.id}`)
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

// ===================  FLeX methods  ======================================

module.exports = {
    proxyPackage,
    clientPackage,
    flexPackage,
    pairPackage,
    pricePackage,
    xchgPairPackage,
    xchgPricePackage,
    tip3WalletPackage,
    flexWalletPackage,
    flexWrapperPackage,
    tip3RootPackage,
    stTONsPackage,
    stTONsClientMockPackage,
    getBalance,
    deploy,
    deployProxy,
    deployFlexClient,
    deployWrongListingMock,
    deployFlex,
    deployTip3Root,
    deployFlexTip3Root,
    deployDePoolMock,
    deployStTONsClientMock,
    FlexClient_setFlexCfg,
    FlexClient_setExtWalletCode,
    FlexClient_setFlexWalletCode,
    FlexClient_setFlexWrapperCode,
    FlexClient_deployTradingPair,
    FlexClient_deployXchgPair,
    FlexClient_deployPriceWithSell,
    FlexClient_deployPriceWithBuy,
    FlexClient_deployPriceXchg,
    FlexClient_cancelSellOrder,
    FlexClient_cancelBuyOrder,
    FlexClient_cancelXchgOrder,
    FlexClient_transfer,
    FlexClient_deployEmptyFlexWallet,
    FlexClient_burnWallet,
    FlexClient_getPayloadForDeployInternalWallet,
    WrongListingMock_setFlexWrapperCode,
    WrongListingMock_deployWrapper,
    WrongListingMock_deployWrapperWithWrongCall,
    WrongListingMock_deployTradingPair,
    WrongListingMock_deployTradingPairWithWrongCall,
    WrongListingMock_deployXchgPair,
    WrongListingMock_deployXchgPairWithWrongCall,
    Tip3Root_deployWallet,
    Tip3Root_getWalletCodeHash,
    Tip3Wallet_transferWithNotify,
    Tip3Wallet_transfer,
    Tip3Wallet_getBalance,
    Tip3Wallet_getDetails,
    Wrapper_getWalletAddress,
    Wrapper_getExternalWallet,
    Wrapper_hasInternalWalletCode,
    Wrapper_getInternalWalletCode,
    Flex_getTradingPairCode,
    Flex_getXchgPairCode,
    Flex_isFullyInitialized,
    Flex_getOwnershipInfo,
    Flex_getXchgTradingPair,
    Flex_getDealsLimit,
    Flex_getWrapperListingRequests,
    Flex_getTradePairListingRequests,
    Flex_getXchgPairListingRequests,
    Flex_transfer,
    Flex_approveWrapper,
    Flex_approveTradingPair,
    Flex_approveXchgPair,
    FlexClient_registerWrapper,
    FlexClient_registerTradingPair,
    FlexClient_registerXchgPair,
    DePoolMock_sendOnTransfer,
    stTONsClientMock_deployStTONs,
    stTONsClientMock_returnStake,
    stTONsClientMock_finalize,
    DePoolMock_getDetails,
    stTONs_getDetails,
    FlexTip3Root_getWalletAddress,
    readConfig,
    getHashCode,
    getCodeFromImage,
    calcDeployAddress,
}
