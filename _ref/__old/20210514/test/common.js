var fs = require('fs');
const os = require('os');
const path = require('path');
const assert = require('assert');

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
        //conf.giverKeys = readGiverKeys();
        conf.giverKeys = readOSGiverKeys();
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
const clientPackage = loadPackage('FLeXClient');
const flexPackage = loadPackage('FLeX');
const pairPackage = loadPackage('TradingPair');
const pricePackage = loadPackage('Price');
const xchgPairPackage = loadPackage('XchgPair');
const xchgPricePackage = loadPackage('PriceXchg');

const tip3RootPackage = loadPackage('../tokens/RootTokenContract');
const tip3WalletPackage = loadPackage('../tokens/TONTokenWallet');

const emptyParams = {};

async function waitForResult(ton, result) {
  for (const msg of (result.transaction.out_messages || [])) {
    if (msg.msg_type === 0) {
      console.log(`waitForResult. Wait for ${msg.id || "Empty ID"}`);
      await ton.queries.transactions.waitFor(
        {
            in_msg: { eq: msg.id },
            status: { eq: 3 },
        },
        'lt',
        undefined,
        60 * 1000
      );
    }
  }
}

async function waitForResultX2(ton, result) {
  for (const msg of (result.transaction.out_messages || [])) {
    if (msg.msg_type === 0) {
      console.log(`waitForResultX2. Wait for ${msg.id || "Empty ID"}`);
      child = await ton.queries.transactions.waitFor(
        {
            in_msg: { eq: msg.id },
            status: { eq: 3 },
        },
        'out_messages { msg_type id }',
        undefined,
        60 * 1000
      );
      for (const msg of (child.out_messages || [])) {
        if (msg.msg_type === 0) {
          console.log(`waitForResultX2. Wait for child ${msg.id || "Empty ID"}`);
          await ton.queries.transactions.waitFor(
            {
                in_msg: { eq: msg.id },
                status: { eq: 3 },
            },
            'lt',
            undefined,
            60 * 1000
          );
        }
      }
    }
  }
}

async function waitForResultXN(ton, result, N) {
  let child = result.transaction;
  let restN = N;
  while (--restN && (child.out_messages || []).length > 0) {
    for (const msg of (child.out_messages || [])) {
      if (msg.msg_type === 0) {
        console.log(`waitForResultXN. Wait for ${msg.id || "Empty ID"}`);
        child = await ton.queries.transactions.waitFor(
          {
            in_msg: { eq: msg.id },
            status: { eq: 3 },
          },
          'out_messages { msg_type id }',
          undefined,
          60 * 1000
        );
      }
    }
  }
  for (const msg of (child.out_messages || [])) {
    if (msg.msg_type === 0) {
      console.log(`waitForResultX2. Wait for child ${msg.id || "Empty ID"}`);
      await ton.queries.transactions.waitFor(
        {
            in_msg: { eq: msg.id },
            status: { eq: 3 },
        },
        'lt',
        undefined,
        60 * 1000
      );
    }
  }
}

async function waitForFinalExternalAnswer(ton, result, orig_addr, abi, functionName, N) {
  console.log(`waitForFinalExternalAnswer. Wait for external chain message processing at `, orig_addr);
  let restN = N;
  let externalMessages = [];
  let processTransactions = [result.transaction];
  while (--restN && processTransactions.length > 0) {
    let child = processTransactions.pop();
    for (const msg of (child.out_messages || [])) {
      if (msg.msg_type === 0) {
        //console.log(`waitForFinalExternalAnswer. Wait for child ${msg.id || "Empty ID"}`);
        let newChild = await ton.queries.transactions.waitFor(
          {
            in_msg: { eq: msg.id },
            status: { eq: 3 },
          },
          'out_messages { msg_type id body }, account_addr',
          undefined,
          60 * 1000
        );
        processTransactions.push(newChild);
      } else {
        if (orig_addr == child.account_addr) {
          externalMessages.push(msg);
        }
      }
    }
  }
  console.log(`waitForFinalExternalAnswer. Loop finalized.`);

  const outputs = await Promise.all(externalMessages.map((x) => {
      return ton.contracts.decodeOutputMessageBody({
          abi: abi,
          bodyBase64: x.body || '',
      });
  }));
  const resultOutput = outputs.find((x) => {
      return x.function.toLowerCase() === functionName.toLowerCase();
  });
  return {
      output: resultOutput ? resultOutput.output : null,
      transaction: result.transaction
  };
}

async function calcDeployAddress(ton, conf, contract, keys, options) {
    return (await ton.contracts.createDeployMessage({
        package: contract,
        constructorParams: options,
        keyPair: keys ? keys : contract.keys,
    })).address;
}

async function deploy(ton, conf, contract, keys, options = {}) {
    const futureAddress = (await ton.contracts.createDeployMessage({
        package: contract,
        constructorParams: options,
        keyPair: keys ? keys : contract.keys,
    })).address;

    if (conf.localNode) {
        await ton.contracts.run({
            address: nodeSeGiverAddress,
            abi: nodeSeGiverAbi,
            functionName: 'sendGrams',
            input: {dest: futureAddress, amount: 100_000_000_000},
        });
    } else {
        // For dev-net:
        await ton.contracts.run({
            address: testnetGiverAddressDev,
            abi: testnetGiverAbiDev,
            functionName: 'grant',
            input: {addr: futureAddress}
        });
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
    console.log("[Test] giver sent grams to ", futureAddress);
    const txn = await ton.contracts.deploy({
        package: contract,
        constructorParams: options,
        keyPair: keys ? keys : contract.keys,
    });
    return txn;
}

async function deployProxy(ton, conf) {
    const proxyKeys = await ton.crypto.ed25519Keypair();
    if (conf.verbose) {
        console.log(`[Test] proxy keys:`, proxyKeys);
    }
    let ctorParams = {
        pubkey: "0x" + proxyKeys.public,
    };
    const proxyAddress = (await deploy(ton, conf, proxyPackage, proxyKeys, ctorParams)).address;
    if (conf.verbose) {
        console.log('[Test]: proxy address', proxyAddress);
    }

    let proxy = {addr: proxyAddress, keys: proxyKeys};
    return proxy;
}

async function deployFLeXClient(ton, conf, tradingPairCode) {
    const clientKeys = await ton.crypto.ed25519Keypair();
    if (conf.verbose) {
        console.log(`[Test] client keys:`, clientKeys);
    }
    let ctorParams = {
        pubkey: "0x" + clientKeys.public,
        trading_pair_code: tradingPairCode
    };
    const clientAddress = (await deploy(ton, conf, clientPackage, clientKeys, ctorParams)).address;
    if (conf.verbose) {
        console.log('[Test]: client address', clientAddress);
    }

    let client = {addr: clientAddress, keys: clientKeys};
    return client;
}

async function Tip3Root_setWalletCode(ton, tip3Root, code) {
    const result = await ton.contracts.run({
        address: tip3Root.addr,
        abi: tip3RootPackage.abi,
        functionName: 'setWalletCode',
        input: {wallet_code: code},
        keyPair: tip3Root.keys
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[SuperRoot setWalletCode] gas used:', gas);
    await waitForResultX2(ton, result);
}

async function deployTip3Root(ton, conf, name, symbol, decimals, walletCode, totalSupply) {
    const rootKeys = await ton.crypto.ed25519Keypair();
    console.log(`[Test] root keys:`, rootKeys);

    let ctorParams = {
        name: utf8ToHex(name), symbol: utf8ToHex(symbol), decimals: decimals,
        root_public_key: '0x' + rootKeys.public, root_owner: '0x0', total_supply: totalSupply,
    };

    const rootAddress = (await deploy(ton, conf, tip3RootPackage, rootKeys, ctorParams)).address;
    console.log('[Test]: root address', rootAddress);
    let root = {addr: rootAddress, keys: rootKeys};
    await Tip3Root_setWalletCode(ton, root, walletCode);
    console.log(`[Test] setWalletCode ok`);
    return root;
}

async function FLeX_setPairCode(ton, flex, code) {
    const result = await ton.contracts.run({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'setPairCode',
        input: {code: code},
        keyPair: flex.keys
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FLeX setPairCode] gas used:', gas);
    await waitForResultX2(ton, result);
}

async function FLeX_setPriceCode(ton, flex, code) {
    const result = await ton.contracts.run({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'setPriceCode',
        input: {code: code},
        keyPair: flex.keys
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[SuperRoot setPriceCode] gas used:', gas);
    await waitForResultX2(ton, result);
}

async function FLeX_setXchgPairCode(ton, flex, code) {
    const result = await ton.contracts.run({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'setXchgPairCode',
        input: {code: code},
        keyPair: flex.keys
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[FLeX setXchgPairCode] gas used:', gas);
    await waitForResultX2(ton, result);
}

async function FLeX_setXchgPriceCode(ton, flex, code) {
    const result = await ton.contracts.run({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'setXchgPriceCode',
        input: {code: code},
        keyPair: flex.keys
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[SuperRoot setXchgPriceCode] gas used:', gas);
    await waitForResultX2(ton, result);
}

async function deployFLeX(ton, conf, pairCode, priceCode, xchgPairCode, xchgPriceCode, tonsCfg, minAmount, dealsLimit, notifyAddr) {
    const flexKeys = await ton.crypto.ed25519Keypair();
    if (conf.verbose) {
        console.log(`[Test] flex keys:`, flexKeys);
    }
    let ctorParams = {
        deployer_pubkey: "0x" + flexKeys.public,
        transfer_tip3: tonsCfg.transfer_tip3,
        return_ownership: tonsCfg.return_ownership,
        trading_pair_deploy: tonsCfg.trading_pair_deploy,
        order_answer: tonsCfg.order_answer,
        process_queue: tonsCfg.process_queue,
        send_notify: tonsCfg.send_notify,
        min_amount: minAmount,
        deals_limit: dealsLimit,
        notify_addr: notifyAddr
    };
    const flexAddress = (await deploy(ton, conf, flexPackage, flexKeys, ctorParams)).address;
    if (conf.verbose) {
        console.log('[Test]: FLeX address', flexAddress);
    }

    let flex = {addr: flexAddress, keys: flexKeys};
    await FLeX_setPairCode(ton, flex, pairCode);
    await FLeX_setPriceCode(ton, flex, priceCode);
    await FLeX_setXchgPairCode(ton, flex, xchgPairCode);
    await FLeX_setXchgPriceCode(ton, flex, xchgPriceCode);
    return flex;
}

async function FLeX_isFullyInitialized(ton, flex) {
    return (await ton.contracts.runLocal({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'isFullyInitialized',
        input: {},
    })).output.value0;
}

async function FLeX_getTradingPairCode(ton, flex) {
    return (await ton.contracts.runLocal({
        address: flex.addr,
        abi: flexPackage.abi,
        functionName: 'getTradingPairCode',
        input: {},
    })).output.value0;
}

// ===================  RootTokenContract methods  ======================================
async function Tip3Root_deployWallet(ton, conf, root, workchain_id, internal_owner, tokens, grams) {
    const walletKeys = await ton.crypto.ed25519Keypair();
    if (conf.verbose) {
        console.log(`[Test] tip3 wallet keys:`, walletKeys);
    }
    const result = await ton.contracts.run({
        address: root.addr,
        abi: tip3RootPackage.abi,
        functionName: 'deployWallet',
        input: {_answer_id: "0x0", workchain_id: workchain_id, pubkey: "0x" + walletKeys.public,
                internal_owner: internal_owner, tokens: tokens, grams: grams},
        keyPair: root.keys,
    });
    const gas = await getGas(ton, result.transaction.id);
    console.log('[deployWallet] gas used:', gas);
    await waitForResultX2(ton, result);
    return {addr: result.output.value0, keys: walletKeys};
}

async function Tip3Root_getWalletCodeHash(ton, root) {
    return (await ton.contracts.runLocal({
        address: root.addr,
        abi: tip3RootPackage.abi,
        functionName: 'getWalletCodeHash',
        input: {},
    })).output.value0;
}

async function Tip3Wallet_getBalance(ton, wallet) {
    return (await ton.contracts.runLocal({
        address: wallet.addr,
        abi: tip3WalletPackage.abi,
        functionName: 'getDetails',
        input: {},
    })).output.balance;
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
    const result = await ton.queries.transactions.query({id: {eq: transId}}, "compute { gas_used }");
    if (result.length) {
        return parseInt(result[0].compute.gas_used);
    }
    return null;
}

async function getBalance(ton, addr) {
    const queryResult = await ton.queries.accounts.query({id: {eq: addr}}, 'id balance')

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
    return await ton.contracts.getBocHash({bocBase64});
}

async function getCodeFromImage(ton, imageBase64) {
    return await ton.contracts.getCodeFromImage({
        imageBase64: imageBase64
    });
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
    tip3RootPackage,
    getBalance,
    deploy,
    deployProxy,
    deployFLeXClient,
    deployFLeX,
    deployTip3Root,
    Tip3Root_deployWallet,
    Tip3Root_getWalletCodeHash,
    Tip3Wallet_getBalance,
    FLeX_getTradingPairCode,
    FLeX_isFullyInitialized,
    readConfig,
    getHashCode,
    getCodeFromImage,
    calcDeployAddress,
}
