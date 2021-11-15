const convert = (from, to) => data => Buffer.from(data, from).toString(to)

module.exports = {
    hexToUtf8: convert('hex', 'utf8'),
    utf8ToHex: convert('utf8', 'hex'),
    d2h: (dec) => `0x${Number(dec).toString(16)}`,
    delay: (sec) => new Promise(resolve => setTimeout(() => resolve(), sec * 1000)),
    stringToArray: string => Array.from(new Uint8Array(Buffer.alloc(string.length, string).buffer)),
    arrayToString: (array) => Buffer.from(array).toString(),
    fixLeadingZero: param => `0x${param.slice(2).padStart(64, '0')}`,
    now: () => Date.now() / 1000 >> 0
}
