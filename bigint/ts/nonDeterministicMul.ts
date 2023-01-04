const { P256 } = require('@noble/curves/p256');
const { bn254 } = require('@noble/curves/bn');
const { ed25519 } = require('@noble/curves/ed25519');
console.log(P256);
console.log(ed25519);

(BigInt.prototype as any).toJSON = function() { return this.toString() }

const primes = [
    1399027476140078653058704379177609361753676736201n,
    1167555264947830116235753479722409858771985625309n,
    778213806565775850770437273987932725759002427n,
    1258158978999755983804345499287890933023315388251n,
    879493383459077038143066346003600091475190167851n,
    882865033011123283515906055612738686262856896339n,
    1011367821446769602611683327392392806638070094663n,
    781307822319767093184989234080120664152777197089n,
    1120359700563689563922307923371865921655240033331n,
    1016524153110029342063341788118432251224877343367n,
];

const findModuli = (useNativeFieldAsModulo: boolean, nativeField: bigint, nonNativeField: bigint, numLimbs: bigint, base: bigint) => {
    let lcm = 1n;
    const moduli: bigint[] = [];
    if (useNativeFieldAsModulo) {
        lcm = lcm * nativeField;
        moduli.push(nativeField);
    }
    while (lcm < (2n * (numLimbs ** 2n) * nonNativeField * (base ** 2n))) {
        const prime = primes.shift();
        if (prime === undefined) {
            throw new Error('LCM constraint not satisfied');
        }
        moduli.push(prime);
        lcm = lcm * prime;
    }
    const moduliMax = nativeField / (4n * (numLimbs ** 2n) * (base ** 2n));
    // To avoid wrap-around, we require each mi (except for p itself)
    // to satisfy mi ≤ p/(4n^2b^2)
    const wrapAroundConstraintSatisfied = moduli.every((mi) => {
        return mi === nativeField || mi <= moduliMax;
    });
    if (!wrapAroundConstraintSatisfied) {
        throw new Error('Wrap-around constraint not satisfied');
    }
    return moduli;
};

// Returns little-endian
const baseConverter = (num: bigint, base: bigint): bigint[] => {
    let unconverted = num;
    const converted: bigint[] = [];
    while (unconverted >= base) {
        converted.unshift(unconverted % base);
        unconverted /= base;
    }
    converted.unshift(unconverted);
    return converted.reverse();
}

const partiallyReducedProduct = (base : bigint, reductionModulo : bigint, x : bigint[], y : bigint[]): bigint => {
    const product = x.map(x_i => BigInt(x_i)).reduce((outerSum, x_i, i) => {
        return outerSum + y.map(y_j => BigInt(y_j)).reduce((innerSum, y_j, j) => {
            const iPlusJ = BigInt(i + j);
            return innerSum + ((base**iPlusJ) % reductionModulo) * (x_i * y_j);
         }, 0n);
    }, 0n);
    return product;
}

const partiallyReducedProductModQ = (base : bigint, q : bigint, reductionModulo : bigint, x : bigint[], y : bigint[]): bigint => {
    const product = x.map(x_i => BigInt(x_i)).reduce((outerSum, x_i, i) => {
        return outerSum + y.map(y_j => BigInt(y_j)).reduce((innerSum, y_j, j) => {
            const iPlusJ = BigInt(i + j);
            const baseExponentiation = (((base**iPlusJ) % q) % reductionModulo);
            return innerSum + baseExponentiation * (x_i * y_j);
         }, 0n);
    }, 0n);
    return product;
}

const partiallyReducedSum = (base : bigint, reductionModulo : bigint, x : bigint[]): bigint => {
    const sum = x.map(x_i => BigInt(x_i)).reduce((s, x_i, i) => {
        return s + ((base**BigInt(i)) % reductionModulo) * x_i;
    }, 0n);
    return sum;
}

const partiallyReducedSumModQ = (base : bigint, q : bigint, reductionModulo : bigint, x : bigint[]): bigint => {
    const sum = x.map(x_i => BigInt(x_i)).reduce((s, x_i, i) => {
        return s + (((base**BigInt(i)) % q) % reductionModulo) * x_i;
    }, 0n);
    return sum;
}

const padArrayToLen = (arr: bigint[], len: number): bigint[] => {
    return Array.from({length: len}, (_, i) => arr[i] ?? 0n)
};

const stringifyBigintArray = (arr: bigint[]): string => {
    let str = JSON.stringify(arr);
    // remove quotes
    str = str.replace(/"/ig, '');
    // separate values by ', '
    str = str.replace(/,/ig, ', ');
    return str;
}

const genProverToml = (numLimbs: number, x: bigint[], y: bigint[], zModQ: bigint[], r: bigint, s: bigint[]): string => {
    let tomlStr = '# Prover.toml'
    tomlStr += `\nx=${stringifyBigintArray(padArrayToLen(x, numLimbs))}`;
    tomlStr += `\ny=${stringifyBigintArray(padArrayToLen(y, numLimbs))}`;
    tomlStr += `\nz_mod_q=${stringifyBigintArray(padArrayToLen(zModQ, numLimbs))}`;
    tomlStr += `\nr=${r}`;
    tomlStr += `\ns=${stringifyBigintArray(s)}`;
    return tomlStr;
}

const genParamsStruct = (numLimbs: number, base: bigint, q: bigint[], m: bigint[], qModM: bigint[], baseExponentiations: bigint[][]): string => {
    let paramsStructStr = 'Self {';
    paramsStructStr += `\n    base: ${base},`;
    paramsStructStr += `\n    q: BigInt::new(${stringifyBigintArray(padArrayToLen(q, numLimbs))}),`;
    paramsStructStr += `\n    m: ${stringifyBigintArray(m)},`;
    paramsStructStr += `\n    q_mod_m: ${stringifyBigintArray(qModM)},`;
    paramsStructStr += `\n    base_exponentiations: ${stringifyBigintArray(baseExponentiations.flat())},`;
    paramsStructStr += `\n}`;
    return paramsStructStr;
}

const mulModNonDeterministicHelper = (
    b: bigint,
    numLimbs: number,
    x: bigint,
    y: bigint,
    q: bigint,
    m: bigint[],
    useNativeFieldAsModulo: boolean,
) => {
    const baseExponentiations: bigint[][] = [];
    const qModM: bigint[] = [];
    const s: bigint[] = []; // witness
    const zModQ = (x * y) % q;
    const xBase32 = baseConverter(x, b); // witness
    const yBase32 = baseConverter(y, b); // witness
    const qBase32 = baseConverter(q, b); // witness
    const zModQBase32 = baseConverter(zModQ, b); // witness
    const productReducedQ = partiallyReducedProduct(b, q, xBase32, yBase32);
    const sumReducedQ = partiallyReducedSum(b, q, zModQBase32);
    const r = (productReducedQ - sumReducedQ) / q; // witness
    m.forEach((m_i) => {
        const baseExponentiationsModQMi: bigint[] = [];
        for (let i = 0; i < (numLimbs - 1) * 2 + 1; i++) {
            const baseExponentiationModQMi = (b ** BigInt(i)) % q % m_i;
            baseExponentiationsModQMi.push(baseExponentiationModQMi);
        }
        const qModMi = q % m_i;
        qModM.push(qModMi);
        const productReducedQMi = partiallyReducedProductModQ(b, q, m_i, xBase32, yBase32);
        const sumReducedQMi = partiallyReducedSumModQ(b, q, m_i, zModQBase32);
        console.log(`m_i: ${m_i}`);
        console.log(`product: ${productReducedQMi}`);
        console.log(`sum: ${sumReducedQMi}`);
        const s_i = (productReducedQMi - sumReducedQMi - (r * qModMi)) / m_i; // witness
        s.push(s_i);
        baseExponentiations.push(baseExponentiationsModQMi);
    });
    // console.log(`x=${x}`);
    // console.log(`y=${y}`);
    // console.log(`q=${q}`);
    // console.log(`z_mod_q=${zModQ}`);
    // console.log(`M=${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`partially_reduced_product=${productReducedQ.valueOf()}`);
    // console.log(`partially_reduced_sum=${sumReducedQ.valueOf()}`);
    // console.log(`base_exponentiations=${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/,/ig, ', '));

    // console.log(`x=${JSON.stringify(padArrayToLen(xBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`y=${JSON.stringify(padArrayToLen(yBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`z_mod_q=${JSON.stringify(padArrayToLen(zModQBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`r=${r.valueOf()}`);
    // console.log(`s=${JSON.stringify(s)}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(s.map(n => String(n).length));

    // console.log(`base: ${b.valueOf()},`);
    // console.log(`q: ${JSON.stringify(padArrayToLen(qBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    // if (useNativeFieldAsModulo) {
    //     m.shift();
    //     const nativeFieldQModM = qModM.shift();
    //     const nativeFieldBaseExponentiation = baseExponentiations.shift();
    //     console.log(`m: ${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`q_mod_m: ${JSON.stringify(qModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`base_exponentiations: ${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`native_field_q_mod_m: ${JSON.stringify(nativeFieldQModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`native_field_base_exponentiation: ${JSON.stringify(nativeFieldBaseExponentiation)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    // } else {
    //     console.log(`m: ${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`q_mod_m: ${JSON.stringify(qModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`base_exponentiations: ${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/\],\[/ig, ',\n').replace(/,/ig, ', ') + ',');
    // }
    return {
        xBase32,
        yBase32,
        qBase32,
        zModQBase32,
        r,
        s,
        qModM,
        baseExponentiations,
    }
}


const run = () => {
    const baseFieldOrder = bn254.CURVE.Fp.ORDER;
    const useNativeFieldAsModulo = false;
    const base = 4294967296n;
    const numLimbs = 9;
    const x = 8457179954364567802776200328751639987550736n;
    const y = 371871151960082407017394978175294924545716958041n;
    // const q = ed25519.CURVE.Fp.ORDER;
    const q = P256.CURVE.Fp.ORDER;

    const m = findModuli(useNativeFieldAsModulo, baseFieldOrder, q, BigInt(numLimbs), base);

    const {
        xBase32,
        yBase32,
        qBase32,
        zModQBase32,
        r,
        s,
        qModM,
        baseExponentiations,
    } = mulModNonDeterministicHelper(
        base,
        numLimbs,
        x,
        y,
        q,
        m,
        useNativeFieldAsModulo,
    );

    console.log(genProverToml(numLimbs, xBase32, yBase32, zModQBase32, r, s));
    console.log();
    console.log(genParamsStruct(numLimbs, base, qBase32, m, qModM, baseExponentiations));
}
run();