declare var require: any;

const { P256 } = require('@noble/curves/p256');
const { bn254 } = require('@noble/curves/bn');
const { ed25519 } = require('@noble/curves/ed25519');

(BigInt.prototype as any).toJSON = function() { return this.toString() }

const precomputeGPowers = (G: any, windows: number, windowLength: number): any[][] => {
    // windows = 64
    // windowLength = 4
    const GPow: any[][] = [];
    let windowBase = G;
    for (let i = 0; i < windows; i++) {
        GPow[i] = [windowBase];
        for (let j = 1; j < 2 ** windowLength; j++) {
            GPow[i].push(GPow[i][j - 1].add(windowBase));
        };
        windowBase = windowBase.multiply(2 ** windowLength)
    }
    console.log(GPow);
    return GPow;
}

precomputeGPowers(P256.Point.BASE, 64, 4);
    
export {}


const L: number = 9;
const L2: number = 18;

function powArr(): bigint[] {
  const arr: bigint[] = Array(L2).fill(1).map(e => BigInt(e));
  for (let i = 1; i < L2; i++) {
    arr[i * L2] = 1n;
    for (let j = 1; j < L2; j++) {
      arr[i * L2 + j] = arr[i * L2 + j - 1] * BigInt(i);
    }
  }
  return arr;
}

function testMul(a: bigint[], b: bigint[]) {
  const prodUncarried = Array(17).fill(0n);
  for (let i = 0; i < L; i++) {
    for (let j = 0; j < L; j++) {
      prodUncarried[i + j] = prodUncarried[i + j] + (a[i] * b[j]);
    }
  }
  return prodUncarried;
}