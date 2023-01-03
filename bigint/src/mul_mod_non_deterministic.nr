// Support functions for BigInt. Performs non-deterministic modular multiplication, as described in
// https://blog.polygon.technology/wp-content/uploads/2022/10/casting-3.pdf

use crate::constants;
use crate::BigInt;

global NUM_REDUCTION_MODULI : Field = 3;
global NUM_BASE_EXPONENTIATIONS : Field = 15; // ((constants::NUM_LIMBS - 1) * 2) + 1
global NUM_TOTAL_BASE_EXPONENTIATIONS : Field = 45; // NUM_BASE_EXPONENTIATIONS * NUM_REDUCTION_MODULI

struct NonDetermMulModder {
    base : Field,
    q : BigInt, // modulus
    m : [Field; NUM_REDUCTION_MODULI],
    q_mod_m : [Field; NUM_REDUCTION_MODULI],
    base_exponentiations : [Field; NUM_TOTAL_BASE_EXPONENTIATIONS], // base^i mod q mod m_i
}

impl NonDetermMulModder {
    // n^2 * b^2 ~ 2^7 * 2^64 (for 8-limbs of 32-bits each)
    fn rMax(self) -> u96 {
        (constants::NUM_LIMBS as u96 * constants::NUM_LIMBS as u96) * (self.base as u96 * self.base as u96)
    }

    // 2 * n^2 * b^2 ~ 2^1 * 2^7 * 2^64 (for 8-limbs of 32-bits each)
    fn sMax(self) -> u96 {
        2 * (constants::NUM_LIMBS as u96 * constants::NUM_LIMBS as u96) * (self.base as u96 * self.base as u96)
    }

    fn range_checks(self, r : Field, s : [Field; NUM_REDUCTION_MODULI]) {
        let rMax = self.rMax();
        constrain r as u96 < rMax;
        let sMax = self.sMax();
        for i in 0..NUM_REDUCTION_MODULI {
            constrain s[i] as u96 < sMax;
        }
    }

    fn mul_mod(
        self,
        x : BigInt,
        y : BigInt,
        z_mod_q : BigInt,
        r : Field,
        s : [Field; NUM_REDUCTION_MODULI],
    ) {
        // small-moduli checks
        for i in 0..NUM_REDUCTION_MODULI {
            let mut base_exponentiations = [0 as Field; NUM_BASE_EXPONENTIATIONS];
            for j in 0..NUM_BASE_EXPONENTIATIONS {
                base_exponentiations[j] = self.base_exponentiations[(i * NUM_BASE_EXPONENTIATIONS) + j];
            };
            let product = partially_reduced_product_mod_q(base_exponentiations, x, y);
            let sum = partially_reduced_sum_mod_q(base_exponentiations, z_mod_q);
            constrain product - sum - (r * self.q_mod_m[i]) == s[i] * self.m[i];
        };
        
        // parameter range checks
        self.range_checks(r, s);
    }
    
    fn curve_25519() -> Self {
        // Note the following params are particular to 256-bit bigints consisting of 8 32-bit limbs
        Self {
            base: 4294967296,
            q: BigInt::new([4294967277, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 2147483647]),
            m: [1399027476140078653058704379177609361753676736201, 1167555264947830116235753479722409858771985625309, 778213806565775850770437273987932725759002427],
            q_mod_m: [1316241300184381109162253431261133960278563944023, 1136987601934002542966226275988151516841676979977, 85301471125930773099268390915675682270633578],
            base_exponentiations: [1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 62474161190824265144980453538673657902255806775, 785544700709767454874630330817893447601751994227, 959298029804956539157843685617882740144615618583, 38, 163208757248, 700976274800962961408, 3010670175542044828554670112768, 12930729942995661611608235082407192035328, 974990649111243422450552855291989638532043921249, 471121628029511571003160608350154412039364320405, 1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 293946372383072801967931352993873160883946917667, 458614169423370178615228557339798183603632722609, 933741043567496358873178845559455842735255904927, 38, 163208757248, 700976274800962961408, 3010670175542044828554670112768, 12930729942995661611608235082407192035328, 661964766026295428659610096265491384642112243565, 1081564728818445160078136462798592954130244704816, 1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 16108600375870456803632166945360680525985070, 102021630299607550116882014397212625540536895, 92710417667727103238048228423331643116445176, 38, 163208757248, 700976274800962961408, 3010670175542044828554670112768, 12930729942995661611608235082407192035328, 612126814283077358538022343923705859987432660, 763966725121983501359767451142348867504392302],
        }
    }
}

fn partially_reduced_sum_mod_q(base_exponentiations : [Field; NUM_BASE_EXPONENTIATIONS], x : BigInt) -> Field {
    let mut result = 0;
    for i in 0..constants::NUM_LIMBS {
        result = result + (base_exponentiations[i] * x.limbs[i] as Field);
    };
    result
}

fn partially_reduced_product_mod_q(base_exponentiations : [Field; NUM_BASE_EXPONENTIATIONS], x : BigInt, y : BigInt) -> Field {
    let mut result = 0;
    for i in 0..constants::NUM_LIMBS {
        for j in 0..constants::NUM_LIMBS {
            result = result + (base_exponentiations[i + j] * (x.limbs[i] as Field * y.limbs[j] as Field));
        };
    };
    result
}

// Tests
fn run_tests() {
    test_partially_reduced_sum_mod_q();
    test_partially_reduced_product_mod_q();
    test_range_checks();
    test_mul_mod();
}

// mul_mod
fn test_mul_mod_case1() {
    let x = BigInt::new([3320379920, 1938147428, 1942509796, 1795943184, 24853, 0, 0, 0]);
    let y = BigInt::new([2912727897, 3590519536, 1687587470, 3896107618, 1092831095, 0, 0, 0]);
    let z_mod_q = BigInt::new([4104057479, 1317660176, 3369491359, 1574675528, 718719913, 3448263837, 3220071330, 1040409407]);
    let r = 913981063;
    let s = [7034590962026984280, 8353757445643061182, 1692690955609806861];

    let curve_25519_mul_modder = NonDetermMulModder::curve_25519();
    curve_25519_mul_modder.mul_mod(x, y, z_mod_q, r, s);
}


fn test_mul_mod() {
    test_mul_mod_case1();
}


// partially_reduced_sum_mod_q
fn test_partially_reduced_sum_mod_q_case1() {
    let base_exponentiations = [1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055];
    let x=BigInt::new([4104057479,1317660176,3369491359,1574675528,718719913,3448263837,3220071330,1040409407]);
    let expected_sum = 196387155814770375;
    let sum = partially_reduced_sum_mod_q(base_exponentiations, x);
    constrain sum == expected_sum;
}

fn test_partially_reduced_sum_mod_q() {
    test_partially_reduced_sum_mod_q_case1();
}

// partially_reduced_product_mod_q
fn test_partially_reduced_product_mod_q_case1() {
    let base_exponentiations = [1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055];
    let x = BigInt::new([3320379920,1938147428,1942509796,1795943184,24853,0,0,0]);
    let y = BigInt::new([2912727897,3590519536,1687587470,3896107618,1092831095,0,0,0]);
    let expected_product = 2418553383339735974797683108;
    let product = partially_reduced_product_mod_q(base_exponentiations, x, y);
    constrain product == expected_product;
}

fn test_partially_reduced_product_mod_q() {
    test_partially_reduced_product_mod_q_case1();
}

// range_checks
fn test_range_checks_case1() {
    let mul_modder = NonDetermMulModder {
        base: 10,
        q: BigInt::new([9; constants::NUM_LIMBS]),
        m: [2; NUM_REDUCTION_MODULI],
        q_mod_m: [1; NUM_REDUCTION_MODULI],
        base_exponentiations: [1; NUM_TOTAL_BASE_EXPONENTIATIONS],
    };
    let r : Field = 6399;
    let s : [Field; NUM_REDUCTION_MODULI] = [12799; NUM_REDUCTION_MODULI];

    // TODO: Range check failure threshold
    // let r : Field = 6400;
    // let s : [Field; NUM_REDUCTION_MODULI] = [12800; NUM_REDUCTION_MODULI];
    
    mul_modder.range_checks(r, s);
}

fn test_range_checks() {
    test_range_checks_case1();
}