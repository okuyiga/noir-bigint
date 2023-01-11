use dep::std;
use dep::bigint;

fn main(
    x : [u32; bigint::constants::NUM_LIMBS],
    y : [u32; bigint::constants::NUM_LIMBS],
    z_mod_q : [u32; bigint::constants::NUM_LIMBS],
    r : Field,
    q : [u32; bigint::constants::NUM_LIMBS],
    s : [Field; bigint::mul_mod_non_deterministic::NUM_REDUCTION_MODULI],
) -> pub u32 {
    // bigint::run_tests();
    // bigint::multiplication::run_tests();

    // let r = bigint::arithmetic::sub_limbs_with_borrow(y[0], y[2], x[0]);


    let x_bi = bigint::BigInt::new(x);
    let y_bi = bigint::BigInt::new(y);
    let z_mod_q_bi = bigint::BigInt::new(z_mod_q);
    let p = bigint::BigInt::new([4294967295, 4294967295, 4294967295, 0, 0, 0, 1, 4294967295, 0]);
    let q_bi = bigint::BigInt::new(q); // 27160588200890
    // let p256_mul_modder = bigint::mul_mod_non_deterministic::NonDetermMulModder::p256();
    // p256_mul_modder.mul_mod(bigint::mul_mod_non_deterministic::MulModArgs {
    //     x: x_bi, y: y_bi, z_mod_q: z_mod_q_bi, r, s,
    // });
    // p256_mul_modder.range_checks(r, s);
    x_bi.verify_mul_mod(y_bi, z_mod_q_bi, p, q_bi);
    0 as u32

    // let base_exponentiations = [1, 4294967296, 18446744073709551616, 79228162514264337593543950336, 340282366920938463463374607431768211456, 62474161190824265144980453538673657902255806775, 785544700709767454874630330817893447601751994227, 959298029804956539157843685617882740144615618583, 38, 163208757248, 700976274800962961408, 3010670175542044828554670112768, 12930729942995661611608235082407192035328, 974990649111243422450552855291989638532043921249, 471121628029511571003160608350154412039364320405, 78610752946303508471746194861700719899798364928, 1444];
    // let sum = bigint::mul_mod_non_deterministic::partially_reduced_sum_mod_q(base_exponentiations, x_bi);
    // constrain sum as u64 != 1;

    // let cmp = x_bi.gte(y_bi);
    // let cmp = x_bi.lt(y_bi);
    // let cmp = x_bi.eq(y_bi);
    // x_bi.constrain_eq(y_bi);
    // constrain cmp == true;

    // let p256_field = bigint::ecdsa::FpField::p256();
    // let diff = p256_field.sub(x_bi, y_bi);
    // constrain diff.limbs[0] != 100;
    
    // let mut a = [0 as u8; bigint::constants::NUM_LIMBS];
    // for i in 0..bigint::constants::NUM_LIMBS {
    //     a[i] = x[i] as u8;
    // }
    // let mut digest = std::hash::sha256(a);
    // digest[0] = 9;
    // digest = std::hash::sha256(a);
    // constrain digest[0] > 0;

    // constrain x != y;
    // let x_as_bigint = bigint::BigInt::new(x);
    // let y_as_bigint = bigint::BigInt::new(y);
    // bigint::arithmetic::mul_limbs_with_carry(x[0], x[1], y[0], 0);
    // let product = x_as_bigint.mul(y_as_bigint);
    // product.limbs[0]
    // let expected_product_limbs = [1 as u32, 0, 0, 0, 0, 0, 0, 0, 4294967294, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295];
    // constrain product.limbs == expected_product_limbs;
    // bigint::test_cmp();
    // let a = bigint::BigInt::new(x);
    // let (a_msl_index, a2, a1, a0) = a.three_most_significant_limbs();
    // let b = bigint::BigInt::new(y);
    // let (b_msl_index, b1, b0) = b.two_most_significant_limbs();
    // let b = bigint::BigInt::new([9, 9, 2, 0, 0, 0, 0, 0]);
    // let result = bigint::division::div_wide(a.limbs[4], a.limbs[3], a.limbs[2], b.limbs[2], b.limbs[1]);
    // let a_trip = bigint::division::to_triple_limb(a0, a1, a2);
    // let b_trip = bigint::division::to_triple_limb(0, b0, b1);
    // let a_trip = ((a.limbs[4] as u96 * bigint::division::U96_POW_2_64) + (a.limbs[3] as u96 * bigint::division::U96_POW_2_32) + a.limbs[2] as u96);
    // let b_trip = ((b.limbs[2] as u96 * bigint::division::U96_POW_2_32) + b.limbs[1] as u96);
    // let q = a_trip / b_trip;
    // let r = lhs - (rhs * q);
    // let d = (a.limbs[4] & a.limbs[3]) + 1 - 1;
    // let e = (b.limbs[2] | b.limbs[1]) + 1 - 1;
    // let c = (a.limbs[4] & a.limbs[3]) / (b.limbs[2] | b.limbs[1]);
    
    // let q = bigint::div_rem_core(a, b);
    // let x = a.mul(b);
    // x.limbs[2]
    // constrain q.limbs[0] == 3221225479;
    // constrain q.limbs[1] == 2147483645;
    // constrain q.limbs[2] == 0;
    // q.limbs[0]
    // a.limbs[0]
    // q.overflow
    // result.0
}