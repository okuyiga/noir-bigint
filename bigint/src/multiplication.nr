use crate::constants;
use crate::BigInt;

// Hardcoded i^j values for i ∈ [0, 2 * constants::NUM_LIMBS - 1], j ∈ [0, 2 * constants::NUM_LIMBS - 1]
// Used for polynomial evaluation
// i^j == pow_arr[i * (2 * constants::NUM_LIMBS) + j]
fn pow_arr() -> [comptime Field; (2 * constants::NUM_LIMBS) * (2 * constants::NUM_LIMBS)] {
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969, 14348907, 43046721, 129140163, 1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216, 67108864, 268435456, 1073741824, 4294967296, 17179869184, 1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125, 9765625, 48828125, 244140625, 1220703125, 6103515625, 30517578125, 152587890625, 762939453125, 1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616, 10077696, 60466176, 362797056, 2176782336, 13060694016, 78364164096, 470184984576, 2821109907456, 16926659444736, 1, 7, 49, 343, 2401, 16807, 117649, 823543, 5764801, 40353607, 282475249, 1977326743, 13841287201, 96889010407, 678223072849, 4747561509943, 33232930569601, 232630513987207, 1, 8, 64, 512, 4096, 32768, 262144, 2097152, 16777216, 134217728, 1073741824, 8589934592, 68719476736, 549755813888, 4398046511104, 35184372088832, 281474976710656, 2251799813685248, 1, 9, 81, 729, 6561, 59049, 531441, 4782969, 43046721, 387420489, 3486784401, 31381059609, 282429536481, 2541865828329, 22876792454961, 205891132094649, 1853020188851841, 16677181699666569, 1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000, 10000000000, 100000000000, 1000000000000, 10000000000000, 100000000000000, 1000000000000000, 10000000000000000, 100000000000000000, 1, 11, 121, 1331, 14641, 161051, 1771561, 19487171, 214358881, 2357947691, 25937424601, 285311670611, 3138428376721, 34522712143931, 379749833583241, 4177248169415651, 45949729863572161, 505447028499293771, 1, 12, 144, 1728, 20736, 248832, 2985984, 35831808, 429981696, 5159780352, 61917364224, 743008370688, 8916100448256, 106993205379072, 1283918464548864, 15407021574586368, 184884258895036416, 2218611106740436992, 1, 13, 169, 2197, 28561, 371293, 4826809, 62748517, 815730721, 10604499373, 137858491849, 1792160394037, 23298085122481, 302875106592253, 3937376385699289, 51185893014090757, 665416609183179841, 8650415919381337933, 1, 14, 196, 2744, 38416, 537824, 7529536, 105413504, 1475789056, 20661046784, 289254654976, 4049565169664, 56693912375296, 793714773254144, 11112006825558016, 155568095557812224, 2177953337809371136, 30491346729331195904, 1, 15, 225, 3375, 50625, 759375, 11390625, 170859375, 2562890625, 38443359375, 576650390625, 8649755859375, 129746337890625, 1946195068359375, 29192926025390625, 437893890380859375, 6568408355712890625, 98526125335693359375, 1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976, 18446744073709551616, 295147905179352825856, 1, 17, 289, 4913, 83521, 1419857, 24137569, 410338673, 6975757441, 118587876497, 2015993900449, 34271896307633, 582622237229761, 9904578032905937, 168377826559400929, 2862423051509815793, 48661191875666868481, 827240261886336764177
]
}

fn handle_carry(prod_uncarried: [Field; 2 * constants::NUM_LIMBS - 1]) -> [u32; 2 * constants::NUM_LIMBS] {
    let mut prod = [0 as u32; 2 * constants::NUM_LIMBS];
    let mut current_prod_uncarried_limb = prod_uncarried[0] as u96;
    prod[0] = current_prod_uncarried_limb as u32;
    let mut carry: u96 = current_prod_uncarried_limb / (1 << constants::LIMB_BITS as u96);
    for i in 1..(2 * constants::NUM_LIMBS - 1) {
        current_prod_uncarried_limb = prod_uncarried[i] as u96 + carry;
        prod[i] = current_prod_uncarried_limb as u32;
        carry = current_prod_uncarried_limb / (1 << constants::LIMB_BITS as u96);
    }
    prod[2 * constants::NUM_LIMBS - 1] = carry as u32;
    prod
}

// https://0xparc.org/blog/zk-ecdsa-2
// For k n-bit limbs, no_carry returns 2*k-1 limbs with a max of k*(2^n)^2 or (2n+log(k)) bits
fn mul_no_carry(a: [Field; constants::NUM_LIMBS], b: [Field; constants::NUM_LIMBS]) -> [Field; 2 * constants::NUM_LIMBS - 1] {
    // assert bit_size_x + bit_size_y <= 253 ?
    let mut prod_uncarried = [0 as Field; 2 * constants::NUM_LIMBS - 1];
    for i in 0..constants::NUM_LIMBS {
        for j in 0..constants::NUM_LIMBS {
            prod_uncarried[i + j] = prod_uncarried[i + j] + (a[i] * b[j]);
        }
    }
    let mut a_poly = [0 as Field; 2 * constants::NUM_LIMBS - 1];
    let mut b_poly = [0 as Field; 2 * constants::NUM_LIMBS - 1];
    let mut prod_poly = [0 as Field; 2 * constants::NUM_LIMBS - 1];
    let mut a_times_b_poly = [0 as Field; 2 * constants::NUM_LIMBS - 1];

    let pows = pow_arr();

    for i in 0..(2 * constants::NUM_LIMBS - 1) {
        for j in 0..(2 * constants::NUM_LIMBS - 1) {
            prod_poly[i] = prod_poly[i] + (prod_uncarried[j] * pows[i * (2 * constants::NUM_LIMBS) + j]);
        }
        for j in 0..constants::NUM_LIMBS {
            let pow = pows[i * (2 * constants::NUM_LIMBS) + j];
            a_poly[i] = a_poly[i] + (a[j] * pow);
            b_poly[i] = b_poly[i] + (b[j] * pow);
        }
        a_times_b_poly[i] = a_poly[i] * b_poly[i];
    }

    for i in 0..((2 * constants::NUM_LIMBS) - 1) {
        constrain prod_poly[i] - a_times_b_poly[i] == 0;
    }
    prod_uncarried
}

fn arr_to_field(arr: [u32; constants::NUM_LIMBS]) -> [Field; constants::NUM_LIMBS] {
    let mut as_field: [Field; constants::NUM_LIMBS] = [0 as Field; constants::NUM_LIMBS];
    for i in 0..constants::NUM_LIMBS {
        as_field[i] = arr[i] as Field;
    }
    as_field
}

fn mul(a: [u32; constants::NUM_LIMBS], b: [u32; constants::NUM_LIMBS]) -> [u32; 2 * constants::NUM_LIMBS] {
    let a_as_field = arr_to_field(a);
    let b_as_field = arr_to_field(b);
    let prod_uncarried = mul_no_carry(a_as_field, b_as_field);
    let prod = handle_carry(prod_uncarried);
    prod
}

fn mul_add(a: [u32; constants::NUM_LIMBS], b: [u32; constants::NUM_LIMBS], c: [u32; constants::NUM_LIMBS]) -> [u32; 2 * constants::NUM_LIMBS] {
    let a_as_field = arr_to_field(a);
    let b_as_field = arr_to_field(b);
    let mut prod_uncarried = mul_no_carry(a_as_field, b_as_field);

    // no_carry returns 2*k-1 limbs with a max of k*(2^n)^2
    // so addition gives us a max of k*(2^n)^2+(2^n) which is only marginally larger
    // with that being said, we should still be careful of how we carry
    for i in 0..constants::NUM_LIMBS {
        prod_uncarried[i] = prod_uncarried[i] + c[i] as Field;
    }
    let result = handle_carry(prod_uncarried);

    result
}

// Verifies a * b = c (mod p) 
// Using witnessed c, q to constrain

// Helper function for verifying multiplication modulo p
// Tring to show a * b == p * q + c
fn verify_mul_mod_helper(a: [u32; constants::NUM_LIMBS], b: [u32; constants::NUM_LIMBS], c: [u32; constants::NUM_LIMBS], p: [u32; constants::NUM_LIMBS], q: [u32; constants::NUM_LIMBS]) -> ([u32; 2 * constants::NUM_LIMBS], [u32; 2 * constants::NUM_LIMBS]){
    let a_times_b = mul(a, b);
    let p_times_q_plus_c = mul_add(p, q, c);
    (a_times_b, p_times_q_plus_c)
}

// Tests
fn run_tests() {
    test_mul_no_carry();
    test_handle_carry();
}

// mul_no_carry
fn test_mul_no_carry_case1() {
    let a = [3320379920,1938147428,1942509796,1795943184,24853,0,0,0, 0];
    let b = [2912727897,3590519536,1687587470,3896107618,1092831095,0,0,0, 0];
    let a_as_field = arr_to_field(a);
    let b_as_field = arr_to_field(b);
    let prod_uncarried = mul_no_carry(a_as_field, b_as_field);
    let expected = [9671363221622628240, 17567185051736516036, 18220390225518734820, 28413064000344936424, 20906442052633841789, 12717195439580232276, 9120064969699874242, 1962759386291136634, 27160131204035, 0, 0, 0, 0, 0, 0, 0, 0];
    constrain expected == prod_uncarried;
}

fn test_mul_no_carry() {
    test_mul_no_carry_case1();
}

// handle_carry
fn test_handle_carry_case1() {
    let prod_uncarried = [9671363221622628240, 17567185051736516036, 18220390225518734820, 28413064000344936424, 20906442052633841789, 12717195439580232276, 9120064969699874242, 1962759386291136634, 27160131204035, 0, 0, 0, 0, 0, 0, 0, 0];
    let carried = handle_carry(prod_uncarried);
    let expected = [3868729232, 1317419871, 3369491359, 1574675528, 718719913, 3448263837, 3220071330, 3187893055, 3509981958, 6323, 0, 0, 0, 0, 0, 0, 0, 0];
    constrain expected == carried;
}

fn test_handle_carry() {
    test_handle_carry_case1();
}