use super::poseidon2_params::Poseidon2Params;
// use crate::merkle_tree::merkle_tree_fp::MerkleTreeHash;
use ark_ff::PrimeField;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct Poseidon2<F: PrimeField> {
    pub(crate) params: Arc<Poseidon2Params<F>>,
}

impl<F: PrimeField> Poseidon2<F> {
    pub fn new(params: &Arc<Poseidon2Params<F>>) -> Self {
        Poseidon2 {
            params: Arc::clone(params),
        }
    }

    pub fn get_t(&self) -> usize {
        self.params.t
    }

    pub fn permutation(&self, input: &[F]) -> Vec<F> {
        let t = self.params.t;
        assert_eq!(input.len(), t);

        let mut current_state = input.to_owned();

        // Linear layer at beginning
        self.matmul_external(&mut current_state);

        for r in 0..self.params.rounds_f_beginning {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }

        let p_end = self.params.rounds_f_beginning + self.params.rounds_p;
        for r in self.params.rounds_f_beginning..p_end {
            current_state[0].add_assign(&self.params.round_constants[r][0]);
            current_state[0] = self.sbox_p(&current_state[0]);
            self.matmul_internal(&mut current_state, &self.params.mat_internal_diag_m_1);
        }
        
        for r in p_end..self.params.rounds {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }
        current_state
    }

    fn sbox(&self, input: &[F]) -> Vec<F> {
        input.iter().map(|el| self.sbox_p(el)).collect()
    }

    fn sbox_p(&self, input: &F) -> F {
        let mut input2 = *input;
        input2.square_in_place();

        match self.params.d {
            3 => {
                let mut out = input2;
                out.mul_assign(input);
                out
            }
            5 => {
                let mut out = input2;
                out.square_in_place();
                out.mul_assign(input);
                out
            }
            7 => {
                let mut out = input2;
                out.square_in_place();
                out.mul_assign(&input2);
                out.mul_assign(input);
                out
            }
            _ => {
                panic!()
            }
        }
    }

    fn matmul_m4(&self, input: &mut[F]) {
        let t = self.params.t;
        let t4 = t / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2.double_in_place();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3.double_in_place();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double_in_place();
            t_4.double_in_place();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double_in_place();
            t_5.double_in_place();
            t_5.add_assign(&t_2);
            let mut t_6 = t_3;
            t_6.add_assign(&t_5);
            let mut t_7 = t_2;
            t_7.add_assign(&t_4);
            input[start_index] = t_6;
            input[start_index + 1] = t_5;
            input[start_index + 2] = t_7;
            input[start_index + 3] = t_4;
        }
    }

    fn matmul_external(&self, input: &mut[F]) {
        let t = self.params.t;
        match t {
            2 => {
                // Matrix circ(2, 1)
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
            }
            3 => {
                // Matrix circ(2, 1, 1)
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                sum.add_assign(&input[2]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
                input[2].add_assign(&sum);
            }
            4 => {
                // Applying cheap 4x4 MDS matrix to each 4-element part of the state
                self.matmul_m4(input);
            }
            8 | 12 | 16 | 20 | 24 => {
                // Applying cheap 4x4 MDS matrix to each 4-element part of the state
                self.matmul_m4(input);

                // Applying second cheap matrix for t > 4
                let t4 = t / 4;
                let mut stored = [F::zero(); 4];
                for l in 0..4 {
                    stored[l] = input[l];
                    for j in 1..t4 {
                        stored[l].add_assign(&input[4 * j + l]);
                    }
                }
                for i in 0..input.len() {
                    input[i].add_assign(&stored[i % 4]);
                }
            }
            _ => {
                panic!()
            }
        }
    }

    fn matmul_internal(&self, input: &mut[F], mat_internal_diag_m_1: &[F]) {
        let t = self.params.t;

        match t {
            2 => {
                // [2, 1]
                // [1, 3]
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                input[0].add_assign(&sum);
                input[1].double_in_place();
                input[1].add_assign(&sum);
            }
            3 => {
                // [2, 1, 1]
                // [1, 2, 1]
                // [1, 1, 3]
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                sum.add_assign(&input[2]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
                input[2].double_in_place();
                input[2].add_assign(&sum);
            }
            4 | 8 | 12 | 16 | 20 | 24 => {
                // Compute input sum
                let mut sum = input[0];
                input
                    .iter()
                    .skip(1)
                    .take(t-1)
                    .for_each(|el| sum.add_assign(el));
                // Add sum + diag entry * element to each element
                for i in 0..input.len() {
                    input[i].mul_assign(&mat_internal_diag_m_1[i]);
                    input[i].add_assign(&sum);
                }
            }
            _ => {
                panic!()
            }
        }
    }

    fn add_rc(&self, input: &[F], rc: &[F]) -> Vec<F> {
        input
            .iter()
            .zip(rc.iter())
            .map(|(a, b)| {
                let mut r = *a;
                r.add_assign(b);
                r
            })
            .collect()
    }
}

// impl<F: PrimeField> MerkleTreeHash<F> for Poseidon2<F> {
//     fn compress(&self, input: &[&F]) -> F {
//         self.permutation(&[input[0].to_owned(), input[1].to_owned(), F::zero()])[0]
//     }
// }

#[allow(unused_imports)]
#[cfg(test)]
mod poseidon2_tests_bn256 {
    use super::*;
    use crate::{fields::{bn256::FpBN256, utils::from_hex, utils::random_scalar}, plain::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS};
    use std::convert::TryFrom;

    type Scalar = FpBN256;

    static TESTRUNS: usize = 5;

    #[test]
    fn consistent_perm() {
        let poseidon2 = Poseidon2::new(&POSEIDON2_BN256_PARAMS);
        let t = poseidon2.params.t;
        for _ in 0..TESTRUNS {
            let input1: Vec<Scalar> = (0..t).map(|_| random_scalar()).collect();

            let mut input2: Vec<Scalar>;
            loop {
                input2 = (0..t).map(|_| random_scalar()).collect();
                if input1 != input2 {
                    break;
                }
            }

            let perm1 = poseidon2.permutation(&input1);
            let perm2 = poseidon2.permutation(&input1);
            let perm3 = poseidon2.permutation(&input2);
            assert_eq!(perm1, perm2);
            assert_ne!(perm1, perm3);
        }
    }

    #[test]
    fn kats() {
        let poseidon2 = Poseidon2::new(&POSEIDON2_BN256_PARAMS);
        let mut input: Vec<Scalar> = vec![];
        for i in 0..poseidon2.params.t {
            input.push(Scalar::from(i as u64));
        }
        let perm = poseidon2.permutation(&input);
        assert_eq!(perm[0], from_hex("0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033"));
        assert_eq!(perm[1], from_hex("0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570"));
        assert_eq!(perm[2], from_hex("0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8"));

    }
}

// #[allow(unused_imports)]
// #[cfg(test)]
// mod poseidon2_tests_pallas {
//     use super::*;
//     use crate::{fields::{pallas::FpPallas, utils::from_hex, utils::random_scalar}};
//     use crate::poseidon2::poseidon2_instance_pallas::{
//         POSEIDON2_PALLAS_3_PARAMS,
//         POSEIDON2_PALLAS_4_PARAMS,
//         POSEIDON2_PALLAS_8_PARAMS,
//     };
//     use std::convert::TryFrom;

//     type Scalar = FpPallas;

//     static TESTRUNS: usize = 5;

//     #[test]
//     fn consistent_perm() {
//         let instances = vec![
//             Poseidon2::new(&POSEIDON2_PALLAS_3_PARAMS),
//             Poseidon2::new(&POSEIDON2_PALLAS_4_PARAMS),
//             Poseidon2::new(&POSEIDON2_PALLAS_8_PARAMS)
//         ];
//         for instance in instances {
//             let t = instance.params.t;
//             for _ in 0..TESTRUNS {
//                 let input1: Vec<Scalar> = (0..t).map(|_| random_scalar()).collect();

//                 let mut input2: Vec<Scalar>;
//                 loop {
//                     input2 = (0..t).map(|_| random_scalar()).collect();
//                     if input1 != input2 {
//                         break;
//                     }
//                 }

//                 let perm1 = instance.permutation(&input1);
//                 let perm2 = instance.permutation(&input1);
//                 let perm3 = instance.permutation(&input2);
//                 assert_eq!(perm1, perm2);
//                 assert_ne!(perm1, perm3);
//             }
//         }
//     }

//     #[test]
//     fn kats() {
//         let poseidon2 = Poseidon2::new(&POSEIDON2_PALLAS_3_PARAMS);
//         let mut input: Vec<Scalar> = vec![];
//         for i in 0..poseidon2.params.t {
//             input.push(Scalar::from(i as u64));
//         }
//         let perm = poseidon2.permutation(&input);
//         assert_eq!(perm[0], from_hex("0x1a9b54c7512a914dd778282c44b3513fea7251420b9d95750baae059b2268d7a"));
//         assert_eq!(perm[1], from_hex("0x1c48ea0994a7d7984ea338a54dbf0c8681f5af883fe988d59ba3380c9f7901fc"));
//         assert_eq!(perm[2], from_hex("0x079ddd0a80a3e9414489b526a2770448964766685f4c4842c838f8a23120b401"));

//     }
// }

// #[allow(unused_imports)]
// #[cfg(test)]
// mod poseidon2_tests_vesta {
//     use super::*;
//     use crate::{fields::{vesta::FpVesta, utils::from_hex, utils::random_scalar}, poseidon2::poseidon2_instance_vesta::POSEIDON2_VESTA_PARAMS};
//     use std::convert::TryFrom;

//     type Scalar = FpVesta;

//     static TESTRUNS: usize = 5;

//     #[test]
//     fn consistent_perm() {
//         let poseidon2 = Poseidon2::new(&POSEIDON2_VESTA_PARAMS);
//         let t = poseidon2.params.t;
//         for _ in 0..TESTRUNS {
//             let input1: Vec<Scalar> = (0..t).map(|_| random_scalar()).collect();

//             let mut input2: Vec<Scalar>;
//             loop {
//                 input2 = (0..t).map(|_| random_scalar()).collect();
//                 if input1 != input2 {
//                     break;
//                 }
//             }

//             let perm1 = poseidon2.permutation(&input1);
//             let perm2 = poseidon2.permutation(&input1);
//             let perm3 = poseidon2.permutation(&input2);
//             assert_eq!(perm1, perm2);
//             assert_ne!(perm1, perm3);
//         }
//     }

//     #[test]
//     fn kats() {
//         let poseidon2 = Poseidon2::new(&POSEIDON2_VESTA_PARAMS);
//         let mut input: Vec<Scalar> = vec![];
//         for i in 0..poseidon2.params.t {
//             input.push(Scalar::from(i as u64));
//         }
//         let perm = poseidon2.permutation(&input);
//         assert_eq!(perm[0], from_hex("0x261ecbdfd62c617b82d297705f18c788fc9831b14a6a2b8f61229bef68ce2792"));
//         assert_eq!(perm[1], from_hex("0x2c76327e0b7653873263158cf8545c282364b183880fcdea93ca8526d518c66f"));
//         assert_eq!(perm[2], from_hex("0x262316c0ce5244838c75873299b59d763ae0849d2dd31bdc95caf7db1c2901bf"));

//     }
// }