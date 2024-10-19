use ark_ff::fields::{Fp256, MontBackend, MontConfig};
use std::convert::TryInto;

cfg_if::cfg_if! {
    if #[cfg(feature = "asm")] {
        #[derive(MontConfig)]
        #[modulus = "21888242871839275222246405745257275088696311157297823662689037894645226208583"]
        #[generator = "7"]
        pub struct FqConfig;
        pub type FpGrumpkin = Fp256<MontBackend<FqConfig, 4>>;
    } else {
        #[derive(MontConfig)]
        #[modulus = "21888242871839275222246405745257275088696311157297823662689037894645226208583"]
        #[generator = "7"]
        pub struct FqConfig;
        pub type FpGrumpkin = Fp256<MontBackend<FqConfig, 4>>;
    }
}