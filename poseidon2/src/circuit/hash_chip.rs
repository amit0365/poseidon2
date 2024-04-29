//! An easy-to-use implementation of the Poseidon Hash in the form of a Halo2 Chip. While the Poseidon Hash function
//! is already implemented in halo2_gadgets, there is no wrapper chip that makes it easy to use in other circuits.
use super::pow5::{Pow5Chip, Pow5Config};
use super::primitives::{ConstantLength, Spec, Hash as inlineHash};
use super::poseidon::{Hash};

use halo2_proofs::halo2curves::serde::SerdeObject;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Chip, Value},
    halo2curves::{bn256::{self, Fq as Fp}, grumpkin},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Circuit}, dev::MockProver,
};
use halo2_proofs::arithmetic::Field;
use crate::circuit::spec::PoseidonSpec;
use crate::utils::TwoChainCurve;
use random::rngs::OsRng;
use std::marker::PhantomData;

pub const T: usize = 3;
pub const R: usize = 2;
pub const L: usize = 1;

pub const NUM_ADVICE: usize = T+1;
pub const NUM_CONSTANTS: usize = 2*T;

#[derive(Debug, Clone)]
pub struct PoseidonConfig<C, const WIDTH: usize, const RATE: usize, const L: usize> 
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    pow5_config: Pow5Config<C::Scalar, WIDTH, RATE>,
}

#[derive(Debug, Clone)]
pub struct PoseidonChip<
    C: TwoChainCurve,
    S: Spec<C::Scalar, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const L: usize,
> 
where
    C::Scalar: SerdeObject,
{
    config: PoseidonConfig<C, WIDTH, RATE, L>,
    _marker: PhantomData<S>,
}

impl<C, S: Spec<C::Scalar, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    PoseidonChip<C, S, WIDTH, RATE, L>
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    /// Constructs a new Poseidon Chip given a PoseidonConfig
    pub fn construct(config: PoseidonConfig<C, WIDTH, RATE, L>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configures the Poseidon Chip
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        state: [Column<Advice>; WIDTH],
        partial_sbox: Column<Advice>,
        rc_a: [Column<Fixed>; WIDTH],
        pad_fixed: [Column<Fixed>; WIDTH],
    ) -> PoseidonConfig<C, WIDTH, RATE, L> {
        let pow5_config = Pow5Chip::configure::<S>(meta, state, partial_sbox, rc_a, pad_fixed);

        PoseidonConfig { pow5_config }
    }

    /// Performs poseidon hash on the given input cells. Returns the output cell.
    pub fn hash(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        input_cells: [AssignedCell<C::Scalar, C::Scalar>; L],
    ) -> Result<AssignedCell<C::Scalar, C::Scalar>, Error> {
        let pow5_chip = Pow5Chip::construct(self.config.pow5_config.clone());

        let hasher = Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
            pow5_chip,
            layouter.namespace(|| "hasher"),
        )?;
        hasher.hash(layouter.namespace(|| "hash"), input_cells)
    }
}

struct PoseidonHashCircuit<C> 
where
    C: TwoChainCurve,
{
    message: [C::Scalar; L],
    // output: Fp,
    //_marker: PhantomData<S>,
}

impl<C> Circuit<C::Scalar> for PoseidonHashCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    type Config = (PoseidonConfig<C, T, R, L>, [Column<Advice>; NUM_ADVICE]);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; NUM_ADVICE].map(|_| meta.advice_column());
        let constants = [0; NUM_CONSTANTS].map(|_| meta.fixed_column());
        meta.enable_constant(constants[5]);


        let poseidon_config = PoseidonChip::<C, PoseidonSpec, T, R, L>::configure(
            meta,
            advices[..T].try_into().unwrap(),
            advices[T],
            constants[..T].try_into().unwrap(), 
            constants[T..].try_into().unwrap(), 
        );

        (poseidon_config, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let chip = PoseidonChip::<C, PoseidonSpec, T, R, L>::construct(
            config.0,
        ); 

        let mut messages_vec: Vec<AssignedCell<C::Scalar, C::Scalar>> = vec![];
        for message in self.message.iter() {
            messages_vec.push(layouter.assign_region(
                || "load message",
                |mut region| {
                    region.assign_advice(
                        || "value",
                        config.1[0],
                        0,
                        || Value::known(*message)
                    )
                },
            )?);
        };

        let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
        match messages_vec.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };
    
        let hash = chip.hash(
            layouter.namespace(|| "perform poseidon entry hash"),
            message,
        )?;

        print!("hash: {:?}", hash.value_field());

        Ok(())

    }
}

#[test]
fn poseidon_hash_longer_input_custom() {

    use plotters::prelude::*;
    let root = BitMapBackend::new("Poseidon2HashChip.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Poseidon2HashChip", ("sans-serif", 60)).unwrap();

    let rng = OsRng;

    let message = [0; L].map(|_| Fp::random(rng));
    let output =
        inlineHash::<_, PoseidonSpec, ConstantLength<L>, T, R>::init().hash(message);
    println!("output: {:?}", output);

    let k = 6;
    let circuit = PoseidonHashCircuit::<grumpkin::G1Affine> {
        message,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    halo2_proofs::dev::CircuitLayout::default()
    .render(k, &circuit, &root)
    .unwrap();
}