//! An easy-to-use implementation of the Poseidon Hash in the form of a Halo2 Chip. While the Poseidon Hash function
//! is already implemented in halo2_gadgets, there is no wrapper chip that makes it easy to use in other circuits.
use super::pow5::{Pow5Chip as Pow5Chip2, Pow5Config as Pow5Config2};
use super::primitives::{ConstantLength as ConstantLengthInline, Hash as inlineHash};
use ark_std::{end_timer, log2, start_timer};
use halo2_gadgets::poseidon::primitives::{ConstantLength, VariableLength};
use halo2_gadgets::poseidon::spec::PoseidonSpec;
use halo2_gadgets::poseidon::{Pow5Chip, Pow5Config, StateWord};
use num_bigint::BigUint;
use super::poseidon::{Hash};
use super::pow5::Pow5Chip as Poseidon2Pow5Chip;
use super::pow5::Pow5Config as Poseidon2Pow5Config;
use halo2_gadgets::poseidon::primitives::Spec;
//use pprof::ProfilerGuard;
use halo2_proofs::halo2curves::serde::SerdeObject;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Chip, Value},
    halo2curves::{bn256::{self, Fq as Fp}, grumpkin},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Circuit}, dev::MockProver,
};
use ff::{PrimeField};
use halo2_gadgets::poseidon::{PaddedWord};
use halo2_gadgets::poseidon::primitives::{Domain, State};
use crate::circuit::spec::PoseidonSpec as Poseidon2Spec;
use crate::utils::TwoChainCurve;
use std::marker::PhantomData;
use std::mem;
use std::time::Instant;

pub const T: usize = 4;
pub const R: usize = 3;
pub const L: usize = 3; // L = 63 - WITNESS COUNT 3400 ; 34 - WITNESS COUNT 1946

pub const NUM_ADVICE: usize = T;
pub const NUM_PARTIAL_SBOX: usize = 4;
pub const NUM_CONSTANTS: usize = 2*T + NUM_PARTIAL_SBOX;

#[derive(Debug, Clone)]
pub struct PoseidonConfig<C, const WIDTH: usize, const RATE: usize, const L: usize> 
where
    C: TwoChainCurve,
{
    pub pow5_config: Pow5Config<C::Scalar, WIDTH, RATE>,
}

#[derive(Debug, Clone)]
pub struct PoseidonChip<
    C,
    S: Spec<C::Scalar, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const L: usize,
> 
where
    C: TwoChainCurve,
{
    config: PoseidonConfig<C, WIDTH, RATE, L>,
    _marker: PhantomData<S>,
}

impl<C, S: Spec<C::Scalar, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    PoseidonChip<C, S, WIDTH, RATE, L>
where
    C: TwoChainCurve,
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
        rc_b: [Column<Fixed>; WIDTH],
    ) -> PoseidonConfig<C, WIDTH, RATE, L> {
        let pow5_config = Pow5Chip::configure::<S>(meta, state, partial_sbox, rc_a, rc_b);

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

        let timer = start_timer!(|| "hash");
        let hash = hasher.hash(layouter.namespace(|| "hash"), input_cells);
        end_timer!(timer);

        hash
    }
}

#[derive(Debug, Clone)]
pub struct Poseidon2Config<C, const WIDTH: usize, const RATE: usize, const L: usize> 
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    pow5_config: Pow5Config2<C::Scalar, WIDTH, RATE>,
}

#[derive(Debug, Clone)]
pub struct Poseidon2Chip<
    C: TwoChainCurve,
    S: Spec<C::Scalar, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const L: usize,
> 
where
    C::Scalar: SerdeObject,
{
    config: Poseidon2Config<C, WIDTH, RATE, L>,
    _marker: PhantomData<S>,
}

impl<C, S: Spec<C::Scalar, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    Poseidon2Chip<C, S, WIDTH, RATE, L>
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    /// Constructs a new Poseidon Chip given a PoseidonConfig
    pub fn construct(config: Poseidon2Config<C, WIDTH, RATE, L>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configures the Poseidon Chip
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        state: [Column<Advice>; WIDTH],
        partial_sbox: [Column<Advice>; NUM_PARTIAL_SBOX],
        partial_sbox_before: Column<Advice>,
        rc_full_rounds: [Column<Fixed>; WIDTH],
        rc_partial_rounds: [Column<Fixed>; NUM_PARTIAL_SBOX],
        pad_fixed: [Column<Fixed>; WIDTH],
    ) -> Poseidon2Config<C, WIDTH, RATE, L> {
        let pow5_config = Pow5Chip2::configure::<S>(meta, state, partial_sbox, partial_sbox_before, rc_full_rounds, rc_partial_rounds, pad_fixed);

        Poseidon2Config { pow5_config }
    }

    /// Performs poseidon hash on the given input cells. Returns the output cell.
    pub fn hash(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        input_cells: [AssignedCell<C::Scalar, C::Scalar>; L],
    ) -> Result<AssignedCell<C::Scalar, C::Scalar>, Error> {
        let pow5_chip = Pow5Chip2::construct(self.config.pow5_config.clone());

        let hasher = Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
            pow5_chip,
            layouter.namespace(|| "hasher"),
        )?;
        hasher.hash(layouter.namespace(|| "hash"), input_cells)
    }
}

// struct PoseidonHashCircuit<C> 
// where
//     C: TwoChainCurve,
// {
//     message: [C::Scalar; L],
// }

// impl<C> Circuit<C::Scalar> for PoseidonHashCircuit<C>
// where
//     C: TwoChainCurve,
//     C::Scalar: FromUniformBytes<64>,
// {
//     type Config = (PoseidonConfig<C, T, R, L>, [Column<Advice>; T + 1]);
//     type FloorPlanner = SimpleFloorPlanner;
//     type Params = ();

//     fn without_witnesses(&self) -> Self {
//         unimplemented!()
//     }

//     fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
//         let advices = [0; T + 1].map(|_| meta.advice_column());
//         let constants = [0; 2*T].map(|_| meta.fixed_column());
//         meta.enable_constant(constants[T]);


//         let poseidon_config = PoseidonChip::<C, PoseidonSpec, T, R, L>::configure(
//             meta,
//             advices[..T].try_into().unwrap(),
//             advices[T],
//             constants[..T].try_into().unwrap(), 
//             constants[T..].try_into().unwrap(), 
//         );

//         (poseidon_config, advices)
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<C::Scalar>,
//     ) -> Result<(), Error> {

//         let chip = PoseidonChip::<C, PoseidonSpec, T, R, L>::construct(
//             config.0,
//         ); 

//         let mut messages_vec: Vec<AssignedCell<C::Scalar, C::Scalar>> = vec![];
//         for message in self.message.iter() {
//             messages_vec.push(layouter.assign_region(
//                 || "load message",
//                 |mut region| {
//                     region.assign_advice(
//                         || "value",
//                         config.1[0],
//                         0,
//                         || Value::known(*message)
//                     )
//                 },
//             )?);
//         };

//         let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
//         match messages_vec.try_into() {
//             Ok(arr) => arr,
//             Err(_) => panic!("Failed to convert Vec to Array"),
//         };
//         let time_start = Instant::now();
//         let hash = chip.hash(
//             layouter.namespace(|| "perform poseidon entry hash"),
//             message,
//         )?;
//         let time_end = Instant::now();
//         println!("Time taken hash: {:?}", time_end - time_start);
//         // let chip = PoseidonChip::<C, PoseidonSpec, 5, 4, L>::construct(
//         //     config.0,
//         // ); 

//         // chip.hash(
//         //     layouter.namespace(|| "perform poseidon entry hash"),
//         //     message,
//         // )?;
        
//         print!("hash: {:?}", hash.value_field());

//         Ok(())

//     }
// }


struct Poseidon2HashCircuit<C> 
where
    C: TwoChainCurve,
{
    message: [C::Scalar; L],
    // output: Fp,
    //_marker: PhantomData<S>,
}

impl<C> Circuit<C::Scalar> for Poseidon2HashCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    type Config = (Poseidon2Config<C, T, R, L>, [Column<Advice>; NUM_ADVICE]);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; NUM_ADVICE].map(|_| meta.advice_column());
        let partial_sbox = [0; NUM_PARTIAL_SBOX].map(|_| meta.advice_column());
        let partial_sbox_before = meta.advice_column();
        let constants = [0; NUM_CONSTANTS].map(|_| meta.fixed_column());
        meta.enable_constant(constants[5]);


        let poseidon_config = Poseidon2Chip::<C, Poseidon2Spec, T, R, L>::configure(
            meta,
            advices[..T].try_into().unwrap(),
            partial_sbox,
            partial_sbox_before,
            constants[..T].try_into().unwrap(), 
            constants[T..T+NUM_PARTIAL_SBOX].try_into().unwrap(), 
            constants[T+NUM_PARTIAL_SBOX..].try_into().unwrap(), 
        );

        (poseidon_config, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        let time_start = Instant::now();
        let chip = Poseidon2Chip::<C, Poseidon2Spec, T, R, L>::construct(
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

#[derive(Clone, Debug)]
/// Poseidon sponge. This is stateful.
pub struct Poseidon2SpongeChip<F, const WIDTH: usize, const RATE: usize> 
where
    F: PrimeField,
{
    pub chip: Pow5Chip2<F, WIDTH, RATE>,
    init_state: State<StateWord<F>, WIDTH>,
    state: State<StateWord<F>, WIDTH>,
    spec: Poseidon2Spec,
    absorbing: Vec<AssignedCell<F, F>>,
}

impl<F, const WIDTH: usize, const RATE: usize> Poseidon2SpongeChip<F, WIDTH, RATE> 
where
    F: PrimeField + Ord,
{
    /// Create new Poseidon hasher.
    pub fn new(
        chip: Pow5Chip2<F, WIDTH, RATE>, mut layouter: impl Layouter<F>) -> Self {
        let init_state = chip.initial_state(layouter.namespace(|| "new inital state")).unwrap();
        let state = init_state.clone();
        Self {
            chip,
            init_state,
            state,
            spec: Poseidon2Spec,
            absorbing: Vec::new(),
        }
    }

    /// Initialize a poseidon hasher from an existing spec.
    pub fn from_spec(chip: Pow5Chip2<F, WIDTH, RATE>, mut layouter: impl Layouter<F>, spec: Poseidon2Spec) -> Self {
        let init_state = chip.initial_state(layouter.namespace(|| "from spec inital state")).unwrap();
        let state = init_state.clone();
        Self {
            chip,
            init_state,
            state,
            spec,
            absorbing: Vec::new(),
        }
    }

    /// Reset state to default and clear the buffer.
    pub fn clear(&mut self) {
        self.state = self.init_state.clone();
        self.absorbing.clear();
    }

    /// Store given `elements` into buffer.
    pub fn update(&mut self, elements: &[AssignedCell<F, F>]) {
        self.absorbing.extend_from_slice(elements);
    }

    /// Consume buffer and perform permutation, then output second element of
    /// state.
    pub fn squeeze(
        &mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<AssignedCell<F, F>, Error> {

        let input_elements = mem::take(&mut self.absorbing);
        for (i, input_chunk) in input_elements.chunks(RATE).enumerate() {
            let chunk_len = input_chunk.len();
            if chunk_len < RATE {
                let mut padded_chunk = input_chunk.iter().cloned().map(|cell| PaddedWord::Message(cell.clone())).collect::<Vec<_>>();
                    padded_chunk.extend(<VariableLength<F, RATE> as Domain<F, RATE>>::padding(chunk_len).iter().cloned().map(PaddedWord::Padding));

                let padded_chunk_array: [PaddedWord<F>; RATE] = padded_chunk.try_into().unwrap();
                self.state = self.chip.add_input(layouter.namespace(|| "squeeze add input"), &self.init_state, &padded_chunk_array)?;
                self.state = self.chip.permutation(layouter.namespace(|| "squeeze permute"), &self.state)?;

            } else {
                let input_chunk: [PaddedWord<F>; RATE] = input_chunk.iter().cloned().map(|cell| PaddedWord::Message(cell.clone())).collect::<Vec<_>>().try_into().unwrap();
                self.state = self.chip.add_input(layouter.namespace(|| "squeeze add input"), &self.init_state, &input_chunk)?;
                self.state = self.chip.permutation(layouter.namespace(|| "squeeze permute"), &self.state)?;
            }
        }

        let hash = self.state[1].0.clone();
        self.update(&[hash.clone()]);
        Ok(hash)
    }
}

struct Poseidon2TranscriptCircuit<C> 
where
    C: TwoChainCurve,
{
    message: [C::Scalar; L],
}

impl<C> Circuit<C::Scalar> for Poseidon2TranscriptCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: SerdeObject,
{
    type Config = (Poseidon2Pow5Config<C::Scalar, T, R>, [Column<Advice>; NUM_ADVICE]);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; NUM_ADVICE].map(|_| meta.advice_column());
        let partial_sbox = [0; NUM_PARTIAL_SBOX].map(|_| meta.advice_column());
        let partial_sbox_before = meta.advice_column();
        let constants = [0; NUM_CONSTANTS].map(|_| meta.fixed_column());
        meta.enable_constant(constants[5]);


        let poseidon_config = Poseidon2Pow5Chip::<C::Scalar, T, R>::configure::<Poseidon2Spec>(
            meta,
            advices[..T].try_into().unwrap(),
            partial_sbox,
            partial_sbox_before,
            constants[..T].try_into().unwrap(), 
            constants[T..T+NUM_PARTIAL_SBOX].try_into().unwrap(), 
            constants[T+NUM_PARTIAL_SBOX..].try_into().unwrap(), 
        );

        (poseidon_config, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        let pow5_chip = Poseidon2Pow5Chip::construct(config.0.clone());
        let mut sponge_chip = Poseidon2SpongeChip::<C::Scalar, T, R>::new(pow5_chip, layouter.namespace(|| "sponge chip"));

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
        
        sponge_chip.update(&message);
        let _ =sponge_chip.squeeze(layouter.namespace(|| "squeeze"));

        Ok(())
    }
}

#[test]
fn poseidon_hash_longer_input_custom() {
    use random::rngs::OsRng;
    use plotters::prelude::*;
    let root = BitMapBackend::new("Poseidon2HashChip.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Poseidon2HashChip", ("sans-serif", 60)).unwrap();

    let rng = OsRng;
    let message = [0; L].map(|_| Fp::one());
    // let output =
    //     inlineHash::<_, PoseidonSpec, ConstantLengthInline<L>, T, R>::init().hash(message);
    // println!("output: {:?}", output);

    let k = 6;
    // let circuit = Poseidon2HashCircuit::<grumpkin::G1Affine> {
    //     message,
    // };

    let circuit = Poseidon2TranscriptCircuit::<grumpkin::G1Affine> {
        message,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    prover.assert_satisfied();
    halo2_proofs::dev::CircuitLayout::default()
    .render(k, &circuit, &root)
    .unwrap();
}

// #[test]
// fn poseidon2_hash_longer_input_custom() {

//     use plotters::prelude::*;
//     let root = BitMapBackend::new("Poseidon2HashChip.png", (1024, 3096)).into_drawing_area();
//     root.fill(&WHITE).unwrap();
//     let root = root.titled("Poseidon2HashChip", ("sans-serif", 60)).unwrap();

//     let rng = OsRng;
//     let message = [0; L].map(|_| Fp::random(rng));
//     // let output =
//     //     inlineHash::<_, PoseidonSpec, ConstantLengthInline<L>, T, R>::init().hash(message);
//     // println!("output: {:?}", output);

//     let k = 9;
//     let circuit = Poseidon2HashCircuit::<grumpkin::G1Affine> {
//         message,
//     };

//     //let guard = ProfilerGuard::new(10).unwrap();
//     let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//     //assert_eq!(prover.verify(), Ok(()));
//     // if let Ok(report) = guard.report().build() {    
//     //     // Generate a flamegraph
//     //     let file = File::create("flamegraph_poseidon.svg").unwrap();
//     //     report.flamegraph(file).unwrap();
//     // }
//     halo2_proofs::dev::CircuitLayout::default()
//     .render(k, &circuit, &root)
//     .unwrap();
// }