use std::convert::TryInto;
use std::iter;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Region, Value},
    plonk::{
        AccU, Advice, Any, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Selector
    },
    poly::Rotation,
};

use super::hash_chip::NUM_PARTIAL_SBOX;
use halo2_gadgets::poseidon::{primitives::{Spec, VariableLength}, StateWord};
use halo2_gadgets::poseidon::{PoseidonInstructions, PoseidonSpongeInstructions, PaddedWord};
use halo2_gadgets::poseidon::primitives::{Absorbing, Domain, Mds, Squeezing, State};

/// Configuration for a [`Pow5Chip`].
#[derive(Clone, Debug)]
pub struct Pow5Config<F: Field, const WIDTH: usize, const RATE: usize> {
    pub state: [Column<Advice>; WIDTH],
    partial_sbox: [Column<Advice>; NUM_PARTIAL_SBOX],
    partial_sbox_before: Column<Advice>,
    rc_full_rounds: [Column<Fixed>; WIDTH],
    rc_partial_rounds: [Column<Fixed>; NUM_PARTIAL_SBOX],
    pad_fixed: [Column<Fixed>; WIDTH],
    s_full: Selector,
    s_first: Selector,
    s_partial: Selector,
    s_pad_and_add: Selector,

    half_full_rounds: usize,
    full_partial_rounds: usize,
    alpha: [u64; 4],
    round_constants: Vec<[F; WIDTH]>,
    mat_external: Mds<F, WIDTH>,
    mat_internal: Mds<F, WIDTH>,
    mat_internal_diag_m_1: [F; WIDTH],
}

/// A Poseidon chip using an $x^5$ S-Box.
///
/// The chip is implemented using a single round per row for full rounds, and two rounds
/// per row for partial rounds.
#[derive(Debug, Clone)]
pub struct Pow5Chip<F: Field, const WIDTH: usize, const RATE: usize> {
    config: Pow5Config<F, WIDTH, RATE>,
}

impl<F: PrimeField, const WIDTH: usize, const RATE: usize> Pow5Chip<F, WIDTH, RATE> {

    pub fn matmul_m4_expr(input: &mut[Expression<F>]) {
        let t4 = WIDTH / 4;
        for i in 0..t4 {
            let two = F::from(2);
            let start_index = i * 4;
            let mut t_0 = input[start_index].clone();
            t_0 = t_0 + input[start_index + 1].clone();
            let mut t_1 = input[start_index + 2].clone();
            t_1 = t_1 + input[start_index + 3].clone();
            let mut t_2 = input[start_index + 1].clone();
            t_2 = t_2 * two;
            t_2 = t_2 + t_1.clone();
            let mut t_3 = input[start_index + 3].clone();
            t_3 = t_3 * two;
            t_3 = t_3 + t_0.clone();
            let mut t_4 = t_1.clone();
            t_4 = t_4 * two;
            t_4 = t_4 * two;
            t_4 = t_4 + t_3.clone();
            let mut t_5 = t_0.clone();
            t_5 = t_5 * two;
            t_5 = t_5 * two;
            t_5 = t_5 + t_2.clone();
            let mut t_6 = t_3.clone();
            t_6 = t_6 + t_5.clone();
            let mut t_7 = t_2.clone();
            t_7 = t_7 + t_4.clone();
            input[start_index] = t_6;
            input[start_index + 1] = t_5;
            input[start_index + 2] = t_7;
            input[start_index + 3] = t_4;
        }
    }
        
    /// Configures this chip for use in a circuit.
    ///
    /// # Side-effects
    ///
    /// All columns in `state` will be equality-enabled.
    //
    // TODO: Does the rate need to be hard-coded here, or only the width? It probably
    // needs to be known wherever we implement the hashing gadget, but it isn't strictly
    // necessary for the permutation.
    pub fn configure<S: Spec<F, WIDTH, RATE>>(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; WIDTH],
        partial_sbox: [Column<Advice>; NUM_PARTIAL_SBOX],
        partial_sbox_before: Column<Advice>,
        rc_full_rounds: [Column<Fixed>; WIDTH],
        rc_partial_rounds: [Column<Fixed>; NUM_PARTIAL_SBOX],
        pad_fixed: [Column<Fixed>; WIDTH],
    ) -> Pow5Config<F, WIDTH, RATE> {
        assert_eq!(RATE, WIDTH - 1);
        // Generate constants for the Poseidon permutation.
        // This gadget requires R_F and R_P to be even.
        assert!(S::full_rounds() & 1 == 0);
        assert!(S::partial_rounds() & 1 == 0);
        let half_full_rounds = S::full_rounds() / 2;
        let full_partial_rounds = S::partial_rounds();
        let (round_constants, mat_external, mat_internal, mat_internal_diag_m_1) = S::constants();

        // This allows state words to be initialized (by constraining them equal to fixed
        // values), and used in a permutation from an arbitrary region. rc_a is used in
        // every permutation round.
        for column in iter::empty()
            .chain(state.iter().cloned().map(Column::<Any>::from))
            .chain(pad_fixed.iter().cloned().map(Column::<Any>::from))
        {
            meta.enable_equality(column);
        }

        let s_first = meta.selector();
        let s_full = meta.selector();
        let s_partial = meta.selector();
        let s_pad_and_add = meta.selector();

        let alpha = [5, 0, 0, 0];
        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };
        let pow_4 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2
        };
        let pow_3 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v
        };
        let pow_2 = |v: Expression<F>| {
            v.clone() * v.clone()
        };

        // linear constraint, doesnt contribute to error no need to homogenize
        meta.create_gate("first layer", |meta| {
            let s_first = meta.query_selector(s_first);
            
            Constraints::with_selector(
                s_first,
                (0..WIDTH)
                    .map(|next_idx| {
                        let state_next = meta.query_advice(state[next_idx], Rotation::next());
                        let expr = (0..WIDTH)
                            .map(|idx| {
                                let state_cur = meta.query_advice(state[idx], Rotation::cur());
                                state_cur * mat_external[next_idx][idx]
                            })
                            .reduce(|acc, term| acc + term)
                            .expect("WIDTH > 0");
                        expr - state_next
                    })
                    .collect::<Vec<_>>(),
            )
        });

        meta.create_gate("full round", |meta| {
            let s_full = meta.query_selector(s_full);
            let u = Expression::AccU(AccU{index: 0});

            Constraints::with_selector(
                s_full,
                (0..WIDTH)
                    .map(|next_idx| {
                        let state_next = meta.query_advice(state[next_idx], Rotation::next());
                        let expr = (0..WIDTH)
                            .map(|idx| {
                                let state_cur = meta.query_advice(state[idx], Rotation::cur());
                                let rc_a = meta.query_fixed(rc_full_rounds[idx], Rotation::cur());
                                pow_5(state_cur + rc_a * u.clone()) * mat_external[next_idx][idx]
                            })
                            .reduce(|acc, term| acc + term)
                            .expect("WIDTH > 0");
                        (expr - state_next * pow_4(u.clone())) * u.clone()
                    })
                    .collect::<Vec<_>>(),
            )
        });

        // dup
        // meta.create_gate("full rounds", |meta| {
        //     let cur = (0..WIDTH).map(|i| meta.query_advice(state[i], Rotation::cur())).collect::<Vec<_>>();
        //     let rc_a = (0..WIDTH).map(|i| meta.query_fixed(rc_full_rounds[i], Rotation::cur())).collect::<Vec<_>>();
        //     let next = (0..WIDTH).map(|i|meta.query_advice(state[i], Rotation::next())).collect::<Vec<_>>();
        //     let s_full = meta.query_selector(s_full);

        //     let mut state = vec![Expression::Constant(F::ZERO); WIDTH];
        //     for i in 0..WIDTH {
        //         state[i] = pow_5(cur[i].clone() + rc_a[i].clone());
        //     }

        //     Pow5Chip::<F, WIDTH, RATE>::matmul_m4_expr(&mut state);

        //     Constraints::with_selector(
        //         s_full,
        //         std::iter::empty()
        //             .chain((0..WIDTH).map(|idx| state[idx].clone() - next[idx].clone()))
        //             .collect::<Vec<_>>(),
        //     )
        // });

        meta.create_gate("partial rounds", |meta| {
            let next = (0..WIDTH).map(|i|meta.query_advice(state[i], Rotation::next())).collect::<Vec<_>>();
            let cur_0 = meta.query_advice(state[0], Rotation::cur());
            let mid_0 = (0..NUM_PARTIAL_SBOX).map(|i| meta.query_advice(partial_sbox[i], Rotation::cur())).collect::<Vec<_>>();
            let mid_before_last_0 = meta.query_advice(partial_sbox_before, Rotation::cur());
            let rc_a = (0..NUM_PARTIAL_SBOX).map(|i| meta.query_fixed(rc_partial_rounds[i], Rotation::cur())).collect::<Vec<_>>();
            let s_partial = meta.query_selector(s_partial);
            let u = Expression::AccU(AccU{index: 0});

            // matmul_internal
            let mut sum = mid_0[0].clone(); // pow_5(rc[0] + state0)
            let mut mid = vec![Expression::Constant(F::ZERO); WIDTH];
            let mut mid_0_before_add = vec![Expression::Constant(F::ZERO); NUM_PARTIAL_SBOX];
            let mut cur_vec = Vec::new();
            cur_vec.push(mid_0[0].clone()); // replace the first elements as the partial sbox output mid_0
            sum = (1..WIDTH).fold(sum, |acc, cur_idx| { //sum of t elements in the current state
                let cur = meta.query_advice(state[cur_idx], Rotation::cur());
                cur_vec.push(cur.clone());
                acc + cur
            });
            for i in 0..WIDTH { // sum + diag entry * element to each element
                mid[i] = sum.clone() + cur_vec[i].clone() * mat_internal_diag_m_1[i];
            }
            mid_0_before_add[0] = mid[0].clone();

            for i in 1..NUM_PARTIAL_SBOX {
                let mut sum = mid_0[i].clone(); // pow5(rc0 + state0)
                sum = (1..WIDTH).fold(sum, |acc, cur_idx| {
                    acc + mid[cur_idx].clone()
                });
                mid[0] = sum.clone() + mid_0[i].clone() * mat_internal_diag_m_1[0];
                if i >= NUM_PARTIAL_SBOX - 2 {
                    mid_0_before_add[i] = mid_before_last_0.clone();
                } else {
                    mid_0_before_add[i] = mid[0].clone();
                }
                // mid_0_before_add[i] = mid[0].clone();
                for j in 1..WIDTH {
                    mid[j] = sum.clone() + mid[j].clone() * mat_internal_diag_m_1[j];
                }
            }

            Constraints::with_selector(
                s_partial,
                std::iter::empty()
                    .chain(Some((pow_5(cur_0 + rc_a[0].clone() * u.clone()) - mid_0[0].clone() * pow_4(u.clone())) * u.clone()))
                    .chain((1..NUM_PARTIAL_SBOX).map(|i| u.clone() * (pow_5(mid_0_before_add[i - 1].clone() + rc_a[i].clone() * u.clone()) - mid_0[i].clone() * pow_4(u.clone()))))
                    .chain((0..WIDTH).map(|idx| mid[idx].clone() - next[idx].clone()))
                    .collect::<Vec<_>>(),
            )
        });

        // linear constraint, doesnt contribute to error no need to homogenize
        meta.create_gate("pad-and-add", |meta| {
            let initial_state_rate = meta.query_advice(state[RATE], Rotation::prev());
            let output_state_rate = meta.query_advice(state[RATE], Rotation::next());
            let s_pad_and_add = meta.query_selector(s_pad_and_add);

            let pad_and_add = |idx: usize| {
                let initial_state = meta.query_advice(state[idx], Rotation::prev());
                let input = meta.query_advice(state[idx], Rotation::cur());
                let output_state = meta.query_advice(state[idx], Rotation::next());

                // We pad the input by storing the required padding in fixed columns and
                // then constraining the corresponding input columns to be equal to it.
                initial_state + input - output_state
            };

            Constraints::with_selector(
                s_pad_and_add,
                (0..RATE)
                    .map(pad_and_add)
                    // The capacity element is never altered by the input.
                    .chain(Some(initial_state_rate - output_state_rate))
                    .collect::<Vec<_>>(),
            )
        });

        Pow5Config {
            state,
            partial_sbox,
            partial_sbox_before,
            rc_full_rounds,
            rc_partial_rounds,
            pad_fixed,
            s_full,
            s_first,
            s_partial,
            s_pad_and_add,
            half_full_rounds,
            full_partial_rounds,
            alpha,
            round_constants,
            mat_external,
            mat_internal,
            mat_internal_diag_m_1,
        }
    }

    /// Construct a [`Pow5Chip`].
    pub fn construct(config: Pow5Config<F, WIDTH, RATE>) -> Self {
        Pow5Chip { config }
    }
}

impl<F: Field, const WIDTH: usize, const RATE: usize> Chip<F> for Pow5Chip<F, WIDTH, RATE> {
    type Config = Pow5Config<F, WIDTH, RATE>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field, S: Spec<F, WIDTH, RATE>, const WIDTH: usize, const RATE: usize>
    PoseidonInstructions<F, S, WIDTH, RATE> for Pow5Chip<F, WIDTH, RATE>
{
    type Word = StateWord<F>;

    fn permute(
        &self,
        layouter: &mut impl Layouter<F>,
        initial_state: &State<Self::Word, WIDTH>,
    ) -> Result<State<Self::Word, WIDTH>, Error> {
        let config = self.config();

        layouter.assign_region(
            || "permute state",
            |mut region| {
                // Load the initial state into this region.
                let state = Pow5State::load(&mut region, config, initial_state)?;
                let state = state.first_layer(&mut region, config)?;
                let state = (0..config.half_full_rounds).try_fold(state, |state, r| {
                    state.full_round(&mut region, config, r, r + 1)
                })?;    

                let state = (0..config.full_partial_rounds/NUM_PARTIAL_SBOX).try_fold(state, |state, r| {
                    state.partial_round(
                        &mut region,
                        config,
                        config.half_full_rounds + r,
                        config.half_full_rounds + r + 1,
                    )
                })?;

                let state = (0..config.half_full_rounds).try_fold(state, |state, r| {
                    state.full_round(
                        &mut region,
                        config,
                        config.half_full_rounds + config.full_partial_rounds/NUM_PARTIAL_SBOX + r,
                        config.half_full_rounds + config.full_partial_rounds/NUM_PARTIAL_SBOX + r + 1,
                    )
                })?;

                Ok(state.0)
            },
        )
    }
}

impl<
        F: Field,
        S: Spec<F, WIDTH, RATE>,
        D: Domain<F, RATE>,
        const WIDTH: usize,
        const RATE: usize,
    > PoseidonSpongeInstructions<F, S, D, WIDTH, RATE> for Pow5Chip<F, WIDTH, RATE>
{
    fn initial_state(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<State<Self::Word, WIDTH>, Error> {
        let config = self.config();
        let state = layouter.assign_region(
            || format!("initial state for domain {}", D::name()),
            |mut region| {
                let mut state = Vec::with_capacity(WIDTH);
                let mut load_state_word = |i: usize, value: F| -> Result<_, Error> {
                    let var = region.assign_advice_from_constant(
                        || format!("state_{}", i),
                        config.state[i],
                        0,
                        value,
                    )?;
                    state.push(StateWord(var));

                    Ok(())
                };

                for i in 0..RATE {
                    load_state_word(i, F::ZERO)?;
                }
                load_state_word(RATE, D::initial_capacity_element())?;

                Ok(state)
            },
        )?;

        Ok(state.try_into().unwrap())
    }

    fn add_input(
        &self,
        layouter: &mut impl Layouter<F>,
        initial_state: &State<Self::Word, WIDTH>,
        input: &Absorbing<PaddedWord<F>, RATE>,
    ) -> Result<State<Self::Word, WIDTH>, Error> {
        let config = self.config();
        layouter.assign_region(
            || format!("add input for domain {}", D::name()),
            |mut region| {
                config.s_pad_and_add.enable(&mut region, 1)?;
                // Load the initial state into this region.
                let load_state_word = |i: usize| {
                    initial_state[i]
                        .0
                        .copy_advice(
                            || format!("load state_{}", i),
                            &mut region,
                            config.state[i],
                            0,
                        )
                        .map(StateWord)
                };
                let initial_state: Result<Vec<_>, Error> =
                    (0..WIDTH).map(load_state_word).collect();
                let initial_state = initial_state?;
                // Load the input into this region.
                let load_input_word = |i: usize| {
                    let (cell, value) = match input.0[i].clone() {
                        Some(PaddedWord::Message(word)) => (word.cell(), word.value().copied()),
                        Some(PaddedWord::Padding(padding_value)) => {
                            let cell = region
                                .assign_fixed(
                                    || format!("load pad_{}", i),
                                    config.pad_fixed[i],
                                    1,
                                    || Value::known(padding_value),
                                )?
                                .cell();
                            (cell, Value::known(padding_value))
                        }
                        _ => panic!("Input is not padded"),
                    };
                    let var = region.assign_advice(
                        || format!("load input_{}", i),
                        config.state[i],
                        1,
                        || value,
                    )?;
                    region.constrain_equal(cell, var.cell())?;

                    Ok(StateWord(var))
                };
                let input: Result<Vec<_>, Error> = (0..RATE).map(load_input_word).collect();
                let input = input?;
                // Constrain the output.
                let constrain_output_word = |i: usize| {
                    let value = initial_state[i].0.value().copied()
                        + input
                            .get(i)
                            .map(|word| word.0.value().cloned())
                            // The capacity element is never altered by the input.
                            .unwrap_or_else(|| Value::known(F::ZERO));
                    region
                        .assign_advice(
                            || format!("load output_{}", i),
                            config.state[i],
                            2,
                            || value,
                        )
                        .map(StateWord)
                };
                let output: Result<Vec<_>, Error> = (0..WIDTH).map(constrain_output_word).collect();
                output.map(|output| output.try_into().unwrap())
            },
        )
    }

    fn get_output(state: &State<Self::Word, WIDTH>) -> Squeezing<Self::Word, RATE> {
        Squeezing(
            state[..RATE]
                .iter()
                .map(|word| Some(word.clone()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        )
    }
}

impl<F: PrimeField, const WIDTH: usize, const RATE: usize> Pow5Chip<F, WIDTH, RATE> {
    pub fn initial_state(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<State<StateWord<F>, WIDTH>, Error> {
        let config = self.config();
        let state = layouter.assign_region(
            || format!("initial state for domain {}", VariableLength::<F, RATE>::name()),
            |mut region| {
                let mut state = Vec::with_capacity(WIDTH);
                let mut load_state_word = |i: usize, value: F| -> Result<_, Error> {
                    let var = region.assign_advice_from_constant(
                        || format!("state_{i}"),
                        config.state[i],
                        0,
                        value,
                    )?;
                    state.push(StateWord(var));

                    Ok(())
                };

                for i in 0..RATE {
                    load_state_word(i, F::ZERO)?;
                }
                load_state_word(RATE, VariableLength::<F, RATE>::initial_capacity_element())?;

                Ok(state)
            },
        )?;

        Ok(state.try_into().unwrap())
    }

    pub fn add_input(
        &self,
        mut layouter: impl Layouter<F>,
        initial_state: &State<StateWord<F>, WIDTH>,
        input: &[PaddedWord<F>; RATE],
    ) -> Result<State<StateWord<F>, WIDTH>, Error> {
        let config = self.config();
        layouter.assign_region(
            || format!("add input for domain {}", VariableLength::<F, RATE>::name()),
            |mut region| {
                config.s_pad_and_add.enable(&mut region, 1)?;

                // Load the initial state into this region.
                let load_state_word = |i: usize| {
                    initial_state[i]
                        .0
                        .copy_advice(
                            || format!("load state_{}", i),
                            &mut region,
                            config.state[i],
                            0,
                        )
                        .map(StateWord)
                };
                let initial_state: Result<Vec<_>, Error> =
                    (0..WIDTH).map(load_state_word).collect();
                let initial_state = initial_state?;

                // Load the input into this region.
                let load_input_word = |i: usize| {
                    let (cell, value) = match input[i].clone() {
                        PaddedWord::Message(word) => (word.cell(), word.value().copied()),
                        PaddedWord::Padding(padding_value) => {
                            let cell = region
                                .assign_fixed(
                                    || format!("load pad_{}", i),
                                    config.pad_fixed[i],
                                    1,
                                    || Value::known(padding_value),
                                )?
                                .cell();
                            (cell, Value::known(padding_value))
                        }
                        _ => panic!("Input is not padded"),
                    };
                    
                    let var = region.assign_advice(
                        || format!("load input_{}", i),
                        config.state[i],
                        1,
                        || value,
                    )?;
                    region.constrain_equal(cell, var.cell())?;

                    Ok(StateWord(var))
                };
                let input: Result<Vec<_>, Error> = (0..RATE).map(load_input_word).collect();
                let input = input?;

                // Constrain the output.
                let constrain_output_word = |i: usize| {
                    let value = initial_state[i].0.value().copied()
                        + input
                            .get(i)
                            .map(|word| word.0.value().cloned())
                            // The capacity element is never altered by the input.
                            .unwrap_or_else(|| Value::known(F::ZERO));
                    region
                        .assign_advice(
                            || format!("load output_{}", i),
                            config.state[i],
                            2,
                            || value,
                        )
                        .map(StateWord)
                };
                let output: Result<Vec<_>, Error> = (0..WIDTH).map(constrain_output_word).collect();
                output.map(|output| output.try_into().unwrap())
            },
        )
    }

    fn get_output(state: &State<StateWord<F>, WIDTH>) -> Squeezing<StateWord<F>, RATE> {
        Squeezing(
            state[..RATE]
                .iter()
                .map(|word| Some(word.clone()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        )
    }

    pub fn permutation(
        &self,
        mut layouter: impl Layouter<F>,
        initial_state: &State<StateWord<F>, WIDTH>,
    ) -> Result<State<StateWord<F>, WIDTH>, Error> {
        let config = self.config();
        layouter.assign_region(
            || "permute state",
            |mut region| {
                // Load the initial state into this region.
                let state = Pow5State::load(&mut region, config, initial_state)?;
                let state = state.first_layer(&mut region, config)?;
                let state = (0..config.half_full_rounds).try_fold(state, |state, r| {
                    state.full_round(&mut region, config, r, r + 1)
                })?;    

                let state = (0..config.full_partial_rounds/NUM_PARTIAL_SBOX).try_fold(state, |state, r| {
                    state.partial_round(
                        &mut region,
                        config,
                        config.half_full_rounds + r,
                        config.half_full_rounds + r + 1,
                    )
                })?;

                let state = (0..config.half_full_rounds).try_fold(state, |state, r| {
                    state.full_round(
                        &mut region,
                        config,
                        config.half_full_rounds + config.full_partial_rounds/NUM_PARTIAL_SBOX + r,
                        config.half_full_rounds + config.full_partial_rounds/NUM_PARTIAL_SBOX + r + 1,
                    )
                })?;

                Ok(state.0)
            },
        )
    }
}

#[derive(Debug)]
struct Pow5State<F: Field, const WIDTH: usize>([StateWord<F>; WIDTH]);

impl<F: Field, const WIDTH: usize> Pow5State<F, WIDTH> {
    pub fn matmul_m4(&self, input: &mut[F]) {
        let t4 = WIDTH / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2 = t_2.double();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3 = t_3.double();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4 = t_4.double();
            t_4 = t_4.double();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5 = t_5.double();
            t_5 = t_5.double();
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

    pub fn matmul_external(&self, input: &mut[F]) {
        let t = WIDTH;
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
                let mut stored = [F::ZERO; 4];
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

    pub fn matmul_internal(&self, input: &mut[F], mat_internal_diag_m_1: &[F]) {
        let t = WIDTH;

        match t {
            2 => {
                // [2, 1]
                // [1, 3]
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                input[0].add_assign(&sum);
                input[1].double();
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
                input[2].double();
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

    fn load<const RATE: usize>(
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
        initial_state: &State<StateWord<F>, WIDTH>,
    ) -> Result<Self, Error> {
        let load_state_word = |i: usize| {
            initial_state[i]
                .0
                .copy_advice(|| format!("load state_{}", i), region, config.state[i], 0)
                .map(StateWord)
        };

        let state: Result<Vec<_>, _> = (0..WIDTH).map(load_state_word).collect();
        state.map(|state| Pow5State(state.try_into().unwrap()))
    }

    fn first_layer<const RATE: usize>(
        self,
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
    ) -> Result<Self, Error> {
        let offset = 0; // first layer
        config.s_first.enable(region, offset)?;
            let q = self.0.iter().map(|word| {
                word.0
                    .value()
                    .map(|v| *v)
            });

            let mut state_raw = [F::ZERO; WIDTH];
            q.enumerate().for_each(|(idx, q)| {
                q.map(|q| state_raw[idx] = q);
            });

            self.matmul_external(&mut state_raw);
            let state: [Value<F>; WIDTH] = state_raw.iter().map(|el| Value::known(*el)).collect::<Vec<_>>().try_into().unwrap();
            let next_state_word = |i: usize| {
                let value = state[i];
                let var = region.assign_advice(
                    || format!("pre_round state_{}", i),
                    config.state[i],
                    offset + 1,
                    || value,
                )?;
                Ok(StateWord(var))
            };
    
            let next_state: Result<Vec<_>, _> = (0..WIDTH).map(next_state_word).collect();
            next_state.map(|next_state| Pow5State(next_state.try_into().unwrap()))
    }

    // mockprover fails here check constraints
    fn full_round<const RATE: usize>(
        self,
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
        round: usize,
        offset: usize,
    ) -> Result<Self, Error> {
        Self::full_round_fn(region, config, round, offset, config.s_full, |_| {
            let q = self.0.iter().enumerate().map(|(idx, word)| {
                word.0
                    .value()
                    .map(|v| *v + config.round_constants[round][idx])
            });
            let mut state = [F::ZERO; WIDTH];
            q.enumerate().for_each(|(idx, q)| {
                q.map(|q| {
                    let q_sq = q.square();
                    let q_5 = q_sq * q_sq * q;
                    state[idx] = q_5;
                });
            });

            self.matmul_external(&mut state);
            Ok((round + 1, state.iter().map(|el| Value::known(*el)).collect::<Vec<_>>().try_into().unwrap()))
        })
    }

    fn partial_round<const RATE: usize>(
        self,
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
        round: usize,
        offset: usize,
    ) -> Result<Self, Error> {
        Self::partial_round_fn(region, config, round, offset, config.s_partial, |region| {
            let p: Value<Vec<_>> = self.0.iter().map(|word| word.0.value().cloned()).collect();
            let r: Value<Vec<_>> = p.map(|p| {
                let r_add = p[0] + config.round_constants[NUM_PARTIAL_SBOX * (round - 3)][0];
                let r_sq = r_add.square();
                let r_0 = r_sq * r_sq * r_add;
                let r_i = p[1..]
                    .iter()
                    .copied();
                std::iter::empty().chain(Some(r_0)).chain(r_i).collect()
            });

            region.assign_advice(
                || format!("round_{} partial_sbox", NUM_PARTIAL_SBOX*round),
                config.partial_sbox[0],
                offset,
                || r.as_ref().map(|r| r[0]),
            )?;
            
            let mut state = [F::ZERO; WIDTH];
            r.as_ref().map(|r| {
                state[..WIDTH].copy_from_slice(&r[..WIDTH]);
            });
            self.matmul_internal(&mut state, &config.mat_internal_diag_m_1);

            for i in 1..NUM_PARTIAL_SBOX {
                if i == NUM_PARTIAL_SBOX - 1 {
                    region.assign_advice(
                        || format!("round_{} partial_sbox_before", 4*round + i),
                        config.partial_sbox_before,
                        offset,
                        || Value::known(state[0]),
                    )?;
                }

                let ri_add = state[0] + config.round_constants[NUM_PARTIAL_SBOX * (round - 3) + i][0];
                let ri_sq = ri_add.square();
                let ri_0 = ri_sq * ri_sq * ri_add;
                let ri_i = state[1..]
                    .iter()
                    .copied();
                let ri: Vec<_> = std::iter::empty().chain(Some(ri_0)).chain(ri_i).collect();

                region.assign_advice(
                    || format!("round_{} partial_sbox", NUM_PARTIAL_SBOX * round + i),
                    config.partial_sbox[i],
                    offset,
                    || Value::known(ri[0]),
                )?;

                state = ri.try_into().unwrap();
                self.matmul_internal(&mut state, &config.mat_internal_diag_m_1);
            }

            Ok((round + 1, state.iter().map(|el| Value::known(*el)).collect::<Vec<_>>().try_into().unwrap()))
        })
    }

    fn full_round_fn<const RATE: usize>(
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
        round: usize,
        offset: usize,
        round_gate: Selector,
        round_fn: impl FnOnce(&mut Region<F>) -> Result<(usize, [Value<F>; WIDTH]), Error>,
    ) -> Result<Self, Error> {
        // Enable the required gate.
        round_gate.enable(region, offset)?;
        // Load the round constants.
        let mut load_round_constant = |i: usize| {
            region.assign_fixed(
                || format!("round_{} rc_{}", round, i),
                config.rc_full_rounds[i],
                offset,
                || Value::known(config.round_constants[round][i]),
            )
        };
        for i in 0..WIDTH {
            load_round_constant(i)?;
        }

        // Compute the next round's state.
        let (next_round, next_state) = round_fn(region)?;
        let next_state_word = |i: usize| {
            let value = next_state[i];
            let var = region.assign_advice(
                || format!("round_{} state_{}", next_round, i),
                config.state[i],
                offset + 1,
                || value,
            )?;
            Ok(StateWord(var))
        };

        let next_state: Result<Vec<_>, _> = (0..WIDTH).map(next_state_word).collect();
        next_state.map(|next_state| Pow5State(next_state.try_into().unwrap()))
    }

    fn partial_round_fn<const RATE: usize>(
        region: &mut Region<F>,
        config: &Pow5Config<F, WIDTH, RATE>,
        round: usize,
        offset: usize,
        round_gate: Selector,
        round_fn: impl FnOnce(&mut Region<F>) -> Result<(usize, [Value<F>; WIDTH]), Error>,
    ) -> Result<Self, Error> {
        // Enable the required gate.
        round_gate.enable(region, offset)?;
        for j in 0..NUM_PARTIAL_SBOX {
            // Load the round constants.
                region.assign_fixed(
                    || format!("round_{} rc_{}", NUM_PARTIAL_SBOX * (round - 3) + j, 0),
                    config.rc_partial_rounds[j],
                    offset,
                    || Value::known(config.round_constants[NUM_PARTIAL_SBOX * (round - 3) + j][0]),
                )?;
            };

        // Compute the next round's state.
        let (next_round, next_state) = round_fn(region)?;

        let next_state_word = |i: usize| {
            let value = next_state[i];
            let var = region.assign_advice(
                || format!("round_{} state_{}", next_round, i),
                config.state[i],
                offset + 1,
                || value,
            )?;
            Ok(StateWord(var))
        };

        let next_state: Result<Vec<_>, _> = (0..WIDTH).map(next_state_word).collect();
        next_state.map(|next_state| Pow5State(next_state.try_into().unwrap()))
    }
}

// #[cfg(test)]
// mod tests {
//     use group::ff::{Field, PrimeField};
//     use halo2_proofs::{
//         circuit::{Layouter, SimpleFloorPlanner, Value},
//         dev::MockProver,
//         plonk::{Circuit, ConstraintSystem, Error},
//     };
//     use halo2_proofs::halo2curves::bn256::{Fq as Fp};
//     //use rand::rngs::OsRng;

//     use crate::circuit::spec::PoseidonSpec;

//     use super::{PoseidonInstructions, Pow5Chip, Pow5Config, StateWord};
//     use super::super::primitives::{self as poseidon, ConstantLength}; // P128Pow5T3 as OrchardNullifier
//     use std::convert::TryInto;
//     use std::marker::PhantomData;
//     use halo2_gadgets::poseidon::primitives::Spec;

    // struct HashCircuit<
    //     S: Spec<Fp, WIDTH, RATE>,
    //     const WIDTH: usize,
    //     const RATE: usize,
    //     const L: usize,
    // > {
    //     message: Value<[Fp; L]>,
    //     // For the purpose of this test, witness the result.
    //     // TODO: Move this into an instance column.
    //     output: Value<Fp>,
    //     _spec: PhantomData<S>,
    // }

    // impl<S: Spec<Fp, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    //     Circuit<Fp> for HashCircuit<S, WIDTH, RATE, L>
    // {
    //     type Config = Pow5Config<Fp, WIDTH, RATE>;
    //     type FloorPlanner = SimpleFloorPlanner;
    //     // #[cfg(feature = "circuit-params")]
    //     type Params = ();

    //     fn without_witnesses(&self) -> Self {
    //         Self {
    //             message: Value::unknown(),
    //             output: Value::unknown(),
    //             _spec: PhantomData,
    //         }
    //     }

    //     fn configure(meta: &mut ConstraintSystem<Fp>) -> Pow5Config<Fp, WIDTH, RATE> {
    //         let state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
    //         let partial_sbox = meta.advice_column();

    //         let rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
    //         let rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

    //         meta.enable_constant(rc_b[0]);

    //         Pow5Chip::configure::<S>(
    //             meta,
    //             state.try_into().unwrap(),
    //             partial_sbox,
    //             rc_a.try_into().unwrap(),
    //             rc_b.try_into().unwrap(),
    //         )
    //     }

    //     fn synthesize(
    //         &self,
    //         config: Pow5Config<Fp, WIDTH, RATE>,
    //         mut layouter: impl Layouter<Fp>,
    //     ) -> Result<(), Error> {
    //         let chip = Pow5Chip::construct(config.clone());

    //         let message = layouter.assign_region(
    //             || "load message",
    //             |mut region| {
    //                 let message_word = |i: usize| {
    //                     let value = self.message.map(|message_vals| message_vals[i]);
    //                     region.assign_advice(
    //                         || format!("load message_{}", i),
    //                         config.state[i],
    //                         0,
    //                         || value,
    //                     )
    //                 };

    //                 let message: Result<Vec<_>, Error> = (0..L).map(message_word).collect();
    //                 Ok(message?.try_into().unwrap())
    //             },
    //         )?;

    //         let hasher = Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
    //             chip,
    //             layouter.namespace(|| "init"),
    //         )?;
    //         let output = hasher.hash(layouter.namespace(|| "hash"), message)?;

    //         layouter.assign_region(
    //             || "constrain output",
    //             |mut region| {
    //                 let expected_var = region.assign_advice(
    //                     || "load output",
    //                     config.state[0],
    //                     0,
    //                     || self.output,
    //                 )?;
    //                 region.constrain_equal(output.cell(), expected_var.cell())
    //             },
    //         )
    //     }
    // }

//     #[test]
//     fn poseidon_hash() {
//         let rng = OsRng;

//         let message = [Fp::random(rng), Fp::random(rng)];
//         let output =
//             poseidon::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init().hash(message);

//         let k = 6;
//         let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
//             message: Value::known(message),
//             output: Value::known(output),
//             _spec: PhantomData,
//         };
//         let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//         assert_eq!(prover.verify(), Ok(()))
//     }

//     #[test]
//     fn poseidon_hash_longer_input() {
//         let rng = OsRng;

//         let message = [Fp::random(rng), Fp::random(rng), Fp::random(rng)];
//         let output =
//             poseidon::Hash::<_, OrchardNullifier, ConstantLength<3>, 3, 2>::init().hash(message);

//         let k = 7;
//         let circuit = HashCircuit::<OrchardNullifier, 3, 2, 3> {
//             message: Value::known(message),
//             output: Value::known(output),
//             _spec: PhantomData,
//         };
//         let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//         assert_eq!(prover.verify(), Ok(()))
//     }

//     #[test]
//     fn poseidon_hash_longer_input_custom() {
//         let rng = OsRng;

//         let message = [Fp::random(rng), Fp::random(rng), Fp::random(rng), Fp::random(rng)];
//         let output =
//             poseidon::Hash::<_, OrchardNullifier, ConstantLength<4>, 3, 2>::init().hash(message);

//         let k = 7;
//         let circuit = HashCircuit::<OrchardNullifier, 3, 2, 4> {
//             message: Value::known(message),
//             output: Value::known(output),
//             _spec: PhantomData,
//         };
//         let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//         assert_eq!(prover.verify(), Ok(()))
//     }

//     #[test]
//     fn hash_test_vectors() {
//         for tv in crate::poseidon::primitives::test_vectors::fp::hash() {
//             let message = [
//                 pallas::Base::from_repr(tv.input[0]).unwrap(),
//                 pallas::Base::from_repr(tv.input[1]).unwrap(),
//             ];
//             let output = poseidon::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init()
//                 .hash(message);

//             let k = 6;
//             let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
//                 message: Value::known(message),
//                 output: Value::known(output),
//                 _spec: PhantomData,
//             };
//             let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//             assert_eq!(prover.verify(), Ok(()));
//         }
//     }

//     #[cfg(feature = "test-dev-graph")]
//     #[test]
//     fn print_poseidon_chip() {
//         use plotters::prelude::*;

//         let root = BitMapBackend::new("poseidon-chip-layout.png", (1024, 768)).into_drawing_area();
//         root.fill(&WHITE).unwrap();
//         let root = root
//             .titled("Poseidon Chip Layout", ("sans-serif", 60))
//             .unwrap();

//         let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
//             message: Value::unknown(),
//             output: Value::unknown(),
//             _spec: PhantomData,
//         };
//         halo2_proofs::dev::CircuitLayout::default()
//             .render(6, &circuit, &root)
//             .unwrap();
//     }
// }
//}
