use core::num;
use std::{default, marker::PhantomData, slice::Windows, usize};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    pasta::group::ff::PrimeFieldBits,
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

/// This gadget range-constrains an element witnessed in the circuit to be N bits.
///
/// Internally, this gadget uses the `range_check` helper, which provides a K-bit
/// lookup table.
///
/// Given an element `value`, we use a running sum to break it into K-bit chunks.
/// Assume for now that N | K, and define C = N / K.
///
///     value = [b_0, b_1, ..., b_{N-1}]   (little-endian)
///           = c_0 + 2^K * c_1  + 2^{2K} * c_2 + ... + 2^{(C-1)K} * c_{C-1}
///
/// Initialise the running sum at
///                                 value = z_0.
///
/// Consequent terms of the running sum are z_{i+1} = (z_i - c_i) * 2^{-K}:
///
///                           z_1 = (z_0 - c_0) * 2^{-K}
///                           z_2 = (z_1 - c_1) * 2^{-K}
///                              ...
///                       z_{C-1} = c_{C-1}
///                           z_C = (z_{C-1} - c_{C-1}) * 2^{-K}
///                               = 0
///
/// One configuration for this gadget could look like:
///
///     | running_sum |  q_decompose  |  table_value  |
///     -----------------------------------------------
///     |     z_0     |       1       |       0       |
///     |     z_1     |       1       |       1       |
///     |     ...     |      ...      |      ...      |
///     |   z_{C-1}   |       1       |      ...      |
///     |     z_C     |       0       |      ...      |
///
/// Stretch task: use the tagged lookup table to constrain arbitrary bitlengths
/// (even non-multiples of K)

#[derive(Debug, Clone)]
struct DecomposeConfig<
    F: FieldExt + PrimeFieldBits,
    const LOOKUP_NUM_BITS: usize,
    const LOOKUP_RANGE: usize,
> {
    // You'll need an advice column to witness your running sum;
    // A selector to constrain the running sum;
    // A selector to lookup the K-bit chunks;
    // And of course, the K-bit lookup table
    q_running_sum: Selector,
    q_lookup: Selector,
    z: Column<Advice>,
    table: TableColumn,
    // table: RangeTableConfig<F, LOOKUP_NUM_BITS, LOOKUP_RANGE>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt + PrimeFieldBits, const LOOKUP_NUM_BITS: usize, const LOOKUP_RANGE: usize>
    DecomposeConfig<F, LOOKUP_NUM_BITS, LOOKUP_RANGE>
{
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        z: Column<Advice>,
        table: TableColumn,
    ) -> Self {
        // Create the needed columns and internal configs.
        let q_running_sum = meta.selector();
        let q_lookup = meta.complex_selector();

        let config = DecomposeConfig {
            q_running_sum,
            q_lookup,
            z,
            table,
            _marker: PhantomData,
        };

        // Check that each interstitial value of the running sum is composed correctly from the previous one.
        // meta.create_gate("z_{i+1} = (z_i - c_i) * 2^{-K}", |meta| todo!());

        // Range-constrain each K-bit chunk `c_i = z_i - z_{i+1} * 2^K` derived from the running sum.
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);

            let z = meta.query_advice(config.z, Rotation::cur());
            let z_next = meta.query_advice(config.z, Rotation::cur());
            let c = z - (z_next * Expression::Constant(FieldExt::from_u128(1 << LOOKUP_NUM_BITS)));

            vec![(q_lookup * c, config.table)]
        });

        config
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        z_0: AssignedCell<F, F>,
        num_bits: usize,
        num_of_windows: usize,
    ) -> Result<(), Error> {
        let offset = 0;
        // 1. Compute the interstitial running sum values {z_0, ..., z_C}}
        // 2. Assign the running sum values
        // 3. Make sure to enable the relevant selector on each row of the running sum

        layouter.assign_region(
            || "range check",
            |mut region: Region<'_, F>| {
                self.q_lookup.enable(&mut region, offset)?;
                z_0.copy_advice(|| "z_0", &mut region, self.z, offset)?;

                let words = z_0
                    .value()
                    .map(|v| decompose_word::<F>(v, num_bits, 1 << LOOKUP_NUM_BITS));

                let mut z_last = z_0.value().copied();
                let mut last_cell = z_0.clone();

                let two_pow_k_inv =
                    Value::known(F::from(1 << LOOKUP_NUM_BITS as u64).invert().unwrap());
                for (i, word) in words.transpose_vec(num_of_windows).into_iter().enumerate() {
                    let word = word.map(|word| F::from(word as u64));

                    let z_curr = (z_last - word) * two_pow_k_inv;
                    z_last = z_curr;

                    last_cell = region.assign_advice(
                        || format!("z_{}", i),
                        self.z,
                        offset + 1 + i,
                        || z_last,
                    )?;
                }

                region.constrain_constant(last_cell.cell(), F::zero())
            },
        )?;

        Ok(())
    }
}

/// [Ref]
fn decompose_word<F: PrimeFieldBits>(
    word: &F,
    word_num_bits: usize,
    window_num_bits: usize,
) -> Vec<u8> {
    let padding = (window_num_bits - (word_num_bits % window_num_bits)) % window_num_bits;
    let bits: Vec<bool> = word
        .to_le_bits()
        .into_iter()
        .take(word_num_bits)
        .chain(std::iter::repeat(false).take(padding))
        .collect();
    bits.chunks_exact(window_num_bits)
        .map(|chunk| {
            chunk
                .iter()
                .rev()
                .fold(0, |acc, val| (acc << 1) + *val as u8)
        })
        .collect()
}
