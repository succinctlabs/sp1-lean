//! Concrete field evaluation and one-row Clean runtime support for export comparisons.

use clean_backend::witness_generation::{Interaction, Mode, Padding, Program, WitnessData};
use p3_koala_bear::KoalaBear as NativeField;
use slop_air::{AirBuilder, AirBuilderWithPublicValues};
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::dense::RowMajorMatrix;
use sp1_core_machine::air::TrivialOperationBuilder;
use sp1_hypercube::{
    air::{AirInteraction, InteractionScope, MessageBuilder},
    InteractionKind,
};
use sp1_primitives::SP1Field;
use std::marker::PhantomData;

pub type Ledger = Vec<(String, u64, Vec<u64>)>;

/// SP1 supplies the actual expressions; this builder records their field evaluations.
pub struct Sp1Evaluation {
    pub row: Vec<SP1Field>,
    pub preprocessed: Vec<SP1Field>,
    pub constraints: Vec<SP1Field>,
    pub ledger: Ledger,
    pub public: Vec<SP1Field>,
}

impl AirBuilder for Sp1Evaluation {
    type F = SP1Field;
    type Expr = SP1Field;
    type Var = SP1Field;
    type M = RowMajorMatrix<SP1Field>;
    fn main(&self) -> Self::M {
        RowMajorMatrix::new(self.row.clone(), self.row.len())
    }
    fn is_first_row(&self) -> Self::Expr {
        SP1Field::one()
    }
    fn is_last_row(&self) -> Self::Expr {
        SP1Field::one()
    }
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        panic!("instruction-local comparison must not read adjacent rows")
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, value: I) {
        self.constraints.push(value.into());
    }
}
impl AirBuilderWithPublicValues for Sp1Evaluation {
    type PublicVar = SP1Field;
    fn public_values(&self) -> &[SP1Field] {
        &self.public
    }
}
impl slop_air::PairBuilder for Sp1Evaluation {
    fn preprocessed(&self) -> Self::M {
        RowMajorMatrix::new(self.preprocessed.clone(), self.preprocessed.len())
    }
}
impl TrivialOperationBuilder for Sp1Evaluation {}

impl Sp1Evaluation {
    fn interaction(
        &mut self,
        interaction: AirInteraction<SP1Field>,
        scope: InteractionScope,
        receiving: bool,
    ) {
        assert_eq!(scope, InteractionScope::Local);
        // Clean's State direction agrees with SP1. Byte, Memory and Program orient
        // guarantees from providers to consumers, reversing SP1's send/receive signs.
        let (channel, reverse) = match interaction.kind {
            InteractionKind::State => ("SP1State", false),
            InteractionKind::Byte => ("SP1Byte", true),
            InteractionKind::Memory => ("SP1Memory", true),
            InteractionKind::Program => ("SP1Program", true),
            other => panic!("unmapped SP1 instruction interaction: {other:?}"),
        };
        let mult = if receiving ^ reverse {
            -interaction.multiplicity
        } else {
            interaction.multiplicity
        };
        self.ledger.push((
            channel.to_owned(),
            mult.as_canonical_u64(),
            interaction
                .values
                .iter()
                .map(Sp1PrimeField64::as_canonical_u64)
                .collect(),
        ));
    }
}
impl MessageBuilder<AirInteraction<SP1Field>> for Sp1Evaluation {
    fn send(&mut self, value: AirInteraction<SP1Field>, scope: InteractionScope) {
        self.interaction(value, scope, false);
    }
    fn receive(&mut self, value: AirInteraction<SP1Field>, scope: InteractionScope) {
        self.interaction(value, scope, true);
    }
}

/// The generated constraint function takes row values directly; no expression interpreter.
pub struct NativeEvaluation;
impl p3_air::AirBuilder for NativeEvaluation {
    type F = NativeField;
    type Expr = NativeField;
    type Var = NativeField;
    type M = p3_matrix::dense::RowMajorMatrix<NativeField>;
    fn main(&self) -> Self::M {
        unreachable!("generated constraints take an explicit row")
    }
    fn is_first_row(&self) -> Self::Expr {
        unreachable!("flat AIR has no row selectors")
    }
    fn is_last_row(&self) -> Self::Expr {
        unreachable!("flat AIR has no row selectors")
    }
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        unreachable!("flat AIR has no adjacent-row constraints")
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, _: I) {
        unreachable!("generated constraints return their values")
    }
}
impl p3_air::AirBuilderWithPublicValues for NativeEvaluation {
    type PublicVar = NativeField;
    fn public_values(&self) -> &[NativeField] {
        &[]
    }
}

/// Use Clean's runtime to construct one row, without satisfying its external buses.
/// Only this test adapter suppresses scheduling interactions. The generated interactions
/// are checked separately against SP1, including repeated and zero-multiplicity entries.
/// The unadapted generated program must still reject an active row with no providers.
pub struct RowWitness<P>(PhantomData<P>);
impl<P: Program<NativeField>> Program<NativeField> for RowWitness<P> {
    const FUEL: usize = <P as Program<NativeField>>::FUEL;
    const COMPONENTS: usize = <P as Program<NativeField>>::COMPONENTS;
    const PUBLIC_INPUTS: usize = <P as Program<NativeField>>::PUBLIC_INPUTS;
    const PROVER_INPUTS: usize = <P as Program<NativeField>>::PROVER_INPUTS;
    const FIXED_WIDTHS: &'static [usize] = <P as Program<NativeField>>::FIXED_WIDTHS;
    const COMPONENT_NAMES: &'static [&'static str] = <P as Program<NativeField>>::COMPONENT_NAMES;
    fn modes() -> Vec<Mode<NativeField>> {
        P::modes()
    }
    fn padding() -> Vec<Padding<NativeField>> {
        P::padding()
    }
    fn initial_rows(
        component: usize,
        input: &[NativeField],
    ) -> Result<Vec<Vec<NativeField>>, String> {
        P::initial_rows(component, input)
    }
    fn complete_row(
        component: usize,
        input: &[NativeField],
        data: &WitnessData<NativeField>,
    ) -> Result<Vec<NativeField>, String> {
        P::complete_row(component, input, data)
    }
    fn interactions(_: usize, _: &[NativeField]) -> Vec<Interaction<NativeField>> {
        vec![]
    }
    fn verifier_interactions(_: &[NativeField]) -> Vec<Interaction<NativeField>> {
        vec![]
    }
}
