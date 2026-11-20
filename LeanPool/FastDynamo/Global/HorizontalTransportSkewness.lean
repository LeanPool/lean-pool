/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.ReducedInductionEnergyIdentity
public import LeanPool.FastDynamo.Operator.VerticalZeroExtend

/-!
# Transport skewness for the horizontal two-component torus operator

The sentence before `eq:background-testing` in the proof of `prop:background-resolvent`
("Since `Div_⊥ (u_n^bg)_⊥ = 0`, the transport term that contains no factor `β_n` has zero real
part") is the one identity behind `eq:background-coercivity` that is not a Hölder estimate.
The three-component statement is proved in
`ReducedInductionEnergyIdentity.re_inner_reducedInductionTransport_eq_zero`; this module
transfers it to the two-component operator `horizontalInductionOperator` of
`eq:background-operator`.

The transfer is by the **isometric zero-extension** `ℂ² ↪ ℂ³` — append a vanishing axial
component.  Unlike the horizontal projection `horizontalProjPoint` of
`Operator/HorizontalSector.lean`, that embedding preserves the inner product, so real parts
are transported verbatim; and the transverse transport term acts diagonally in the fibre, so
it commutes with the embedding.

The zero-extension is also the natural way to move any other fibre-diagonal three-component
identity (diffusion, axial multiplier) down to two components; the stretching term is the one
term that does **not** commute with it, which is exactly the `(3,⊥)` block recorded in
`Operator/HorizontalSector.lean`.

The `L²`/`H²` tower of the zero-extension itself is generic and lives in
`Operator/VerticalZeroExtend.lean`; only the transport application is kept here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Two-component transport skewness

The three-component transport skewness is
`ReducedInductionEnergyIdentity.re_inner_reducedInductionTransport_eq_zero`,
and the transport term acts diagonally in the fibre, so it suffices to embed a two-component
field as a three-component field with vanishing axial component.  The generic `L²`/`H²` tower
of that embedding is `Operator/VerticalZeroExtend.lean`; only its application to the transport
term is below. -/

/-- The transverse transport term commutes with the zero-extension: it acts diagonally in
the fibre, through scalar multiplication and the transverse derivatives only. -/
theorem reducedInductionTransport_verticalZeroExtendH2
    (u : TransverseRealW1Inf) (h : TransverseC2H2) :
    reducedInductionTransport u (verticalZeroExtendH2 h) =
      verticalZeroExtendL2 (horizontalInductionTransport u h) := by
  rw [reducedInductionTransport_apply, horizontalInductionTransport_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [verticalZeroExtendL2_scalarVectorMulTransverse,
    verticalZeroExtendL2_transverseVecDerivFromH2]

/--
**Transport skewness on two components.**  For every real periodic `W^{1,∞}` velocity with
vanishing transverse weak divergence, `Re ⟨h, u_⊥·∇_⊥ h⟩ = 0`
(the sentence before `eq:background-testing`: "Since `Div_⊥ (u_n^bg)_⊥ = 0`, the transport
term that contains no factor `β_n` has zero real part").  This is the two-component analogue of
`ReducedInductionEnergyIdentity.re_inner_reducedInductionTransport_eq_zero`, obtained from it
by the isometric zero-extension `ℂ² ↪ ℂ³`.
-/
theorem re_inner_horizontalInductionTransport_eq_zero
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (h : TransverseC2H2) :
    (inner ℂ (transverseH2Embedding h) (horizontalInductionTransport u h)).re = 0 := by
  have h1 := re_inner_reducedInductionTransport_eq_zero u hu 0 (verticalZeroExtendH2 h)
  rw [transverseH2Embedding_verticalZeroExtendH2,
    reducedInductionTransport_verticalZeroExtendH2, inner_verticalZeroExtendL2] at h1
  exact h1

end

end FastDynamo
