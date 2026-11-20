/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WeakLeibniz

/-!
# Fibre-generic multiplier algebra on the transverse torus

Every localisation step of the paper's proof — the cut-off commutators of §7, the axial
recovery of §8, the horizontal reduction of §5 — multiplies a `ℂ^ι`-valued `L²` field on the
transverse torus by a scalar `L∞` coefficient and then reads a single fibre coordinate, or
applies a pointwise fibre map.  The two operations commute, for the trivial reason that both are
pointwise.

This module states that once, generically in the fibre map and in the index type `ι`:

* `compLpL_scalarVectorMulL2` / `compLpL_vectorScalarMulL2` — a pointwise fibre map commutes
  with Hölder multiplication by a scalar `L∞` (resp. `L²`) factor;
* `transverseCoordL2_scalarVectorMulTransverseVec` — a scalar `L∞` coefficient acts
  componentwise on a `ℂ^ι`-valued field, with the three-component specialisation
  `transverseCoordL2_scalarVectorMulTransverse` that the reduced induction operator uses.

Nothing here is specific to a step of the proof; the statements are used in
`Operator/HorizontalSector.lean`, `Global/HorizontalCutoffCommutator.lean`,
`Global/PeriodicSecondOrderCutoffs.lean` and `Finish/AxialRecoveryDivergence.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

section PointwiseCommutation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A pointwise fibre map commutes with multiplication by a scalar `L∞` factor. -/
theorem compLpL_scalarVectorMulL2 (L : E →L[ℂ] F)
    (a : TransverseScalarLInf) (f : Lp E 2 transverseMeasure) :
    L.compLpL 2 transverseMeasure (scalarVectorMulL2 transverseMeasure a f) =
      scalarVectorMulL2 transverseMeasure a (L.compLpL 2 transverseMeasure f) := by
  ext1
  filter_upwards [L.coeFn_compLpL (scalarVectorMulL2 transverseMeasure a f),
    scalarVectorMulL2_coe_ae transverseMeasure a f,
    scalarVectorMulL2_coe_ae transverseMeasure a (L.compLpL 2 transverseMeasure f),
    L.coeFn_compLpL f] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4, map_smul]

/-- A pointwise fibre map commutes with multiplication by a scalar `L²` factor, provided the
same map is applied to the vector-valued `L∞` coefficient. -/
theorem compLpL_vectorScalarMulL2 (L : E →L[ℂ] F)
    (a : Lp E ∞ transverseMeasure) (g : TransverseScalarL2) :
    L.compLpL 2 transverseMeasure (vectorScalarMulL2 transverseMeasure a g) =
      vectorScalarMulL2 transverseMeasure (L.compLpL ∞ transverseMeasure a) g := by
  ext1
  filter_upwards [L.coeFn_compLpL (vectorScalarMulL2 transverseMeasure a g),
    vectorScalarMulL2_coe_ae transverseMeasure a g,
    vectorScalarMulL2_coe_ae transverseMeasure (L.compLpL ∞ transverseMeasure a) g,
    L.coeFn_compLpL a] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4, map_smul]

end PointwiseCommutation

/-! ## Reading one fibre coordinate of a multiplied field -/

/-- A scalar `L∞` coefficient acts componentwise on a `ℂ^ι`-valued `L²` field. -/
theorem transverseCoordL2_scalarVectorMulTransverseVec {ι : Type*} [Fintype ι]
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) (i : ι) :
    transverseCoordL2 i (scalarVectorMulTransverseVec ι a f) =
      scalarMulTransverse a (transverseCoordL2 i f) :=
  compLpL_scalarVectorMulL2 (EuclideanSpace.proj (𝕜 := ℂ) i) a f

/-- The three-component case: multiplication by a scalar `L∞` coefficient acts coordinatewise
on transverse vector fields, `(a f)_i = a f_i`. -/
theorem transverseCoordL2_scalarVectorMulTransverse
    (a : TransverseScalarLInf) (f : TransverseC3L2) (i : Fin 3) :
    transverseCoordL2 i (scalarVectorMulTransverse a f) =
      scalarMulTransverse a (transverseCoordL2 i f) :=
  transverseCoordL2_scalarVectorMulTransverseVec a f i

end

end FastDynamo
