/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DoubledMinimizerReadouts

/-!
# High-contrast homogenization: Analytic.WeightedBlockCoordOperator

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weighted coordinate pairings of block `L²` fields

A localized quadratic observable of a doubled field is an integral of a bounded
weight against a product of two of its doubled coordinates.  This file realizes
such a pairing as the ambient inner product against the image of a bounded
multiplication operator, so that it is continuous in both field arguments, and
records the resulting measurability rule: the pairing of two strongly measurable
sample-dependent fields is a measurable function of the sample.

The operator is the pointwise rank-one field `x ↦ eta x • (u ↦ u_alpha • e_beta)`,
which is measurable and uniformly bounded whenever the weight is.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The coordinate units of the doubled Hilbert carrier -/

/-- The unit of the doubled Hilbert carrier at one doubled coordinate. -/
@[expose]
def blockCoordUnit (alpha : BlockCoord d) : HilbertBlockVec d :=
  HilbertBlockVec.ofBlockVec (blockBasis alpha)

theorem inner_blockCoordUnit (alpha : BlockCoord d) (u : HilbertBlockVec d) :
    inner ℝ (blockCoordUnit alpha) u = toFullBlockVec u.toBlockVec alpha := by
  rw [HilbertBlockVec.inner_def, blockCoordUnit, HilbertBlockVec.toBlockVec_ofBlockVec]
  cases alpha with
  | inl i =>
      simp [blockBasis, blockVecDot, vecDot, toFullBlockVec, Pi.single_apply, ite_mul,
        Finset.sum_ite_eq']
  | inr i =>
      simp [blockBasis, blockVecDot, vecDot, toFullBlockVec, Pi.single_apply, ite_mul,
        Finset.sum_ite_eq']

/-- The pointwise rank-one operator pairing one doubled coordinate against
another. -/
@[expose]
def coordOperator (alpha beta : BlockCoord d) :
    HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
  (innerSL ℝ (blockCoordUnit alpha)).smulRight (blockCoordUnit beta)

theorem inner_coordOperator (alpha beta : BlockCoord d) (u v : HilbertBlockVec d) :
    inner ℝ (coordOperator alpha beta u) v =
      toFullBlockVec u.toBlockVec alpha * toFullBlockVec v.toBlockVec beta := by
  rw [coordOperator]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_left,
    inner_blockCoordUnit]

/-! ## The weighted coordinate operator -/

/-- The pointwise operator field of a weighted coordinate pairing. -/
@[expose]
def weightedCoordOperatorField {U : Set (Vec d)} {eta : Vec d → ℝ}
    (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C)
    (alpha beta : BlockCoord d) : PointwiseHilbertBlockOperatorField U where
  field := fun x => eta x • coordOperator alpha beta
  measurable_field := by
    exact ((continuous_id.smul continuous_const).measurable).comp hmeas
  opNormBound := C * ‖coordOperator (d := d) alpha beta‖
  opNormBound_nonneg := mul_nonneg hC (norm_nonneg _)
  le_opNormBound := by
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

/-- The weighted coordinate pairing operator on block `L²` fields. -/
@[expose]
def weightedCoordOperator {U : Set (Vec d)} {eta : Vec d → ℝ}
    (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C)
    (alpha beta : BlockCoord d) : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (weightedCoordOperatorField (U := U) hmeas hC hbound alpha beta).toContinuousLinearMap

/-- The ambient inner product against the image of a pointwise operator field is
the integral of the pointwise inner products. -/
theorem inner_pointwiseOperator_eq_integral {U : Set (Vec d)}
    (M : PointwiseHilbertBlockOperatorField U) (F G : HilbertBlockL2 U) :
    inner ℝ (M.toContinuousLinearMap F) G =
      ∫ x in U, inner ℝ (M.field x ((F : Vec d → HilbertBlockVec d) x))
        ((G : Vec d → HilbertBlockVec d) x) ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [M.coeFn_toContinuousLinearMap F] with x hx
  rw [hx]
  rfl

/-- **The weighted coordinate pairing is an ambient inner product.** -/
theorem inner_weightedCoordOperator {U : Set (Vec d)} {eta : Vec d → ℝ}
    (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C)
    (alpha beta : BlockCoord d) (F G : HilbertBlockL2 U) :
    inner ℝ (weightedCoordOperator (U := U) hmeas hC hbound alpha beta F) G =
      ∫ x in U, eta x *
          toFullBlockVec ((F : Vec d → HilbertBlockVec d) x).toBlockVec alpha *
          toFullBlockVec ((G : Vec d → HilbertBlockVec d) x).toBlockVec beta ∂volume := by
  rw [weightedCoordOperator, inner_pointwiseOperator_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change inner ℝ (eta x • coordOperator alpha beta ((F : Vec d → HilbertBlockVec d) x))
    ((G : Vec d → HilbertBlockVec d) x) = _
  rw [real_inner_smul_left, inner_coordOperator]
  ring

/-! ## Measurability of the pairing of two sample-dependent fields -/

end

end Selection
end HighContrast
end HCPolySupport
