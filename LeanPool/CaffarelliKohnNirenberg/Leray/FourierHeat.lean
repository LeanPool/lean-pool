/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierSpace
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic

/-!
# The heat multiplier on spatial `L²`

The heat operator is the inverse Fourier transform of multiplication by its
Gaussian symbol, as in `sec:regularised`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The heat symbol in the Fourier convention of `sec:regularised`. -/
@[expose]
def heatSymbol (t : ℝ) (ξ : L2Vec3) : ℂ :=
  (Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) : ℂ)

/-- The heat symbol is bounded by one for nonnegative time. -/
theorem heatSymbol_norm_le_one {t : ℝ} (ht : 0 ≤ t) (ξ : L2Vec3) :
    ‖heatSymbol t ξ‖ ≤ 1 := by
  rw [heatSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  calc
    -4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 =
        -(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) := by ring
    _ ≤ 0 := neg_nonpos.mpr
      (mul_nonneg (mul_nonneg (by positivity) ht) (sq_nonneg ‖ξ‖))

/-- The heat multiplier as a bounded multiplier on frequency-space `L²`. -/
@[expose]
def heatMultiplier (t : ℝ) (ht : 0 ≤ t) : Lp (α := L2Vec3) ℂ ∞ :=
  let hmem : MemLp (heatSymbol t) ∞ volume := by
    apply memLp_top_of_bound (by
      change AEStronglyMeasurable
        (fun ξ : L2Vec3 => (Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) : ℂ)) volume
      fun_prop) 1
    filter_upwards [] with ξ
    exact heatSymbol_norm_le_one ht ξ
  hmem.toLp (heatSymbol t)

/-- The Gaussian multiplier has essential-supremum norm at most one. -/
theorem heatMultiplier_norm_le_one (t : ℝ) (ht : 0 ≤ t) :
    ‖heatMultiplier t ht‖ ≤ 1 := by
  let hmem : MemLp (heatSymbol t) ∞ volume := by
    apply memLp_top_of_bound (by
      change AEStronglyMeasurable
        (fun ξ : L2Vec3 => (Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) : ℂ)) volume
      fun_prop) 1
    filter_upwards [] with ξ
    exact heatSymbol_norm_le_one ht ξ
  change ‖hmem.toLp (heatSymbol t)‖ ≤ 1
  rw [Lp.norm_toLp, eLpNorm_exponent_top hmem.aestronglyMeasurable]
  have hess : eLpNormEssSup (heatSymbol t) volume ≤ (1 : ℝ≥0∞) := by
    simpa using eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall fun ξ => heatSymbol_norm_le_one ht ξ)
  exact ENNReal.toReal_mono (by norm_num) hess

/-- The heat semigroup on complex velocity `L²`, defined by its Fourier
multiplier. -/
@[expose]
def heatSemigroup (t : ℝ) (ht : 0 ≤ t)
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  exact ℱ.symm (heatMultiplier t ht • ℱ v)

/-- The heat semigroup is an `L²` contraction, by Plancherel and the Gaussian
symbol bound in `lem:reg-multiplier-bounds`. -/
theorem heatSemigroup_norm_le (t : ℝ) (ht : 0 ≤ t)
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    ‖heatSemigroup t ht v‖ ≤ ‖v‖ := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ‖ℱ.symm (heatMultiplier t ht • ℱ v)‖ ≤ ‖v‖
  rw [ℱ.symm.norm_map]
  calc
    ‖heatMultiplier t ht • ℱ v‖ ≤ ‖heatMultiplier t ht‖ * ‖ℱ v‖ :=
      MeasureTheory.Lp.norm_smul_le _ _
    _ ≤ 1 * ‖v‖ := by
      rw [ℱ.norm_map]
      exact mul_le_mul_of_nonneg_right (heatMultiplier_norm_le_one t ht)
        (norm_nonneg v)
    _ = ‖v‖ := by ring

end CKN.Leray
