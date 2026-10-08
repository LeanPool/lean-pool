/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMoment
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyLp

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakEnergyTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bad-event optimizer energy under the source envelope

The bad-event optimizer energy of the weak-norm split, at the inflated
reference `2·boundaryConst·3^{gG}·E`, is bounded through the parametric bad-energy estimate: the
excess part `(M − 1/2)⁺` of the maximal
function is supported on the source tail and has fourth moments decaying
like `3^{-2Δ}` by the crude-moment display, with `Δ = t + G − 1 − s_K` the
gap between the generation scale and the growth witness.  No window
multiplier and no history enters.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The crude-moment constant of order six. -/
@[expose]
def sourceMomentSix (K : ℝ) : ℝ :=
  1 + 2 * (6 : ℝ) * (1 + Real.log (growthBar K)) *
    growthBar K ^ IndependentSums.natTriangular 6

/-- The decayed fourth-moment majorant of the maximal excess. -/
@[expose]
def badMomentMajorant (K : ℝ) (Delta : ℤ) : ℝ :=
  (3 : ℝ) ^ (-((2 : ℝ) * (Delta : ℝ))) * sourceMomentSix K / 16

theorem sourceMomentSix_nonneg (K : ℝ) :
    0 ≤ sourceMomentSix K := by
  have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [h2])
  have hpow : (0 : ℝ) ≤ growthBar K ^ IndependentSums.natTriangular 6 := by
    positivity
  rw [sourceMomentSix]
  nlinarith only [hlog, hpow]

theorem badMomentMajorant_nonneg (K : ℝ) (Delta : ℤ) :
    0 ≤ badMomentMajorant K Delta := by
  rw [badMomentMajorant]
  have h1 := sourceMomentSix_nonneg K
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((2 : ℝ) * (Delta : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  positivity

/-- The `L⁴` norm of a nonnegative extended statistic through its fourth
moment. -/
theorem eLpNorm_four_le_of_lintegral_le
    {P : Measure (CoeffSpace d)}
    {W : CoeffSpace d → ℝ≥0∞} {h : ℝ} (hh : 0 ≤ h)
    (hmom : ∫⁻ a, W a ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal h) (hW : AEMeasurable W P) :
    eLpNorm W (ENNReal.ofReal 4) P ≤ ENNReal.ofReal (h ^ ((4 : ℝ)⁻¹)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hW.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [enorm_eq_self]
  calc
    (∫⁻ a, W a ^ (4 : ℝ) ∂P) ^ (1 / (4 : ℝ)) ≤
        (ENNReal.ofReal h) ^ (1 / (4 : ℝ)) :=
      ENNReal.rpow_le_rpow hmom (by norm_num)
    _ = ENNReal.ofReal (h ^ ((4 : ℝ)⁻¹)) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hh (by norm_num)]
      norm_num

/-- The `L⁴` norm of an extended constant on a probability space. -/
theorem eLpNorm_const_four
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (c : ℝ≥0∞) :
    eLpNorm (fun _ : CoeffSpace d => c) (ENNReal.ofReal 4) P = c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) aestronglyMeasurable_const,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [enorm_eq_self]
  rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul]
  norm_num

end

end HCPolySupport.HighContrast.Quenched
