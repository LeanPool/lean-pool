/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalGaussianEstimates

/-!
# Real denominator-free event bounds from actual finite Gaussian comparison

The conversion retains zero probabilities. No division by a probability
is used, and both comparison coefficients are explicit upper bounds on
the corresponding genuine Rényi quantity.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace ENNReal

theorem real_event_bound_of_ennreal {x y K r : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hK : 0 ≤ K) (hr : 1 < r)
    (h : ENNReal.ofReal x ^ r ≤ ENNReal.ofReal K * ENNReal.ofReal y ^ (r - 1)) :
    x ^ r ≤ K * y ^ (r - 1) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (lt_trans zero_lt_one hr).le,
    ENNReal.ofReal_rpow_of_nonneg hy (sub_pos.mpr hr).le, ← ENNReal.ofReal_mul hK] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (Real.rpow_nonneg hy _))).mp h

variable {m : ℝ} {hm : 0 < m} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : FreeFieldVacuum m H} {S T : Submodule ℝ TimeZeroSource}

namespace FiniteGaussianPairModel

variable (X : FiniteGaussianPairModel hm V S T)

theorem forward_event_bound {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hQ : sandwichedRenyiQuantity X.density X.reference r ≤ ENNReal.ofReal K)
    {A B : H →L[ℂ] H} (hA : A ∈ effects (canonicalSourceAlgebra V hm S))
    (hB : B ∈ effects (canonicalSourceAlgebra V hm T)) (hAB : A * B = B * A) :
    (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ r ≤
      K * ((⟪V.vacuum, A V.vacuum⟫_ℂ).re * (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ (r - 1) := by
  have hA₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA.2.1
  have hA₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA.2.2)
  have hB₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hB.2.1
  have hB₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB.2.2)
  have hprod := commuting_effect_product hA₀ hA₁ hB₀ hB₁ hAB
  have hw : 0 ≤ (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hprod.1).re_inner_nonneg_right _
  have hp : 0 ≤ (⟪V.vacuum, A V.vacuum⟫_ℂ).re * (⟪V.vacuum, B V.vacuum⟫_ℂ).re :=
    mul_nonneg (hA.2.1.re_inner_nonneg_right _) (hB.2.1.re_inner_nonneg_right _)
  exact real_event_bound_of_ennreal hw hp hK hr
    ((X.effect_renyi_bounds hr hA.1 hB.1 hA₀ hA₁ hB₀ hB₁ hAB).1.trans
      (_root_.mul_le_mul_left hQ _))

theorem reverse_event_bound {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hQ : sandwichedRenyiQuantity X.reference X.density r ≤ ENNReal.ofReal K)
    {A B : H →L[ℂ] H} (hA : A ∈ effects (canonicalSourceAlgebra V hm S))
    (hB : B ∈ effects (canonicalSourceAlgebra V hm T)) (hAB : A * B = B * A) :
    ((⟪V.vacuum, A V.vacuum⟫_ℂ).re * (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ r ≤
      K * (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ (r - 1) := by
  have hA₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA.2.1
  have hA₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA.2.2)
  have hB₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hB.2.1
  have hB₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB.2.2)
  have hprod := commuting_effect_product hA₀ hA₁ hB₀ hB₁ hAB
  have hw : 0 ≤ (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hprod.1).re_inner_nonneg_right _
  have hp : 0 ≤ (⟪V.vacuum, A V.vacuum⟫_ℂ).re * (⟪V.vacuum, B V.vacuum⟫_ℂ).re :=
    mul_nonneg (hA.2.1.re_inner_nonneg_right _) (hB.2.1.re_inner_nonneg_right _)
  exact real_event_bound_of_ennreal hp hw hK hr
    ((X.effect_renyi_bounds hr hA.1 hB.1 hA₀ hA₁ hB₀ hB₁ hAB).2.trans
      (_root_.mul_le_mul_left hQ _))

end FiniteGaussianPairModel

end VacuumBellSeparation
