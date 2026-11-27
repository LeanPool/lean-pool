/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwich

/-!
# Sharp trace-class criterion for the commuting thermal sandwich

The strict scalar inequality `p < q^τ` is necessary as well as sufficient
for a positive trace-class solution of the actual density factorization.
The necessity argument applies to every bounded operator solution, and
does not interpret the default value of a nonsummable operator series as
an inverse-power sandwich.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem IsPositiveTraceClass.summable_diagonal (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    Summable fun i => (inner ℂ (b i) (A (b i))).re := by
  have hfinite := hA.2.ne
  rw [positiveTrace_eq_tsum_diagonal b hA.1] at hfinite
  have hnonneg (i : ι) : 0 ≤ (inner ℂ (b i) (A (b i))).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hA.1).re_inner_nonneg_right (b i)
  simpa only [ENNReal.toReal_ofReal (hnonneg _)] using ENNReal.summable_toReal hfinite

/-- Every bounded solution has the forced number-basis eigenvalues,
including outside the trace-class domain. -/
theorem thermal_factorization_apply_numberBasis {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ : 0 < τ) {A : OscillatorSpace →L[ℂ] OscillatorSpace}
    (hA : (thermalDensity q ^ (τ / 2)) * A *
      (thermalDensity q ^ (τ / 2)) = thermalDensity p) (n : ℕ) :
    A (numberBasis n) = thermalSandwichWeight p q τ n • numberBasis n := by
  let S := thermalDensity q ^ (τ / 2)
  let a := thermalWeight q n ^ (τ / 2)
  have ha : 0 < a := Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ n) _
  have heig : S (numberBasis n) = a • numberBasis n :=
    thermalDensity_rpow_apply_numberBasis hq₀.le hq₁ (half_pos hτ) n
  have hpow : a * a = thermalWeight q n ^ τ := by
    dsimp [a]
    rw [← Real.rpow_add (thermalWeight_pos hq₀ hq₁ n), add_halves]
  have hscalar : a * (thermalSandwichWeight p q τ n * a) = thermalWeight p n := by
    rw [thermalSandwichWeight]
    calc
      _ = (thermalWeight p n / thermalWeight q n ^ τ) * (a * a) := by ring
      _ = _ := by rw [hpow, div_mul_cancel₀ _
        (ne_of_gt (Real.rpow_pos_of_pos (thermalWeight_pos hq₀ hq₁ n) τ))]
  apply smul_right_injective OscillatorSpace ha.ne'
  apply thermalDensity_rpow_injective hq₀ hq₁ (half_pos hτ)
  change S (a • A (numberBasis n)) =
    S (a • (thermalSandwichWeight p q τ n • numberBasis n))
  calc
    _ = (S * A * S) (numberBasis n) := by
      simp only [mul_apply_eq_comp, heig, map_smul_of_tower]
    _ = thermalWeight p n • numberBasis n := by
      rw [show S * A * S = thermalDensity p from hA,
        thermalDensity_apply_numberBasis hp₀ hp₁]
    _ = _ := by
      simp only [map_smul_of_tower, heig, smul_smul, mul_assoc, hscalar]

theorem thermal_factorization_traceClass_implies_lt {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ : 0 < τ) {A : OscillatorSpace →L[ℂ] OscillatorSpace}
    (hA : (thermalDensity q ^ (τ / 2)) * A *
      (thermalDensity q ^ (τ / 2)) = thermalDensity p)
    (htrace : IsPositiveTraceClass A) : p < q ^ τ := by
  have hdiag (n : ℕ) : (inner ℂ (numberBasis n) (A (numberBasis n))).re =
      thermalSandwichWeight p q τ n := by
    rw [thermal_factorization_apply_numberBasis hp₀ hp₁ hq₀ hq₁ hτ hA,
      inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
      numberBasis.orthonormal.norm_eq_one]
    simp [Algebra.smul_def]
  have hsum : Summable (thermalSandwichWeight p q τ) := by
    simpa only [hdiag] using htrace.summable_diagonal numberBasis
  have hc : (1 - p) / (1 - q) ^ τ ≠ 0 :=
    ne_of_gt (div_pos (sub_pos.mpr hp₁) (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _))
  have hgeometric : Summable fun n : ℕ => (p / q ^ τ) ^ n := by
    apply (summable_mul_left_iff hc).mp
    have heq : thermalSandwichWeight p q τ =
        fun n => ((1 - p) / (1 - q) ^ τ) * (p / q ^ τ) ^ n :=
      funext fun n => thermalSandwichWeight_geometric hq₀.le hq₁ n
    rw [heq] at hsum
    exact hsum
  have hqτ : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  have hr : p / q ^ τ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp₀ hqτ.le)] using
      summable_geometric_iff_norm_lt_one.mp hgeometric
  exact (div_lt_one hqτ).mp hr

/-- The commuting one-mode analogue of the strict Gaussian sandwich
criterion, stated as existence of an actual positive trace-class operator. -/
theorem exists_positiveTraceClass_thermal_factorization_iff {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    (∃ A : OscillatorSpace →L[ℂ] OscillatorSpace,
      IsPositiveTraceClass A ∧
      (thermalDensity q ^ (τ / 2)) * A *
        (thermalDensity q ^ (τ / 2)) = thermalDensity p) ↔ p < q ^ τ := by
  constructor
  · rintro ⟨A, htrace, hA⟩
    exact thermal_factorization_traceClass_implies_lt hp₀ hp₁ hq₀ hq₁ hτ hA htrace
  · intro hpq
    exact ⟨thermalSandwich p q τ,
      thermalSandwich_isPositiveTraceClass hp₀ hp₁ hq₀ hq₁ hpq,
      thermalSandwich_factorization hp₀ hp₁ hq₀ hq₁ hτ hpq⟩

end VacuumBellSeparation.Gaussian
