/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionBounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute scalar convergence of compact-distribution exponential coefficients

These are the actual Schwartz polynomial coefficients. Every Schwartz
seminorm gives an absolutely summable series at every scalar radius when
the phase is bounded on the cutoff support. Evaluation by an actual tempered
distribution therefore has absolutely summable scalar coefficients. This
module does not identify their sum with evaluation on the cutoff exponential;
that identification requires convergence of the Schwartz Taylor remainders and
is proved in `FreeField/CompactDistributionEntire.lean`
(`hasSum_distribution_spatialSchwartzExponential`).
-/

@[expose] public section

open scoped SchwartzMap

namespace VacuumBellSeparation

private theorem descFactorial_div_factorial {n i : ℕ} (hi : i ≤ n) :
    (n.descFactorial i : ℝ) / n.factorial = 1 / (n - i).factorial := by
  apply (div_eq_div_iff (by positivity : (n.factorial : ℝ) ≠ 0)
    (by positivity : ((n - i).factorial : ℝ) ≠ 0)).mpr
  exact_mod_cast (by simpa [mul_comm] using Nat.factorial_mul_descFactorial hi)

/-- Descending factorials turn the differentiated exponential majorant into a shifted
exponential. -/
theorem summable_exponential_derivative_majorant (r R : ℝ) (i : ℕ) :
    Summable (fun n : ℕ => (n.descFactorial i : ℝ) / n.factorial * (r ^ n * R ^ (n - i))) := by
  apply (summable_nat_add_iff i).mp
  convert (Real.summable_pow_div_factorial (r * R)).mul_left (r ^ i) using 1
  funext n
  rw [descFactorial_div_factorial (Nat.le_add_left i n), Nat.add_sub_cancel,
    pow_add, mul_pow]
  ring

/-- The actual `a(x)^n φ(x)/n!` Schwartz coefficient. -/
noncomputable def spatialExponentialCoefficient
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (n.factorial : ℂ)⁻¹ • spatialLinearMoment a n φ

theorem seminorm_spatialExponentialCoefficient_le
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ x ∈ tsupport φ, |a x| ≤ R) (k j n : ℕ) :
    SchwartzMap.seminorm ℂ k j (spatialExponentialCoefficient a φ n) ≤
      ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * ‖a‖ ^ i * SchwartzMap.seminorm ℂ k (j - i) φ) *
          ((n.descFactorial i : ℝ) / n.factorial * R ^ (n - i)) := by
  rw [spatialExponentialCoefficient, map_smul_eq_mul]
  simp only [norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (seminorm_spatialLinearMoment_le a φ hR ha k j n)
    (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)).trans
  apply le_of_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every fixed genuine Schwartz seminorm gives an absolutely convergent coefficient series. -/
theorem summable_seminorm_spatialExponentialCoefficient
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ x ∈ tsupport φ, |a x| ≤ R)
    {r : ℝ} (hr : 0 ≤ r) (k j : ℕ) :
    Summable (fun n => r ^ n *
      SchwartzMap.seminorm ℂ k j (spatialExponentialCoefficient a φ n)) := by
  have hsum : Summable (fun n => ∑ i ∈ Finset.range (j + 1),
      ((j.choose i : ℝ) * ‖a‖ ^ i * SchwartzMap.seminorm ℂ k (j - i) φ) *
        ((n.descFactorial i : ℝ) / n.factorial * (r ^ n * R ^ (n - i)))) := by
    apply summable_sum
    intro i hi
    exact (summable_exponential_derivative_majorant r R i).mul_left _
  apply hsum.of_nonneg_of_le (fun n => by positivity)
  intro n
  apply (mul_le_mul_of_nonneg_left
    (seminorm_spatialExponentialCoefficient_le a φ hR ha k j n) (by positivity)).trans
  apply le_of_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Applying an actual continuous distribution gives scalar absolute convergence at every radius. -/
theorem summable_distribution_spatialExponentialCoefficient
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ x ∈ tsupport φ, |a x| ≤ R) (z : ℂ) :
    Summable (fun n => z ^ n * T (spatialExponentialCoefficient a φ n)) := by
  obtain ⟨s, C, hC, hb⟩ := temperedDistribution_finite_seminorm_bound T
  have hsum : Summable (fun n => (C : ℝ) *
      ∑ i ∈ s, ‖z‖ ^ n *
        SchwartzMap.seminorm ℂ i.1 i.2 (spatialExponentialCoefficient a φ n)) := by
    apply Summable.mul_left
    apply summable_sum
    intro i hi
    exact summable_seminorm_spatialExponentialCoefficient a φ hR ha (norm_nonneg z) i.1 i.2
  apply hsum.of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  have hsup := Seminorm.finset_sup_le_sum
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 3)) ℂ) s
      (spatialExponentialCoefficient a φ n)
  have hb' := (hb (spatialExponentialCoefficient a φ n)).trans
    (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)
  apply (mul_le_mul_of_nonneg_left hb' (by positivity)).trans
  apply le_of_eq
  simp only [sum_apply, schwartzSeminormFamily, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end VacuumBellSeparation
