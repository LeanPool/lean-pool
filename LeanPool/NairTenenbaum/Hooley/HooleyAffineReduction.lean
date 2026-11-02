/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyFixedFactor
public import LeanPool.NairTenenbaum.Hooley.HooleyShortSum
public import LeanPool.NairTenenbaum.Progressions.AffineIrreducibility

/-! # Reducing Hooley short sums to primitive affine restrictions -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset Real

theorem hooleyDelta_affine_eval_le (Q : ℤ[X]) (M a n : ℤ) :
    hooleyDelta (Q.eval (M * n + a)).natAbs ≤
      (affineRestriction Q M a).content.natAbs.divisors.card *
        hooleyDelta ((affineRestriction Q M a).primPart.eval n).natAbs := by
  have H : Q.eval (M * n + a) =
      (affineRestriction Q M a).content * (affineRestriction Q M a).primPart.eval n := by
    have HE := congrArg (fun R : ℤ[X] => R.eval n) (affineRestriction Q M
        a).eq_C_content_mul_primPart
    simpa only [affineRestriction, eval_comp, eval_add, eval_mul, eval_C, eval_X] using HE
  rw [H, Int.natAbs_mul]
  exact hooleyDelta_mul_le_without_coprime _ _

theorem hooley_affine_eval_rpow_le (Q : ℤ[X]) (M a n : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    (hooleyDelta (Q.eval (M * n + a)).natAbs : ℝ) ^ t ≤
      ((affineRestriction Q M a).content.natAbs.divisors.card : ℝ) ^ t *
        (hooleyDelta ((affineRestriction Q M a).primPart.eval n).natAbs : ℝ) ^ t := by
  have HC : (hooleyDelta (Q.eval (M * n + a)).natAbs : ℝ) ≤
      ((affineRestriction Q M a).content.natAbs.divisors.card : ℝ) *
        (hooleyDelta ((affineRestriction Q M a).primPart.eval n).natAbs : ℝ) := by
    exact_mod_cast hooleyDelta_affine_eval_le Q M a n
  have H := Real.rpow_le_rpow (Nat.cast_nonneg _) HC ht
  simpa only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] using H

theorem quotient_mem_affine_shortInterval {M a n : ℕ} (hM : 0 < M) (ha : a < M)
    {x y : ℝ} (hx : (M : ℝ) ≤ x) (hy : 0 ≤ y)
    (hn : n ∈ shortInterval x y) (hr : n % M = a) :
    n / M ∈ shortInterval ((x - a) / M) (y / M) := by
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  have ha' : (a : ℝ) < M := by exact_mod_cast ha
  have hbase : 0 ≤ (x - a) / M := div_nonneg (by linarith) hM₀.le
  have hn' := mem_Ioc.mp hn
  have hnlo : x < (n : ℝ) := Nat.lt_of_floor_lt hn'.1
  have hnhi : (n : ℝ) ≤ x + y := (Nat.le_floor_iff (by linarith)).mp hn'.2
  have HE : (M : ℝ) * (n / M : ℕ) + a = n := by
    exact_mod_cast (show M * (n / M) + a = n by simpa only [hr, add_comm] using Nat.mod_add_div n M)
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt hbase).mpr
    apply (div_lt_iff₀ hM₀).mpr
    nlinarith
  · apply Nat.le_floor
    rw [← add_div]
    apply (le_div_iff₀ hM₀).mpr
    nlinarith

theorem hooleyPolynomialSum_residue_le (Q : ℤ[X]) {M a : ℕ} (hM : 0 < M) (ha : a < M)
    {t x y : ℝ} (ht : 0 ≤ t) (hx : (M : ℝ) ≤ x) (hy : 0 ≤ y) :
    (∑ n ∈ (shortInterval x y).filter (fun n => n % M = a),
      (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ t) ≤
      ((affineRestriction Q M a).content.natAbs.divisors.card : ℝ) ^ t *
        hooleyPolynomialSum (affineRestriction Q M a).primPart t ((x - a) / M) (y / M) := by
  classical
  unfold hooleyPolynomialSum
  rw [mul_sum]
  apply sum_le_sum_of_injOn (fun n : ℕ => n / M)
  · intro n hn m hm heq
    change n / M = m / M at heq
    have hn' := (mem_filter.mp hn).2
    have hm' := (mem_filter.mp hm).2
    have Hn := Nat.mod_add_div n M
    have Hm := Nat.mod_add_div m M
    rw [hn', heq] at Hn
    rw [hm'] at Hm
    exact Hn.symm.trans Hm
  · apply image_subset_iff.mpr
    intro n hn
    exact quotient_mem_affine_shortInterval hM ha hx hy (mem_filter.mp hn).1 (mem_filter.mp hn).2
  · intro n hn
    have HE : (M : ℤ) * (n / M : ℕ) + a = n := by
      exact_mod_cast (show M * (n / M) + a = n by
        simpa only [(mem_filter.mp hn).2, add_comm] using Nat.mod_add_div n M)
    simpa only [HE] using hooley_affine_eval_rpow_le Q M a ((n / M : ℕ) : ℤ) ht
  · intro _ _ _
    positivity

theorem hooleyPolynomialSum_le_affine_primitive_sums (Q : ℤ[X]) {M : ℕ} (hM : 0 < M)
    {t x y : ℝ} (ht : 0 ≤ t) (hx : (M : ℝ) ≤ x) (hy : 0 ≤ y) :
    hooleyPolynomialSum Q t x y ≤ ∑ a ∈ range M,
      ((affineRestriction Q M a).content.natAbs.divisors.card : ℝ) ^ t *
        hooleyPolynomialSum (affineRestriction Q M a).primPart t ((x - a) / M) (y / M) := by
  classical
  have HE := sum_fiberwise_of_maps_to (s := shortInterval x y) (t := range M)
    (g := fun n : ℕ => n % M) (fun n _ => mem_range.mpr (Nat.mod_lt n hM))
    (fun n : ℕ => (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ t)
  change _ = hooleyPolynomialSum Q t x y at HE
  rw [← HE]
  exact sum_le_sum (fun a ha => hooleyPolynomialSum_residue_le Q hM (mem_range.mp ha) ht hx hy)

end NairTenenbaum
