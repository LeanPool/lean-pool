/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothCutoffComparison

/-! # Auxiliary series with a fractional denominator

The least common multiple of `r` coordinates is at least the `r`-th root of
their product. Dividing each auxiliary by a small positive power therefore
provides a separable majorant for the contribution of bad-prime valuations.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Auxiliary weight with a fractional-power denominator. -/
noncomputable def fractionalAuxiliary (A B ε α : ℝ) (γ n : ℕ) : ℝ :=
  auxiliary A B ε γ n / (n : ℝ) ^ α

@[simp] theorem fractionalAuxiliary_one (A B ε α : ℝ) (γ : ℕ) :
    fractionalAuxiliary A B ε α γ 1 = 1 := by simp [fractionalAuxiliary]

theorem fractionalAuxiliary_nonneg {A B ε α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (γ n : ℕ) :
    0 ≤ fractionalAuxiliary A B ε α γ n :=
  div_nonneg (auxiliary_nonneg hA hB γ n) (Real.rpow_nonneg (Nat.cast_nonneg n) α)

theorem fractionalAuxiliary_mul (A B ε α : ℝ) (γ : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    fractionalAuxiliary A B ε α γ (m * n) =
      fractionalAuxiliary A B ε α γ m * fractionalAuxiliary A B ε α γ n := by
  simp only [fractionalAuxiliary, auxiliary_mul γ hmn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_div_mul_comm]

/-- Prime-power values are bounded by a geometric series with exponent
`γ ε - α`. -/
theorem fractionalAuxiliary_prime_pow_le {A B ε α : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    fractionalAuxiliary A B ε α γ (p ^ ν) ≤ B * ((p : ℝ) ^ ((γ : ℝ) * ε - α)) ^ ν := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have H : auxiliaryLocal A B ε γ p ν ≤ B * ((p : ℝ) ^ ε) ^ (γ * ν) :=
    (auxiliaryLocal_le_geometric hA hB hε γ p ν).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_min hA (by positivity)) (min_le_right _ _) _) (zero_le_one.trans hB))
  rw [fractionalAuxiliary, auxiliary_prime_pow A B ε γ hp, Nat.cast_pow]
  calc
    _ ≤ (B * ((p : ℝ) ^ ε) ^ (γ * ν)) / ((p : ℝ) ^ ν) ^ α :=
      div_le_div_of_nonneg_right H (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hp₀, div_pow, pow_mul, Real.rpow_natCast_mul hp₀.le,
        ← Real.rpow_pow_comm hp₀.le, ← Real.rpow_pow_comm hp₀.le]
      ring

/-- A fixed negative exponent gives a uniform ratio at every prime. -/
theorem fractionalAuxiliary_prime_pow_le_uniform {A B ε α σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0)
    (γ : ℕ) (hγ : (γ : ℝ) * ε - α ≤ σ) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    fractionalAuxiliary A B ε α γ (p ^ ν) ≤ B * ((2 : ℝ) ^ σ) ^ ν := by
  refine (fractionalAuxiliary_prime_pow_le hA hB hε γ hp ν).trans ?_
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hB)
  apply pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) hγ).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) hσ.le)

theorem fractionalAuxiliary_prime_pow_summable {A B ε α σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0)
    (γ : ℕ) (hγ : (γ : ℝ) * ε - α ≤ σ) {p : ℕ} (hp : p.Prime) :
    Summable (fun ν : ℕ => fractionalAuxiliary A B ε α γ (p ^ ν)) :=
  Summable.of_nonneg_of_le
    (fun _ => fractionalAuxiliary_nonneg hA (zero_le_one.trans hB) γ _)
    (fractionalAuxiliary_prime_pow_le_uniform hA hB hε hσ γ hγ hp)
    ((summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ)).mul_left B)

theorem fractionalAuxiliary_local_tsum_le {A B ε α σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0)
    (γ : ℕ) (hγ : (γ : ℝ) * ε - α ≤ σ) {p : ℕ} (hp : p.Prime) :
    (∑' ν : ℕ, fractionalAuxiliary A B ε α γ (p ^ ν)) ≤ B / (1 - (2 : ℝ) ^ σ) := by
  have hq₀ : 0 ≤ (2 : ℝ) ^ σ := by positivity
  have hq₁ : (2 : ℝ) ^ σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ
  calc
    _ ≤ ∑' ν : ℕ, B * ((2 : ℝ) ^ σ) ^ ν :=
      Summable.tsum_le_tsum (fractionalAuxiliary_prime_pow_le_uniform hA hB hε hσ γ hγ hp)
        (fractionalAuxiliary_prime_pow_summable hA hB hε hσ γ hγ hp)
        ((summable_geometric_of_lt_one hq₀ hq₁).mul_left B)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]; rfl

theorem fractionalAuxiliary_smooth_hasSum {A B ε α σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0)
    (γ : ℕ) (hγ : (γ : ℝ) * ε - α ≤ σ) (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => fractionalAuxiliary A B ε α γ n)
      (∏ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, fractionalAuxiliary A B ε α γ (p ^ ν)) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (fractionalAuxiliary_one A B ε α γ) (fun hmn => fractionalAuxiliary_mul A B ε α γ hmn) ?_ s).2
  intro p hp
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (fractionalAuxiliary_nonneg hA (zero_le_one.trans hB) γ
      _)]
  exact fractionalAuxiliary_prime_pow_summable hA hB hε hσ γ hγ hp

/-- A coefficient-independent bound for every finite sum on fixed prime support. -/
theorem fractionalAuxiliary_sum_le {A B ε α σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0)
    (γ : ℕ) (hγ : (γ : ℝ) * ε - α ≤ σ) (s : Finset ℕ) (T : Finset ℕ+)
    (hT : ∀ n ∈ T, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ T, fractionalAuxiliary A B ε α γ n) ≤
      (B / (1 - (2 : ℝ) ^ σ)) ^ (s.filter Nat.Prime).card := by
  have H := fractionalAuxiliary_smooth_hasSum hA hB hε hσ γ hγ s
  refine ((sum_positive_factored_le_tsum
    (fractionalAuxiliary_nonneg hA (zero_le_one.trans hB) γ) s H.summable T hT).trans_eq
        H.tsum_eq).trans ?_
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · exact fun _ _ => tsum_nonneg (fun _ => fractionalAuxiliary_nonneg hA (zero_le_one.trans hB) γ _)
  · exact fun _ hp => fractionalAuxiliary_local_tsum_le hA hB hε hσ γ hγ (Finset.mem_filter.mp hp).2

end NairTenenbaum
