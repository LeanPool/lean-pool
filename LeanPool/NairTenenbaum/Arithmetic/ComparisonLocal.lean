/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.RootAuxiliary
public import Mathlib.Analysis.PSeries

/-! # A sufficient weighted local hypothesis for the comparison argument

The printed Lemma 1 is false for general multiplicative twists. This module
checks the local convergence step for twists constant on positive powers of
each prime and satisfying `|θ(p)-1| ≤ L/p`. These hypotheses cover the shape of
the totient correction used in the main proof, once its elementary estimates
are supplied. The global finite-weight comparison is still a separate step.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- The geometric estimate remains valid for every root-weighted local tail. -/
theorem rootAuxiliary_tail_le {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) (N : ℕ) :
    (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ (ν + N))) ≤
      (C : ℝ) * B * auxiliaryRatio ε γ p ^ N / (1 - auxiliaryRatio ε γ p) := by
  have hr₀ := auxiliaryRatio_nonneg ε γ p
  have hr₁ := auxiliaryRatio_lt_one hp hγε
  have hg := (summable_geometric_of_lt_one hr₀ hr₁).mul_left
    ((C : ℝ) * B * auxiliaryRatio ε γ p ^ N)
  have hf := (summable_nat_add_iff N).mpr
    (rootAuxiliary_prime_pow_summable hA hB hε γ hγε Q hp C hρ)
  calc
    _ ≤ ∑' ν : ℕ, ((C : ℝ) * B * auxiliaryRatio ε γ p ^ N) *
        auxiliaryRatio ε γ p ^ ν := by
      apply Summable.tsum_le_tsum _ hf hg
      intro ν
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
        rootAuxiliary_prime_pow_le hA hB hε γ Q hp C (ν + N) (hρ _)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
      rfl

/-- The local expression which actually occurs after splitting the divisor
convolution in the proof of Lemma 1. -/
noncomputable def localComparisonError (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X])
    (θ : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑' ν : ℕ, |θ (p ^ (ν + 1)) - θ (p ^ ν)| *
    ∑' j : ℕ, rootAuxiliary A B ε γ Q (p ^ (j + (ν + 1)))

theorem localComparisonError_nonneg {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : ℕ) (Q : ℤ[X]) (θ : ℕ → ℝ) (p : ℕ) :
    0 ≤ localComparisonError A B ε γ Q θ p :=
  tsum_nonneg (fun _ => mul_nonneg (abs_nonneg _) (tsum_nonneg
    (fun _ => rootAuxiliary_nonneg hA hB _ _ _)))

/-- For a twist constant on positive prime powers, only the first difference
contributes to the corrected weighted hypothesis. -/
theorem localComparisonError_eq (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X])
    {θ : ℕ → ℝ} (hθ₁ : θ 1 = 1) {p : ℕ}
    (hθ : ∀ ν : ℕ, θ (p ^ (ν + 1)) = θ p) :
    localComparisonError A B ε γ Q θ p =
      |θ p - 1| * ∑' j : ℕ, rootAuxiliary A B ε γ Q (p ^ (j + 1)) := by
  unfold localComparisonError
  rw [tsum_eq_single 0]
  · simp [hθ₁]
  · intro ν hν
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hν
    simp only [hθ, sub_self, abs_zero, zero_mul]

/-- A pointwise summable bound for the corrected local expression. -/
theorem localComparisonError_le {A B ε L : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hL : 0 ≤ L) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {θ : ℕ → ℝ} (hθ₁ : θ 1 = 1) {p : ℕ} (hp : p.Prime)
    (hθ : ∀ ν : ℕ, θ (p ^ (ν + 1)) = θ p) (hθp : |θ p - 1| ≤ L / p)
    (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    localComparisonError A B ε γ Q θ p ≤
      (L * C * B / (1 - auxiliaryRatio ε γ 2)) * (p : ℝ) ^ ((γ : ℝ) * ε - 2) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr : auxiliaryRatio ε γ p ≤ auxiliaryRatio ε γ 2 :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le)
      (by linarith)
  have hd : 0 < 1 - auxiliaryRatio ε γ 2 := sub_pos.mpr (auxiliaryRatio_lt_one Nat.prime_two hγε)
  rw [localComparisonError_eq A B ε γ Q hθ₁ hθ]
  calc
    _ ≤ (L / p) * ((C : ℝ) * B * auxiliaryRatio ε γ p / (1 - auxiliaryRatio ε γ p)) := by
      apply mul_le_mul hθp _ (tsum_nonneg (fun _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB)
          _ _ _))
        (by positivity)
      simpa only [pow_one] using rootAuxiliary_tail_le hA hB hε γ hγε Q hp C hρ 1
    _ ≤ (L / p) * ((C : ℝ) * B * auxiliaryRatio ε γ p / (1 - auxiliaryRatio ε γ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg C) (zero_le_one.trans hB))
          (auxiliaryRatio_nonneg ε γ p)) hd
      linarith
    _ = _ := by
      have he : (p : ℝ) ^ ((γ : ℝ) * ε - 2) = auxiliaryRatio ε γ p / p := by
        calc
          _ = (p : ℝ) ^ (((γ : ℝ) * ε - 1) - 1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_sub hp₀, Real.rpow_one]; rfl
      rw [he]
      ring

/-- The weighted local errors are summable over all primes under the explicit
stronger hypotheses; no use is made of the invalid printed Lemma 1. -/
theorem localComparisonError_summable {A B ε L : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hL : 0 ≤ L) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {θ : ℕ → ℝ} (hθ₁ : θ 1 = 1)
    (hθ : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, θ (p ^ (ν + 1)) = θ p)
    (hθp : ∀ p : ℕ, p.Prime → |θ p - 1| ≤ L / p)
    (C : ℕ) (hρ : ∀ p : ℕ, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (fun p : Nat.Primes => localComparisonError A B ε γ Q θ p) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ ((γ : ℝ) * ε - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le
    (fun p : Nat.Primes => localComparisonError_nonneg hA (zero_le_one.trans hB) γ Q θ p)
    (fun p : Nat.Primes => localComparisonError_le hA hB hε hL γ hγε Q hθ₁ p.prop
      (hθ p p.prop) (hθp p p.prop) C (hρ p p.prop))
  exact (hs.comp_injective Subtype.val_injective).mul_left _

/-- A total bound depending only on the growth parameters and the root/twist
bounds, rather than on the coefficients of the individual polynomial. -/
theorem localComparisonError_tsum_le {A B ε L : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (hL : 0 ≤ L) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {θ : ℕ → ℝ} (hθ₁ : θ 1 = 1)
    (hθ : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, θ (p ^ (ν + 1)) = θ p)
    (hθp : ∀ p : ℕ, p.Prime → |θ p - 1| ≤ L / p)
    (C : ℕ) (hρ : ∀ p : ℕ, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' p : Nat.Primes, localComparisonError A B ε γ Q θ p) ≤
      (L * C * B / (1 - auxiliaryRatio ε γ 2)) *
        ∑' n : ℕ, (n : ℝ) ^ ((γ : ℝ) * ε - 2) := by
  let K := L * C * B / (1 - auxiliaryRatio ε γ 2)
  have hK : 0 ≤ K := div_nonneg (by positivity)
    (sub_nonneg.mpr (auxiliaryRatio_lt_one Nat.prime_two hγε).le)
  have hs : Summable (fun n : ℕ => K * (n : ℝ) ^ ((γ : ℝ) * ε - 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left K
  calc
    _ ≤ ∑' p : Nat.Primes, K * (p : ℕ) ^ ((γ : ℝ) * ε - 2) := by
      apply Summable.tsum_le_tsum
        (fun p : Nat.Primes => localComparisonError_le hA hB hε hL γ hγε Q hθ₁
          p.prop (hθ p p.prop) (hθp p p.prop) C (hρ p p.prop))
        (localComparisonError_summable hA hB hε hL γ hγε Q hθ₁ hθ hθp C hρ)
      exact hs.comp_injective Subtype.val_injective
    _ ≤ ∑' n : ℕ, K * (n : ℝ) ^ ((γ : ℝ) * ε - 2) :=
      tsum_comp_le_tsum_of_inj hs (fun n => mul_nonneg hK (by positivity)) Subtype.val_injective
    _ = _ := tsum_mul_left

end NairTenenbaum
