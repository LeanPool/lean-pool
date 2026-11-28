/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Inverse
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

/-!
# Śliwa's Lemma 6: an approximate inverse with a bounded norm

Śliwa (p. 638): let `0 < ε < 1/2`, `2 < M < ε⁻¹`, `m ≤ n` and `|y| ≤ M` with `|Pₘ y| ≥ M ε`. Then
there is `q` of degree at most `n` with `|q| ≤ ε^{-(2n)!}` and `|Pₙ (q y) - xᵐ| < ε`
(`ReadL1.lemma6`; for `y` of degree at most `n`, `ReadL1.lemma6_of_natDegree_le`).

The proof is by induction on `n`. With `τ = (ε/2)^{(2n-2)!+1}`: if `|y₀| ≥ τ`, the exact inverse
of `ReadL1.invPoly` works; if `|y₀| < τ`, apply the inductive hypothesis at `ε/2` to `y / x` and
`m - 1`.
-/

@[expose] public section

namespace ReadL1

open Polynomial

/- ### Polynomial facts -/

lemma ptrunc_ptrunc {m n : ℕ} (h : m ≤ n) (p : ℂ[X]) : ptrunc m (ptrunc n p) = ptrunc m p := by
  ext k; simp only [coeff_ptrunc]; split_ifs <;> first | rfl | omega

lemma natDegree_ptrunc_le (n : ℕ) (p : ℂ[X]) : (ptrunc n p).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_ptrunc, ite_eq_right (by exact_mod_cast not_le.2 hk)]

/-- `Pₙ (q y)` only sees `Pₙ y`. -/
lemma ptrunc_mul_ptrunc (n : ℕ) (q y : ℂ[X]) : ptrunc n (q * ptrunc n y) = ptrunc n (q * y) := by
  ext l
  rw [coeff_ptrunc, coeff_ptrunc]
  split_ifs with hl
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [coeff_ptrunc, ite_eq_left (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx; omega)]
  · rfl

lemma natDegree_divX_le_of {p : ℂ[X]} {k : ℕ} (h : p.natDegree ≤ k + 1) :
    (divX p).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hj' : k < j := by exact_mod_cast hj
  rw [coeff_divX]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma pnorm_C (c : ℂ) : pnorm (C c) = ‖c‖ := by
  rw [← monomial_zero_left, pnorm_monomial]

/-- `P₁ (y₁⁻¹ y) - x = y₁⁻¹ y₀`. -/
lemma ptrunc_one_C_inv_mul {y : ℂ[X]} (hb : y.coeff 1 ≠ 0) :
    ptrunc 1 (C (y.coeff 1)⁻¹ * y) - X ^ 1 = C ((y.coeff 1)⁻¹ * y.coeff 0) := by
  ext k
  rcases k with _ | _ | k
  · simp [coeff_ptrunc, coeff_C]
  · simp [coeff_ptrunc, coeff_C_mul, inv_mul_cancel₀ hb]
  · simp [coeff_ptrunc, coeff_X]

/- ### The numerical bounds -/

lemma two_lt_inv {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) : 2 < ε⁻¹ := by
  rw [lt_inv_comm₀ (by norm_num) hε]; linarith

lemma inv_half_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) : (ε / 2)⁻¹ ≤ ε⁻¹ ^ 2 := by
  have h := two_lt_inv hε hε2
  rw [inv_div, div_eq_mul_inv, sq]
  exact mul_le_mul_of_nonneg_right h.le (by positivity)

lemma factorial_two_mul_succ (k : ℕ) :
    (2 * (k + 1)).factorial = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]

lemma two_mul_factorial_le (k : ℕ) : 2 * (2 * k).factorial ≤ (2 * (k + 1)).factorial := by
  rw [factorial_two_mul_succ]
  calc 2 * (2 * k).factorial ≤ ((2 * k + 2) * (2 * k + 1)) * (2 * k).factorial :=
        Nat.mul_le_mul_right _ (by nlinarith)
    _ = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := by ring

/-- The exponent count of the second case. -/
lemma exponent_le (k : ℕ) (hk : 1 ≤ k) :
    (k + 1) + ((2 * ((2 * k).factorial + 1) + 1) * (k + 1) + 2 * ((2 * k).factorial + 1)) ≤
      (2 * (k + 1)).factorial := by
  have hF : 2 ≤ (2 * k).factorial := by
    simpa using Nat.factorial_le (show 2 ≤ 2 * k by omega)
  rw [factorial_two_mul_succ]
  set F := (2 * k).factorial
  have h1 : 1 * (k * F) ≤ k * (k * F) := Nat.mul_le_mul_right _ hk
  have h2 : 1 * F ≤ k * F := Nat.mul_le_mul_right F hk
  have h3 : k * 2 ≤ k * F := Nat.mul_le_mul_left k hF
  nlinarith

/-- `|q| ≤ (n + 1) (M/τ)ⁿ / τ` for the exact inverse when `|y₀| ≥ τ`. -/
lemma pnorm_invPoly_le_of {y : ℂ[X]} {M τ : ℝ} (hτ : 0 < τ) (hy0 : τ ≤ ‖y.coeff 0‖)
    (hM : pnorm y ≤ M) {m n : ℕ} (hmn : m ≤ n) :
    pnorm (invPoly y m n) ≤ ((n + 1 : ℕ) : ℝ) * ((M / τ) ^ n / τ) := by
  have hy0' : 0 < ‖y.coeff 0‖ := hτ.trans_le hy0
  have hy0M : ‖y.coeff 0‖ ≤ M := (sum_norm_coeff_le_pnorm y {0}).trans hM |>.trans_eq' (by simp)
  have hr : 1 ≤ M / ‖y.coeff 0‖ := (one_le_div hy0').2 hy0M
  have hM0 : 0 ≤ M := (pnorm_nonneg y).trans hM
  refine (pnorm_invPoly_le hy0' hM hmn).trans ?_
  have hc : ((n - m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hpow : (M / ‖y.coeff 0‖) ^ (n - m) ≤ (M / τ) ^ n :=
    (pow_le_pow_right₀ hr (Nat.sub_le n m)).trans
      (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hM0 hτ hy0) n)
  have hdiv : (M / ‖y.coeff 0‖) ^ (n - m) / ‖y.coeff 0‖ ≤ (M / τ) ^ n / τ :=
    div_le_div₀ (by positivity) hpow hτ hy0
  exact mul_le_mul hc hdiv (by positivity) (by positivity)

/-- The second case's norm count: `(k + 2) (M/τ)^{k+1} / τ ≤ ε^{-(2k+2)!}`. -/
lemma case2_bound {ε M : ℝ} {k : ℕ} (hk : 1 ≤ k) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hM0 : 0 ≤ M)
    (hME : M < ε⁻¹) :
    ((k + 1 + 1 : ℕ) : ℝ) * ((M / (ε / 2) ^ ((2 * k).factorial + 1)) ^ (k + 1) /
      (ε / 2) ^ ((2 * k).factorial + 1)) ≤ ε⁻¹ ^ (2 * (k + 1)).factorial := by
  set F := (2 * k).factorial
  set E := ε⁻¹ with hE
  have hE2 : 2 < E := two_lt_inv hε hε2
  have hE1 : 1 ≤ E := by linarith
  set τ := (ε / 2) ^ (F + 1)
  have hτ0 : 0 < τ := by positivity
  have hτinv : τ⁻¹ ≤ E ^ (2 * (F + 1)) := by
    rw [← inv_pow, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (inv_half_le hε hε2) _
  have hc : ((k + 1 + 1 : ℕ) : ℝ) ≤ E ^ (k + 1) := by
    have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast Nat.lt_two_pow_self
    exact h2.trans (pow_le_pow_left₀ (by norm_num) hE2.le _)
  have hMτ : M * τ⁻¹ ≤ E * E ^ (2 * (F + 1)) :=
    mul_le_mul hME.le hτinv (by positivity) (by positivity)
  calc ((k + 1 + 1 : ℕ) : ℝ) * ((M / τ) ^ (k + 1) / τ)
      = ((k + 1 + 1 : ℕ) : ℝ) * ((M * τ⁻¹) ^ (k + 1) * τ⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
    _ ≤ E ^ (k + 1) * ((E * E ^ (2 * (F + 1))) ^ (k + 1) * E ^ (2 * (F + 1))) := by
        refine mul_le_mul hc (mul_le_mul (pow_le_pow_left₀ (by positivity) hMτ _) hτinv
          (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = E ^ ((k + 1) + ((2 * (F + 1) + 1) * (k + 1) + 2 * (F + 1))) := by
        rw [← pow_succ', ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ E ^ (2 * (k + 1)).factorial := pow_le_pow_right₀ hE1 (exponent_le k hk)

/- ### The lemma -/

/-- The case `n = 1`. -/
lemma lemma6_one {m : ℕ} (hm : m ≤ 1) {ε M : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hM2 : 2 < M)
    (hME : M < ε⁻¹) {y : ℂ[X]} (hyM : pnorm y ≤ M) (hPm : M * ε ≤ pnorm (ptrunc m y)) :
    ∃ q : ℂ[X], q.natDegree ≤ 1 ∧ pnorm q ≤ ε⁻¹ ^ 2 ∧ pnorm (ptrunc 1 (q * y) - X ^ m) < ε := by
  have hMε : 0 < M * ε := by positivity
  interval_cases m
  · -- `|y₀| ≥ M ε`: the exact inverse.
    rw [pnorm_ptrunc_zero] at hPm
    have hy0 : y.coeff 0 ≠ 0 := norm_pos_iff.1 (hMε.trans_le hPm)
    refine ⟨invPoly y 0 1, natDegree_invPoly_le _ _ _, ?_, ?_⟩
    · refine (pnorm_invPoly_le_of hMε hPm hyM (Nat.zero_le 1)).trans ?_
      have hM0 : M ≠ 0 := by positivity
      have hε0 : ε ≠ 0 := hε.ne'
      have : 2 / M ≤ 1 := (div_le_one (by positivity)).2 hM2.le
      calc _ = 2 / M * ε⁻¹ ^ 2 := by push_cast; field_simp
        _ ≤ 1 * ε⁻¹ ^ 2 := by gcongr
        _ = ε⁻¹ ^ 2 := one_mul _
    · rw [ptrunc_invPoly_mul hy0 (Nat.zero_le 1), sub_self, pnorm_zero]; exact hε
  · rw [pnorm_ptrunc_succ, pnorm_ptrunc_zero, coeff_divX] at hPm
    by_cases h0 : ε ^ 2 ≤ ‖y.coeff 0‖
    · -- `|y₀| ≥ ε²`: `q = y₀⁻¹ x`.
      have hy0' : 0 < ‖y.coeff 0‖ := (by positivity : (0 : ℝ) < ε ^ 2).trans_le h0
      have hy0 : y.coeff 0 ≠ 0 := norm_pos_iff.1 hy0'
      refine ⟨invPoly y 1 1, natDegree_invPoly_le _ _ _, ?_, ?_⟩
      · have hq := pnorm_invPoly_le hy0' hyM (le_refl 1)
        simp only [Nat.sub_self, zero_add, Nat.cast_one, one_mul, pow_zero, one_div] at hq
        refine hq.trans ?_
        rw [inv_pow]
        exact inv_anti₀ (by positivity) h0
      · rw [ptrunc_invPoly_mul hy0 (le_refl 1), sub_self, pnorm_zero]; exact hε
    · -- `|y₀| < ε²`, so `|y₁| > ε`: `q = y₁⁻¹`.
      push Not at h0
      have hε1 : ε ^ 2 < ε := by nlinarith
      have h2ε : 2 * ε < M * ε := by nlinarith
      have hy1 : ε < ‖y.coeff (0 + 1)‖ := by linarith
      have hy1' : 0 < ‖y.coeff 1‖ := hε.trans hy1
      have hb : y.coeff 1 ≠ 0 := norm_pos_iff.1 hy1'
      refine ⟨C (y.coeff 1)⁻¹, by rw [natDegree_C]; omega, ?_, ?_⟩
      · rw [pnorm_C, norm_inv]
        have h1 : ‖y.coeff 1‖⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hy1.le
        have h2 : ε⁻¹ ≤ ε⁻¹ ^ 2 := by
          have := two_lt_inv hε hε2
          nlinarith
        exact h1.trans h2
      · rw [ptrunc_one_C_inv_mul hb, pnorm_C, norm_mul, norm_inv, inv_mul_lt_iff₀ hy1']
        nlinarith [mul_lt_mul_of_pos_left hy1 hε]

/-- **Śliwa's Lemma 6**, for `y` of degree at most `n`. -/
theorem lemma6_of_natDegree_le : ∀ n : ℕ, 1 ≤ n → ∀ m ≤ n, ∀ ε M : ℝ, 0 < ε → ε < 1 / 2 →
    2 < M → M < ε⁻¹ → ∀ y : ℂ[X], y.natDegree ≤ n → pnorm y ≤ M → M * ε ≤ pnorm (ptrunc m y) →
    ∃ q : ℂ[X], q.natDegree ≤ n ∧ pnorm q ≤ ε⁻¹ ^ (2 * n).factorial ∧
      pnorm (ptrunc n (q * y) - X ^ m) < ε := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro m hm ε M hε hε2 hM2 hME y _ hyM hPm
    rw [show Nat.factorial (2 * 1) = 2 by decide]
    exact lemma6_one hm hε hε2 hM2 hME hyM hPm
  | succ k hk ih =>
    intro m hm ε M hε hε2 hM2 hME y hy hyM hPm
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (ε / 2) ^ ((2 * k).factorial + 1) := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by rw [hτ]; positivity
    have hτε : τ ≤ ε / 2 := by
      rw [hτ]
      exact pow_le_of_le_one (by positivity) (by linarith) (by omega)
    have h2ε : 2 * ε < M * ε := by nlinarith
    by_cases hy0 : τ ≤ ‖y.coeff 0‖
    · -- `|y₀| ≥ τ`: the exact inverse.
      have hy0' : y.coeff 0 ≠ 0 := norm_pos_iff.1 (hτ0.trans_le hy0)
      refine ⟨invPoly y m (k + 1), natDegree_invPoly_le _ _ _, ?_, ?_⟩
      · refine (pnorm_invPoly_le_of hτ0 hy0 hyM hm).trans ?_
        rw [hτ]
        exact case2_bound hk hε hε2 (by linarith) hME
      · rw [ptrunc_invPoly_mul hy0' hm, sub_self, pnorm_zero]; exact hε
    · -- `|y₀| < τ`: apply the inductive hypothesis to `y / x`.
      push Not at hy0
      rcases m with _ | m
      · rw [pnorm_ptrunc_zero] at hPm
        linarith
      rw [pnorm_ptrunc_succ] at hPm
      have hME' : M < (ε / 2)⁻¹ := by
        rw [inv_div]
        have : ε⁻¹ ≤ 2 / ε := by rw [div_eq_mul_inv]; linarith [inv_pos.2 hε]
        linarith
      have hPm' : M * (ε / 2) ≤ pnorm (ptrunc m (divX y)) := by
        have : M * (ε / 2) = M * ε / 2 := by ring
        linarith
      obtain ⟨q, hqd, hqn, hqe⟩ := ih m (by omega) (ε / 2) M (by positivity) (by linarith) hM2
        hME' (divX y) (natDegree_divX_le_of hy) ((pnorm_divX_le y).trans hyM) hPm'
      refine ⟨q, hqd.trans (by omega), ?_, ?_⟩
      · -- `|q| ≤ (2/ε)^{(2k)!} ≤ ε^{-2 (2k)!}`.
        refine hqn.trans ?_
        calc (ε / 2)⁻¹ ^ (2 * k).factorial ≤ (ε⁻¹ ^ 2) ^ (2 * k).factorial :=
              pow_le_pow_left₀ (by positivity) (inv_half_le hε hε2) _
          _ = ε⁻¹ ^ (2 * (2 * k).factorial) := by rw [← pow_mul]
          _ ≤ ε⁻¹ ^ (2 * (k + 1)).factorial :=
              pow_le_pow_right₀ (by linarith [two_lt_inv hε hε2]) (two_mul_factorial_le k)
      · -- `Pₖ₊₁ (q y) - x^{m+1} = x (Pₖ (q (y/x)) - xᵐ) + y₀ Pₖ₊₁ q`.
        have hdec : y = X * divX y + C (y.coeff 0) := by
          conv_lhs => rw [← divX_mul_X_add y]
          ring
        have key : ptrunc (k + 1) (q * y) - X ^ (m + 1) =
            X * (ptrunc k (q * divX y) - X ^ m) + C (y.coeff 0) * ptrunc (k + 1) q := by
          conv_lhs => rw [hdec]
          rw [mul_add, ptrunc_add, show q * (X * divX y) = X * (q * divX y) by ring,
            ← X_mul_ptrunc, show q * C (y.coeff 0) = C (y.coeff 0) * q by ring, ptrunc_C_mul]
          ring
        rw [key]
        have h2 : ‖y.coeff 0‖ * pnorm (ptrunc (k + 1) q) ≤ τ * (ε / 2)⁻¹ ^ (2 * k).factorial :=
          mul_le_mul hy0.le ((pnorm_ptrunc_le _ _).trans hqn) (pnorm_nonneg _) hτ0.le
        have h3 : τ * (ε / 2)⁻¹ ^ (2 * k).factorial = ε / 2 := by
          rw [hτ, inv_pow, pow_succ]
          field_simp
        calc pnorm (X * (ptrunc k (q * divX y) - X ^ m) + C (y.coeff 0) * ptrunc (k + 1) q)
            ≤ pnorm (X * (ptrunc k (q * divX y) - X ^ m)) +
                pnorm (C (y.coeff 0) * ptrunc (k + 1) q) := pnorm_add_le _ _
          _ = pnorm (ptrunc k (q * divX y) - X ^ m) +
                ‖y.coeff 0‖ * pnorm (ptrunc (k + 1) q) := by rw [pnorm_X_mul, pnorm_C_mul]
          _ < ε := by linarith

/-- **Śliwa's Lemma 6**, with his remark (p. 639): any `y`, since `Pₙ (q y) = Pₙ (q Pₙ y)`. -/
theorem lemma6 {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm : m ≤ n) {ε M : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (hM2 : 2 < M) (hME : M < ε⁻¹) {y : ℂ[X]} (hyM : pnorm y ≤ M)
    (hPm : M * ε ≤ pnorm (ptrunc m y)) :
    ∃ q : ℂ[X], q.natDegree ≤ n ∧ pnorm q ≤ ε⁻¹ ^ (2 * n).factorial ∧
      pnorm (ptrunc n (q * y) - X ^ m) < ε := by
  obtain ⟨q, hqd, hqn, hqe⟩ := lemma6_of_natDegree_le n hn m hm ε M hε hε2 hM2 hME (ptrunc n y)
    (natDegree_ptrunc_le n y) ((pnorm_ptrunc_le n y).trans hyM) (by rwa [ptrunc_ptrunc hm])
  exact ⟨q, hqd, hqn, by rwa [ptrunc_mul_ptrunc] at hqe⟩

end ReadL1
