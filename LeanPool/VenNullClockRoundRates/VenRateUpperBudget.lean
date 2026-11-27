/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Factorial error and the exponential profile budget
-/

@[expose] public section

open Filter

namespace VenRateUpper

private theorem factorial_log_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log (Nat.factorial (n + 1) : ℝ) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hnFactorial : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hTerm := Real.pow_div_factorial_le_exp (n : ℝ) hnReal.le n
  have hLog := (Real.log_le_iff_le_exp (div_pos (pow_pos hnReal n) hnFactorial)).2 hTerm
  rw [Real.log_div (pow_pos hnReal n).ne' hnFactorial.ne', Real.log_pow] at hLog
  have hFactorial : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  exact (by linarith : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤
    Real.log (Nat.factorial n : ℝ)).trans (Real.log_le_log hnFactorial hFactorial)

/-- A single natural degree meets a fixed geometric budget and gives the
factorial error at most `exp (-c * log M * log (log M))` for every large budget. -/
theorem exists_factorial_budget {C B : ℝ} (hC : 0 < C) (hB : 1 < B) :
    ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁, ∃ n : ℕ, 1 ≤ n ∧
      C * B ^ n ≤ M ∧ C * B ^ n / (Nat.factorial (n + 1) : ℝ) ≤
        Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
  let L := 2 * (Real.log B + 1)
  let D := Real.log B + 1 + max 0 (Real.log C)
  have hLogB := Real.log_pos hB
  have hBPos : 0 < B := zero_lt_one.trans hB
  have hL : 0 < L := by dsimp [L]; linarith
  have hD : 0 < D := by
    dsimp [D]
    linarith [le_max_left (0 : ℝ) (Real.log C)]
  let c := ((2 * L)⁻¹) / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hLarge₁ : ∀ᶠ M : ℝ in atTop, max (2 * L) (2 * Real.log C) ≤ Real.log M :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hLarge₂ : ∀ᶠ M : ℝ in atTop,
      max (2 * Real.log (2 * L)) (4 * D) ≤ Real.log (Real.log M) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _
  have hResult : ∀ᶠ M : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧ C * B ^ n ≤ M ∧
      C * B ^ n / (Nat.factorial (n + 1) : ℝ) ≤
        Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
    filter_upwards [hLarge₁, hLarge₂, eventually_ge_atTop (2 : ℝ)] with M h₁ h₂ hM
    let x := Real.log M
    let y := Real.log x
    have hxL : 2 * L ≤ x := (le_max_left _ _).trans h₁
    have hxC : 2 * Real.log C ≤ x := (le_max_right _ _).trans h₁
    have hyL : 2 * Real.log (2 * L) ≤ y := (le_max_left _ _).trans h₂
    have hyD : 4 * D ≤ y := (le_max_right _ _).trans h₂
    have hx : 0 < x := by linarith
    have hy : 0 ≤ y := by linarith
    let n := ⌊x / L⌋₊
    have hnUpper : (n : ℝ) ≤ x / L := Nat.floor_le (div_nonneg hx.le hL.le)
    have hnFloor : x / L < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hxDiv : 2 ≤ x / L := (le_div_iff₀ hL).2 hxL
    have hnOne : 1 ≤ n := by
      have : (1 : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hnOne)
    have hnHalf : x / (2 * L) ≤ (n : ℝ) := by
      rw [show x / (2 * L) = (x / L) / 2 by rw [div_div, mul_comm L 2]]
      linarith
    have hTwoL : 0 < 2 * L := mul_pos (by positivity) hL
    have hHalfPos : 0 < x / (2 * L) := div_pos hx hTwoL
    have hnLog := Real.log_le_log hHalfPos hnHalf
    rw [Real.log_div hx.ne' hTwoL.ne'] at hnLog
    have hnLogHalf : y / 2 ≤ Real.log (n : ℝ) := by
      linarith [show y - Real.log (2 * L) ≤ Real.log (n : ℝ) from hnLog]
    have hPowPos : 0 < B ^ n := pow_pos hBPos n
    have hLogNumerator : Real.log (C * B ^ n) = Real.log C + (n : ℝ) * Real.log B := by
      rw [Real.log_mul hC.ne' hPowPos.ne', Real.log_pow]
    refine ⟨n, hnOne, ?_, ?_⟩
    · have hUpperMul : (n : ℝ) * L ≤ x := (le_div_iff₀ hL).1 hnUpper
      have hLogBLe : Real.log B ≤ L / 2 := by dsimp [L]; linarith
      have hNumLog : Real.log (C * B ^ n) ≤ x := by
        rw [hLogNumerator]
        linarith [mul_le_mul_of_nonneg_left hLogBLe hnPos.le]
      exact (Real.log_le_log_iff (mul_pos hC hPowPos) (by linarith : 0 < M)).1 hNumLog
    · have hLogC : Real.log C ≤ (n : ℝ) * max 0 (Real.log C) := by
        have hnOneReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
        exact (le_max_right _ _).trans (le_mul_of_one_le_left (le_max_left _ _) hnOneReal)
      have hFactPos : 0 < (Nat.factorial (n + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (n + 1)
      apply (Real.log_le_iff_le_exp (div_pos (mul_pos hC hPowPos) hFactPos)).1
      rw [Real.log_div (mul_pos hC hPowPos).ne' hFactPos.ne', hLogNumerator]
      change Real.log C + (n : ℝ) * Real.log B - Real.log (Nat.factorial (n + 1) : ℝ) ≤
        -c * x * y
      calc
        _ ≤ (n : ℝ) * D - (n : ℝ) * Real.log (n : ℝ) := by
          dsimp [D]
          linarith [factorial_log_lower n hnOne]
        _ ≤ -((n : ℝ) * y) / 4 := by
          have hDTerm := mul_le_mul_of_nonneg_left (show D ≤ y / 4 by linarith) hnPos.le
          have hLogTerm := mul_le_mul_of_nonneg_left hnLogHalf hnPos.le
          linarith
        _ ≤ -(x / (2 * L) * y) / 4 := by
          linarith [mul_le_mul_of_nonneg_right hnHalf hy]
        _ = _ := by dsimp [c]; simp only [div_eq_mul_inv]; ring
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hResult
  refine ⟨c, max M₀ 2, hc, (by linarith : (1 : ℝ) < 2).trans_le (le_max_right _ _), ?_⟩
  intro M hM
  exact hM₀ M ((le_max_left _ _).trans hM)

/-- Budget conversion in the form of C196 v0.3, Eqs. (45) and (48).
The fixed constant `K` can include the sup norm of the signed kernel and `exp a`. -/
theorem exists_factorial_budget_with_kernel {A a K : ℝ} (hA : 1 < A) (ha : 0 ≤ a)
    (hK : 0 ≤ K) :
    ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁, ∃ n : ℕ, 1 ≤ n ∧ A ^ (n + 1) ≤ M ∧
      K * A ^ (n + 1) * a ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) ≤
        Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
  let B := A * max 1 a
  let C := max 1 K * B
  have hAPos : 0 < A := zero_lt_one.trans hA
  have hAB : A ≤ B := le_mul_of_one_le_right hAPos.le (le_max_left _ _)
  have hB : 1 < B := hA.trans_le hAB
  have hBPos : 0 < B := zero_lt_one.trans hB
  have hMaxK : 0 < max 1 K := zero_lt_one.trans_le (le_max_left _ _)
  have hC : 0 < C := mul_pos hMaxK hBPos
  obtain ⟨c, M₁, hc, hM₁, hBudget⟩ := exists_factorial_budget hC hB
  refine ⟨c, M₁, hc, hM₁, ?_⟩
  intro M hM
  obtain ⟨n, hn, hCost, hTail⟩ := hBudget M hM
  have hAbsorb : max 1 K * B ^ (n + 1) = C * B ^ n := by
    dsimp [C]
    rw [pow_succ']
    ring
  have hCostBase : A ^ (n + 1) ≤ B ^ (n + 1) := pow_le_pow_left₀ hAPos.le hAB _
  refine ⟨n, hn, ?_, ?_⟩
  · calc
      _ ≤ B ^ (n + 1) := hCostBase
      _ ≤ max 1 K * B ^ (n + 1) := le_mul_of_one_le_left (by positivity) (le_max_left _ _)
      _ = C * B ^ n := hAbsorb
      _ ≤ M := hCost
  · have hNumerator : K * A ^ (n + 1) * a ^ (n + 1) ≤ C * B ^ n := by
      calc
        _ ≤ max 1 K * A ^ (n + 1) * (max 1 a) ^ (n + 1) := by
          have hK' := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) K)
            (pow_nonneg hAPos.le (n + 1))
          have ha' := pow_le_pow_left₀ ha (le_max_right (1 : ℝ) a) (n + 1)
          exact (mul_le_mul_of_nonneg_left ha' (mul_nonneg hK (pow_nonneg hAPos.le _))).trans
            (mul_le_mul_of_nonneg_right hK' (by positivity))
        _ = max 1 K * B ^ (n + 1) := by dsimp [B]; rw [mul_pow, mul_assoc]
        _ = C * B ^ n := hAbsorb
    exact (div_le_div_of_nonneg_right hNumerator (by positivity)).trans hTail

end VenRateUpper
