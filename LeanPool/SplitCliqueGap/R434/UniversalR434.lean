/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.DensityThreshold
public import LeanPool.SplitCliqueGap.R434.UniformOrder
public import LeanPool.SplitCliqueGap.R434.FiniteR434
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! R434 for every sufficiently large graph order, with no external hypotheses. -/

@[expose] public section

namespace GapExtremal.R434

open Real EHPS

theorem universal_R434 (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
          (n : ℝ)^2 * exp (-(2 * sqrt (log (24/7)) + η) * sqrt (log n)) ≤ gap G := by
  let a := sqrt (log (24/7))
  have ha : 0 ≤ a := sqrt_nonneg _
  have ha2 : a^2 = log (24/7) := sq_sqrt (log_nonneg (by norm_num))
  let c := (a + η/4)^2
  have hc : 0 < c := sq_pos_of_pos (by linarith)
  have hc' : log (24/7) < c := by
    dsimp [c]
    nlinarith only [ha,ha2,hη,mul_nonneg ha hη.le,sq_pos_of_pos hη]
  have hcoeff : 2 * sqrt c + η/2 = 2 * a + η := by
    simp only [c, sqrt_sq (show 0 ≤ a + η/4 by linarith)]
    ring
  let ρ := exp (-c)
  have hρ₀ : 0 < ρ := exp_pos _
  have hρ₁ : ρ < 7/24 := by
    have h : ρ < exp (-log (24/7)) := exp_lt_exp.mpr (by linarith only [hc'])
    rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 24/7)] at h
    norm_num at h ⊢
    exact h
  obtain ⟨ε,m₀,hε,hε₁,hdensity⟩ := density_below_seven_twentyfour hρ₀ hρ₁
  have hH (j : ℕ) (hj : 1 ≤ j) : 1 ≤ hostFactor j ∧ (hostFactor j : ℝ) ≤ 1050015*(j : ℝ) := by
    constructor
    · unfold hostFactor
      omega
    · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      unfold hostFactor
      push_cast
      linarith
  obtain ⟨N,hN⟩ := uniform_order_parameters hostFactor 1050015 (200/ε^2) c (η/2)
    (by norm_num) (by positivity) hc (by positivity) m₀ hH
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨m,j,hmpos,hm₀,hmOdd,_,horder,hsize⟩ := hN n hn
  let : NeZero m := ⟨by omega⟩
  have horder' : hostFactor j * (m^2)^j ≤ n := by simpa only [pow_mul] using horder
  obtain ⟨V,fV,dV,G,hcard,hsplit,hconn,hgap⟩ :=
    finite_gap_of_product hε hε₁ hmOdd horder'
  refine ⟨V,fV,dV,G,hcard,hsplit,hconn,?_⟩
  rw [hcoeff] at hsize
  refine hsize.trans (le_trans ?_ hgap)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hden := hdensity m hm₀
  have hpw := pow_le_pow_left₀ (mul_nonneg hρ₀.le (sq_nonneg (m : ℝ))) hden j
  have hprod := mul_le_mul_of_nonneg_right hpw
    (show 0 ≤ ((m : ℝ)^2)^j by positivity)
  have hre : (ρ * (m : ℝ)^2)^j * ((m : ℝ)^2)^j =
      exp (-c * (j : ℝ)) * (m : ℝ)^(4*j) := by
    rw [mul_pow, show ρ^j = exp (-c * (j : ℝ)) by
      change exp (-c) ^ j = _
      rw [← exp_nat_mul, mul_comm (j : ℝ) (-c)]]
    rw [mul_assoc, ← pow_add, ← pow_mul]
    congr 2
    omega
  rw [hre] at hprod
  exact hprod

end GapExtremal.R434
