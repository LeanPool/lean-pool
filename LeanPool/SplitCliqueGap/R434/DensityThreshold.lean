/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSDensity
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! A fixed EHPS region attains any density strictly below 7/24. -/

@[expose] public section

namespace GapExtremal.R434.EHPS

theorem density_grid_uniform {ε : ℝ} {m : ℕ} [NeZero m]
    (he : 0 < ε) (he_small : 0 ≤ 1 / 12 - 3 * ε) (hεm : 43 ≤ ε * (m : ℝ)) :
    (7/24 - 30*ε) * (m : ℝ)^2 ≤ ((gridSupport ε m).card : ℝ) := by
  have hm₀ : 0 ≤ (m : ℝ) := by positivity
  let q := m / 12
  let d := ⌈ε * (m : ℝ)⌉₊ + 20
  let p := q - 2*d
  have hqL : 12*q ≤ m := by dsimp [q]; omega
  have hqU : m ≤ 12*q+11 := by dsimp [q]; omega
  have hql : 12 * (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqL
  have hqu : (m : ℝ) ≤ 12 * (q : ℝ)+11 := by exact_mod_cast hqU
  have hd20 : 20 ≤ d := by dsimp [d]; omega
  have hdL : ε * (m : ℝ) + 20 ≤ (d : ℝ) := by
    dsimp [d]
    push_cast
    linarith only [Nat.le_ceil (ε * (m : ℝ))]
  have hdU : (d : ℝ) ≤ ε * (m : ℝ) + 21 := by
    dsimp [d]
    push_cast
    linarith only [Nat.ceil_lt_add_one (show 0 ≤ ε * (m : ℝ) by positivity)]
  have hgap : (1/12 - 3*ε) * (m : ℝ) ≤ (q : ℝ) - 2*(d : ℝ) := by
    nlinarith only [hεm,hqu,hdU]
  have hqd : 2*d ≤ q := by
    have h : 2 * (d : ℝ) ≤ (q : ℝ) := by
      linarith only [hgap,mul_nonneg he_small hm₀]
    exact_mod_cast h
  have hpL : (1/12 - 3*ε) * (m : ℝ) ≤ (p : ℝ) := by
    simpa only [p, Nat.cast_sub hqd, Nat.cast_mul, Nat.cast_ofNat] using hgap
  have hpU : (p : ℝ) ≤ (m : ℝ)/12 := by
    have h : p ≤ q := Nat.sub_le _ _
    have h' : (p : ℝ) ≤ q := by exact_mod_cast h
    linarith only [h',hql]
  have hdU' : (d : ℝ) ≤ 2*ε*(m : ℝ) := by linarith only [hdU,hεm]
  have hcount := density_grid_lower (q := q) (d := d) (p := p) (m := m)
    (by dsimp [p]; omega) hqL hqU hd20 hdL
  have hcountR : 42*(p : ℝ)^2 - (p : ℝ) - 26*(d : ℝ)*(p : ℝ) ≤
      ((gridSupport ε m).card : ℝ) := by exact_mod_cast hcount
  have hsq := pow_le_pow_left₀ (mul_nonneg he_small hm₀) hpL 2
  have hm_sq : (m : ℝ) ≤ ε * (m : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ ε * (m : ℝ) by linarith) hm₀
    nlinarith only [h]
  have hploss : (p : ℝ) ≤ ε * (m : ℝ)^2 := by linarith only [hpU,hm_sq,hm₀]
  have hdloss := mul_le_mul hdU' hpU (show 0 ≤ (p : ℝ) by positivity)
    (show 0 ≤ 2*ε*(m : ℝ) by positivity)
  nlinarith only [hcountR,hsq,hploss,hdloss,mul_nonneg (sq_nonneg ε) (sq_nonneg (m : ℝ)),
    mul_nonneg he.le (sq_nonneg (m : ℝ))]

theorem density_below_seven_twentyfour {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 7 / 24) :
    ∃ (ε : ℝ) (m₀ : ℕ), 0 < ε ∧ ε ≤ 1 ∧
      ∀ (m : ℕ) [NeZero m], m₀ ≤ m → ρ * (m : ℝ)^2 ≤ ((gridSupport ε m).card : ℝ) := by
  let ε := (7/24 - ρ) / 30
  have he : 0 < ε := by dsimp [ε]; linarith
  refine ⟨ε, ⌈43/ε⌉₊, he, by dsimp [ε]; linarith, fun m _ hm => ?_⟩
  have hm' : 43/ε ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have h := density_grid_uniform he (by dsimp [ε]; linarith)
    (m := m) (by linarith only [(div_le_iff₀ he).mp hm'])
  convert h using 1; dsimp [ε]; ring

end GapExtremal.R434.EHPS
