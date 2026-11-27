/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Actual complex derivative bounds on successively smaller balls

Repeated Banach-space Schwarz estimates give bounds for the actual
iterated Fréchet derivatives. Analyticity and a function supremum on
the larger ball are the only inputs; no derivative estimate is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem norm_iteratedFDeriv_le_shrinking_ball {f : E → F} {c : E} {R r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball c R))
    (hbound : ∀ x ∈ ball c R, ‖f x‖ ≤ M) (n : ℕ) :
    ∀ x ∈ ball c (R - (n : ℝ) * r), ‖iteratedFDeriv ℂ n f x‖ ≤ M * (2 / r) ^ n := by
  induction n with
  | zero =>
    intro x hx
    simpa only [Nat.cast_zero, zero_mul, sub_zero, norm_iteratedFDeriv_zero,
      pow_zero, mul_one] using hbound x (by simpa using hx)
  | succ n ih =>
    intro x hx
    have hx' : dist x c < R - ((n : ℝ) + 1) * r := by
      simpa only [mem_ball, Nat.cast_add, Nat.cast_one] using hx
    have hnr : 0 ≤ (n : ℝ) * r := mul_nonneg (Nat.cast_nonneg _) hr.le
    have hinner : ball x r ⊆ ball c (R - (n : ℝ) * r) := by
      intro y hy
      rw [mem_ball] at hy ⊢
      have ht := dist_triangle y x c
      linarith
    have houter : ball c (R - (n : ℝ) * r) ⊆ ball c R := by
      intro y hy
      rw [mem_ball] at hy ⊢
      linarith
    have hxinner : x ∈ ball c (R - (n : ℝ) * r) := by
      rw [mem_ball]
      linarith
    have hC : 0 ≤ M * (2 / r) ^ n := by positivity
    have hg : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) (ball x r) :=
      ((hf.iteratedFDeriv n).mono (hinner.trans houter)).differentiableOn
    have hmaps : MapsTo (iteratedFDeriv ℂ n f) (ball x r)
        (closedBall (iteratedFDeriv ℂ n f x) (2 * (M * (2 / r) ^ n))) := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [ih y (hinner hy), ih x hxinner])
    have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hg hmaps hr
    rw [norm_fderiv_iteratedFDeriv] at h
    apply h.trans_eq
    rw [pow_succ]
    ring

/-- Derivatives through order four at the center need only a radius-one
complex neighborhood. The common constant is 10000. -/
theorem norm_iteratedFDeriv_le_four {f : E → F} {c : E} {M : ℝ}
    (hM : 0 ≤ M) (hf : AnalyticOnNhd ℂ f (ball c 1))
    (hbound : ∀ x ∈ ball c 1, ‖f x‖ ≤ M) {n : ℕ} (hn : n ≤ 4) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ 10000 * M := by
  have hnreal : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have h := norm_iteratedFDeriv_le_shrinking_ball (r := 1 / 5)
    (by norm_num) hM hf hbound n c (by
      rw [mem_ball, dist_self]
      nlinarith)
  norm_num only [show (2 : ℝ) / (1 / 5) = 10 by norm_num] at h
  have hp : (10 : ℝ) ^ n ≤ 10000 := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) hn
    norm_num at hpow ⊢
    exact hpow
  exact h.trans (by nlinarith)

end VacuumBellSeparation
