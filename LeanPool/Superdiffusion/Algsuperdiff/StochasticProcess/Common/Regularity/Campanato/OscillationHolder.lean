/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# OscillationHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Convex chaining and continuity from a Hölder bound

A local two-point Hölder estimate globalizes across a convex set by subdividing
each segment. This file also records the elementary ball geometry and the
continuity consequence of a positive Hölder exponent.

## Main results

* `holderSeminormBoundOn_of_local_of_convex` — convex chaining, at the sharp
  price `N ^ (1 - α)` for `N` steps.
* `norm_sub_le_two_mul_of_mem_ball` — the diameter bound for a sup-ball.
* `continuousOn_of_holderBound` — a Hölder modulus is a modulus of continuity,
  for every positive exponent.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open HCPolySupport Topology
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Convex chaining -/

private theorem segment_point_mem {W : Set (Vec d)} (hW : Convex ℝ W) {x y : Vec d}
    (hx : x ∈ W) (hy : y ∈ W) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ W := by
  have hid : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hid]
  exact hW hx hy (by linarith only [ht1]) ht0 (by ring)

private theorem segment_step_norm (x y : Vec d) (N k : ℕ) :
    ‖(x + ((k : ℝ) / N) • (y - x)) - (x + (((k : ℕ) + 1 : ℝ) / N) • (y - x))‖ =
      ‖x - y‖ / (N : ℝ) := by
  have hid : (x + ((k : ℝ) / N) • (y - x)) - (x + (((k : ℕ) + 1 : ℝ) / N) • (y - x)) =
      ((k : ℝ) / N - ((k : ℝ) + 1) / N) • (y - x) := by
    rw [sub_smul]
    abel
  rw [hid, norm_smul]
  have hcoef : (k : ℝ) / N - ((k : ℝ) + 1) / N = -(1 / (N : ℝ)) := by ring
  rw [hcoef, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)), norm_sub_rev]
  ring

/-- **Convex chaining.**  A Hölder bound valid for separations at most `ell`
globalizes to a convex set of diameter at most `N * ell`, at the price
`N ^ (1 - α)`. -/
theorem holderSeminormBoundOn_of_local_of_convex
    {W : Set (Vec d)} {alpha L ell : ℝ} {N : ℕ} {G : Vec d → ℝ}
    (hW : Convex ℝ W) (hN : 0 < N)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ (N : ℝ) * ell)
    (hloc : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ ell → |G x - G y| ≤ L * ‖x - y‖ ^ alpha) :
    HolderSeminormBoundOn W alpha ((N : ℝ) ^ (1 - alpha) * L) G := by
  intro x hx y hy
  rw [Real.norm_eq_abs]
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  set p : ℕ → Vec d := fun k => x + ((k : ℝ) / N) • (y - x) with hp
  have hmem : ∀ k : ℕ, k ≤ N → p k ∈ W := by
    intro k hk
    refine segment_point_mem hW hx hy (by positivity) ?_
    rw [div_le_one hNreal]
    exact_mod_cast hk
  have hstepR : ‖x - y‖ / (N : ℝ) ≤ ell :=
    (div_le_iff₀ hNreal).2 (by simpa only [mul_comm] using hdiam x hx y hy)
  have hstep : ∀ k : ℕ, k + 1 ≤ N →
      |G (p k) - G (p (k + 1))| ≤ L * (‖x - y‖ / (N : ℝ)) ^ alpha := by
    intro k hk
    have hnorm : ‖p k - p (k + 1)‖ = ‖x - y‖ / (N : ℝ) := by
      simpa only [hp, Nat.cast_add, Nat.cast_one] using segment_step_norm x y N k
    have h := hloc (p k) (hmem k (Nat.le_of_succ_le hk)) (p (k + 1)) (hmem (k + 1) hk)
      (by rw [hnorm]; exact hstepR)
    rwa [hnorm] at h
  have hind : ∀ k : ℕ, k ≤ N →
      |G x - G (p k)| ≤ (k : ℝ) * (L * (‖x - y‖ / (N : ℝ)) ^ alpha) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [hp, Nat.cast_zero, zero_div, zero_smul, add_zero, sub_self,
          abs_zero, Nat.cast_zero, zero_mul]
        exact le_rfl
    | succ k ih =>
        intro hk
        have htri : |G x - G (p (k + 1))| ≤
            |G x - G (p k)| + |G (p k) - G (p (k + 1))| := by
          have hid : G x - G (p (k + 1)) =
              (G x - G (p k)) + (G (p k) - G (p (k + 1))) := by ring
          rw [hid]
          exact abs_add_le _ _
        calc |G x - G (p (k + 1))|
            ≤ |G x - G (p k)| + |G (p k) - G (p (k + 1))| := htri
          _ ≤ (k : ℝ) * (L * (‖x - y‖ / (N : ℝ)) ^ alpha) +
              L * (‖x - y‖ / (N : ℝ)) ^ alpha :=
            add_le_add (ih (Nat.le_of_succ_le hk)) (hstep k hk)
          _ = ((k + 1 : ℕ) : ℝ) * (L * (‖x - y‖ / (N : ℝ)) ^ alpha) := by
            push_cast
            ring
  have hpN : p N = y := by
    simp only [hp, div_self hNne, one_smul]
    abel
  have hfin := hind N le_rfl
  rw [hpN] at hfin
  have hdivpow : (‖x - y‖ / (N : ℝ)) ^ alpha =
      ‖x - y‖ ^ alpha / (N : ℝ) ^ alpha :=
    Real.div_rpow (norm_nonneg _) (Nat.cast_nonneg N) alpha
  have hNpow : (N : ℝ) * ((N : ℝ) ^ alpha)⁻¹ = (N : ℝ) ^ (1 - alpha) := by
    rw [Real.rpow_sub hNreal, Real.rpow_one, div_eq_mul_inv]
  refine hfin.trans_eq ?_
  rw [hdivpow, div_eq_mul_inv]
  calc (N : ℝ) * (L * (‖x - y‖ ^ alpha * ((N : ℝ) ^ alpha)⁻¹))
      = ((N : ℝ) * ((N : ℝ) ^ alpha)⁻¹) * L * ‖x - y‖ ^ alpha := by ring
    _ = (N : ℝ) ^ (1 - alpha) * L * ‖x - y‖ ^ alpha := by rw [hNpow]

/-! ## 2. Ball geometry -/

/-- Two points of a sup-ball are separated by at most twice its radius. -/
theorem norm_sub_le_two_mul_of_mem_ball {x0 : Vec d} {rho : ℝ} {x y : Vec d}
    (hx : x ∈ Metric.ball x0 rho) (hy : y ∈ Metric.ball x0 rho) :
    ‖x - y‖ ≤ 2 * rho := by
  have hxd : ‖x - x0‖ < rho := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hyd : ‖y - x0‖ < rho := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hid : x - y = (x - x0) - (y - x0) := by abel
  rw [hid]
  calc ‖(x - x0) - (y - x0)‖ ≤ ‖x - x0‖ + ‖y - x0‖ := norm_sub_le _ _
    _ ≤ 2 * rho := by linarith only [hxd, hyd]

/-! ## 3. Continuity -/

/-- A Hölder modulus is a modulus of continuity, for every positive exponent.
The explicit modulus is `(ε / (L + 1)) ^ (1 / α)`, so no restriction on `α` is
needed. -/
theorem continuousOn_of_holderBound {W : Set (Vec d)} {alpha L : ℝ} {G : Vec d → ℝ}
    (halpha : 0 < alpha) (hL : 0 ≤ L)
    (hholder : ∀ x ∈ W, ∀ y ∈ W, |G x - G y| ≤ L * ‖x - y‖ ^ alpha) :
    ContinuousOn G W := by
  rw [Metric.continuousOn_iff]
  intro p hp eps heps
  have hL1 : 0 < L + 1 := by linarith only [hL]
  have hquot : 0 < eps / (L + 1) := div_pos heps hL1
  refine ⟨(eps / (L + 1)) ^ (1 / alpha), Real.rpow_pos_of_pos hquot _, ?_⟩
  intro q hq hd
  have hnorm : ‖q - p‖ < (eps / (L + 1)) ^ (1 / alpha) := by
    rwa [← dist_eq_norm]
  have hpow : ‖q - p‖ ^ alpha < eps / (L + 1) := by
    have hmono := Real.rpow_lt_rpow (norm_nonneg _) hnorm halpha
    rwa [← Real.rpow_mul hquot.le, one_div_mul_cancel halpha.ne', Real.rpow_one] at hmono
  have hmain : |G q - G p| ≤ L * (eps / (L + 1)) :=
    (hholder q hq p hp).trans (mul_le_mul_of_nonneg_left hpow.le hL)
  have hlt : L * (eps / (L + 1)) < eps := by
    rw [mul_div_assoc', div_lt_iff₀ hL1]
    linarith only [heps]
  rw [Real.dist_eq]
  exact hmain.trans_lt hlt

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
