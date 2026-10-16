/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.TensorBounds
public import LeanPool.PlanarMidpoint.BVPStability
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Quantitative comparison of geodesics and polynomial trajectories

These estimates preserve the quadratic dependence of acceleration on velocity.
The contraction constants tend to zero with the allowed velocity radius.
-/

@[expose] public section

namespace PlanarMidpoint
open Set

/-- Spatial and velocity Lipschitz constants for the Christoffel force on a
small phase neighborhood. -/
theorem force_difference_bound (C : E → Coeff) (S : Set E) (M L r : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (_hr : 0 ≤ r)
    (hbound : ∀ x ∈ S, ‖C x‖ ≤ M)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖C x - C y‖ ≤ L * ‖x - y‖)
    {x y v w : E} (hx : x ∈ S) (hy : y ∈ S) (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖K (C x) v v - K (C y) w w‖ ≤
      (8 * L * r ^ 2) * ‖x - y‖ + (16 * M * r) * ‖v - w‖ := by
  calc
    ‖K (C x) v v - K (C y) w w‖ ≤
        8 * ‖C x - C y‖ * ‖v‖ ^ 2 + 8 * ‖C y‖ * (‖v‖ + ‖w‖) * ‖v - w‖ :=
      norm_K_diagonal_sub_le _ _ _ _
    _ ≤ 8 * (L * ‖x - y‖) * r ^ 2 + 8 * M * (r + r) * ‖v - w‖ := by
      gcongr
      · exact hLip x hx y hy
      · exact hbound y hy
    _ = _ := by ring

/-- A true geodesic and a polynomial trajectory with the same endpoints are
close whenever the latter has a small acceleration residual. -/
theorem geodesic_polynomial_comparison
    (C : E → Coeff) (S : Set E) (M L r R : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ S, ‖C x‖ ≤ M)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖C x - C y‖ ≤ L * ‖x - y‖)
    (hsmall : 8 * L * r ^ 2 + 16 * M * r < 1)
    (x v y w b : ℝ → E)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt v (-K (C (x t)) (v t) (v t)) t)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt y (w t) t)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (b t) t)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (hxS : ∀ t ∈ Icc (0 : ℝ) 1, x t ∈ S)
    (hyS : ∀ t ∈ Icc (0 : ℝ) 1, y t ∈ S)
    (hvsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖v t‖ ≤ r)
    (hwsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ ≤ r)
    (hres : ∀ t ∈ Icc (0 : ℝ) 1, ‖b t + K (C (y t)) (w t) (w t)‖ ≤ R)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x t - y t‖ ≤ R / (1 - 8 * L * r ^ 2 - 16 * M * r) ∧
      ‖v t - w t‖ ≤ R / (1 - 8 * L * r ^ 2 - 16 * M * r) := by
  apply bvp_stability x v (fun s ↦ -K (C (x s)) (v s) (v s)) y w b
    R (8 * L * r ^ 2) (16 * M * r) hx hv hy hw h0 h1
    (by positivity) (by positivity) hsmall _ t ht
  intro s hs
  have hforce := force_difference_bound C S M L r hM hL hr hbound hLip
    (hxS s hs) (hyS s hs) (hvsmall s hs) (hwsmall s hs)
  calc
    ‖ - K (C (x s)) (v s) (v s) - b s‖ =
        ‖ - (K (C (x s)) (v s) (v s) - K (C (y s)) (w s) (w s)) - (b s + K (C (y s)) (w s) (w s))‖
            := by congr 1; module
    _ ≤ ‖K (C (x s)) (v s) (v s) - K (C (y s)) (w s) (w s)‖ + ‖b s + K (C (y s)) (w s) (w s)‖ := by
      simpa only [norm_neg] using norm_sub_le
        (-(K (C (x s)) (v s) (v s) - K (C (y s)) (w s) (w s)))
        (b s + K (C (y s)) (w s) (w s))
    _ ≤ R + (8 * L * r ^ 2) * ‖x s - y s‖ + (16 * M * r) * ‖v s - w s‖ := by
      linarith [hres s hs]

/-- A coefficient Taylor error, quadratic in displacement, becomes a fourth-order
force error when displacement and velocity are both first order. -/
theorem force_taylor_error_bound (c d : Coeff) (x v : E) (η B ε : ℝ)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hcoeff : ‖c - d‖ ≤ η * ‖x‖ ^ 2)
    (hx : ‖x‖ ≤ B * ε) (hv : ‖v‖ ≤ B * ε) :
    ‖K c v v - K d v v‖ ≤ 8 * η * B ^ 4 * ε ^ 4 := by
  have he : K c v v - K d v v = K (c - d) v v := by
    apply vec_ext <;> simp [K] <;> ring
  rw [he]
  calc
    ‖K (c - d) v v‖ ≤ 8 * ‖c - d‖ * ‖v‖ * ‖v‖ := norm_K_le _ _ _
    _ ≤ 8 * (η * (B * ε) ^ 2) * (B * ε) * (B * ε) := by
      gcongr
      exact hcoeff.trans (by gcongr)
    _ = _ := by ring

end PlanarMidpoint
