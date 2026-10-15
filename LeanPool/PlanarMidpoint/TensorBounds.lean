/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Explicit operator bounds for the planar cubic tensor. -/

@[expose] public section
namespace PlanarMidpoint

/-- The Euclidean norm is bounded by the sum of absolute coordinates. -/
theorem norm_le_abs_coordinates (u : E) : ‖u‖ ≤ |u 0| + |u 1| := by
  have he : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq u
  nlinarith [norm_nonneg u, abs_nonneg (u 0), abs_nonneg (u 1),
    mul_nonneg (abs_nonneg (u 0)) (abs_nonneg (u 1)), sq_abs (u 0), sq_abs (u 1)]

private theorem four_terms_bound (c : Coeff) (u v : E) (i j k : Fin 4) :
    |c i * u 0 * v 0 + c j * (u 0 * v 1 + u 1 * v 0) + c k * u 1 * v 1| ≤
      4 * ‖c‖ * ‖u‖ * ‖v‖ := by
  have term (r : Fin 4) (s t : Fin 2) :
      |c r * u s * v t| ≤ ‖c‖ * ‖u‖ * ‖v‖ := by
    rw [abs_mul, abs_mul]
    apply mul_le_mul
    · apply mul_le_mul
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm c r
      · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u s
      · exact abs_nonneg _
      · exact norm_nonneg _
    · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v t
    · exact abs_nonneg _
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have he : c i * u 0 * v 0 + c j * (u 0 * v 1 + u 1 * v 0) + c k * u 1 * v 1 =
      c i * u 0 * v 0 + c j * u 0 * v 1 + c j * u 1 * v 0 + c k * u 1 * v 1 := by ring
  rw [he]
  have h1 := norm_add_le (c i * u 0 * v 0 + c j * u 0 * v 1 + c j * u 1 * v 0) (c k * u 1 * v 1)
  have h2 := norm_add_le (c i * u 0 * v 0 + c j * u 0 * v 1) (c j * u 1 * v 0)
  have h3 := norm_add_le (c i * u 0 * v 0) (c j * u 0 * v 1)
  simp only [Real.norm_eq_abs] at h1 h2 h3
  linarith [term i 0 0, term j 0 1, term j 1 0, term k 1 1]

/-- A uniform trilinear bound; the constant is deliberately coarse. -/
theorem norm_K_le (c : Coeff) (u v : E) :
    ‖K c u v‖ ≤ 8 * ‖c‖ * ‖u‖ * ‖v‖ := by
  have h := norm_le_abs_coordinates (K c u v)
  have h0 := four_terms_bound c u v 0 1 2
  have h1 := four_terms_bound c u v 1 2 3
  simp only [K, vec_zero, vec_one] at h
  dsimp only [K]
  linarith


/-- Difference decomposition retaining the quadratic velocity structure. -/
theorem K_diagonal_sub (c d : Coeff) (v w : E) :
    K c v v - K d w w =
      K (c - d) v v + K d (v - w) v + K d w (v - w) := by
  apply vec_ext <;> simp [K, Pi.sub_apply] <;> ring

/-- The Christoffel force is locally Lipschitz in coefficients and velocity. -/
theorem norm_K_diagonal_sub_le (c d : Coeff) (v w : E) :
    ‖K c v v - K d w w‖ ≤
      8 * ‖c - d‖ * ‖v‖ ^ 2 + 8 * ‖d‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  rw [K_diagonal_sub]
  calc
    ‖K (c - d) v v + K d (v - w) v + K d w (v - w)‖ ≤
        ‖K (c - d) v v‖ + ‖K d (v - w) v‖ + ‖K d w (v - w)‖ := norm_add₃_le
    _ ≤ 8 * ‖c - d‖ * ‖v‖ * ‖v‖ + 8 * ‖d‖ * ‖v - w‖ * ‖v‖ + 8 * ‖d‖ * ‖w‖ * ‖v - w‖ :=
      add_le_add (add_le_add (norm_K_le _ _ _) (norm_K_le _ _ _)) (norm_K_le _ _ _)
    _ = _ := by ring

end PlanarMidpoint
