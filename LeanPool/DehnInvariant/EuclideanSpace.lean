/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Coordinate calculations in Euclidean three-space.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-- Coordinate 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

instance : Fact (finrank ℝ R3 = 3) := ⟨by simp⟩

lemma inner3 (p q r : ℝ) (x : R3) : ⟪(!₂[p, q, r] : R3), x⟫ = p * x 0 + q * x 1 + r * x 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]; ring

lemma bounded_of_coords {S : Set R3} (C : ℝ) (h : ∀ x ∈ S, ∀ i, |x i| ≤ C)
    : Bornology.IsBounded S := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨√(3 * C ^ 2), fun x hx => ?_⟩
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_three]
  have h1 : ∀ i, ‖x i‖ ^ 2 ≤ C ^ 2 := fun i => by
    rw [Real.norm_eq_abs, sq_abs]
    exact sq_le_sq' (abs_le.1 (h x hx i)).1 (abs_le.1 (h x hx i)).2
  have := h1 0; have := h1 1; have := h1 2
  linarith

/-- Squared length in coordinates. -/
lemma norm3_sq (p q r : ℝ) : ‖(!₂[p, q, r] : R3)‖ ^ 2 = p ^ 2 + q ^ 2 + r ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Distance in coordinates. -/
lemma dist3 (x y : R3) {d : ℝ} (hd : 0 ≤ d)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = d ^ 2) : dist x y = d := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]
  rw [h, Real.sqrt_sq hd]

end DehnCanon.Library
