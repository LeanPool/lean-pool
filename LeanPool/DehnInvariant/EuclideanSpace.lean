/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.EdgeData
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part G: the bridge stated in
coordinate
3-space ℝ³, and two concrete solids (a regular tetrahedron and the cubes) as convex polytopes.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-- Coordinate 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

instance : Fact (finrank ℝ R3 = 3) := ⟨by simp⟩

/-- **Dehn's theorem, the bridge, in ℝ³.** Scissors-congruent convex polytopes have the same Dehn
invariant. -/
theorem dehn_bridge_R3 {P Q : Set R3} (hP : IsPoly P) (hQ : IsPoly Q) (h : ScissorsCongruent P Q) :
    dehnSet P = dehnSet Q :=
  dehnSet_eq_of_scissorsCongruent hP hQ h

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

/-- Outward face normals of the regular tetrahedron with corners (−1,−1,−1), (1,1,−1), (1,−1,1),
(−1,1,1). -/
def tetN : Fin 4 → R3 := ![!₂[1, 1, 1], !₂[-1, -1, 1], !₂[-1, 1, -1], !₂[1, -1, -1]]

/-- The regular tetrahedron with corners (−1,−1,−1), (1,1,−1), (1,−1,1), (−1,1,1) (edge 2√2). -/
noncomputable def tetraSet : Set R3 := sol tetN (fun _ => 1)

/-- Outward face normals of a cube: ± the three coordinate directions. -/
noncomputable def cubeN : Fin 3 × Bool → R3 :=
  fun p => if p.2 then EuclideanSpace.single p.1 1 else -EuclideanSpace.single p.1 1

/-- The cube `[-s, s]³` (edge 2s). -/
noncomputable def cubeSet (s : ℝ) : Set R3 := sol cubeN (fun _ => s)

theorem isPoly_tetra : IsPoly tetraSet := by
  refine ⟨bounded_of_coords 1 (fun x hx i => ?_), Fin 4, inferInstance, tetN, _, rfl⟩
  have h0 : ⟪(!₂[1, 1, 1] : R3), x⟫ ≤ 1 := hx 0
  have h1 : ⟪(!₂[-1, -1, 1] : R3), x⟫ ≤ 1 := hx 1
  have h2 : ⟪(!₂[-1, 1, -1] : R3), x⟫ ≤ 1 := hx 2
  have h3 : ⟪(!₂[1, -1, -1] : R3), x⟫ ≤ 1 := hx 3
  rw [inner3] at h0 h1 h2 h3
  have key : |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
    refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> linarith
  fin_cases i
  exacts [key.1, key.2.1, key.2.2]

theorem isPoly_cube (s : ℝ) : IsPoly (cubeSet s) := by
  refine ⟨bounded_of_coords s (fun x hx i => ?_), Fin 3 × Bool, inferInstance, cubeN, _, rfl⟩
  have h1 : ⟪(EuclideanSpace.single i (1 : ℝ) : R3), x⟫ ≤ s := hx (i, true)
  have h2 : ⟪(-EuclideanSpace.single i (1 : ℝ) : R3), x⟫ ≤ s := hx (i, false)
  rw [inner_neg_left] at h2
  rw [EuclideanSpace.inner_single_left] at h1 h2
  simp only [map_one, one_mul] at h1 h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

end DehnCanon.Library
