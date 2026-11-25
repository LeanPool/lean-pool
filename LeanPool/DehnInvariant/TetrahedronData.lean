/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.PlaneCut
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Barycentric coordinates and edges of a tetrahedron

Positive multiples of the defining face functionals give barycentric coordinates.
The two coordinates away from an edge vanish along that edge.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma fin4_cover : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    ∀ m, m = i ∨ m = j ∨ m = k ∨ ∀ n, n = i ∨ n = j ∨ n = k ∨ n = m := by decide

/-- The data of a tetrahedron: corners `p`, outward face normals `n` (face `m` is opposite the
corner `m`),
face offsets `b`, and positive weights `w` that turn the face functionals into barycentric
coordinates. -/
structure IsTetraData (n p : Fin 4 → E) (b w : Fin 4 → ℝ) : Prop where
  w_pos : ∀ m, 0 < w m
  delta : ∀ m k, w m * (b m - ⟪n m, p k⟫) = if m = k then 1 else 0
  sum_one : ∀ x, ∑ m, w m * (b m - ⟪n m, x⟫) = 1
  rebuild : ∀ x, ∑ m, (w m * (b m - ⟪n m, x⟫)) • p m = x

namespace IsTetraData

variable {n p : Fin 4 → E} {b w : Fin 4 → ℝ}

lemma mem_sol_iff (h : IsTetraData n p b w) (x : E) :
    x ∈ sol n b ↔ ∀ m, 0 ≤ w m * (b m - ⟪n m, x⟫) := by
  constructor
  · intro hx m
    exact mul_nonneg (h.w_pos m).le (sub_nonneg.2 (hx m))
  · intro hx m
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_right (hx m) (h.w_pos m))

lemma mem_act_iff (h : IsTetraData n p b w) (x : E) (m : Fin 4) :
    m ∈ act n b x ↔ w m * (b m - ⟪n m, x⟫) = 0 := by
  change ⟪n m, x⟫ = b m ↔ _
  rw [mul_eq_zero, sub_eq_zero]
  constructor
  · intro h1; exact Or.inr h1.symm
  · rintro (h1 | h1)
    · exact absurd h1 (h.w_pos m).ne'
    · exact h1.symm

lemma bary_comb (n : Fin 4 → E) (b w : Fin 4 → ℝ) (m : Fin 4) {α β : ℝ} (hab : α + β = 1)
    (u v : E) :
    w m * (b m - ⟪n m, α • u + β • v⟫) =
      α * (w m * (b m - ⟪n m, u⟫)) + β * (w m * (b m - ⟪n m, v⟫)) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  linear_combination (-(w m * b m)) * hab

/-- The four normals have no common perpendicular direction. -/
lemma inj (h : IsTetraData n p b w) {v : E} (hv : ∀ m, ⟪n m, v⟫ = 0) : v = 0 := by
  calc v = ∑ m, (w m * (b m - ⟪n m, v⟫)) • p m := (h.rebuild v).symm
    _ = ∑ m, (w m * (b m - ⟪n m, (0 : E)⟫)) • p m := by
        apply Finset.sum_congr rfl; intro m _; rw [hv m, inner_zero_right]
    _ = 0 := h.rebuild 0

/-- Three of the four normals have no common perpendicular direction. -/
lemma three (h : IsTetraData n p b w) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {v : E} (hi : ⟪n i, v⟫ = 0) (hj : ⟪n j, v⟫ = 0) (hk : ⟪n k, v⟫ = 0) : v = 0 := by
  have hs : ∑ m, w m * ⟪n m, v⟫ = 0 := by
    have h1 := h.sum_one v
    have h2 := h.sum_one 0
    simp only [inner_zero_right, sub_zero] at h2
    have h3 : ∑ m, w m * (b m - ⟪n m, v⟫) = ∑ m, w m * b m - ∑ m, w m * ⟪n m, v⟫ := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro m _; ring
    linarith
  apply h.inj
  intro m
  rcases fin4_cover i j k hij hik hjk m with rfl | rfl | rfl | hc
  · exact hi
  · exact hj
  · exact hk
  · have hsum : ∑ l, w l * ⟪n l, v⟫ = w m * ⟪n m, v⟫ :=
      Finset.sum_eq_single m (fun l _ hlm => by
        rcases hc l with rfl | rfl | rfl | rfl
        · rw [hi, mul_zero]
        · rw [hj, mul_zero]
        · rw [hk, mul_zero]
        · exact absurd rfl hlm) (fun h' => absurd (Finset.mem_univ m) h')
    rw [hs] at hsum
    exact (mul_eq_zero.1 hsum.symm).resolve_left (h.w_pos m).ne'

lemma corner_ne (h : IsTetraData n p b w) {k l : Fin 4} (hkl : k ≠ l) : p k ≠ p l := by
  intro he
  have h1 := h.delta k k
  have h2 := h.delta k l
  rw [he, h2, ite_eq_left rfl, ite_eq_right hkl] at h1
  exact zero_ne_one h1

/-- **The edges**: the points of the solid where exactly the two faces other than `k`, `l` are
tight are the
points of the open segment between the corners `k` and `l`. -/
lemma openSegment_iff (h : IsTetraData n p b w) {k l : Fin 4} (hkl : k ≠ l) (x : E) :
    x ∈ openSegment ℝ (p k) (p l) ↔ x ∈ sol n b ∧ act n b x = ({k, l}ᶜ : Set (Fin 4)) := by
  constructor
  · rintro ⟨α, β, hα, hβ, hab, rfl⟩
    have hb : ∀ m, w m * (b m - ⟪n m, α • p k + β • p l⟫) =
        α * (if m = k then 1 else 0) + β * (if m = l then 1 else 0) := by
      intro m; rw [bary_comb n b w m hab, h.delta, h.delta]
    refine ⟨(h.mem_sol_iff _).2 fun m => ?_, ?_⟩
    · rw [hb]; split_ifs <;> linarith
    · ext m
      rw [h.mem_act_iff, hb, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      by_cases hmk : m = k
      · rw [ite_eq_left hmk, ite_eq_right (fun h' => hkl (hmk.symm.trans h'))]
        constructor
        · intro h'; exfalso; linarith
        · intro h'; exact absurd hmk h'.1
      · by_cases hml : m = l
        · rw [ite_eq_right hmk, ite_eq_left hml]
          constructor
          · intro h'; exfalso; linarith
          · intro h'; exact absurd hml h'.2
        · rw [ite_eq_right hmk, ite_eq_right hml]
          constructor
          · intro _; exact ⟨hmk, hml⟩
          · intro _; ring
  · rintro ⟨hx, hA⟩
    have hmem : ∀ m, w m * (b m - ⟪n m, x⟫) = 0 ↔ (m ≠ k ∧ m ≠ l) := by
      intro m
      rw [← h.mem_act_iff, hA, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    have hnn := (h.mem_sol_iff x).1 hx
    have hk1 : 0 < w k * (b k - ⟪n k, x⟫) :=
      lt_of_le_of_ne (hnn k) (fun h' => ((hmem k).1 h'.symm).1 rfl)
    have hl1 : 0 < w l * (b l - ⟪n l, x⟫) :=
      lt_of_le_of_ne (hnn l) (fun h' => ((hmem l).1 h'.symm).2 rfl)
    have hsum : w k * (b k - ⟪n k, x⟫) + w l * (b l - ⟪n l, x⟫) = 1 := by
      rw [← h.sum_one x]
      exact (Fintype.sum_eq_add k l hkl (fun m hm => (hmem m).2 hm)).symm
    have hreb : (w k * (b k - ⟪n k, x⟫)) • p k + (w l * (b l - ⟪n l, x⟫)) • p l = x := by
      have h1 := Fintype.sum_eq_add (f := fun m => (w m * (b m - ⟪n m, x⟫)) • p m) k l hkl
        (fun m hm => by change (w m * (b m - ⟪n m, x⟫)) • p m = 0; rw [(hmem m).2 hm, zero_smul])
      rw [← h1]; exact h.rebuild x
    exact ⟨_, _, hk1, hl1, hsum, hreb⟩

/-- The solid is bounded. -/
lemma bounded (h : IsTetraData n p b w) : Bornology.IsBounded (sol n b) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∑ m, ‖p m‖, fun x hx => ?_⟩
  have hnn := (h.mem_sol_iff x).1 hx
  have hle : ∀ m, w m * (b m - ⟪n m, x⟫) ≤ 1 := by
    intro m
    rw [← h.sum_one x]
    exact Finset.single_le_sum (f := fun m => w m * (b m - ⟪n m, x⟫)) (fun i _ => hnn i)
      (Finset.mem_univ m)
  calc ‖x‖ = ‖∑ m, (w m * (b m - ⟪n m, x⟫)) • p m‖ := by rw [h.rebuild x]
    _ ≤ ∑ m, ‖(w m * (b m - ⟪n m, x⟫)) • p m‖ := norm_sum_le _ _
    _ ≤ ∑ m, ‖p m‖ := by
        apply Finset.sum_le_sum; intro m _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn m)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hle m)

/-- The solid is a convex polytope. -/
lemma isPoly (h : IsTetraData n p b w) : IsPoly (sol n b) :=
  ⟨h.bounded, Fin 4, inferInstance, n, b, rfl⟩

/-- **The solid is the convex hull of its four corners.** -/
theorem eq_convexHull (h : IsTetraData n p b w) : sol n b = convexHull ℝ (Set.range p) := by
  apply Subset.antisymm
  · intro x hx
    rw [← h.rebuild x]
    exact (convex_convexHull ℝ _).sum_mem (fun m _ => (h.mem_sol_iff x).1 hx m) (h.sum_one x)
      (fun m _ => subset_convexHull ℝ _ (mem_range_self m))
  · apply convexHull_min _ (convex_sol n b)
    rintro _ ⟨k, rfl⟩
    rw [h.mem_sol_iff]
    intro m
    rw [h.delta]; split_ifs <;> norm_num

end IsTetraData

end DehnCanon.Library
