/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThreeBranchCount

/-!
# Relabelling the three branches by their surrounding cuffs

Condition (iv) of XII (3.1), page 245, pairs each branch with the disc
bounded by the other two. The surrounding-cuff classification need not
use this indexing. Relabel the branches by their cuff permutation.
The union, normality and vertex count stay the same, while each
opposite pair now surrounds the prescribed cuff with that index.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A bijection of branch indices also bijects the indices excluding
one chosen index. -/
theorem iUnion_except_comp_equiv
    {S ι κ : Type*} (e : ι ≃ κ) (P : ι → Set S) (i : κ) :
    (⋃ j : {j : κ // j ≠ i}, P (e.symm j.val)) =
      ⋃ j : {j : ι // j ≠ e.symm i}, P j.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨e.symm j.val, fun he => j.property (e.symm.injective he)⟩, hj⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hji : e j.val ≠ i := by
      intro he
      apply j.property
      apply e.injective
      rw [he, e.apply_symm_apply]
    refine mem_iUnion.mpr ⟨⟨e j.val, hji⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hj

/-- The bound of XII (3.1)(iv) is unchanged when branches are indexed
by the permutation of the cuffs their opposite circles surround. -/
theorem three_branch_vertex_count_gt_relabelled
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hsphere : IsSphere S) (Γ : Drawing S)
    (Δ : Fin 3 → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hUC : Γ.U ⊆ discComplement Δ) (N : ℕ)
    (hbound : IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
      Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
      (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
      (∀ i, IsClosedDisc (D i) ∧
        discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ i ⊆ D i ∧ ¬ P i ⊆ D i) →
      N < (Γ.V ∩ ⋃ i, P i).ncard)
    (P : Fin 3 → Set (discComplement Δ)) {a b : discComplement Δ} (hab : a ≠ b)
    (hP : ∀ i, IsLineWithEnds (P i) a b)
    (hcap : ∀ i j, i ≠ j → P i ∩ P j = {a, b})
    (hQ : ∀ i, IsOArc (⋃ j : {j // j ≠ i}, P j.val))
    (e : Fin 3 ≃ Fin 3)
    (hs : ∀ i, GM07.SurroundsCuff (⋃ j : {j // j ≠ i}, P j.val)
      (Subtype.val ⁻¹' discBd (Δ (e i))))
    (hn : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (⋃ i, P i))
    (hnot : ¬ GM07.IsNearPlanar (⋃ i, P i)) :
    N < ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ ⋃ i, P i).ncard := by
  let A : Fin 3 → Set (discComplement Δ) := fun i => P (e.symm i)
  have hU : (⋃ i, A i) = ⋃ i, P i := e.symm.surjective.iUnion_comp P
  have hO : ∀ i, (⋃ j : {j // j ≠ i}, A j.val) =
      ⋃ j : {j // j ≠ e.symm i}, P j.val := fun i => iUnion_except_comp_equiv e P i
  have hQ' : ∀ i, IsOArc (⋃ j : {j // j ≠ i}, A j.val) := by
    intro i
    rw [hO]
    exact hQ (e.symm i)
  have hs' : ∀ i, GM07.SurroundsCuff (⋃ j : {j // j ≠ i}, A j.val)
      (Subtype.val ⁻¹' discBd (Δ i)) := by
    intro i
    rw [hO]
    simpa only [e.apply_symm_apply] using hs (e.symm i)
  have hnormal : (drawingInSubspace Γ (discComplement Δ) hUC).IsNormal (⋃ i, A i) := by
    rw [hU]
    exact hn
  have hnot' : ¬ GM07.IsNearPlanar (⋃ i, A i) := by rw [hU]; exact hnot
  have hbig := three_branch_vertex_count_gt hS hsphere Γ Δ hΔ hdisj hUC N hbound A hab
    (fun i => hP (e.symm i))
    (fun i j hij => hcap (e.symm i) (e.symm j) (fun he => hij (e.symm.injective he)))
    hQ' hs' hnormal hnot'
  rw [hU] at hbig
  exact hbig

end GraphMinor.GM12
