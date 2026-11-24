/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ArcMeetingParameters
public import LeanPool.GraphMinor.GM12.Section4ArcSubdivision
import Mathlib.Data.Set.Card

/-!
# Subdividing an edge at all its meetings

XII (4.5), page 252, replaces an edge with `k` crossings by `k`
edge portions. Order the actual meeting points through the arc
homeomorphism, then apply the midpoint subdivision. The pieces
cover the original edge, have distinct cut vertices, and each
contain exactly one of the original meetings.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Subdivide an actual edge arc at a finite nonempty set of
interior meetings, giving one meeting per new edge. This proves
the per-edge geometric subdivision step in XII (4.5), page 252. -/
theorem exists_one_meeting_arc_subdivision {E X : Set ℂ} {a b : ℂ}
    (hE : IsLineWithEnds E a b) (hX : X.Finite) (hXne : X.Nonempty)
    (hXE : X ⊆ E) (haX : a ∉ X) (hbX : b ∉ X) :
    ∃ k : ℕ, 0 < k ∧ ∃ (w : Fin (k + 1) → ℂ) (P : Fin k → Set ℂ),
      Function.Injective w ∧ w 0 = a ∧ w (Fin.last k) = b ∧
      (∀ i, IsLineWithEnds (P i) (w i.castSucc) (w i.succ)) ∧
      (⋃ i, P i) = E ∧
      (∀ i, ∃ x ∈ X, P i ∩ X = {x}) ∧
      (∀ i, w i ∉ X) ∧
      (∀ i j, i ≠ j → P i ∩ P j ⊆ range w) ∧
      (∀ i, P i ∩ range w = {w i.castSucc, w i.succ}) ∧ X.ncard = k := by
  obtain ⟨k, hk, φ, hφ0, hφ1, t, ht, ht01, hXrange⟩ :=
    exists_ordered_arc_meeting_parameters hE hX hXne hXE haX hbX
  let g : unitInterval → ℂ := fun u => (φ u).val
  have hg : IsArcMap g := ⟨continuous_subtype_val.comp φ.continuous,
    Subtype.val_injective.comp φ.injective⟩
  have hgrange : range g = E := by
    apply Subset.antisymm
    · rintro x ⟨u, rfl⟩
      exact (φ u).property
    · intro x hx
      exact ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
  have hXg : X = range (fun i => g (t i)) := hXrange
  refine ⟨k, hk, arcSubdivisionVertex g t, arcSubdivisionPiece g t,
    arcSubdivisionVertex_injective hk hg.2 t ht ht01, ?_, ?_,
    fun i => arcSubdivisionPiece_isLine hk hg t ht ht01 i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [arcSubdivisionVertex_zero]
    exact hφ0
  · rw [arcSubdivisionVertex_last hk]
    exact hφ1
  · exact (iUnion_arcSubdivisionPieces hk hg.2 t ht ht01).trans hgrange
  · intro i
    refine ⟨g (t i), hXg ▸ mem_range_self i, ?_⟩
    rw [hXg]
    exact arcSubdivisionPiece_inter_marked hk hg.2 t ht ht01 i
  · intro i
    rw [hXg]
    exact arcSubdivisionVertex_not_mem_marked hk hg.2 t ht ht01 i
  · intro i j hij
    exact arcSubdivisionPieces_inter_subset_vertices hk hg.2 t ht ht01 hij
  · intro i
    exact arcSubdivisionPiece_inter_vertices hk hg.2 t ht ht01 i
  · rw [hXg]
    change (range (g ∘ t)).ncard = k
    rw [ncard_range_of_injective (hg.2.comp ht.injective), Nat.card_fin]

end GraphMinor.GM12
