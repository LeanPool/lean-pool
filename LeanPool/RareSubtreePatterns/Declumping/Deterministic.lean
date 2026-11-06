/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Basic

/-!
# Deterministic comparison of raw and declumped occurrences

The two set inclusions in the proof of Lemma `lem:declump_to_raw`, source
lines 2361–2389. No probability assumptions are required. Propagation is the
paper's stated hypothesis, not a substitute for the conclusion.
-/

@[expose] public section

namespace PoissonDeclumping.PlaneTree

variable {B : Set ℕ} {G : PlaneTree → Prop} {T : PlaneTree}

/-- A declumped occurrence contains a marked child and hence a raw occurrence. -/
theorem declumped_count_pos_imp_raw_count_pos
    (h : 0 < markCount (declumpedMark B G) T) : 0 < markCount G T := by
  obtain ⟨U, hU, _, V, hV, hG⟩ := (markCount_pos_iff (declumpedMark B G) T).mp h
  exact (markCount_pos_iff G T).mpr
    ⟨V, mem_fringeTrees_trans hU (child_mem_fringeTrees hV), hG⟩

/-- Absence of raw occurrences implies absence of declumped occurrences. -/
theorem raw_count_zero_imp_declumped_count_zero (h : markCount G T = 0) :
    markCount (declumpedMark B G) T = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have := declumped_count_pos_imp_raw_count_pos hpos
  omega

/-- With no declumped occurrence, propagation carries any raw mark to the root.
This is the deterministic core of Lemma `lem:declump_to_raw`. -/
theorem marked_root_of_no_declumped (hprop : PropagatesOutside B G)
    (hraw : 0 < markCount G T) (hno : markCount (declumpedMark B G) T = 0) : G T := by
  revert hraw hno
  induction T using induction_children with
  | step T ih =>
    intro hraw hno
    rcases (markCount_pos_iff_root_or_child G T).mp hraw with hroot | ⟨U, hU, hpos⟩
    · exact hroot
    · have hchild : markCount (declumpedMark B G) U = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro h
        have := markCount_pos_of_child hU h
        omega
      have hGU := ih U hU hpos hchild
      apply hprop T U hU hGU
      intro hB
      have hroot : declumpedMark B G T := ⟨hB, U, hU, hGU⟩
      have := markCount_pos_of_root hroot
      omega

/-- First event inclusion used in the probabilistic comparison. -/
theorem raw_zero_subset_declumped_zero (B : Set ℕ) (G : PlaneTree → Prop) :
    {T | markCount G T = 0} ⊆ {T | markCount (declumpedMark B G) T = 0} := by
  intro T hT
  exact raw_count_zero_imp_declumped_count_zero hT

/-- The discrepancy between the two zero events requires a mark at the root. -/
theorem declumped_zero_subset_raw_zero_union_root (hprop : PropagatesOutside B G) :
    {T | markCount (declumpedMark B G) T = 0} ⊆
      {T | markCount G T = 0} ∪ {T | G T} := by
  intro T hT
  by_cases hraw : markCount G T = 0
  · exact Or.inl hraw
  · exact Or.inr (marked_root_of_no_declumped hprop (Nat.pos_of_ne_zero hraw) hT)

end PoissonDeclumping.PlaneTree
