/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4NormalArcDisc
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Disjoint discs around disjoint residual arcs

In XII (4.3), claim (7), page 251, the residual edges form
disjoint arcs whose ends lie on the vertex discs. Thicken these
arcs into mutually disjoint closed discs, meeting the vertex discs
only at the prescribed ends. In the finite induction, forbid the
next arc while constructing the earlier discs, then forbid those
discs while constructing the next one.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Disjoint residual arcs have disjoint thin discs with the same
contacts with a forbidden closed set. This supplies the source edge
discs for XII (4.3), claim (7), page 251. -/
theorem exists_disjoint_arc_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {F : Set ι} (hF : F.Finite) (a : ι → unitInterval → S)
    (hArc : ∀ i ∈ F, IsArcMap (a i))
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (range (a i)) (range (a j))) :
    ∀ B : Set S, IsClosed B → (∀ i ∈ F, range (a i) ∩ B = {a i 0, a i 1}) →
    ∃ D : ι → Set S,
      (∀ i ∈ F, IsClosedDisc (D i) ∧ D i ∩ B = {a i 0, a i 1} ∧
        ({a i 0, a i 1} : Set S) ⊆ discBd (D i) ∧ range (a i) ⊆ D i) ∧
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (D i) (D j) := by
  classical
  revert hArc hdisj
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _ _ B _ _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert i F hi hF ih =>
    intro hArc hdisj B hB hcontact
    have hArcF := fun j hj => hArc j (Or.inr hj)
    have hdisjF := fun j hj k hk hjk => hdisj j (Or.inr hj) k (Or.inr hk) hjk
    have hAi : IsClosed (range (a i)) := (isCompact_range (hArc i (Or.inl rfl)).1).isClosed
    let B' : Set S := B ∪ range (a i)
    have hcontact' : ∀ j ∈ F, range (a j) ∩ B' = {a j 0, a j 1} := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hjiDisj := hdisj j (Or.inr hj) i (Or.inl rfl) hji
      change range (a j) ∩ (B ∪ range (a i)) = _
      rw [inter_union_distrib_left, hcontact j (Or.inr hj), hjiDisj.inter_eq, union_empty]
    obtain ⟨D, hD, hDD⟩ := ih hArcF hdisjF B' (hB.union hAi) hcontact'
    have hendsB : ∀ j ∈ insert i F, ({a j 0, a j 1} : Set S) ⊆ B := by
      intro j hj z hz
      exact ((hcontact j hj).symm.subset hz).2
    have hendsArc : ∀ j, ({a j 0, a j 1} : Set S) ⊆ range (a j) := by
      intro j z hz
      rcases hz with hz | hz
      · exact hz ▸ mem_range_self 0
      · exact (Set.mem_singleton_iff.mp hz) ▸ mem_range_self 1
    have hOldArc : ∀ j ∈ F, Disjoint (D j) (range (a i)) := by
      intro j hj
      apply Set.disjoint_left.mpr
      intro z hzD hzA
      have hzends := (hD j hj).2.1.subset ⟨hzD, Or.inr hzA⟩
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact Set.disjoint_left.mp (hdisj j (Or.inr hj) i (Or.inl rfl) hji)
        (hendsArc j hzends) hzA
    let Z : Set S := B ∪ ⋃ j ∈ F, D j
    have hZ : IsClosed Z := hB.union (hF.isClosed_biUnion fun j hj => (hD j hj).1.isClosed)
    have hmeet : range (a i) ∩ Z ⊆ {a i 0, a i 1} := by
      rintro z ⟨hzA, hzZ⟩
      rcases hzZ with hzB | hzD
      · exact (hcontact i (Or.inl rfl)).subset ⟨hzA, hzB⟩
      · obtain ⟨j, hj, hzDj⟩ := mem_iUnion₂.mp hzD
        exact False.elim (Set.disjoint_left.mp (hOldArc j hj) hzDj hzA)
    obtain ⟨Q, hQ, hQZ, hQbd, haQ⟩ := exists_normal_arc_disc hS (hArc i (Or.inl rfl)) hZ
      (Or.inl (hendsB i (Or.inl rfl) (by simp)))
      (Or.inl (hendsB i (Or.inl rfl) (by simp))) hmeet
    have hQB : Q ∩ B = {a i 0, a i 1} := by
      apply Set.Subset.antisymm
      · exact fun z hz => hQZ.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨discBd_subset Q (hQbd hz), hendsB i (Or.inl rfl) hz⟩
    have hQD : ∀ j ∈ F, Disjoint Q (D j) := by
      intro j hj
      apply Set.disjoint_left.mpr
      intro z hzQ hzD
      have hzends := hQZ.subset ⟨hzQ, Or.inr (mem_iUnion₂.mpr ⟨j, hj, hzD⟩)⟩
      exact Set.disjoint_left.mp (hOldArc j hj) hzD (hendsArc i hzends)
    have hDB : ∀ j ∈ F, D j ∩ B = {a j 0, a j 1} := by
      intro j hj
      apply Set.Subset.antisymm
      · exact fun z hz => (hD j hj).2.1.subset ⟨hz.1, Or.inl hz.2⟩
      · intro z hz
        exact ⟨discBd_subset (D j) ((hD j hj).2.2.1 hz), hendsB j (Or.inr hj) hz⟩
    let D' : ι → Set S := fun j => if j = i then Q else D j
    refine ⟨D', ?_, ?_⟩
    · intro j hj
      rcases hj with hji | hj
      · subst j
        simpa only [D', ↓reduceIte] using
          (show IsClosedDisc Q ∧ Q ∩ B = {a i 0, a i 1} ∧
            ({a i 0, a i 1} : Set S) ⊆ discBd Q ∧ range (a i) ⊆ Q from ⟨hQ, hQB, hQbd, haQ⟩)
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [D', hji, ↓reduceIte] using
          (show IsClosedDisc (D j) ∧ D j ∩ B = {a j 0, a j 1} ∧
            ({a j 0, a j 1} : Set S) ⊆ discBd (D j) ∧ range (a j) ⊆ D j from
              ⟨(hD j hj).1, hDB j hj, (hD j hj).2.2⟩)
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := Ne.symm hjk
        simpa only [D', ↓reduceIte, hki] using hQD k (hk.resolve_left hki)
      · have hjF : j ∈ F := hj.resolve_left hji
        by_cases hki : k = i
        · subst k
          simpa only [D', ↓reduceIte, hji] using (hQD j hjF).symm
        · simpa only [D', hji, hki, ↓reduceIte] using hDD j hjF k (hk.resolve_left hki) hjk

end GraphMinor.GM12
