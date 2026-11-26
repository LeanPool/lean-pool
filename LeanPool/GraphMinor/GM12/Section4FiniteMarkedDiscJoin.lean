/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4MarkedDiscJoin
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Joining all arms of a vertex star

In XII (4.5), claim (1), page 253, a vertex disc and the thin
discs around its residual edge halves form a star. Attach these
arm discs one at a time. While joining the other arms, protect
the next arm as part of the closed set. It still meets the
joined disc at its original boundary point when its turn comes.
All contacts with the crossing discs stay fixed.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Finitely many pairwise disjoint discs attached at separate
boundary points of one disc can be joined inside an open set.
The construction preserves exact contacts with a closed set
avoiding all attachment points, including the boundary status
of those contacts. This thickens a vertex star in XII (4.5),
claim (1), page 253. -/
theorem exists_finite_join_preserving_contacts {S ι : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (A U : Set S) (B : ι → Set S) (p : ι → S)
    (hA : IsClosedDisc A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∀ (F : Finset ι) (Z : Set S), IsClosed Z →
      (∀ i ∈ F, IsClosedDisc (B i)) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) →
      (∀ i ∈ F, A ∩ B i = {p i}) →
      (∀ i ∈ F, p i ∈ discBd A) →
      (∀ i ∈ F, p i ∈ discBd (B i)) →
      (∀ i ∈ F, B i ⊆ U) → (∀ i ∈ F, p i ∉ Z) →
      ∃ D : Set S, IsClosedDisc D ∧ (A ∪ ⋃ i ∈ F, B i) ⊆ D ∧ D ⊆ U ∧
        D ∩ Z = (A ∪ ⋃ i ∈ F, B i) ∩ Z ∧
        (discBd A ∪ ⋃ i ∈ F, discBd (B i)) ∩ Z ⊆ discBd D := by
  classical
  have ht2 : T2Space S := hS.2.1
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro Z _ _ _ _ _ _ _ _
    refine ⟨A, hA, ?_, hAU, ?_, ?_⟩
    · simp
    · simp
    · simp
  | @insert i F hi ih =>
    intro Z hZ hB hBB hAB hpA hpB hBU hpZ
    have hiF : i ∈ insert i F := Finset.mem_insert_self i F
    have hF : ∀ j ∈ F, j ∈ insert i F := fun j hj => Finset.mem_insert_of_mem hj
    have hpiB : p i ∈ B i := Surface.discBd_subset _ (hpB i hiF)
    have hpZ' : ∀ j ∈ F, p j ∉ Z ∪ B i := by
      intro j hj hmem
      rcases hmem with hz | hb
      · exact hpZ j (hF j hj) hz
      · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        exact disjoint_left.mp (hBB j (hF j hj) i hiF hji)
          (Surface.discBd_subset _ (hpB j (hF j hj))) hb
    obtain ⟨D, hd, hsub, hDU, hcontact, hbd⟩ := ih (Z ∪ B i)
      (hZ.union (hB i hiF).isClosed)
      (fun j hj => hB j (hF j hj))
      (fun j hj k hk => hBB j (hF j hj) k (hF k hk))
      (fun j hj => hAB j (hF j hj)) (fun j hj => hpA j (hF j hj))
      (fun j hj => hpB j (hF j hj)) (fun j hj => hBU j (hF j hj)) hpZ'
    have hDB : D ∩ B i = {p i} := by
      apply Subset.antisymm
      · rintro z ⟨hzD, hzB⟩
        have hzK : z ∈ A ∪ ⋃ j ∈ F, B j :=
          (show z ∈ (A ∪ ⋃ j ∈ F, B j) ∩ (Z ∪ B i) from hcontact ▸ ⟨hzD, Or.inr hzB⟩).1
        rcases hzK with hzA | hzarms
        · exact (hAB i hiF).subset ⟨hzA, hzB⟩
        · obtain ⟨j, hzj⟩ := mem_iUnion.mp hzarms
          obtain ⟨hjF, hzj⟩ := mem_iUnion.mp hzj
          have hji : j ≠ i := fun heq => hi (heq ▸ hjF)
          exact False.elim (disjoint_left.mp (hBB j (hF j hjF) i hiF hji) hzj hzB)
      · intro z hz
        have heq : z = p i := mem_singleton_iff.mp hz
        rw [heq]
        exact ⟨hsub (Or.inl (Surface.discBd_subset _ (hpA i hiF))), hpiB⟩
    have hpiD : p i ∈ discBd D := hbd ⟨Or.inl (hpA i hiF), Or.inr hpiB⟩
    obtain ⟨D', hd', hsub', hD'U, hcontact', hbd'⟩ := exists_join_preserving_contacts hS
      hd (hB i hiF) hDB hpiD (hpB i hiF) hU hDU (hBU i hiF) hZ (hpZ i hiF)
    have hunion : (A ∪ ⋃ j ∈ insert i F, B j) = (A ∪ ⋃ j ∈ F, B j) ∪ B i := by
      simp only [Finset.set_biUnion_insert]
      rw [← union_assoc]
      exact union_right_comm A (B i) (⋃ j ∈ F, B j)
    have hbdunion : (discBd A ∪ ⋃ j ∈ insert i F, discBd (B j)) =
        (discBd A ∪ ⋃ j ∈ F, discBd (B j)) ∪ discBd (B i) := by
      simp only [Finset.set_biUnion_insert]
      rw [← union_assoc]
      exact union_right_comm (discBd A) (discBd (B i)) (⋃ j ∈ F, discBd (B j))
    refine ⟨D', hd', ?_, hD'U, ?_, ?_⟩
    · rw [hunion]
      rintro z (hz | hz)
      · exact hsub' (Or.inl (hsub hz))
      · exact hsub' (Or.inr hz)
    · rw [hcontact', hunion]
      ext z
      constructor
      · rintro ⟨hz, hzZ⟩
        rcases hz with hzD | hzB
        · have hzK := (show z ∈ (A ∪ ⋃ j ∈ F, B j) ∩ (Z ∪ B i) from
            hcontact ▸ ⟨hzD, Or.inl hzZ⟩).1
          exact ⟨Or.inl hzK, hzZ⟩
        · exact ⟨Or.inr hzB, hzZ⟩
      · rintro ⟨hz, hzZ⟩
        rcases hz with hzK | hzB
        · exact ⟨Or.inl (hsub hzK), hzZ⟩
        · exact ⟨Or.inr hzB, hzZ⟩
    · rw [hbdunion]
      rintro z ⟨hz, hzZ⟩
      apply hbd'
      refine ⟨?_, hzZ⟩
      rcases hz with hzold | hzB
      · exact Or.inl (hbd ⟨hzold, Or.inl hzZ⟩)
      · exact Or.inr hzB

end GraphMinor.GM12
