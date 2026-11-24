/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Connected.Clopen

/-!
# Connectedness after removing disjoint discs

The space used in XII (3.1), page 245, remains connected. A closed
separation of that space would extend across each deleted disc,
because its intersection with the remaining space is connected.
Finitely many closed fillings would then separate the original space.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- Removing finitely many disjoint closed fillings preserves
preconnectedness when each filling meets the remaining closed set
in a preconnected set. -/
theorem isPreconnected_of_finite_fillings
    {S ι : Type*} [TopologicalSpace S] [PreconnectedSpace S] [Finite ι]
    {C : Set S} (hC : IsClosed C) (D : ι → Set S)
    (hD : ∀ i, IsClosed (D i))
    (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hbd : ∀ i, IsPreconnected (C ∩ D i))
    (hcover : univ ⊆ C ∪ ⋃ i, D i) : IsPreconnected C := by
  classical
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hC).mpr
  intro A B hA hB hAB hdisAB
  have choices : ∀ i, C ∩ D i ⊆ A ∨ C ∩ D i ⊆ B := by
    intro i
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (hbd i) A B hA hB
    · exact inter_subset_left.trans hAB
    · rw [hdisAB.inter_eq, inter_empty]
  let P : ι → Prop := fun i => C ∩ D i ⊆ A
  let A' : Set S := (C ∩ A) ∪ ⋃ i : {i // P i}, D i.val
  let B' : Set S := (C ∩ B) ∪ ⋃ i : {i // ¬ P i}, D i.val
  have hA' : IsClosed A' := (hC.inter hA).union
    (isClosed_iUnion_of_finite fun i => hD i.val)
  have hB' : IsClosed B' := (hC.inter hB).union
    (isClosed_iUnion_of_finite fun i => hD i.val)
  have hcover' : univ ⊆ A' ∪ B' := by
    intro x _
    rcases hcover (mem_univ x) with hxC | hxD
    · rcases hAB hxC with hxA | hxB
      · exact Or.inl (Or.inl ⟨hxC, hxA⟩)
      · exact Or.inr (Or.inl ⟨hxC, hxB⟩)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      by_cases hi : P i
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩))
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩))
  have hdis' : Disjoint A' B' := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
    · exact Set.disjoint_left.mp hdisAB hxA.2 hxB.2
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxB
      have hjB := (choices j.val).resolve_left j.property
      exact Set.disjoint_left.mp hdisAB hxA.2 (hjB ⟨hxA.1, hxj⟩)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
      exact Set.disjoint_left.mp hdisAB (i.property ⟨hxB.1, hxi⟩) hxB.2
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxB
      by_cases hij : i.val = j.val
      · exact j.property (hij ▸ i.property)
      · exact Set.disjoint_left.mp (hdisj hij) hxi hxj
  have hwhole := isPreconnected_iff_subset_of_disjoint_closed.mp
    isPreconnected_univ A' B' hA' hB' hcover' (by rw [hdis'.inter_eq, inter_empty])
  rcases hwhole with hwhole | hwhole
  · left
    intro x hxC
    rcases hwhole (mem_univ x) with hxA | hxD
    · exact hxA.2
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      exact i.property ⟨hxC, hxi⟩
  · right
    intro x hxC
    rcases hwhole (mem_univ x) with hxB | hxD
    · exact hxB.2
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      exact (choices i.val).resolve_left i.property ⟨hxC, hxi⟩

end GraphMinor.GM12
