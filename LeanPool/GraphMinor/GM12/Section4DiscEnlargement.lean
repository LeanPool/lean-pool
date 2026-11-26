/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar

/-!
# Enlarging disjoint discs away from a closed set

For XII (4.3), claim (7), page 251, motions must avoid discs
already placed. Enlarge a finite disjoint family slightly, keeping
it disjoint and avoiding any prescribed closed set. At each step,
first enlarge the other discs while forbidding the current one.
Then enlarge the current disc while forbidding those enlargements.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Enlarge one disc away from a disjoint closed set. -/
theorem exists_disc_enlargement_avoiding
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {D B : Set S} (hD : IsClosedDisc D)
    (hB : IsClosed B) (hDB : Disjoint D B) :
    ∃ E, IsClosedDisc E ∧ D ⊆ E \ discBd E ∧ Disjoint E B := by
  obtain ⟨E, hE, hDE, hED⟩ := exists_disc_around
    (fun x => (hS.2.2 x).isManifoldPoint) hD
    (fun x _ => hS.2.2 x) hB.isOpen_compl
    (fun x hx => Set.disjoint_left.mp hDB (discBd_subset D hx))
  refine ⟨E, hE, hDE, Set.disjoint_left.mpr ?_⟩
  intro x hxE hxB
  rcases hED hxE with hxD | hxnot
  · exact Set.disjoint_left.mp hDB hxD hxB
  · exact hxnot hxB

/-- Simultaneously enlarge a finite disjoint family while keeping
it disjoint and avoiding an arbitrary disjoint closed set. -/
theorem exists_disjoint_disc_enlargements
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {F : Set ι} (hF : F.Finite) (D : ι → Set S)
    (hD : ∀ i ∈ F, IsClosedDisc (D i))
    (hDD : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (D i) (D j)) :
    ∀ B : Set S, IsClosed B → (∀ i ∈ F, Disjoint (D i) B) →
    ∃ E : ι → Set S,
      (∀ i ∈ F, IsClosedDisc (E i) ∧ D i ⊆ E i \ discBd (E i) ∧ Disjoint (E i) B) ∧
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (E i) (E j) := by
  classical
  revert hD hDD
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    intro _ _ B _ _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert i F hi hF ih =>
    intro hD hDD B hB hDB
    have hD' := fun j hj => hD j (Or.inr hj)
    have hDD' := fun j hj k hk hjk => hDD j (Or.inr hj) k (Or.inr hk) hjk
    have hDB' : ∀ j ∈ F, Disjoint (D j) (B ∪ D i) := by
      intro j hj
      exact (hDB j (Or.inr hj)).union_right
        (hDD j (Or.inr hj) i (Or.inl rfl) (fun h => hi (h ▸ hj)))
    obtain ⟨E, hE, hEE⟩ := ih hD' hDD' (B ∪ D i)
      (hB.union (hD i (Or.inl rfl)).isClosed) hDB'
    let Z := B ∪ ⋃ j ∈ F, E j
    have hZ : IsClosed Z := hB.union (hF.isClosed_biUnion fun j hj => (hE j hj).1.isClosed)
    have hDiZ : Disjoint (D i) Z := by
      apply Set.disjoint_left.mpr
      intro x hxD hxZ
      rcases hxZ with hxB | hxE
      · exact Set.disjoint_left.mp (hDB i (Or.inl rfl)) hxD hxB
      · obtain ⟨j, hj, hxEj⟩ := mem_iUnion₂.mp hxE
        exact Set.disjoint_left.mp (hE j hj).2.2 hxEj (Or.inr hxD)
    obtain ⟨Q, hQ, hDQ, hQZ⟩ := exists_disc_enlargement_avoiding hS
      (hD i (Or.inl rfl)) hZ hDiZ
    have hQB : Disjoint Q B := hQZ.mono_right subset_union_left
    have hQE : ∀ j ∈ F, Disjoint Q (E j) := by
      intro j hj
      exact hQZ.mono_right (fun x hx => Or.inr (mem_iUnion₂.mpr ⟨j, hj, hx⟩))
    let E' := fun j => if j = i then Q else E j
    refine ⟨E', ?_, ?_⟩
    · intro j hj
      rcases hj with hji | hj
      · subst j
        simpa only [E', ↓reduceIte] using And.intro hQ (And.intro hDQ hQB)
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        have hjB : Disjoint (E j) B := (hE j hj).2.2.mono_right subset_union_left
        simpa only [E', hji, ↓reduceIte] using
          And.intro (hE j hj).1 (And.intro (hE j hj).2.1 hjB)
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        have hki := Ne.symm hjk
        simpa only [E', ↓reduceIte, hki] using hQE k (hk.resolve_left hki)
      · by_cases hki : k = i
        · subst k
          simpa only [E', ↓reduceIte, hji] using (hQE j (hj.resolve_left hji)).symm
        · simpa only [E', hji, hki, ↓reduceIte] using
            hEE j (hj.resolve_left hji) k (hk.resolve_left hki) hjk

end GraphMinor.GM12
