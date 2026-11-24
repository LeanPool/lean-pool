/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4MarkedDiscMatch
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Matching finite families of discs with two boundary marks

XII (4.3), claim (7), page 251, uses one ambient homeomorphism
for all residual edges. Match the discs successively. After each
step the images of all unmatched source discs remain disjoint from
the discs already placed. The one-disc motion fixes those placed
discs pointwise, preserving their ordered boundary marks.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Match finite disjoint disc families and their ordered pairs of
distinct boundary points, as needed in XII (4.3), claim (7). -/
theorem exists_disc_family_match
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (A B : ι → Set S)
    (hA : ∀ i, IsClosedDisc (A i)) (hB : ∀ i, IsClosedDisc (B i))
    (hAA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hBB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (a b a' b' : ι → S)
    (ha : ∀ i, a i ∈ discBd (A i)) (hb : ∀ i, b i ∈ discBd (A i))
    (hab : ∀ i, a i ≠ b i)
    (ha' : ∀ i, a' i ∈ discBd (B i)) (hb' : ∀ i, b' i ∈ discBd (B i))
    (hab' : ∀ i, a' i ≠ b' i) :
    ∃ e : S ≃ₜ S, ∀ i, e '' A i = B i ∧ e (a i) = a' i ∧ e (b i) = b' i := by
  classical
  have hex : ∀ F : Set ι, F.Finite →
      ∃ e : S ≃ₜ S, ∀ i ∈ F, e '' A i = B i ∧ e (a i) = a' i ∧ e (b i) = b' i := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty => exact ⟨Homeomorph.refl S, by simp⟩
    | @insert i F hi hF ih =>
      obtain ⟨e, he⟩ := ih
      have hnonempty : Nonempty S := ⟨a i⟩
      have himage := isClosedDisc_image_injOn (hA i) (hA i).isCompact
        e.continuous.continuousOn e.injective.injOn
      let D : F → Set S := fun j => B j.val
      have hD : ∀ j, IsClosedDisc (D j) := fun j => hB j.val
      have hDD : Pairwise (fun j k => Disjoint (D j) (D k)) := by
        intro j k hjk
        exact hBB (fun h => hjk (Subtype.ext h))
      have hAD : Disjoint (e '' A i) (⋃ j : F, D j) := by
        apply Set.disjoint_left.mpr
        rintro z ⟨x, hx, rfl⟩ hzD
        obtain ⟨j, hj⟩ := mem_iUnion.mp hzD
        have hjB : e x ∈ B j.val := hj
        obtain ⟨y, hy, hye⟩ := (he j.val j.property).1.symm ▸ hjB
        have hxy : y = x := e.injective hye
        exact Set.disjoint_left.mp (hAA (show i ≠ j.val from fun hij => hi (hij ▸ j.property))) hx
          (hxy ▸ hy)
      have hBD : Disjoint (B i) (⋃ j : F, D j) := by
        apply Set.disjoint_left.mpr
        intro z hzB hzD
        obtain ⟨j, hj⟩ := mem_iUnion.mp hzD
        exact Set.disjoint_left.mp (hBB (show i ≠ j.val from fun hij => hi
          (hij ▸ j.property))) hzB hj
      have hea : e (a i) ∈ discBd (e '' A i) := himage.2 ▸ mem_image_of_mem e (ha i)
      have heb : e (b i) ∈ discBd (e '' A i) := himage.2 ▸ mem_image_of_mem e (hb i)
      obtain ⟨k, hkA, hka, hkb, hkfix⟩ := exists_marked_disc_match_fixing_discs
        hS D hD hDD himage.1 (hB i) hAD hBD hea heb
        (fun h => hab i (e.injective h)) (ha' i) (hb' i) (hab' i)
      refine ⟨e.trans k, ?_⟩
      intro j hj
      rcases hj with hji | hj
      · subst j
        refine ⟨?_, hka, hkb⟩
        change (fun x => k (e x)) '' A i = B i
        simpa only [image_image] using hkA
      · have hBj : k '' B j = B j := by
          apply Set.Subset.antisymm
          · rintro _ ⟨z, hz, rfl⟩
            rw [hkfix ⟨j, hj⟩ z hz]
            exact hz
          · intro z hz
            exact ⟨z, hz, hkfix ⟨j, hj⟩ z hz⟩
        refine ⟨?_, ?_, ?_⟩
        · change (fun x => k (e x)) '' A j = B j
          have h := congrArg (fun C => k '' C) (he j hj).1
          simpa only [image_image, hBj] using h
        · change k (e (a j)) = a' j
          rw [(he j hj).2.1]
          exact hkfix ⟨j, hj⟩ _ (discBd_subset _ (ha' j))
        · change k (e (b j)) = b' j
          rw [(he j hj).2.2]
          exact hkfix ⟨j, hj⟩ _ (discBd_subset _ (hb' j))
  obtain ⟨e, he⟩ := hex univ (Set.toFinite _)
  exact ⟨e, fun i => he i (mem_univ i)⟩

end GraphMinor.GM12
