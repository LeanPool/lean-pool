/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4QuadDiscMatch
import LeanPool.GraphMinor.GM19.MarkedMatch
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Matching all four-marked crossing discs

For XII (4.5), claim (1), page 253, match the finite disc
families one disc at a time. Each new match fixes every disc
already placed, so it preserves the earlier boundary marks.
On each disc the second and fourth marks may exchange places,
which preserves the two opposite crossing pairs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Match finite families of whole crossing discs and four
boundary marks on each, preserving the two opposite pairs.
This is the finite matching construction in XII (4.5), claim
(1), page 253. -/
theorem exists_quad_disc_family_match {S ι : Type}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (A B : ι → Set S)
    (hA : ∀ i, IsClosedDisc (A i)) (hB : ∀ i, IsClosedDisc (B i))
    (hAA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hBB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (p q : ι → Circle → S)
    (hp : ∀ i, Continuous (p i) ∧ Function.Injective (p i) ∧ range (p i) = discBd (A i))
    (hq : ∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (B i))
    (b₀ b₁ b₂ b₃ : ι → ℝ) (hb₀₁ : ∀ i, b₀ i < b₁ i) (hb₁₂ : ∀ i, b₁ i < b₂ i)
    (hb₂₃ : ∀ i, b₂ i < b₃ i) (hb₃ : ∀ i, b₃ i < b₀ i + 1) :
    ∃ e : S ≃ₜ S, ∀ i, e '' A i = B i ∧
      ((e (p i (ee 0)) = q i (ee (b₀ i)) ∧ e (p i (ee (1 / 4))) = q i (ee (b₁ i)) ∧
        e (p i (ee (1 / 2))) = q i (ee (b₂ i)) ∧ e (p i (ee (3 / 4))) = q i (ee (b₃ i))) ∨
       (e (p i (ee 0)) = q i (ee (b₀ i)) ∧ e (p i (ee (1 / 4))) = q i (ee (b₃ i)) ∧
        e (p i (ee (1 / 2))) = q i (ee (b₂ i)) ∧ e (p i (ee (3 / 4))) = q i (ee (b₁ i)))) := by
  classical
  let Good := fun (e : S ≃ₜ S) i => e '' A i = B i ∧
    ((e (p i (ee 0)) = q i (ee (b₀ i)) ∧ e (p i (ee (1 / 4))) = q i (ee (b₁ i)) ∧
      e (p i (ee (1 / 2))) = q i (ee (b₂ i)) ∧ e (p i (ee (3 / 4))) = q i (ee (b₃ i))) ∨
     (e (p i (ee 0)) = q i (ee (b₀ i)) ∧ e (p i (ee (1 / 4))) = q i (ee (b₃ i)) ∧
      e (p i (ee (1 / 2))) = q i (ee (b₂ i)) ∧ e (p i (ee (3 / 4))) = q i (ee (b₁ i))))
  change ∃ e, ∀ i, Good e i
  have hex : ∀ F : Set ι, F.Finite → ∃ e : S ≃ₜ S, ∀ i ∈ F, Good e i := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty => exact ⟨Homeomorph.refl S, by simp⟩
    | @insert i F hi hF ih =>
      obtain ⟨e, he⟩ := ih
      have himage := (hA i).image e.continuous.continuousOn e.symm.continuous.continuousOn
        (fun z _ => e.symm_apply_apply z)
      let D : F → Set S := fun j => B j.val
      have hD : ∀ j, IsClosedDisc (D j) := fun j => hB j.val
      have hDD : Pairwise (fun j k => Disjoint (D j) (D k)) := by
        intro j k hjk
        exact hBB (fun h => hjk (Subtype.ext h))
      have hAD : Disjoint (e '' A i) (⋃ j : F, D j) := by
        apply disjoint_left.mpr
        rintro z ⟨x, hx, rfl⟩ hzD
        obtain ⟨j, hj⟩ := mem_iUnion.mp hzD
        have hjB : e x ∈ B j.val := hj
        obtain ⟨y, hy, hye⟩ := (he j.val j.property).1.symm ▸ hjB
        have hxy : y = x := e.injective hye
        exact disjoint_left.mp (hAA (show i ≠ j.val from fun hij => hi (hij ▸ j.property))) hx
          (hxy ▸ hy)
      have hBD : Disjoint (B i) (⋃ j : F, D j) := by
        apply disjoint_left.mpr
        intro z hzB hzD
        obtain ⟨j, hj⟩ := mem_iUnion.mp hzD
        exact disjoint_left.mp (hBB (show i ≠ j.val from fun hij => hi (hij ▸ j.property))) hzB hj
      have hpI : GM19.IsBdParam (A i) (p i) := hp i
      have hpimage := hpI.image e (hA i)
      obtain ⟨k, hkA, hkmarks, hkfix⟩ := exists_quad_disc_match_fixing_discs hS D hD hDD
        himage.1 (hB i) hAD hBD (fun w => e (p i w)) (q i) hpimage (hq i)
        (hb₀₁ i) (hb₁₂ i) (hb₂₃ i) (hb₃ i)
      refine ⟨e.trans k, ?_⟩
      intro j hj
      rcases hj with hji | hj
      · subst j
        refine ⟨?_, hkmarks⟩
        change (fun z => k (e z)) '' A i = B i
        simpa only [image_image] using hkA
      · have hBj : k '' B j = B j := by
          apply Subset.antisymm
          · rintro _ ⟨z, hz, rfl⟩
            rw [hkfix ⟨j, hj⟩ z hz]
            exact hz
          · intro z hz
            exact ⟨z, hz, hkfix ⟨j, hj⟩ z hz⟩
        have hkeep : ∀ w : Circle, k (e (p j w)) = e (p j w) := by
          intro w
          apply hkfix ⟨j, hj⟩
          change e (p j w) ∈ B j
          have hpbd : p j w ∈ discBd (A j) := (hp j).2.2 ▸ mem_range_self w
          exact (he j hj).1 ▸ mem_image_of_mem e (discBd_subset _ hpbd)
        refine ⟨?_, ?_⟩
        · change (fun z => k (e z)) '' A j = B j
          have h := congrArg (fun C => k '' C) (he j hj).1
          simpa only [image_image, hBj] using h
        · simpa only [Homeomorph.trans_apply, hkeep] using (he j hj).2
  obtain ⟨e, he⟩ := hex univ (Set.toFinite _)
  exact ⟨e, fun i => he i (mem_univ i)⟩

end GraphMinor.GM12
