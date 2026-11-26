/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedSurface

/-!
# Filling one of the deleted discs

To compare the cuffs in XII (3.1), page 245, with the capped surfaces
of VII, fill one disc and retain the other deletions. The resulting
space is exactly the union of Sigma-star and that disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Omitting one disc from the deletion fills exactly that disc. -/
theorem discComplement_except_eq_union
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (i : ι) :
    discComplement (fun j : {j // j ≠ i} => Δ j.val) = discComplement Δ ∪ Δ i := by
  classical
  let B : Set S := ⋃ j : {j // j ≠ i}, Δ j.val
  have hsmall : (⋃ j, Δ j)ᶜ ⊆ Bᶜ := by
    intro x hx hB
    obtain ⟨j, hj⟩ := mem_iUnion.mp hB
    exact hx (mem_iUnion.mpr ⟨j.val, hj⟩)
  apply Subset.antisymm
  · intro x hx
    by_cases hxi : x ∈ Δ i
    · exact Or.inr hxi
    · left
      apply mem_closure_iff.mpr
      intro O hO hxO
      obtain ⟨y, hyO, hyB⟩ := mem_closure_iff.mp hx
        (O ∩ (Δ i)ᶜ) (hO.inter (hΔ i).isCompact.isClosed.isOpen_compl) ⟨hxO, hxi⟩
      refine ⟨y, hyO.1, ?_⟩
      intro hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · exact hyO.2 (hji ▸ hj)
      · exact hyB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  · intro x hx
    rcases hx with hx | hx
    · exact closure_mono hsmall hx
    · apply subset_closure
      intro hxB
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
      exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj

end GraphMinor.GM12
