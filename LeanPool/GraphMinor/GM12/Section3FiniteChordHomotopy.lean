/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ReplaceChordHomotopy

/-!
# Removing finitely many homotopically redundant chords

For the extraction used by XII (3.1), page 245, complete gaps of an
injective path have disjoint interiors. If each chord is homotopic to
a path in the first circle, remove the chords one at a time. The
one-chord pasting lemma preserves the homotopy of any path in the
carrier. After the finite induction, the resulting path stays in
the first circle.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Finitely many chords, meeting one another only in the closed base,
can all be removed from a path when each is homotopic into the base. -/
theorem exists_homotopic_path_in_base_of_finite_chords
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    {F : Set S} (hF : IsClosed F) (a b : ι → S)
    (c r : ∀ i, Path (a i) (b i))
    (hci : ∀ i, Function.Injective (c i))
    (hmeet : ∀ i, range (c i) ∩ F ⊆ {a i, b i})
    (hdisj : ∀ i j, i ≠ j → range (c i) ∩ range (c j) ⊆ F)
    (hcr : ∀ i, (c i).Homotopic (r i)) (hrF : ∀ i, range (r i) ⊆ F)
    (K : Finset ι) {x y : S} (q : Path x y) (hx : x ∈ F) (hy : y ∈ F)
    (hq : range q ⊆ F ∪ ⋃ i ∈ K, range (c i)) :
    ∃ q' : Path x y, q.Homotopic q' ∧ range q' ⊆ F := by
  classical
  induction K using Finset.induction_on generalizing q with
  | empty =>
    refine ⟨q, Path.Homotopic.refl q, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hq
  | @insert i K hi ih =>
    let B := F ∪ ⋃ k ∈ K, range (c k)
    have hBc : IsClosed B := hF.union (isClosed_biUnion_finset
      (fun k _ => (isCompact_range (c k).continuous).isClosed))
    have hFB : F ⊆ B := subset_union_left
    have hmeetB : range (c i) ∩ B ⊆ {a i, b i} := by
      rintro z ⟨hzi, hzF | hzK⟩
      · exact hmeet i ⟨hzi, hzF⟩
      · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hzK
        have hik : i ≠ k := fun he => hi (he.symm ▸ hk)
        exact hmeet i ⟨hzi, hdisj i k hik ⟨hzi, hzk⟩⟩
    have hqB : range q ⊆ B ∪ range (c i) := by
      intro z hz
      rcases hq hz with hzF | hzK
      · exact Or.inl (Or.inl hzF)
      · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hzK
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inr hzk
        · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨k, hk, hzk⟩))
    have hrB : range (r i) ⊆ (ContinuousMap.id S) '' B := by
      simpa only [ContinuousMap.coe_id, image_id] using (hrF i).trans hFB
    obtain ⟨q', hqq', hq'⟩ := exists_homotopic_path_after_replacing_chord hBc
      (c i) (hci i) hmeetB (ContinuousMap.id S) (r i) (hcr i) hrB q hqB (hFB hx) (hFB hy)
    change q.Homotopic q' at hqq'
    have hq'B : range q' ⊆ B := by
      simpa only [ContinuousMap.coe_id, image_id] using hq'
    obtain ⟨q'', hq'q'', hq''⟩ := ih q' hq'B
    exact ⟨q'', hqq'.trans hq'q'', hq''⟩

end GraphMinor.GM12
