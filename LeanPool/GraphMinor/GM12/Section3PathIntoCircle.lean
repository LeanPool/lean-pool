/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DistinctCompleteChords
public import LeanPool.GraphMinor.GM12.Section3PlanarChordHomotopy
import LeanPool.GraphMinor.GM12.Section3FiniteChordHomotopy
import LeanPool.GraphMinor.GM12.Section3FiniteGraphSolid

/-!
# Moving a path into a circle using its planar chords

For the extraction used by XII (3.1), page 245, first replace the
injective path by a homotopic path in the circle and finitely many
complete chords. Planarity of each chord together with the circle
makes that chord homotopic into the circle. Their interiors are
disjoint, so finite chord removal moves the entire path into the
circle without changing its fixed-end homotopy class.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- If every complete chord of an injective path is planar together
with the circle after an embedding, the image path is homotopic into
the image circle. -/
theorem exists_homotopic_path_in_circle_of_planar_chords
    {S T : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
    (hS : IsSurface S) {F : Set S} (hF : IsOArc F)
    {a b : S} (p : Path a b) (hpi : Function.Injective p) (ha : a ∈ F) (hb : b ∈ F)
    (j : C(S, T)) (hj : IsEmbedding j)
    (hchord : ∀ l r : unitInterval, l < r → p l ∈ F → p r ∈ F →
      Disjoint (p '' Ioo l r) F → IsPlanar (j '' (F ∪ p '' Icc l r))) :
    ∃ r : Path (j a) (j b), (p.map j.continuous).Homotopic r ∧ range r ⊆ j '' F := by
  classical
  obtain ⟨J, q, hpq, hq, hvalid, hdisj⟩ :=
    exists_homotopic_path_in_distinct_complete_chords hS (isSolid_oArc hF) p hpi ha hb
  let I := {g : unitInterval × unitInterval // g ∈ J}
  let : Fintype I := J.finite_toSet.fintype
  let c₀ : ∀ i : I, Path (p i.val.1) (p i.val.2) := fun i => p.subpath i.val.1 i.val.2
  let c : ∀ i : I, Path (j (p i.val.1)) (j (p i.val.2)) := fun i => (c₀ i).map j.continuous
  have hc₀i : ∀ i : I, Function.Injective (c₀ i) := by
    intro i
    exact hpi.comp (lerpI_injective (hvalid i.val i.property).1.ne)
  have hci : ∀ i : I, Function.Injective (c i) := fun i => hj.injective.comp (hc₀i i)
  have hc₀range : ∀ i : I, range (c₀ i) = p '' Icc i.val.1 i.val.2 :=
    fun i => Path.range_subpath_of_le p _ _ (hvalid i.val i.property).1.le
  have hcrange : ∀ i : I, range (c i) = j '' (p '' Icc i.val.1 i.val.2) := by
    intro i
    change range (j ∘ c₀ i) = _
    rw [range_comp, hc₀range]
  have hex : ∀ i : I, ∃ r : Path (j (p i.val.1)) (j (p i.val.2)),
      (c i).Homotopic r ∧ range r ⊆ j '' F := by
    intro i
    have hi := hvalid i.val i.property
    have hplan := hchord i.val.1 i.val.2 hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    rw [← hc₀range i] at hplan
    exact exists_homotopic_path_in_oArc_of_planar_chord hF (c₀ i) (hc₀i i)
      hi.2.1 hi.2.2.1 j hplan
  choose r hcr hrF using hex
  have hmeet : ∀ i : I, range (c i) ∩ (j '' F) ⊆ {j (p i.val.1), j (p i.val.2)} := by
    intro i z hz
    rw [hcrange] at hz
    obtain ⟨w, ⟨t, ht, rfl⟩, rfl⟩ := hz.1
    obtain ⟨v, hvF, he⟩ := hz.2
    have hpF : p t ∈ F := (hj.injective he) ▸ hvF
    have hi := hvalid i.val i.property
    by_cases htl : t = i.val.1
    · exact Or.inl (congrArg (fun t => j (p t)) htl)
    · by_cases htr : t = i.val.2
      · exact Or.inr (congrArg (fun t => j (p t)) htr)
      · have htopen : t ∈ Ioo i.val.1 i.val.2 :=
          ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
        exact (disjoint_left.mp hi.2.2.2 ⟨t, htopen, rfl⟩ hpF).elim
  have hdisj' : ∀ i k : I, i ≠ k → range (c i) ∩ range (c k) ⊆ j '' F := by
    intro i k hik z hz
    rw [hcrange i, hcrange k] at hz
    obtain ⟨v, hv, rfl⟩ := hz.1
    obtain ⟨w, hw, he⟩ := hz.2
    have hwv : w = v := hj.injective he
    have hiv : i.val ≠ k.val := fun he => hik (Subtype.ext he)
    exact ⟨v, hdisj i.val i.property k.val k.property hiv ⟨hv, hwv ▸ hw⟩, rfl⟩
  have hq' : range (q.map j.continuous) ⊆
      (j '' F) ∪ ⋃ i ∈ (Finset.univ : Finset I), range (c i) := by
    rintro z ⟨t, rfl⟩
    rcases hq (mem_range_self t) with htF | htJ
    · exact Or.inl ⟨q t, htF, rfl⟩
    · obtain ⟨g, hg, htg⟩ := mem_iUnion₂.mp htJ
      let i : I := ⟨g, hg⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i,
        (hcrange i).symm ▸ (show j (q t) ∈ j '' (p '' Icc g.1 g.2) from ⟨q t, htg, rfl⟩)⟩)
  obtain ⟨r', hqr', hr'⟩ := exists_homotopic_path_in_base_of_finite_chords
    (hF.isCompact.image j.continuous).isClosed (fun i : I => j (p i.val.1))
    (fun i : I => j (p i.val.2)) c r hci hmeet hdisj' hcr hrF Finset.univ
    (q.map j.continuous) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hq'
  exact ⟨r', (hpq.map j).trans hqr', hr'⟩

end GraphMinor.GM12
