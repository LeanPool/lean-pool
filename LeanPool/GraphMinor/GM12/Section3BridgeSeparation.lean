/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Cutting the bridge of the first two-loop shape

For the Section 8 argument used by XII (3.1), page 245, cut the joining
line at its midpoint. The first circle together with the first half
and the second circle together with the second half are closed sets
meeting only at that midpoint. The attachment points lie on opposite
sides. A circle containing the bridge would therefore become disconnected
when its midpoint is removed.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Cutting the joining line of two disjoint circles gives a closed
separation whose intersection is one point and whose sides separate
the two attachment points. -/
theorem exists_closed_separation_of_joining_line
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A P : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A)
    (hP : IsLineWithEnds P a b) (ha : a ∈ F) (hb : b ∈ A)
    (hPF : P ∩ F = {a}) (hPA : P ∩ A = {b}) :
    ∃ p U V, IsClosed U ∧ IsClosed V ∧ U ∪ V = F ∪ A ∪ P ∧ U ∩ V = {p} ∧
      a ∈ U ∧ a ∉ V ∧ b ∈ V ∧ b ∉ U := by
  obtain ⟨φ, hφ0, hφ1⟩ := hP
  let g : unitInterval → S := fun s => (φ s).val
  have hgc : Continuous g := continuous_subtype_val.comp φ.continuous
  have hgi : Function.Injective g := fun s t he => φ.injective (Subtype.ext he)
  have hg0 : g 0 = a := hφ0
  have hg1 : g 1 = b := hφ1
  have hgP : range g = P := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (φ s).property
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
  let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have ht0 : (0 : unitInterval) < t := by change (0 : ℝ) < 1 / 2; norm_num
  have ht1 : t < (1 : unitInterval) := by change (1 / 2 : ℝ) < 1; norm_num
  let L := g '' Iic t
  let R := g '' Ici t
  have hLc : IsClosed L := (isClosed_Iic.isCompact.image hgc).isClosed
  have hRc : IsClosed R := (isClosed_Ici.isCompact.image hgc).isClosed
  have hLa : a ∈ L := ⟨0, ht0.le, hg0⟩
  have hRb : b ∈ R := ⟨1, ht1.le, hg1⟩
  have hRa : a ∉ R := by
    rintro ⟨s, hs, hgs⟩
    have hs0 := hgi (hgs.trans hg0.symm)
    rw [hs0] at hs
    exact ht0.not_ge hs
  have hLb : b ∉ L := by
    rintro ⟨s, hs, hgs⟩
    have hs1 := hgi (hgs.trans hg1.symm)
    rw [hs1] at hs
    exact ht1.not_ge hs
  have hLP : L ⊆ P := (image_subset_range _ _).trans hgP.le
  have hRP : R ⊆ P := (image_subset_range _ _).trans hgP.le
  have hFR : Disjoint F R := by
    apply Set.disjoint_left.mpr
    intro x hxF hxR
    have hx : x ∈ P ∩ F := ⟨hRP hxR, hxF⟩
    rw [hPF] at hx
    have hxa : x = a := hx
    exact hRa (hxa ▸ hxR)
  have hLA : Disjoint L A := by
    apply Set.disjoint_left.mpr
    intro x hxL hxA
    have hx : x ∈ P ∩ A := ⟨hLP hxL, hxA⟩
    rw [hPA] at hx
    have hxb : x = b := hx
    exact hLb (hxb ▸ hxL)
  have hLR : L ∩ R = {g t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, ⟨r, hr, he⟩⟩
      have hrs := hgi he
      have hts : t ≤ s := hrs ▸ hr
      exact congrArg g (le_antisymm hs hts)
    · intro x hx
      rw [show x = g t from hx]
      exact ⟨⟨t, le_rfl, rfl⟩, ⟨t, le_rfl, rfl⟩⟩
  have hcover : L ∪ R = P := by
    apply Subset.antisymm (union_subset hLP hRP)
    intro x hx
    obtain ⟨s, rfl⟩ := hgP.symm ▸ hx
    rcases le_total s t with hst | hts
    · exact Or.inl ⟨s, hst, rfl⟩
    · exact Or.inr ⟨s, hts, rfl⟩
  refine ⟨g t, F ∪ L, A ∪ R, hF.isCompact.isClosed.union hLc,
    hA.isCompact.isClosed.union hRc, ?_, ?_, Or.inl ha, ?_, Or.inl hb, ?_⟩
  · rw [← hcover]
    ac_rfl
  · apply Subset.antisymm
    · rintro x ⟨hxF | hxL, hxA | hxR⟩
      · exact False.elim (Set.disjoint_left.mp hdis hxF hxA)
      · exact False.elim (Set.disjoint_left.mp hFR hxF hxR)
      · exact False.elim (Set.disjoint_left.mp hLA hxL hxA)
      · exact hLR ▸ (show x ∈ L ∩ R from ⟨hxL, hxR⟩)
    · intro x hx
      have hxLR : x ∈ L ∩ R := hLR.symm ▸ hx
      exact ⟨Or.inr hxLR.1, Or.inr hxLR.2⟩
  · rintro (haA | haR)
    · exact Set.disjoint_left.mp hdis ha haA
    · exact hRa haR
  · rintro (hbF | hbL)
    · exact Set.disjoint_left.mp hdis hbF hb
    · exact hLb hbL

end GraphMinor.GM12
