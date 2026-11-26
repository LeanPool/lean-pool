/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Closed subsets of a circle inside an arc

For the region preparation in XII (4.5), page 253, a proper
closed part of a circle with two distinct points lies in a
simple arc. Cut out the open complementary arc around a point
outside the closed set, and keep the other arc.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A compact proper part of a simple closed curve, with at
least two points, lies in a simple arc of that curve. -/
theorem exists_arc_containing_compact_circle_subset
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {C F : Set S} (hC : IsOArc C) (hF : IsCompact F)
    (hFC : F ⊆ C) (hne : F.Nontrivial) {p : S}
    (hp : p ∈ C) (hpF : p ∉ F) :
    ∃ L : Set S, ∃ a b : S,
      IsLineWithEnds L a b ∧ F ⊆ L ∧ L ⊆ C := by
  obtain ⟨φ⟩ := hC
  let T : Set Circle := (fun w : Circle => (φ w).val) ⁻¹' F
  have hTc : IsClosed T := hF.isClosed.preimage
    (continuous_subtype_val.comp φ.continuous)
  let z : Circle := φ.symm ⟨p, hp⟩
  have hz : z ∉ T := by simpa [T, z] using hpF
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  let u : Circle := φ.symm ⟨x, hFC hx⟩
  let v : Circle := φ.symm ⟨y, hFC hy⟩
  have hu : u ∈ T := by simpa [T, u] using hx
  have hv : v ∈ T := by simpa [T, v] using hy
  have huv : u ≠ v := fun h => hxy
    (congrArg Subtype.val (φ.symm.injective h))
  obtain ⟨a, b, hab, hr, ha, hb, hint, -⟩ :=
    exists_circle_chord hTc hz hu hv huv
  have hTb : T ⊆ range b := by
    intro w hw
    have hwab : w ∈ range a ∪ range b := hr.symm ▸ mem_univ w
    rcases hwab with ⟨t, rfl⟩ | hw
    · by_cases h0 : t = 0
      · subst t
        exact ⟨0, hab.3⟩
      by_cases h1 : t = 1
      · subst t
        exact ⟨1, hab.4⟩
      exact False.elim (hint t h0 h1 hw)
    · exact hw
  let g : unitInterval → S := fun t => (φ (b t)).val
  have hg : IsArcMap g :=
    ⟨(continuous_subtype_val.comp φ.continuous).comp hab.2.1,
      fun s t h => hab.2.2 (φ.injective (Subtype.ext h))⟩
  refine ⟨range g, g 0, g 1, hg.isLineWithEnds, ?_, ?_⟩
  · intro w hw
    have hwT : φ.symm ⟨w, hFC hw⟩ ∈ T := by simpa [T] using hw
    obtain ⟨t, ht⟩ := hTb hwT
    exact ⟨t, by simp [g, ht]⟩
  · rintro w ⟨t, rfl⟩
    exact (φ (b t)).property


/-- The same arc containment, including a one-point closed set. -/
theorem exists_arc_containing_nonempty_compact_circle_subset
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {C F : Set S} (hC : IsOArc C) (hF : IsCompact F)
    (hFC : F ⊆ C) (hne : F.Nonempty) {p : S}
    (hp : p ∈ C) (hpF : p ∉ F) :
    ∃ L : Set S, ∃ a b : S,
      IsLineWithEnds L a b ∧ F ⊆ L ∧ L ⊆ C := by
  rcases F.subsingleton_or_nontrivial with hs | hn
  · obtain ⟨q, hq⟩ := hne
    have hqp : q ≠ p := fun h => hpF (h ▸ hq)
    obtain ⟨a, b, hab, ha, hb, hr⟩ := hC.exists_arcs (hFC hq) hp hqp
    refine ⟨range a, a 0, a 1, hab.1.isLineWithEnds, ?_, ?_⟩
    · intro w hw
      exact ⟨0, ha.trans (hs hq hw)⟩
    · exact subset_union_left.trans hr.subset
  · exact exists_arc_containing_compact_circle_subset hC hF hFC hn hp hpF

end GraphMinor.GM12
