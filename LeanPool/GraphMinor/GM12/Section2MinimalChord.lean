/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ChordGap
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# A minimal line between components of a closed set in a region

In Case 2 of XII (2.1), page 244, the intersection of the circle with
a region is not connected. Separate that relatively closed set into
two closed pieces, join points of those pieces through the region,
and select the gap between the last point of the first piece and the
first point of the second. Its ends belong to different components.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The minimal line required in Case 2 of XII (2.1), page 244, exists
in any path-connected region where the intersection with the closed
curve is disconnected. No finiteness of its components is needed. -/
theorem exists_minimal_chord_between_components {S : Type*} [TopologicalSpace S] [T2Space S]
    {r F : Set S} (hr : IsPathConnected r) (hF : IsClosed F)
    (hdisconn : ¬ IsPreconnected (F ∩ r)) :
    ∃ (L : Set S) (a b : S), IsLineWithEnds L a b ∧ L ⊆ r ∧
      a ∈ F ∩ r ∧ b ∈ F ∩ r ∧ Disjoint (L \ {a, b}) F ∧
      connectedComponentIn (F ∩ r) a ≠ connectedComponentIn (F ∩ r) b := by
  classical
  let A : Set r := (Subtype.val : r → S) ⁻¹' F
  have hA : IsClosed A := hF.preimage continuous_subtype_val
  have hnot : ¬ IsPreconnected A := by
    intro hp
    have hm := hp.image Subtype.val continuous_subtype_val.continuousOn
    rw [Subtype.image_preimage_coe, inter_comm] at hm
    exact hdisconn hm
  rw [isPreconnected_closed_iff] at hnot
  push Not at hnot
  obtain ⟨U, V, hU, hV, hcover, hAU, hAV, hnone⟩ := hnot
  let C := A ∩ U
  let D := A ∩ V
  have hC : IsClosed C := hA.inter hU
  have hD : IsClosed D := hA.inter hV
  have hCD : Disjoint C D := Set.disjoint_left.mpr fun z hzC hzD => by
    have hm : z ∈ A ∩ (U ∩ V) := ⟨hzC.1, hzC.2, hzD.2⟩
    rw [hnone] at hm
    exact hm
  obtain ⟨x, hx⟩ := hAU
  obtain ⟨y, hy⟩ := hAV
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hCD hx (h.symm ▸ hy)
  have : PathConnectedSpace r := isPathConnected_iff_pathConnectedSpace.mp hr
  let p := PathConnectedSpace.somePath x y
  obtain ⟨g, hg, hgi, hg0, hg1, _⟩ := exists_arc_of_path p.continuous (by
    rw [p.source, p.target]
    exact hxy)
  have h0 : g 0 ∈ C := by rw [hg0, p.source]; exact hx
  have h1 : g 1 ∈ D := by rw [hg1, p.target]; exact hy
  obtain ⟨s, t, hst, hsC, htD, hgap⟩ := exists_parameter_gap (hC.preimage hg)
    (hD.preimage hg) hCD h0 h1
  let q : unitInterval → S := fun u => (g u).val
  have hq : Continuous q := continuous_subtype_val.comp hg
  have hqi : Function.Injective q := Subtype.val_injective.comp hgi
  have hsF : q s ∈ F ∩ r := ⟨hsC.1, (g s).property⟩
  have htF : q t ∈ F ∩ r := ⟨htD.1, (g t).property⟩
  refine ⟨q '' Icc s t, q s, q t, isLine_piece hq hqi hst, ?_, hsF, htF,
    Set.disjoint_left.mpr ?_, ?_⟩
  · rintro z ⟨u, _, rfl⟩
    exact (g u).property
  · rintro z ⟨⟨u, hu, rfl⟩, hends⟩ huF
    have hsu : s < u := lt_of_le_of_ne hu.1 (by
      intro heq
      exact hends (Or.inl (congrArg q heq.symm)))
    have hut : u < t := lt_of_le_of_ne hu.2 (by
      intro heq
      exact hends (Or.inr (congrArg q heq)))
    have huA : g u ∈ A := huF
    rcases hcover huA with huU | huV
    · exact hgap u ⟨hsu, hut⟩ (Or.inl ⟨huA, huU⟩)
    · exact hgap u ⟨hsu, hut⟩ (Or.inr ⟨huA, huV⟩)
  · intro heq
    let K := connectedComponentIn (F ∩ r) (q s)
    have hKsub : K ⊆ F ∩ r := connectedComponentIn_subset _ _
    have hKr : K ⊆ r := fun z hz => (hKsub hz).2
    have hpre : IsPreconnected ((Subtype.val : r → S) ⁻¹' K) := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hKr]
      exact isPreconnected_connectedComponentIn
    have hKtoA : ∀ z : r, z.val ∈ K → z ∈ A := fun z hz => (hKsub hz).1
    have hKcov : (Subtype.val : r → S) ⁻¹' K ⊆ U ∪ V := fun z hz => hcover (hKtoA z hz)
    have hsK : (g s).val ∈ K := mem_connectedComponentIn hsF
    have htK : (g t).val ∈ K := by
      change q t ∈ connectedComponentIn (F ∩ r) (q s)
      rw [heq]
      exact mem_connectedComponentIn htF
    obtain ⟨z, hzK, hzU, hzV⟩ := isPreconnected_closed_iff.mp hpre U V hU hV hKcov
      ⟨g s, hsK, hsC.2⟩ ⟨g t, htK, htD.2⟩
    have hm : z ∈ A ∩ (U ∩ V) := ⟨hKtoA z hzK, hzU, hzV⟩
    rw [hnone] at hm
    exact hm

end GraphMinor.GM12
