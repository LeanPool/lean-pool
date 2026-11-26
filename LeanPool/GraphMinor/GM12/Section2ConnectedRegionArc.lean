/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import Mathlib.Topology.Maps.Basic
import LeanPool.GraphMinor.GM11.Regions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A connected region intersection has only one curve interval

In Case 1 of XII (2.1), page 244, each visited region occurs once.
For an embedded original circle, pull its connected intersection with
a region back to the parameter circle. The open parameter arc of one
visit is relatively both open and closed in this intersection: its
closed arc adds only the two drawing vertices, which are outside the
region. Connectedness therefore puts the whole intersection in that
one parameter arc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- If the image of an embedded circle meets a region in a preconnected
set, every region parameter lies in any one open visit arc bounded by
drawing vertices. This is the distinct-region-visit step in XII (2.1). -/
theorem preimage_region_subset_parameter_arc
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S}
    {φ : C(Circle, S)} (hφ : IsEmbedding φ) {r : Set S} (hr : r ∈ Γ.R)
    (hconn : IsPreconnected (range φ ∩ r)) {a c : ℝ} (hac : a < c)
    (ha : periodicCurve φ a ∈ Γ.V) (hc : periodicCurve φ c ∈ Γ.V)
    (hfr : ∀ t ∈ Ioo a c, periodicCurve φ t ∈ r) :
    φ ⁻¹' r ⊆ (fun t : ℝ => Circle.exp (2 * Real.pi * t)) '' Ioo a c := by
  let B : Set Circle := φ ⁻¹' r
  let E : ℝ → Circle := fun t => Circle.exp (2 * Real.pi * t)
  let O := E '' Ioo a c
  let D := E '' Icc a c
  have hE : Continuous E := by fun_prop
  have hEopen : IsOpenMap E := isLocalHomeomorph_circleExp.isOpenMap.comp
    (Homeomorph.mulLeft₀ (2 * Real.pi) (ne_of_gt Real.two_pi_pos)).isOpenMap
  have hO : IsOpen O := hEopen _ isOpen_Ioo
  have hD : IsClosed D := (isCompact_Icc.image hE).isClosed
  have hOD : O ⊆ D := image_mono Ioo_subset_Icc_self
  have hφB : φ '' B = range φ ∩ r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mem_range_self z, hz⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, hz, rfl⟩
  have hB : IsPreconnected B := hφ.isInducing.isPreconnected_image.mp (hφB.symm ▸ hconn)
  have hBO : (B ∩ O).Nonempty := by
    let m := (a + c) / 2
    have hm : m ∈ Ioo a c := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
    exact ⟨E m, hfr m hm, m, hm, rfl⟩
  have hBDoff : Disjoint B (D \ O) := by
    apply disjoint_left.mpr
    rintro z hzB ⟨⟨t, ht, rfl⟩, htO⟩
    by_cases hta : t = a
    · subst t
      exact region_subset hr hzB (Γ.V_subset_U ha)
    · by_cases htc : t = c
      · subst t
        exact region_subset hr hzB (Γ.V_subset_U hc)
      · exact htO ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htc⟩, rfl⟩
  intro z hzB
  by_contra hzO
  have hcover : B ⊆ D ∪ Oᶜ := by
    intro x _
    by_cases hx : x ∈ O
    · exact Or.inl (hOD hx)
    · exact Or.inr hx
  obtain ⟨x, hxB, hxD, hxO⟩ := isPreconnected_closed_iff.mp hB D Oᶜ hD hO.isClosed_compl
    hcover (hBO.mono (inter_subset_inter_right B hOD)) ⟨z, hzB, hzO⟩
  exact disjoint_left.mp hBDoff hxB ⟨hxD, hxO⟩

end GraphMinor.GM12
