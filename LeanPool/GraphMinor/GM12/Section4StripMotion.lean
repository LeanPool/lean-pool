/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcDisc
import LeanPool.GraphMinor.GM12.Section4StripRectangle

/-!
# Moving an arc endpoint while fixing a closed set

The homeomorphism in XII (4.3), claim (7), page 251, must preserve
objects already placed. In straight arc coordinates, remove the
closed set to be fixed and take a thin rectangle around the arc.
The strip slide is the identity outside that rectangle, and hence
on the prescribed closed set.
-/

public section

namespace GraphMinor.GM12

open Set Surface Complex

/-- Slide the last endpoint of a straightened arc to its first
endpoint, fixing a closed set disjoint from the arc. -/
theorem exists_endpoint_motion_of_strip
    {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {O : Set ℂ} {K : ℂ → S} (hK : StripChart O K)
    {a : unitInterval → S} {θ : unitInterval → ℝ}
    (hθc : Continuous θ) (hθm : StrictMono θ)
    (hθK : ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (range a) F) :
    ∃ e : S ≃ₜ S, e (a 1) = a 0 ∧ ∀ x ∈ F, e x = x := by
  let G := O ∩ K ⁻¹' Fᶜ
  have hG : IsOpen G := hK.hc.isOpen_inter_preimage hK.isOpen hF.isOpen_compl
  have h01 : θ 0 < θ 1 := hθm (show (0 : unitInterval) < 1 by norm_num)
  have hseg : Complex.ofReal '' Icc (θ 0) (θ 1) ⊆ G := by
    rintro z ⟨r, hr, rfl⟩
    have himage := hθc.image_Icc_of_strictMono (a := 0) (b := 1) hθm
    obtain ⟨t, _, ht⟩ := (himage.symm ▸ hr : r ∈ θ '' Icc 0 1)
    subst r
    refine ⟨(hθK t).1, ?_⟩
    change K (θ t) ∉ F
    rw [(hθK t).2]
    exact fun hx => Set.disjoint_left.mp havoid (mem_range_self t) hx
  obtain ⟨δ, hδ, hrect⟩ := exists_strip_rectangle hG h01.le hseg
  have hleft : θ 0 - δ < θ 0 := sub_lt_self _ hδ
  have hright : θ 1 < θ 1 + δ := lt_add_of_pos_right _ hδ
  obtain ⟨ψ, hψc, hψm, hψl, hψr, hψend, hψle⟩ :=
    exists_slide_fun hleft h01 hright
  have hab : θ 0 - δ < θ 1 + δ := hleft.trans (h01.trans hright)
  obtain ⟨e, hfix, haxis, _⟩ := exists_slide hK hab hδ
    (fun z hz => (hrect hz).1) hψc hψm hψl hψr hψle
  refine ⟨e, ?_, ?_⟩
  · have he := haxis (θ 1) ⟨hleft.le.trans h01.le, hright.le⟩
    rw [hψend, (hθK 1).2, (hθK 0).2] at he
    exact he
  · intro x hx
    apply hfix
    rintro ⟨z, hz, rfl⟩
    exact (hrect hz).2 hx

end GraphMinor.GM12
