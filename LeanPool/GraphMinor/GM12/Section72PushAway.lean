/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Regions
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Diverting a circle that misses the boundary vertex

In the rerouting step of XII (7.2), page 260, first consider a circle
that misses the one vertex on the removed disc boundary. A short arc
of that boundary around the vertex misses the circle. Pushing across
the rest of the disc, while fixing the outside drawing and the two
ends of the short arc, moves the circle completely off the disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A short line of a circle through a prescribed point avoids a closed set
missing that point and contains the circle near that point. -/
theorem exists_small_boundary_line {F C : Set S} (hF : IsOArc F)
    {v : S} (hv : v ∈ F) (hC : IsClosed C) (hvn : v ∉ C) :
    ∃ (L : Set S) (a b : S), IsLineWithEnds L a b ∧ L ⊆ F ∧ v ∈ L ∧
      Disjoint L C ∧ a ≠ v ∧ b ≠ v ∧
      ∃ O : Set S, IsOpen O ∧ v ∈ O ∧ F ∩ O ⊆ L := by
  obtain ⟨p, hp, hp0, _, hperiod, himg, hpF⟩ := exists_oArc_par hF hv
  have hO : IsOpen (p ⁻¹' Cᶜ) := hC.isOpen_compl.preimage hp
  have h0O : (0 : ℝ) ∈ p ⁻¹' Cᶜ := by
    change p 0 ∉ C
    rwa [hp0]
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hO (0 : ℝ) h0O
  let δ := min (ε / 2) (Real.pi / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hi : InjOn p (Icc (-δ) δ) := by
    intro s hs t ht hst
    obtain ⟨m, hm⟩ := hperiod s t hst
    rcases lt_trichotomy m 0 with hn | hz | hp
    · have hn' : (m : ℝ) ≤ -1 := by
        have hmneg : m ≤ -1 := by omega
        exact_mod_cast hmneg
      have hmul := mul_le_mul_of_nonneg_right hn' (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith [hs.1, ht.2]
    · simpa only [hz, Int.cast_zero, zero_mul, add_zero] using hm
    · have hp' : (1 : ℝ) ≤ m := by exact_mod_cast hp
      have hmul := mul_le_mul_of_nonneg_right hp' (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith [hs.2, ht.1]
  let L := p '' Icc (-δ) δ
  have hline : IsLineWithEnds L (p (-δ)) (p δ) := isLine_of_injOn hp (by linarith) hi
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  refine ⟨L, p (-δ), p δ, hline, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (image_subset_range p _).trans hpF
  · exact ⟨0, h0, hp0⟩
  · refine disjoint_left.mpr ?_
    rintro x ⟨s, hs, rfl⟩ hsC
    have hsball : s ∈ ball (0 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact hεsub hsball hsC
  · intro ha
    have heq := hi ⟨le_rfl, by linarith⟩ h0 (ha.trans hp0.symm)
    linarith
  · intro hb
    have heq := hi ⟨by linarith, le_rfl⟩ h0 (hb.trans hp0.symm)
    linarith
  · have hshift : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi), p (t - 2 * Real.pi) = p t := by
      intro t ht
      obtain ⟨u, hu, hups⟩ := himg.symm ▸ hpF (mem_range_self (t - 2 * Real.pi))
      obtain ⟨m, hm⟩ := hperiod u (t - 2 * Real.pi) hups
      have hmlo : 1 ≤ m := by
        by_contra hn
        have hm0 : m ≤ 0 := by omega
        have hm0' : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        have hmul := mul_nonpos_of_nonpos_of_nonneg hm0' (show 0 ≤ 2 * Real.pi by positivity)
        linarith [hu.1, ht.2]
      have hmhi : m ≤ 1 := by
        by_contra hn
        have hm2 : 2 ≤ m := by omega
        have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        have hmul := mul_le_mul_of_nonneg_right hm2' (show 0 ≤ 2 * Real.pi by positivity)
        nlinarith [hu.2, ht.1]
      have hm1 : m = 1 := le_antisymm hmhi hmlo
      have hut : u = t := by rw [hm1] at hm; norm_num at hm; linarith
      exact hut ▸ hups.symm
    let K := p '' Icc δ (2 * Real.pi - δ)
    have hK : IsClosed K := (isCompact_Icc.image hp).isClosed
    have hvK : v ∉ K := by
      rintro ⟨t, ht, htv⟩
      obtain ⟨m, hm⟩ := hperiod t 0 (htv.trans hp0.symm)
      by_cases hm0 : m ≤ 0
      · have hm0' : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        have hmul := mul_nonpos_of_nonpos_of_nonneg hm0' (show 0 ≤ 2 * Real.pi by positivity)
        linarith [ht.1]
      · have hm1 : 1 ≤ m := by omega
        have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        have hmul := mul_le_mul_of_nonneg_right hm1' (show 0 ≤ 2 * Real.pi by positivity)
        nlinarith [ht.2]
    refine ⟨Kᶜ, hK.isOpen_compl, hvK, ?_⟩
    rintro x ⟨hxF, hxK⟩
    obtain ⟨t, ht, rfl⟩ := himg.symm ▸ hxF
    by_cases htlo : t ≤ δ
    · exact ⟨t, ⟨by linarith [ht.1], htlo⟩, rfl⟩
    · by_cases hthi : 2 * Real.pi - δ ≤ t
      · exact ⟨t - 2 * Real.pi, ⟨by linarith, by linarith [ht.2]⟩, hshift t ht⟩
      · exact (hxK ⟨t, ⟨(not_le.mp htlo).le, (not_le.mp hthi).le⟩, rfl⟩).elim

/-- The diversion used in XII (7.2), page 260, for a closed circle missing
the boundary vertex. The resulting homeomorphism fixes the outside drawing
pointwise and moves the circle completely off the selected disc. -/
theorem theorem_7_2_push_away_of_notMem (hS : IsClosedSurface S)
    {Δ G C : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hv : v ∈ discBd Δ)
    (hG : IsClosed G) (hGD : G ∩ Δ ⊆ {v}) (hC : IsOArc C) (hvn : v ∉ C) :
    ∃ h : S ≃ₜ S, (∀ x ∈ G, h x = x) ∧ Disjoint (h '' C) Δ := by
  have : CompactSpace S := hS.1
  have hCc : IsClosed C := by
    obtain ⟨e⟩ := hC
    have : CompactSpace C := e.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  obtain ⟨L, a, b, hL, hLF, hvL, hLC, _, _, _⟩ :=
    exists_small_boundary_line hΔ.isOArc_discBd hv hCc hvn
  obtain ⟨e, hea, heb⟩ := hL
  have haL : a ∈ L := hea ▸ (e 0).2
  have hbL : b ∈ L := heb ▸ (e 1).2
  let Y := G ∪ {a, b}
  have hYc : IsClosed Y := hG.union ((finite_singleton b).insert a).isClosed
  have hYD : Y ∩ Δ ⊆ L := by
    rintro x ⟨hxG | hxpair, hxD⟩
    · exact mem_singleton_iff.mp (hGD ⟨hxG, hxD⟩) ▸ hvL
    · rcases mem_insert_iff.mp hxpair with rfl | hx
      · exact haL
      · exact mem_singleton_iff.mp hx ▸ hbL
  have hCL : C ∩ L ⊆ ({a, b} : Set S) := fun _ hx => (disjoint_left.mp hLC hx.2 hx.1).elim
  obtain ⟨h, hfix, hpush⟩ := push_disc (fun x => hS.2.2 x) hΔ ⟨e, hea, heb⟩
    (hLF.trans (Surface.discBd_subset Δ)) (Or.inl ⟨hLF, hYD⟩)
    (hLF haL) (hLF hbL) hYc (Or.inr (mem_insert a _))
    (Or.inr (mem_insert_of_mem a rfl)) hCc hCL
  refine ⟨h, fun x hx => hfix x (Or.inl hx), disjoint_left.mpr ?_⟩
  rintro x ⟨y, hy, rfl⟩ hyD
  have hyab := hpush ⟨mem_image_of_mem h hy, hyD⟩
  rcases mem_insert_iff.mp hyab with hya | hyb
  · have heq : h y = h a := hya.trans (hfix a (Or.inr (mem_insert a _))).symm
    exact disjoint_left.mp hLC haL (h.injective heq ▸ hy)
  · have heq : h y = h b := (mem_singleton_iff.mp hyb).trans
      (hfix b (Or.inr (mem_insert_of_mem a rfl))).symm
    exact disjoint_left.mp hLC hbL (h.injective heq ▸ hy)

end GraphMinor.GM12
