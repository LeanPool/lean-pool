/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RadialDeletion
public import LeanPool.GraphMinor.Surface.PushOff
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Moving a possible extra spoke off the deleted disc

For maximality in XII (7.2), page 260, keep the reduced drawing and
its retained radial drawing fixed. Their intersection with the removed
disc lies on its retained boundary spoke. The disc-pushing theorem
moves a possible extra spoke off the disc, apart from its ends. It
then misses the whole old radial drawing in its interior. A region
with a fixed point is preserved by a homeomorphism fixing the drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- Push a possible extra spoke off the deleted disc while fixing the
retained drawings. Its interior then misses the old radial drawing,
as needed for maximality in XII (7.2), page 260. -/
theorem push_extra_spoke_off_disc (hS : IsClosedSurface S)
    {K C : Drawing S} (hC : C.IsSubdrawing K) {D E G L f : Set S} {v u x : S}
    (hD : IsClosedDisc D) (hb : frontier D = C.U) (hfC : f ∈ C.E)
    (hE : IsLineWithEnds E v u) (hEbd : E ⊆ discBd D)
    (hG : IsClosed G) (hvG : v ∈ G) (huG : u ∈ G) (hGD : G ∩ D ⊆ E)
    (hKG : (radialDiscDeletion K D f).U ⊆ G)
    (hL : IsClosed L) (hLE : L ∩ E ⊆ {v, u}) (hLG : L ∩ G ⊆ {x, u}) :
    ∃ h : S ≃ₜ S, (∀ y ∈ G, h y = y) ∧
      (h '' L) ∩ D ⊆ {v, u} ∧ Disjoint ((h '' L) \ {x, u}) K.U := by
  have : CompactSpace S := hS.1
  have hvE : v ∈ E := by obtain ⟨a, h0, _⟩ := hE; exact h0 ▸ (a 0).2
  have huE : u ∈ E := by obtain ⟨a, _, h1⟩ := hE; exact h1 ▸ (a 1).2
  obtain ⟨h, hfix, hpush⟩ := Surface.push_disc (fun y => hS.2.2 y) hD hE
    (hEbd.trans (Surface.discBd_subset D)) (Or.inl ⟨hEbd, hGD⟩) (hEbd hvE) (hEbd huE)
    hG hvG huG hL hLE
  have hdisG : Disjoint ((h '' L) \ {x, u}) G := by
    apply disjoint_left.mpr
    rintro y ⟨⟨z, hzL, hzy⟩, hyn⟩ hyG
    have hzy' : z = y := h.injective (hzy.trans (hfix y hyG).symm)
    exact hyn (hLG ⟨hzy' ▸ hzL, hyG⟩)
  have hfD : f ⊆ D := by
    intro y hy
    have hybd : y ∈ frontier D := hb.symm ▸ (hfC.2.1 hy).1
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl hybd.1
  refine ⟨h, hfix, hpush, disjoint_left.mpr ?_⟩
  intro y hyL hyK
  by_cases hyD : y ∈ D
  · have hyends := hpush ⟨hyL.1, hyD⟩
    have hyG : y ∈ G := by
      rcases hyends with hyv | hyu
      · exact mem_singleton_iff.mp hyv ▸ hvG
      · exact mem_singleton_iff.mp hyu ▸ huG
    exact disjoint_left.mp hdisG hyL hyG
  · have hyK' : y ∈ (radialDiscDeletion K D f).U := by
      rw [radialDiscDeletion_U hC hb hfC]
      exact ⟨⟨hyK, subset_closure ⟨mem_univ _, hyD⟩⟩, fun hyf => hyD (hfD hyf)⟩
    exact disjoint_left.mp hdisG hyL (hKG hyK')

omit [T2Space S] in
/-- A homeomorphism fixing a drawing maps a region with a fixed point
into itself. This keeps a diverted spoke in its original region. -/
theorem image_region_subset_of_fixed {Γ : Drawing S} (h : S ≃ₜ S)
    (hfix : ∀ y ∈ Γ.U, h y = y) {r : Set S} (hr : r ∈ Γ.R)
    {u : S} (hur : u ∈ r) (hu : h u = u) : h '' r ⊆ r := by
  have hconn : IsPreconnected (h '' r) := (region_isPreconnected hr).image h
    h.continuous.continuousOn
  have hdis : Disjoint (h '' r) Γ.U := by
    apply disjoint_left.mpr
    rintro y ⟨z, hzr, hzy⟩ hyΓ
    have hzy' : z = y := h.injective (hzy.trans (hfix y hyΓ).symm)
    exact region_subset hr (hzy' ▸ hzr) hyΓ
  exact subset_region hr hconn hdis ⟨u, hur, hu⟩ hur

/-- A homeomorphism sends a line with specified ends to the line
with the corresponding image ends. -/
theorem lineWithEnds_image_homeomorph (h : S ≃ₜ S) {L : Set S} {u x : S}
    (hL : IsLineWithEnds L u x) : IsLineWithEnds (h '' L) (h u) (h x) := by
  obtain ⟨p, hp0, hp1⟩ := hL
  let q : unitInterval → S := fun t => h (p t).val
  have hqc : Continuous q := h.continuous.comp (continuous_subtype_val.comp p.continuous)
  have hqi : Function.Injective q := h.injective.comp (Subtype.val_injective.comp p.injective)
  have hrange : range q = h '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(p t).val, (p t).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨p.symm ⟨z, hz⟩, congrArg h (congrArg Subtype.val (p.apply_symm_apply ⟨z, hz⟩))⟩
  simpa only [q, hp0, hp1, hrange] using isLine_range hqc hqi

omit [T2Space S] in
/-- Pull an empty spoke disc back after a diversion fixing the
retained drawings. Its boundary and its containing region return
to the original extra spoke. -/
theorem pullback_spoke_disc (hS : IsClosedSurface S)
    {Γ K : Drawing S} (h : S ≃ₜ S)
    (hΓ : ∀ y ∈ Γ.U, h y = y) (hK : ∀ y ∈ K.U, h y = y)
    {r Q L e : Set S} {u x : S} (hr : r ∈ Γ.R) (hur : u ∈ r)
    (hu : h u = u) (hx : h x = x) (he : e ∈ K.E)
    (hQ : IsClosedDisc Q) (hQr : Q ⊆ r ∪ {x}) (hbd : subBd Q = closure e ∪ h '' L) :
    ∃ P : Set S, IsClosedDisc P ∧ P ⊆ r ∪ {x} ∧ subBd P = closure e ∪ L := by
  have hΓsymm : ∀ y ∈ Γ.U, h.symm y = y := by
    intro y hy
    exact h.symm_apply_eq.mpr (hΓ y hy).symm
  have huSymm : h.symm u = u := h.symm_apply_eq.mpr hu.symm
  have hxSymm : h.symm x = x := h.symm_apply_eq.mpr hx.symm
  have hrimage : h.symm '' r ⊆ r := image_region_subset_of_fixed h.symm hΓsymm hr hur huSymm
  obtain ⟨hP, hPbd⟩ := hQ.image h.symm.continuous.continuousOn h.continuous.continuousOn
    (fun y _ => h.apply_symm_apply y)
  have heimage : h.symm '' closure e = closure e := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzfix : h.symm z = z := h.symm_apply_eq.mpr (hK z (K.closure_subset_U he hz)).symm
      rw [hzfix]
      exact hz
    · intro hy
      exact ⟨y, hy, h.symm_apply_eq.mpr (hK y (K.closure_subset_U he hy)).symm⟩
  refine ⟨h.symm '' Q, hP, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    rcases hQr hz with hzr | hzx
    · exact Or.inl (hrimage ⟨z, hzr, rfl⟩)
    · exact Or.inr (mem_singleton_iff.mpr
        ((congrArg h.symm (mem_singleton_iff.mp hzx)).trans hxSymm))
  · rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hP, hPbd,
      ← IsClosedDisc.frontier_eq_discBd hS hQ, ← subBd_eq_frontier, hbd,
      image_union, heimage, image_image]
    have hinv : (fun y => h.symm (h y)) = id := funext h.symm_apply_apply
    rw [hinv, image_id]

end GraphMinor.GM12
