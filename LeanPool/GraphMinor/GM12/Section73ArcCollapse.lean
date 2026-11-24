/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ThinStripCollapse
import LeanPool.GraphMinor.GM12.Section4StripRectangle
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Contracting a drawn arc while fixing a disjoint closed set

For the radial-edge contractions in XII (7.3), page 261, straighten
the arc in a surface strip. Take a thin rectangle avoiding the closed
set to be fixed and contract its axis interval. The resulting map is
continuous and onto, and identifies precisely the arc. Conjugating
through a surface model makes the construction work in every universe.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric

private theorem exists_arc_collapse_type
    {S : Type} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {a : unitInterval → S} (ha : IsArcMap a)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (range a) F) :
    ∃ f : C(S, S), Function.Surjective f ∧ (∀ x ∈ F, f x = x) ∧
      (∀ x ∈ range a, f x = a 0) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ range a ∧ y ∈ range a)) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨E, hE, haE⟩ := Surface.exists_disc_of_arc hS ha
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨c.isOpen_image_ball hman, c.hc.mono ?_, c.gc.mono ball_subset_closedBall,
      ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact c.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [c.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [c.hg (ball_subset_closedBall hz)]
    · exact fun z hz => c.hg (ball_subset_closedBall hz)
  have haU : range a ⊆ g '' ball 0 1 := by rw [← c.discInt_eq]; exact haE
  obtain ⟨O, K, θ, hK, hθc, hθm, hθK⟩ := Surface.exists_stripChart hman hbc ha haU
  let G := O ∩ K ⁻¹' Fᶜ
  have hG : IsOpen G := hK.hc.isOpen_inter_preimage hK.isOpen hF.isOpen_compl
  have hθ01 : θ 0 < θ 1 := hθm (by norm_num : (0 : unitInterval) < 1)
  have hseg : Complex.ofReal '' Icc (θ 0) (θ 1) ⊆ G := by
    rintro z ⟨t, ht, rfl⟩
    have himage := hθc.image_Icc_of_strictMono (a := 0) (b := 1) hθm
    obtain ⟨s, _, hs⟩ := (himage.symm ▸ ht : t ∈ θ '' Icc 0 1)
    subst t
    refine ⟨(hθK s).1, ?_⟩
    change K (θ s) ∉ F
    rw [(hθK s).2]
    exact disjoint_left.mp havoid (mem_range_self s)
  obtain ⟨δ, hδ, hrect⟩ := exists_strip_rectangle hG hθ01.le hseg
  obtain ⟨f, hfs, hfix, hconst, _, hfibre⟩ := exists_thin_strip_interval_collapse hK hθ01 hδ
    (fun z hz => (hrect hz).1)
  have haxis : K '' (Complex.ofReal '' Icc (θ 0) (θ 1)) = range a := by
    ext x
    constructor
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      have himage := hθc.image_Icc_of_strictMono (a := 0) (b := 1) hθm
      obtain ⟨s, _, hs⟩ := (himage.symm ▸ ht : t ∈ θ '' Icc 0 1)
      exact ⟨s, (hθK s).2.symm.trans (congrArg K (congrArg Complex.ofReal hs))⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(θ t : ℂ), ⟨θ t, ⟨hθm.monotone (unitInterval.nonneg _),
        hθm.monotone (unitInterval.le_one _)⟩, rfl⟩, (hθK t).2⟩
  refine ⟨f, hfs, ?_, ?_, ?_⟩
  · intro x hx
    apply hfix
    rintro ⟨z, hz, rfl⟩
    exact (hrect hz).2 hx
  · intro x hx
    have h := hconst x (haxis.symm ▸ hx)
    exact h.trans (hθK 0).2
  · simpa only [haxis] using hfibre

/-- Contract an arc to its first endpoint by a continuous surjection,
fixing any closed set disjoint from it and identifying no other
points. This realizes the edge contractions in XII (7.3), page 261. -/
theorem exists_arc_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a : unitInterval → S} (ha : IsArcMap a)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (range a) F) :
    ∃ f : C(S, S), Function.Surjective f ∧ (∀ x ∈ F, f x = x) ∧
      (∀ x ∈ range a, f x = a 0) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ range a ∧ y ∈ range a)) := by
  let : CompactSpace S := hS.1
  have hSurface : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨n, m, c, ⟨e⟩⟩ := classification S hSurface inferInstance
  let : T2Space (SurfaceModel n m c) := e.t2Space
  have hM : IsClosedSurface (SurfaceModel n m c) := by
    refine ⟨e.compactSpace, e.t2Space, ?_⟩
    intro x
    have hx := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hS.2.2 (e.symm x))
    simpa only [e.apply_symm_apply] using hx
  let a' : unitInterval → SurfaceModel n m c := fun t => e (a t)
  let F' : Set (SurfaceModel n m c) := e.symm ⁻¹' F
  have ha' : IsArcMap a' := ⟨e.continuous.comp ha.1, e.injective.comp ha.2⟩
  have hF' : IsClosed F' := hF.preimage e.symm.continuous
  have havoid' : Disjoint (range a') F' := by
    apply disjoint_left.mpr
    rintro z ⟨t, rfl⟩ hz
    have hzF : a t ∈ F := by simpa only [F', a', mem_preimage, e.symm_apply_apply] using hz
    exact disjoint_left.mp havoid (mem_range_self t) hzF
  obtain ⟨f, hfs, hfix, hconst, hfibre⟩ := exists_arc_collapse_type hM ha' hF' havoid'
  let g : C(S, S) := ⟨fun x => e.symm (f (e x)),
    e.symm.continuous.comp (f.continuous.comp e.continuous)⟩
  have hrange : ∀ x : S, e x ∈ range a' ↔ x ∈ range a := by
    intro x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, e.injective ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  refine ⟨g, e.symm.surjective.comp (hfs.comp e.surjective), ?_, ?_, ?_⟩
  · intro x hx
    change e.symm (f (e x)) = x
    rw [hfix (e x) (by simpa only [F', mem_preimage, e.symm_apply_apply] using hx),
      e.symm_apply_apply]
  · intro x hx
    change e.symm (f (e x)) = a 0
    rw [hconst (e x) ((hrange x).mpr hx)]
    exact e.symm_apply_apply _
  · intro x y
    change e.symm (f (e x)) = e.symm (f (e y)) ↔ _
    rw [e.symm.injective.eq_iff, hfibre]
    simp only [e.injective.eq_iff, hrange]

end GraphMinor.GM12
