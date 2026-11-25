/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.GlueDiscs
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.Surface.Epstein
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Disc bounding by capping cuffs for Graph Minors VII, Section 11

An `O`-arc in `Z` that is null-homotopic in `Z` bounds a closed disc in `Z`. The relative
lemma extends Robertson and Seymour's Graph Minors XI (7.2), page 93, to surfaces with
boundary. The case `Z = univ` gives the ambient disc-bounding result that Graph Minors VII,
Section 2, page 214, cites to H. I. Levine.

The proof reduces to `Surface.EpsteinStatement` (which applies to `O`-arcs disjoint from the
surface boundary in a connected surface) by capping all cuffs of `S` via `Surface.exists_capAll`
to obtain a closed surface `T` (`bd T = ∅`), restricting to the clopen connected component of `T`
containing the image of `F`, applying `EpsteinStatement` there, and pulling the resulting closed
disc back along the closed embedding `j : S → T`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A clopen subset of a closed surface is a closed surface in the subspace topology. -/
private theorem isClosedSurface_subtype_of_isClopen {T : Type u} [TopologicalSpace T]
    (hT : IsClosedSurface T) {C : Set T} (hC : IsClopen C) :
    IsClosedSurface C := by
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  refine ⟨isCompact_iff_compactSpace.mp hC.1.isCompact, inferInstance, fun x => ?_⟩
  obtain ⟨U, hU, hxU, ⟨e⟩⟩ := hT.2.2 x.1
  let W : Set OpenUnitDisc := (e.symm ⁻¹' {u : U | u.1 ∈ C})
  have hW_open : IsOpen W :=
    (hC.2.preimage continuous_subtype_val).preimage e.symm.continuous
  let hxW : e ⟨x.1, hxU⟩ ∈ W := by
    change (e.symm (e ⟨x.1, hxU⟩)).1 ∈ C
    rw [e.symm_apply_apply]
    exact x.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hW_open)
    (e ⟨x.1, hxU⟩).1 ⟨e ⟨x.1, hxU⟩, hxW, rfl⟩
  let c : ℂ := complexPlane.symm (e ⟨x.1, hxU⟩).1
  have hball_sub : Metric.ball c ε ⊆ complexPlane.symm '' (Subtype.val '' W) := by
    intro z hz
    have hz' : complexPlane z ∈ Metric.ball (e ⟨x.1, hxU⟩).1 ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have : complexPlane z - (e ⟨x.1, hxU⟩).1 = complexPlane (z - c) := by
        simp [c, map_sub]
      rw [this, LinearIsometryEquiv.norm_map]
      exact hz
    have h1 := mem_image_of_mem complexPlane.symm (hball hz')
    rw [LinearIsometryEquiv.symm_apply_apply] at h1
    exact h1
  obtain ⟨b⟩ := exists_homeomorph_ball c hε
  let B_disc : Set OpenUnitDisc :=
    {u : OpenUnitDisc | complexPlane.symm u.1 ∈ Metric.ball c ε}
  have hB_sub_W : B_disc ⊆ W := by
    intro u hu
    obtain ⟨_, ⟨w, hwW, rfl⟩, hweq⟩ := hball_sub hu
    have : u = w := Subtype.ext (complexPlane.symm.injective hweq.symm)
    exact this ▸ hwW
  let U' : Set C := {y : C | ∃ hy : y.1 ∈ U, e ⟨y.1, hy⟩ ∈ B_disc}
  have hU'_eq : U' = Subtype.val ⁻¹' (Subtype.val '' (e ⁻¹' B_disc)) := by
    ext y
    constructor
    · rintro ⟨hy, hB⟩
      exact ⟨⟨y.1, hy⟩, hB, rfl⟩
    · rintro ⟨⟨z, hzU⟩, hB, hzy⟩
      cases hzy
      exact ⟨hzU, hB⟩
  have hB_open : IsOpen B_disc :=
    Metric.isOpen_ball.preimage (complexPlane.symm.continuous.comp continuous_subtype_val)
  have hU'_open : IsOpen U' := by
    rw [hU'_eq]
    exact (hU.isOpenEmbedding_subtypeVal.isOpenMap _ (hB_open.preimage e.continuous)).preimage
      continuous_subtype_val
  have hxU' : x ∈ U' := ⟨hxU, by simp [B_disc, c, hε]⟩
  let toBall : U' → Metric.ball c ε := fun y =>
    ⟨complexPlane.symm (e ⟨y.1.1, y.2.choose⟩).1, y.2.choose_spec⟩
  let fromBall : Metric.ball c ε → U' := fun z =>
    have hz_in : complexPlane z.1 ∈ OpenUnitDisc := by
      obtain ⟨_, ⟨w, _, rfl⟩, hweq⟩ := hball_sub z.2
      have : complexPlane z.1 = w.1 := by
        rw [← hweq, complexPlane.apply_symm_apply]
      exact this ▸ w.2
    let u : OpenUnitDisc := ⟨complexPlane z.1, hz_in⟩
    have huB : u ∈ B_disc := by
      change complexPlane.symm (complexPlane z.1) ∈ Metric.ball c ε
      rw [complexPlane.symm_apply_apply]
      exact z.2
    have huW : u ∈ W := hB_sub_W huB
    ⟨⟨(e.symm u).1, huW⟩, (e.symm u).2, by
      change e (e.symm u) ∈ B_disc
      rw [e.apply_symm_apply]
      exact huB⟩
  have h_left : LeftInverse fromBall toBall := by
    intro y
    ext1
    ext1
    change (e.symm ⟨complexPlane (complexPlane.symm (e ⟨y.1.1, y.2.choose⟩).1), _⟩).1 = y.1.1
    simp only [complexPlane.apply_symm_apply, Subtype.coe_eta, e.symm_apply_apply]
  have h_right : RightInverse fromBall toBall := by
    intro z
    ext1
    change complexPlane.symm (e (e.symm ⟨complexPlane z.1, _⟩)).1 = z.1
    simp only [e.apply_symm_apply, complexPlane.symm_apply_apply]
  have h_to_cont : Continuous toBall := by
    refine Continuous.subtype_mk ?_ _
    refine complexPlane.symm.continuous.comp (continuous_subtype_val.comp (e.continuous.comp ?_))
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have h_from_cont : Continuous fromBall := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine continuous_subtype_val.comp (e.symm.continuous.comp ?_)
    exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) _
  let e' : U' ≃ₜ Metric.ball c ε :=
    { toFun := toBall
      invFun := fromBall
      left_inv := h_left
      right_inv := h_right
      continuous_toFun := h_to_cont
      continuous_invFun := h_from_cont }
  exact ⟨U', hU'_open, hxU', ⟨e'.trans b⟩⟩

/-- Every closed surface is a surface with empty boundary. -/
private theorem isSurface_and_bd_empty_of_isClosedSurface {T : Type u} [TopologicalSpace T]
    (hT : IsClosedSurface T) : IsSurface T ∧ bd T = ∅ := by
  refine ⟨⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩, ?_⟩
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  exact hx (hT.2.2 x)

/-- Relative disc bounding for an `O`-arc null-homotopic in `Z`. This extends Robertson and
Seymour's Graph Minors XI (7.2), page 93, to surfaces with boundary. The proof caps the cuffs of
`S` and applies the relative clause of `Surface.epstein`. -/
theorem nullHomotopicOArcIn_bounds_disc
    (hS : IsSurface S) {Z F : Set S} (_hF : IsOArc F) (hFZ : F ⊆ Z)
    (hnull : IsNullHomotopicOArcIn Z F) :
    ∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨T, _, j, K, hT_closed, hj, _, _, _⟩ := exists_capAll S hS
  have : T2Space T := hT_closed.2.1
  have : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT_closed
  obtain ⟨φ, c, hcZ, ψ, hψZ, hψ0, hψ1⟩ := hnull
  let x₀ : S := (φ 1).1
  let C : Set T := connectedComponent (j x₀)
  have hC_clopen : IsClopen C := isClopen_connectedComponent
  have hC_closedSurf : IsClosedSurface C := isClosedSurface_subtype_of_isClopen hT_closed hC_clopen
  obtain ⟨hC_surf, hC_bd⟩ := isSurface_and_bd_empty_of_isClosedSurface hC_closedSurf
  have hC_conn : ConnectedSpace C :=
    isConnected_iff_connectedSpace.mp ⟨⟨j x₀, mem_connectedComponent⟩,
      isPreconnected_connectedComponent⟩
  have hψ_conn : IsPreconnected (range (j ∘ ψ)) := by
    have : PreconnectedSpace (Circle × unitInterval) := inferInstance
    exact isPreconnected_range (hj.continuous.comp ψ.continuous)
  have hψ0_eq : ∀ w : Circle, ψ (w, 0) = (φ w).1 := hψ0
  have hψ1_eq : ∀ w : Circle, ψ (w, 1) = c := hψ1
  have hψ_sub_C : range (j ∘ ψ) ⊆ C := by
    refine hψ_conn.subset_connectedComponent ⟨(1, 0), ?_⟩
    change j (ψ (1, 0)) = j x₀
    rw [hψ0_eq 1]
  have hF_sub_C : j '' F ⊆ C := by
    rintro _ ⟨y, hyF, rfl⟩
    obtain ⟨w, hw⟩ := φ.surjective ⟨y, hyF⟩
    have hw' : (φ w).1 = y := congrArg Subtype.val hw
    rw [← hw', ← hψ0_eq w]
    exact hψ_sub_C ⟨(w, 0), rfl⟩
  have hc_mem_C : j c ∈ C := by
    rw [← hψ1_eq 1]
    exact hψ_sub_C ⟨(1, 1), rfl⟩
  let Z_C : Set C := Subtype.val ⁻¹' (j '' Z)
  let F_C : Set C := Subtype.val ⁻¹' (j '' F)
  have hFC_sub_ZC : F_C ⊆ Z_C := preimage_mono (image_mono hFZ)
  let toFC : F → F_C := fun y => ⟨⟨j y.1, hF_sub_C (mem_image_of_mem j y.2)⟩, mem_image_of_mem j
    y.2⟩
  have htoFC_bij : Bijective toFC := by
    constructor
    · intro y₁ y₂ h
      exact Subtype.ext (hj.injective (congrArg (fun u : F_C => u.1.1) h))
    · intro u
      obtain ⟨y, hyF, hyu⟩ := u.2
      refine ⟨⟨y, hyF⟩, ?_⟩
      ext1
      ext1
      exact hyu
  have htoFC_cont : Continuous toFC :=
    Continuous.subtype_mk (Continuous.subtype_mk (hj.continuous.comp continuous_subtype_val) _) _
  have : CompactSpace F := φ.compactSpace
  let eFC : F ≃ₜ F_C := htoFC_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective toFC htoFC_bij)
  let φ_C : Circle ≃ₜ F_C := φ.trans eFC
  have hFC_oarc : IsOArc F_C := ⟨φ_C⟩
  have hFC_null : IsNullHomotopicOArcIn Z_C F_C := by
    refine ⟨φ_C, ⟨j c, hc_mem_C⟩, mem_image_of_mem j hcZ,
      ⟨fun p => ⟨j (ψ p), hψ_sub_C ⟨p, rfl⟩⟩,
        Continuous.subtype_mk (hj.continuous.comp ψ.continuous) _⟩,
      fun p => mem_image_of_mem j (hψZ p), fun x => ?_, fun x => ?_⟩
    · apply Subtype.ext
      change j (ψ (x, 0)) = j (φ x).1
      rw [hψ0_eq x]
    · apply Subtype.ext
      change j (ψ (x, 1)) = j c
      rw [hψ1_eq x]
  have hFC_disj : Disjoint F_C (bd C) := by
    rw [hC_bd]
    exact disjoint_empty F_C
  obtain ⟨Δ_C, hΔC_sub, hΔC_disc, hΔC_bd⟩ :=
    (Surface.epstein C Z_C F_C hC_surf hC_conn hFC_oarc hFC_sub_ZC hFC_disj).1 hFC_null
  have hΔC_in_range : Subtype.val '' Δ_C ⊆ j '' Z :=
    image_subset_iff.mpr hΔC_sub
  let Δ : Set S := j ⁻¹' (Subtype.val '' Δ_C)
  have hΔ_sub_Z : Δ ⊆ Z := by
    intro x hx
    obtain ⟨y, hyZ, hyx⟩ := hΔC_in_range hx
    exact hj.injective hyx ▸ hyZ
  have : Nonempty S := ⟨x₀⟩
  obtain ⟨j_inv, hj_inv_cont, hj_inv_left⟩ :=
    exists_inv_of_compactOn isCompact_univ hj.continuous.continuousOn hj.injective.injOn
  rw [image_univ] at hj_inv_cont
  have hsub_cont : ContinuousOn (j_inv ∘ (Subtype.val : C → T)) Δ_C := by
    refine (hj_inv_cont.mono ?_).comp continuous_subtype_val.continuousOn (mapsTo_image _ _)
    exact hΔC_in_range.trans (image_subset_range _ _)
  have hsub_inj : InjOn (j_inv ∘ (Subtype.val : C → T)) Δ_C := by
    intro u₁ hu₁ u₂ hu₂ heq
    obtain ⟨x₁, _, hx₁⟩ := hΔC_in_range (mem_image_of_mem Subtype.val hu₁)
    obtain ⟨x₂, _, hx₂⟩ := hΔC_in_range (mem_image_of_mem Subtype.val hu₂)
    have h1 : j_inv u₁.1 = x₁ := by rw [← hx₁, hj_inv_left (mem_univ x₁)]
    have h2 : j_inv u₂.1 = x₂ := by rw [← hx₂, hj_inv_left (mem_univ x₂)]
    have h12 : x₁ = x₂ := h1.symm.trans (heq.trans h2)
    exact Subtype.ext (hx₁.symm.trans (by rw [h12, hx₂]))
  obtain ⟨hΔ_disc', hΔ_bd'⟩ := isClosedDisc_image hΔC_disc hsub_cont hsub_inj
  have himg_eq : (j_inv ∘ (Subtype.val : C → T)) '' Δ_C = Δ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨y, _, hy⟩ := hΔC_in_range (mem_image_of_mem Subtype.val hu)
      have h1 : j_inv u.1 = y := by rw [← hy, hj_inv_left (mem_univ y)]
      change j (j_inv u.1) ∈ Subtype.val '' Δ_C
      rw [h1, hy]
      exact ⟨u, hu, rfl⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      refine ⟨u, hu, ?_⟩
      change j_inv u.1 = x
      rw [hux, hj_inv_left (mem_univ x)]
  rw [himg_eq] at hΔ_disc' hΔ_bd'
  refine ⟨Δ, hΔ_sub_Z, hΔ_disc', ?_⟩
  rw [hΔ_bd', hΔC_bd]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hyF, hyu⟩ := hu
    have h1 : j_inv u.1 = y := by rw [← hyu, hj_inv_left (mem_univ y)]
    change j_inv u.1 ∈ F
    rw [h1]
    exact hyF
  · intro hxF
    refine ⟨⟨j x, hF_sub_C (mem_image_of_mem j hxF)⟩, mem_image_of_mem j hxF, ?_⟩
    change j_inv (j x) = x
    exact hj_inv_left (mem_univ x)

/-- The ambient disc-bounding result cited to H. I. Levine in Graph Minors VII, Section 2,
page 214. This is the case `Z = univ` of `nullHomotopicOArcIn_bounds_disc`. -/
theorem nullHomotopicOArc_bounds_disc
    (hS : IsSurface S) {F : Set S} (hF : IsOArc F) (hnull : IsNullHomotopicOArc F) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F := by
  obtain ⟨Δ, _, hΔ, hbd⟩ :=
    nullHomotopicOArcIn_bounds_disc hS hF (subset_univ F) hnull
  exact ⟨Δ, hΔ, hbd⟩

end GraphMinor.GM07
