/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.SphereDisc
import Mathlib.Topology.LocalAtTarget

/-!
# Tools for gluing surfaces

* `t2Space_quotient_of_isClosed`: the quotient of a compact Hausdorff space by a closed equivalence
  relation is Hausdorff.
* `IsInteriorPoint.isManifoldPoint`: a point with a disc around it is a manifold point.
* `isInteriorPoint_iff_of_isOpenEmbedding`, `isManifoldPoint_of_isOpenEmbedding`: being an interior
  point or a manifold point is a local property.
* `isInteriorPoint_of_injOn`: a continuous injective map of a compact plane set whose image of an
  open set is open gives an interior point.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u v

/-- The quotient of a compact Hausdorff space by a closed equivalence relation is Hausdorff. -/
theorem t2Space_quotient_of_isClosed {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) : T2Space (Quotient r) := by
  let q : X → Quotient r := Quotient.mk r
  have hqc : Continuous q := continuous_quotient_mk'
  have hsat : ∀ A : Set X, IsClosed A → IsClosed (q ⁻¹' (q '' A)) := by
    intro A hA
    have hK : IsCompact ({p : X × X | r p.1 p.2} ∩ (A ×ˢ univ)) :=
      (hr.inter (hA.prod isClosed_univ)).isCompact
    have : q ⁻¹' (q '' A) = Prod.snd '' ({p : X × X | r p.1 p.2} ∩ (A ×ˢ univ)) := by
      ext y
      constructor
      · rintro ⟨a, ha, he⟩
        exact ⟨(a, y), ⟨Quotient.exact he, ha, mem_univ _⟩, rfl⟩
      · rintro ⟨⟨a, y'⟩, ⟨h1, h2, -⟩, rfl⟩
        exact ⟨a, h2, Quotient.sound h1⟩
    rw [this]
    exact (hK.image continuous_snd).isClosed
  have hcl : IsClosedMap q := fun A hA => by
    have h := hsat A hA
    exact (isQuotientMap_quotient_mk').isClosed_preimage.mp h
  refine ⟨fun y y' hne => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  obtain ⟨x', rfl⟩ := Quotient.exists_rep y'
  have hF : IsClosed (q ⁻¹' {Quotient.mk r x}) := by
    have := hsat {x} isClosed_singleton
    rwa [image_singleton] at this
  have hF' : IsClosed (q ⁻¹' {Quotient.mk r x'}) := by
    have := hsat {x'} isClosed_singleton
    rwa [image_singleton] at this
  have hdisj : Disjoint (q ⁻¹' {Quotient.mk r x}) (q ⁻¹' {Quotient.mk r x'}) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact hne (ha.symm.trans ha')
  obtain ⟨U, U', hU, hU', hsub, hsub', hd⟩ := normal_separation hF hF' hdisj
  have hV : IsOpen (q '' Uᶜ)ᶜ := (hcl _ hU.isClosed_compl).isOpen_compl
  have hV' : IsOpen (q '' U'ᶜ)ᶜ := (hcl _ hU'.isClosed_compl).isOpen_compl
  refine ⟨_, _, hV, hV', ?_, ?_, ?_⟩
  · rintro ⟨a, ha, he⟩
    exact ha (hsub he)
  · rintro ⟨a, ha, he⟩
    exact ha (hsub' he)
  · rw [Set.disjoint_left]
    intro y hy hy'
    obtain ⟨a, rfl⟩ := Quotient.exists_rep y
    have h1 : a ∈ U := by
      by_contra h
      exact hy ⟨a, h, rfl⟩
    have h2 : a ∈ U' := by
      by_contra h
      exact hy' ⟨a, h, rfl⟩
    exact Set.disjoint_left.mp hd h1 h2

/-- A point with a disc around it is a manifold point. -/
theorem IsInteriorPoint.isManifoldPoint {X : Type u} [TopologicalSpace X] {x : X}
    (h : IsInteriorPoint x) : IsManifoldPoint x := by
  obtain ⟨U, hU, hx, ⟨f⟩⟩ := h
  let c : EuclideanPlane := EuclideanSpace.single 0 1
  have hc0 : c 0 = 1 := by simp [c]
  let V : Set (EuclideanHalfSpace 2) := {p | dist p.1 c < 1}
  have hV : IsOpen V := isOpen_lt (continuous_dist.comp₂ continuous_subtype_val continuous_const)
    continuous_const
  have hpos : ∀ y : EuclideanPlane, y ∈ OpenUnitDisc → 0 ≤ (y + c) 0 := by
    intro y hy
    have h1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have h2 : |y 0| ≤ ‖y‖ := by
      simpa using PiLp.norm_apply_le y 0
    have h3 := (abs_le.mp h2).1
    simp only [PiLp.add_apply, hc0]
    linarith
  have hsub : ∀ p : V, p.1.1 - c ∈ OpenUnitDisc := fun p => by
    have : dist p.1.1 c < 1 := p.2
    rwa [dist_eq_norm, ← mem_ball_zero_iff] at this
  let g : OpenUnitDisc ≃ₜ V :=
    { toFun := fun y => ⟨⟨y.1 + c, by
          exact hpos y.1 y.2⟩, by
          change dist (y.1 + c) c < 1
          rw [dist_eq_norm, add_sub_cancel_right]
          exact mem_ball_zero_iff.mp y.2⟩
      invFun := fun p => ⟨p.1.1 - c, hsub p⟩
      left_inv := fun y => Subtype.ext (add_sub_cancel_right _ _)
      right_inv := fun p => Subtype.ext (Subtype.ext (sub_add_cancel _ _))
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        exact continuous_subtype_val.add continuous_const
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const }
  exact ⟨U, V, hU, hV, hx, ⟨f.trans g⟩⟩

/-- Being an interior point is preserved by open embeddings. -/
theorem isInteriorPoint_of_isOpenEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e) {x : X} (h : IsInteriorPoint x) :
    IsInteriorPoint (e x) := by
  obtain ⟨U, hU, hx, ⟨f⟩⟩ := h
  exact ⟨e '' U, he.isOpenMap _ hU, ⟨x, hx, rfl⟩,
    ⟨(he.isEmbedding.homeomorphImage U).symm.trans f⟩⟩

/-- Being a manifold point is preserved by open embeddings. -/
theorem isManifoldPoint_of_isOpenEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e) {x : X} (h : IsManifoldPoint x) :
    IsManifoldPoint (e x) := by
  obtain ⟨U, V, hU, hV, hx, ⟨f⟩⟩ := h
  exact ⟨e '' U, V, he.isOpenMap _ hU, hV, ⟨x, hx, rfl⟩,
    ⟨(he.isEmbedding.homeomorphImage U).symm.trans f⟩⟩

/-- Manifold points are detected in an open embedding. -/
theorem isManifoldPoint_iff_of_isOpenEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e) {x : X} :
    IsManifoldPoint (e x) ↔ IsManifoldPoint x := by
  refine ⟨fun h => ?_, isManifoldPoint_of_isOpenEmbedding he⟩
  obtain ⟨U, V, hU, hV, hx, ⟨f⟩⟩ := h
  let m : e ⁻¹' U → EuclideanHalfSpace 2 := fun y => (f ⟨e y.1, y.2⟩).1
  have hm : IsOpenEmbedding m :=
    (hV.isOpenEmbedding_subtypeVal.comp f.isOpenEmbedding).comp (he.restrictPreimage U)
  exact ⟨e ⁻¹' U, range m, hU.preimage he.continuous, hm.isOpen_range, hx,
    ⟨hm.isEmbedding.toHomeomorph⟩⟩

/-- An interior point has arbitrarily small discs around it. -/
theorem IsInteriorPoint.exists_subset {Y : Type u} [TopologicalSpace Y] {y : Y}
    (h : IsInteriorPoint y) {W : Set Y} (hW : IsOpen W) (hy : y ∈ W) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ W ∧ Nonempty (U ≃ₜ OpenUnitDisc) := by
  obtain ⟨U, hU, hyU, ⟨f⟩⟩ := h
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  have : Nonempty Y := ⟨y⟩
  obtain ⟨h', g, h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (f.trans b.symm)
  have hO : IsOpen (ball (0 : ℂ) 1 ∩ g ⁻¹' W) := h2.isOpen_inter_preimage isOpen_ball hW
  have hmem : h' y ∈ ball (0 : ℂ) 1 ∩ g ⁻¹' W := ⟨h3 hyU, by
    change g (h' y) ∈ W
    rwa [h5 hyU]⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hO _ hmem
  have himg : g '' ball (h' y) ρ = U ∩ h' ⁻¹' ball (h' y) ρ := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨h4 (hsub hz).1, ?_⟩
      change h' (g z) ∈ ball (h' y) ρ
      rwa [h6 (hsub hz).1]
    · rintro ⟨h7, h8⟩
      exact ⟨h' p, h8, h5 h7⟩
  have hUo : IsOpen (U ∩ h' ⁻¹' ball (h' y) ρ) := h1.isOpen_inter_preimage hU isOpen_ball
  obtain ⟨E, -⟩ := exists_homeomorph_image (f := g) (f' := h') (Δ := ball (h' y) ρ)
    (h2.mono fun z hz => (hsub hz).1) (h1.mono (by rw [himg]; exact inter_subset_left))
    (h6.mono fun z hz => (hsub hz).1)
  obtain ⟨b'⟩ := exists_homeomorph_ball (h' y) hρ
  refine ⟨_, hUo, ⟨hyU, mem_ball_self hρ⟩, ?_, ⟨?_⟩⟩
  · rw [← himg]
    rintro _ ⟨z, hz, rfl⟩
    exact (hsub hz).2
  · exact (Homeomorph.setCongr himg.symm).trans (E.symm.trans b')

/-- Interior points are detected in an open embedding. -/
theorem isInteriorPoint_iff_of_isOpenEmbedding {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {e : X → Y} (he : IsOpenEmbedding e) {x : X} :
    IsInteriorPoint (e x) ↔ IsInteriorPoint x := by
  refine ⟨fun h => ?_, isInteriorPoint_of_isOpenEmbedding he⟩
  obtain ⟨U, hU, hx, hsub, ⟨f⟩⟩ := h.exists_subset he.isOpen_range ⟨x, rfl⟩
  have hr : e '' (e ⁻¹' U) = U := image_preimage_eq_of_subset hsub
  exact ⟨e ⁻¹' U, hU.preimage he.continuous, hx,
    ⟨(he.isEmbedding.homeomorphImage _).trans ((Homeomorph.setCongr hr).trans f)⟩⟩

/-- A continuous injective map on a compact set has a continuous inverse on its image. -/
theorem exists_inv_of_compactOn {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [Nonempty X] {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K)
    (hinj : InjOn f K) : ∃ f' : Y → X, ContinuousOn f' (f '' K) ∧ LeftInvOn f' f K := by
  classical
  by_cases hne : K.Nonempty
  · have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have : Nonempty K := hne.to_subtype
    have hemb : IsEmbedding (fun x : K => f x.1) :=
      ((continuousOn_iff_continuous_domRestrict.mp hf).isClosedEmbedding
        fun x y h => Subtype.ext (hinj x.2 y.2 h)).isEmbedding
    obtain ⟨f', hc, hl⟩ := exists_inv_of_isEmbedding hemb
    have hr : range (fun x : K => f x.1) = f '' K := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hr] at hc
    exact ⟨fun y => (f' y).1, continuous_subtype_val.comp_continuousOn hc,
      fun x hx => congrArg Subtype.val (hl ⟨x, hx⟩)⟩
  · obtain ⟨x₀⟩ := ‹Nonempty X›
    refine ⟨fun _ => x₀, continuousOn_const, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- A continuous injective map on a compact set of `ℂ` gives an interior point, as soon as the image
of an open subset is open. This is how pasted charts are checked. -/
theorem isInteriorPoint_of_injOn {Y : Type v} [TopologicalSpace Y] [T2Space Y] {K V : Set ℂ}
    (hK : IsCompact K) {Ψ : ℂ → Y} (hΨ : ContinuousOn Ψ K) (hi : InjOn Ψ K) (hVK : V ⊆ K)
    (hV : IsOpen V) (hopen : IsOpen (Ψ '' V)) {c : ℂ} (hc : c ∈ V) : IsInteriorPoint (Ψ c) := by
  obtain ⟨f', hf', hl⟩ := exists_inv_of_compactOn hK hΨ hi
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hV c hc
  have hf'V : ContinuousOn f' (Ψ '' V) := hf'.mono (image_mono hVK)
  have himg : Ψ '' ball c ρ = Ψ '' V ∩ f' ⁻¹' ball c ρ := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hsub hz, rfl⟩, ?_⟩
      change f' (Ψ z) ∈ ball c ρ
      rwa [hl (hVK (hsub hz))]
    · rintro ⟨⟨z, hz, rfl⟩, h⟩
      have h' : f' (Ψ z) ∈ ball c ρ := h
      rw [hl (hVK hz)] at h'
      exact ⟨z, h', rfl⟩
  have hUo : IsOpen (Ψ '' V ∩ f' ⁻¹' ball c ρ) := hf'V.isOpen_inter_preimage hopen isOpen_ball
  have hmc : ContinuousOn Ψ (ball c ρ) := hΨ.mono fun z hz => hVK (hsub hz)
  obtain ⟨E, -⟩ := exists_homeomorph_image (f := Ψ) (f' := f') (Δ := ball c ρ) hmc
    (hf'.mono (image_mono fun z hz => hVK (hsub hz))) (hl.mono fun z hz => hVK (hsub hz))
  obtain ⟨b⟩ := exists_homeomorph_ball c hρ
  have hUo' : IsOpen (Ψ '' ball c ρ) := himg ▸ hUo
  exact ⟨_, hUo', ⟨c, mem_ball_self hρ, rfl⟩, ⟨E.symm.trans b⟩⟩

end GraphMinor.Surface
