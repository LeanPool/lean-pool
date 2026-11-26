/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import LeanPool.GraphMinor.GM19.CuffPieces
public import LeanPool.GraphMinor.GM19.CutMap
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import LeanPool.GraphMinor.Surface.CutComp

/-!
# Lifting sets along a fragment

Let `Σ₁` be a fragment of `Σ` after cutting along `U(K)`, with its associated surjection `ψ`. Then
`ψ` maps
the interior of `Σ₁` homeomorphically onto a component `R` of `Σ \ (bd(Σ) ∪ U(K))`. This file proves
that,
and then studies the closure of the lift of a set `A ⊆ R`. If `A` is connected near a point `v`,
then the
closure of the lift of `A` has just one point over `v`. So the closure of the lift of an edge of a
painting is a copy of the closure of the edge (`homeoClosure`).
-/

@[expose] public section

namespace GraphMinor.GM19

universe u

open Set Topology GraphMinor.Surface

variable {S S₁ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] [T2Space S] [T2Space S₁]
  {K : Drawing S} {ψ : S₁ → S}

namespace IsCuttingFragment

/-- The part of `Σ` that the interior of the fragment covers. -/
def R (ψ : S₁ → S) : Set S := ψ '' (bd S₁)ᶜ

section Fragment

variable {A : Set S} (h : IsCuttingFragment S K S₁ ψ)
include h

omit [T2Space S₁] in
theorem isClosedMap : IsClosedMap ψ :=
  have : CompactSpace S₁ := h.isSurface.1
  h.continuous_ψ.isClosedMap

omit [T2Space S] [T2Space S₁] in
theorem notMem_R_of_bd {x : S₁} (hx : x ∈ bd S₁) : ψ x ∉ R ψ := fun hR ↦
  disjoint_left.mp h.maps_interior_disjoint hR (h.maps_bd (mem_image_of_mem ψ hx))

omit [T2Space S] [T2Space S₁] in
theorem mem_R_iff {x : S₁} : ψ x ∈ R ψ ↔ x ∉ bd S₁ :=
  ⟨fun hR hx ↦ h.notMem_R_of_bd hx hR, fun hx ↦ mem_image_of_mem ψ hx⟩

omit [T2Space S] [T2Space S₁] in
theorem disjoint_R : Disjoint (R ψ) (bd S ∪ K.U) := h.maps_interior_disjoint

omit [T2Space S] [T2Space S₁] in
theorem isOpen_R (hS : IsSurface S) (hK : IsClosed K.U) : IsOpen (R ψ) := by
  have : LocallyConnectedSpace S := IsSurface.locallyConnected hS
  obtain ⟨x, hx, hR⟩ := h.interior_component
  rw [R, ← hR]
  exact IsOpen.connectedComponentIn (((cuff_statement S hS).1.union hK).isOpen_compl)

omit [T2Space S₁] in
/-- `ψ` maps open subsets of the interior to open sets. -/
theorem isOpen_image (hR : IsOpen (R ψ)) {W : Set S₁} (hW : W ⊆ (bd S₁)ᶜ) (hWo : IsOpen W) :
    IsOpen (ψ '' W) := by
  have heq : ψ '' W = R ψ \ ψ '' Wᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem ψ (hW hx), ?_⟩
      rintro ⟨z, hz, hzx⟩
      by_cases hzb : z ∈ bd S₁
      · exact h.notMem_R_of_bd hzb (hzx ▸ mem_image_of_mem ψ (hW hx))
      · exact hz (h.injOn_interior hzb (hW hx) hzx ▸ hx)
    · rintro ⟨⟨z, hz, rfl⟩, hn⟩
      by_contra hne
      exact hn ⟨z, fun hzW ↦ hne (mem_image_of_mem ψ hzW), rfl⟩
  rw [heq]
  exact hR.sdiff (h.isClosedMap _ hWo.isClosed_compl)

/-- `ψ` as a bijection from the interior onto `R`. -/
noncomputable def intEquiv : ↥(bd S₁)ᶜ ≃ ↥(R ψ) :=
  Equiv.ofBijective (fun x : ↥(bd S₁)ᶜ ↦ (⟨ψ x.1, mem_image_of_mem ψ x.2⟩ : ↥(R ψ)))
    ⟨fun _ _ hxy ↦ Subtype.ext (h.injOn_interior (Subtype.property _) (Subtype.property _)
      (congrArg Subtype.val hxy)), by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩⟩

omit [T2Space S₁] in
theorem isOpenMap_intEquiv (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) :
    IsOpenMap (h.intEquiv) := by
  intro W hW
  have hW' := hbd.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap W hW
  have himg := h.isOpen_image hR (W := Subtype.val '' W) (by rintro _ ⟨x, -, rfl⟩; exact x.2) hW'
  refine (hR.isOpenEmbedding_subtypeVal.isInducing.isOpen_iff).mpr ⟨_, himg, ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x.1, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩

/-- The inverse of `ψ` on the interior is continuous: `ψ` is a homeomorphism from the interior of
the
fragment onto `R`. -/
noncomputable def intHomeo (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) :
    ↥(bd S₁)ᶜ ≃ₜ ↥(R ψ) :=
  h.intEquiv.toHomeomorphOfContinuousOpen
    ((h.continuous_ψ.comp continuous_subtype_val).subtype_mk _) (h.isOpenMap_intEquiv hbd hR)

omit [T2Space S₁] in
theorem intHomeo_apply (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) (x : ↥(bd S₁)ᶜ) :
    (h.intHomeo hbd hR x).1 = ψ x.1 := rfl

omit [T2Space S₁] in
/-- The lift of a subset of `R` is the homeomorphic image of the subset. -/
theorem preimage_eq (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) {A : Set S} (hA : A ⊆ R ψ) :
    ψ ⁻¹' A = Subtype.val '' ((h.intHomeo hbd hR).symm '' (Subtype.val ⁻¹' A)) := by
  ext x
  constructor
  · intro hx
    have hxi : x ∉ bd S₁ := h.mem_R_iff.mp (hA hx)
    refine ⟨⟨x, hxi⟩, ⟨h.intHomeo hbd hR ⟨x, hxi⟩, hx, by simp⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyy : ψ ((h.intHomeo hbd hR).symm y).1 = y.1 := by
      rw [← h.intHomeo_apply hbd hR, Homeomorph.apply_symm_apply]
    change ψ _ ∈ A
    rw [hyy]
    exact hy

omit [T2Space S₁] in
theorem isPathConnected_preimage (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) {A : Set S}
    (hA : A ⊆ R ψ) (hAc : IsPathConnected A) : IsPathConnected (ψ ⁻¹' A) := by
  rw [h.preimage_eq hbd hR hA]
  refine IsPathConnected.image ?_ continuous_subtype_val
  refine IsPathConnected.image ?_ (h.intHomeo hbd hR).symm.continuous
  rw [IsInducing.subtypeVal.isPathConnected_iff, image_preimage_eq_of_subset]
  · exact hAc
  · rwa [Subtype.range_coe]

omit [T2Space S₁] in
theorem isPreconnected_preimage (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) {A : Set S}
    (hA : A ⊆ R ψ) (hAc : IsPreconnected A) : IsPreconnected (ψ ⁻¹' A) := by
  rw [h.preimage_eq hbd hR hA]
  refine IsPreconnected.image ?_ _ continuous_subtype_val.continuousOn
  refine IsPreconnected.image ?_ _ (h.intHomeo hbd hR).symm.continuous.continuousOn
  rw [← IsInducing.subtypeVal.isPreconnected_image, image_preimage_eq_of_subset]
  · exact hAc
  · rwa [Subtype.range_coe]

/-- **One side at each point.** Let `A ⊆ R` be connected near `v`. Then the closure of the lift of
`A`
has at most one point over `v`. Two such points have disjoint open neighbourhoods. These can be
chosen
to cover the finite fibre, so they cover the lift of a small connected part of `A`, which meets
both. -/
theorem eq_of_mem_closure_preimage (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) {A : Set S} {v : S}
    (hA : A ⊆ R ψ)
    (hloc : ∀ W ∈ 𝓝 v, ∃ B ⊆ A ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 v, A ∩ W' ⊆ B) {v₁ v₂ : S₁}
    (h₁ : ψ v₁ = v) (h₂ : ψ v₂ = v) (hc₁ : v₁ ∈ closure (ψ ⁻¹' A)) (hc₂ : v₂ ∈ closure (ψ ⁻¹' A)) :
    v₁ = v₂ := by
  by_contra hne
  have hfin := h.finite_fibres v
  -- Separate `v₁` from the rest of the fibre.
  obtain ⟨U₁, U₂, hU₁, hU₂, hv₁, hv₂, hdis⟩ :
      ∃ U₁ U₂ : Set S₁, IsOpen U₁ ∧ IsOpen U₂ ∧ v₁ ∈ U₁ ∧ ψ ⁻¹' {v} \ {v₁} ⊆ U₂ ∧ Disjoint U₁ U₂
        := by
    have hcomp : IsCompact (ψ ⁻¹' {v} \ {v₁}) := (hfin.subset sdiff_subset).isCompact
    obtain ⟨U₁, U₂, hU₁, hU₂, hv, hsub, hd⟩ := SeparatedNhds.of_isCompact_isCompact
      (isCompact_singleton (x := v₁)) hcomp (by
        rw [disjoint_singleton_left]
        exact fun hx ↦ hx.2 rfl)
    exact ⟨U₁, U₂, hU₁, hU₂, hv rfl, hsub, hd⟩
  have hWo : IsOpen (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ := (h.isClosedMap _ (hU₁.union
    hU₂).isClosed_compl).isOpen_compl
  have hvW : v ∈ (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ := by
    rintro ⟨x, hx, hxv⟩
    by_cases hxv₁ : x = v₁
    · exact hx (Or.inl (hxv₁ ▸ hv₁))
    · exact hx (Or.inr (hv₂ ⟨hxv, hxv₁⟩))
  obtain ⟨B, hBsub, hBc, W', hW', hsub⟩ := hloc _ (hWo.mem_nhds hvW)
  have hBA : B ⊆ R ψ := fun y hy ↦ hA (hBsub hy).1
  have hcov : ψ ⁻¹' B ⊆ U₁ ∪ U₂ := by
    intro x hx
    by_contra hnx
    exact (hBsub hx).2 ⟨x, hnx, rfl⟩
  have hpt : ∀ {w : S₁} {U : Set S₁}, ψ w = v → IsOpen U → w ∈ U → w ∈ closure (ψ ⁻¹' A) →
      (ψ ⁻¹' B ∩ U).Nonempty := by
    intro w U hw hU hwU hc
    have hn : U ∩ ψ ⁻¹' W' ∈ 𝓝 w :=
      Filter.inter_mem (hU.mem_nhds hwU) (h.continuous_ψ.continuousAt.preimage_mem_nhds
        (hw.symm ▸ hW'))
    obtain ⟨p, ⟨hpU, hpW⟩, hpA⟩ := mem_closure_iff_nhds.mp hc _ hn
    exact ⟨p, hsub ⟨hpA, hpW⟩, hpU⟩
  have hv₂U : v₂ ∈ U₂ := hv₂ ⟨h₂, fun hx ↦ hne hx.symm⟩
  obtain ⟨p, -, hp₁, hp₂⟩ := h.isPreconnected_preimage hbd hR hBA hBc U₁ U₂ hU₁ hU₂ hcov
    (hpt h₁ hU₁ hv₁ hc₁) (hpt h₂ hU₂ hv₂U hc₂)
  exact disjoint_left.mp hdis hp₁ hp₂

omit [T2Space S₁] in
/-- The closure of the lift of `A` maps onto the closure of `A`. -/
theorem image_closure_preimage (hA : A ⊆ R ψ) : ψ '' closure (ψ ⁻¹' A) = closure A := by
  have hsur : ψ '' (ψ ⁻¹' A) = A := image_preimage_eq_of_subset (hA.trans (image_subset_range _ _))
  refine Subset.antisymm ?_ ?_
  · refine (image_closure_subset_closure_image h.continuous_ψ).trans (closure_mono hsur.subset)
  · conv_lhs => rw [← hsur]
    exact (h.isClosedMap.closure_image_subset _)

/-- `ψ` as a map from the closure of the lift of `A` to the closure of `A`. -/
def closureMap (A : Set S) (hA : A ⊆ R ψ) : ↥(closure (ψ ⁻¹' A)) → ↥(closure A) := fun x ↦
  ⟨ψ x.1, h.image_closure_preimage hA ▸ mem_image_of_mem ψ x.2⟩

theorem bijective_closureMap (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) (hA : A ⊆ R ψ)
    (hloc : ∀ v ∈ tilde A, ∀ W ∈ 𝓝 v, ∃ B ⊆ A ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 v, A ∩ W' ⊆ B) :
    Function.Bijective (h.closureMap A hA) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : ψ x = ψ y := congrArg Subtype.val hxy
    refine Subtype.ext ?_
    change x = y
    by_cases hv : ψ x ∈ A
    · exact h.injOn_interior (h.mem_R_iff.mp (hA hv)) (h.mem_R_iff.mp (hA (hxy' ▸ hv))) hxy'
    · have hcl : ψ x ∈ closure A := (h.image_closure_preimage hA) ▸ mem_image_of_mem ψ hx
      exact h.eq_of_mem_closure_preimage hbd hR hA (hloc _ ⟨hcl, hv⟩) rfl hxy'.symm hx hy
  · rintro ⟨y, hy⟩
    rw [← h.image_closure_preimage hA] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

/-- If `A ⊆ R` is connected near each point of its frontier, then `ψ` maps the closure of the lift
of `A`
homeomorphically onto the closure of `A`. The map is a continuous bijection from a compact space to
a
Hausdorff space. -/
noncomputable def homeoClosure (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) (hA : A ⊆ R ψ)
    (hloc : ∀ v ∈ tilde A, ∀ W ∈ 𝓝 v, ∃ B ⊆ A ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 v, A ∩ W' ⊆ B) :
    ↥(closure (ψ ⁻¹' A)) ≃ₜ ↥(closure A) :=
  have : CompactSpace S₁ := h.isSurface.1
  have : CompactSpace ↥(closure (ψ ⁻¹' A)) := isCompact_iff_compactSpace.mp
    isClosed_closure.isCompact
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (h.bijective_closureMap hbd hR hA
    hloc))
    ((h.continuous_ψ.comp continuous_subtype_val).subtype_mk _)

theorem homeoClosure_apply (hbd : IsClosed (bd S₁)) (hR : IsOpen (R ψ)) (hA : A ⊆ R ψ)
    (hloc : ∀ v ∈ tilde A, ∀ W ∈ 𝓝 v, ∃ B ⊆ A ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 v, A ∩ W' ⊆ B)
    (x : ↥(closure (ψ ⁻¹' A))) : (h.homeoClosure hbd hR hA hloc x).1 = ψ x.1 := rfl

omit [T2Space S₁] in
/-- The closure of the lift has the frontier one expects: a point over `tilde A`, and only such
points. -/
theorem image_tilde_preimage (hA : A ⊆ R ψ) : ψ '' tilde (ψ ⁻¹' A) = tilde A := by
  have hsur : ψ '' (ψ ⁻¹' A) = A := image_preimage_eq_of_subset (hA.trans (image_subset_range _ _))
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    exact ⟨h.image_closure_preimage hA ▸ mem_image_of_mem ψ hx, hxn⟩
  · rintro ⟨hy, hyn⟩
    rw [← h.image_closure_preimage hA] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨hx, hyn⟩, rfl⟩

end Fragment

end IsCuttingFragment

/-! ### Connected near a point -/

/-- `A` is connected near `v`: inside any neighbourhood of `v` there is a connected part of `A` that
holds
all of `A` near `v`. -/
def IsConnectedNear (A : Set S) (v : S) : Prop :=
  ∀ W ∈ 𝓝 v, ∃ B ⊆ A ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 v, A ∩ W' ⊆ B

/-- A homeomorphism from a compact space `X` onto `closure A` carries the property to `A` from a
subset of
`X`. If `B ⊆ X` has, for each `ε`-neighbourhood of `p`, a connected part as in `IsConnectedNear`,
then
so does its image. -/
theorem isConnectedNear_of_homeo {X : Type} [TopologicalSpace X] [CompactSpace X] {L : Set S}
    (f : X ≃ₜ L) {Y : Set X} {p : X}
    (hY : ∀ W ∈ 𝓝 p, ∃ B ⊆ Y ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 p, Y ∩ W' ⊆ B) :
    IsConnectedNear ((fun x ↦ (f x).1) '' Y) (f p).1 := by
  intro W hW
  have hcont : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp f.continuous
  obtain ⟨B, hB, hBc, W', hW', hsub⟩ := hY _ (hcont.continuousAt.preimage_mem_nhds hW)
  refine ⟨_, ?_, hBc.image _ hcont.continuousOn, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ (hB hx).1, (hB hx).2⟩
  -- The part of `L` far from `p` is compact and misses `f p`.
  obtain ⟨O, hOW, hO, hpO⟩ := mem_nhds_iff.mp hW'
  have hclosed : IsClosed ((fun x ↦ (f x).1) '' Oᶜ) :=
    (hO.isClosed_compl.isCompact.image hcont).isClosed
  refine ⟨_, hclosed.isOpen_compl.mem_nhds ?_, ?_⟩
  · rintro ⟨x, hx, hxp⟩
    have : x = p := f.injective (Subtype.ext hxp)
    exact hx (this ▸ hpO)
  · rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    have hxO : x ∈ O := by
      by_contra hxO
      exact hn ⟨x, hxO, rfl⟩
    exact mem_image_of_mem _ (hsub ⟨hx, hOW hxO⟩)

/-- In a convex set `C`, take a finite set `T` and a point `p ∈ T` that is extreme in `C`. Then the
complement of `T` in `C` is connected near `p`: a small ball around `p` with `p` removed is convex.
-/
theorem connected_near_extreme {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {p :
  C}
    (_hconv : Convex ℝ C) (hext : Convex ℝ (C \ {p.1})) {T : Set C} (hT : T.Finite) (hp : p ∈ T) :
    ∀ W ∈ 𝓝 p, ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 p, Tᶜ ∩ W' ⊆ B := by
  intro W hW
  have hcl : (T \ {p})ᶜ ∈ 𝓝 p :=
    (hT.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW hcl)
  refine ⟨Metric.ball p ε ∩ {p}ᶜ, ?_, ?_, Metric.ball p ε, Metric.ball_mem_nhds p hε, ?_⟩
  · rintro x ⟨hx, hxp⟩
    exact ⟨fun hxT ↦ (hsub hx).2 ⟨hxT, hxp⟩, (hsub hx).1⟩
  · rw [← IsInducing.subtypeVal.isPreconnected_image]
    have himg : Subtype.val '' (Metric.ball p ε ∩ {p}ᶜ) = (C \ {p.1}) ∩ Metric.ball p.1 ε := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
        exact ⟨⟨y.2, fun h ↦ hyp (Subtype.ext h)⟩, hy⟩
      · rintro ⟨⟨hxC, hxp⟩, hx⟩
        exact ⟨⟨x, hxC⟩, ⟨hx, fun h ↦ hxp (congrArg Subtype.val h)⟩, rfl⟩
    rw [himg]
    exact (hext.inter (convex_ball _ _)).isPreconnected
  · rintro x ⟨hxT, hx⟩
    exact ⟨hx, fun h ↦ hxT (h ▸ hp)⟩

/-- A point of the unit circle is extreme in the closed disc, since the disc is strictly convex. -/
theorem convex_disc_sdiff {p : EuclideanPlane} (hp : p ∈ UnitCircle) :
    Convex ℝ (ClosedUnitDisc \ {p}) := by
  have hstrict : StrictConvex ℝ ClosedUnitDisc := strictConvex_closedBall ℝ _ _
  have hconv : Convex ℝ ClosedUnitDisc := convex_closedBall _ _
  rintro x ⟨hx, hxp⟩ y ⟨hy, hyp⟩ a b ha hb hab
  refine ⟨hconv hx hy ha hb hab, fun h ↦ ?_⟩
  have h' : a • x + b • y = p := h
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    exact hyp (by simpa [hb1] using h')
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    exact hxp (by simpa [ha1] using h')
  by_cases hxy : x = y
  · subst hxy
    rw [← add_smul, hab, one_smul] at h'
    exact hxp h'
  have hint := hstrict.openSegment_subset hx hy hxy ⟨a, b, ha', hb', hab, h'⟩
  have hint' : p ∈ Metric.ball (0 : EuclideanPlane) 1 := by
    have := hint
    rwa [ClosedUnitDisc, interior_closedBall _ one_ne_zero] at this
  have hp' : dist p 0 = 1 := hp
  exact absurd (Metric.mem_ball.mp hint') (by rw [hp']; exact lt_irrefl _)

/-- An edge of a painting is connected near each of its ends. -/
theorem Painting.isConnectedNear (Γ : Painting S) {e : Set S}
    (he : e ∈ Γ.E) {v : S} (hv : v ∈ tilde e) : IsConnectedNear e v := by
  have hfin : (tilde e).Finite := (Γ.finite_V.subset (Γ.tilde_subset_V he))
  have hcore : ∀ {X : Type} [TopologicalSpace X] (f : X ≃ₜ ↥(closure e)) {T : Set X} {p : X},
      f p = v → (∀ x, x ∈ T ↔ (f x).1 ∈ tilde e) →
      [CompactSpace X] →
      (∀ W ∈ 𝓝 p, ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 p, Tᶜ ∩ W' ⊆ B) →
      IsConnectedNear e v := by
    intro X _ f T p hp hT _ hY
    have himg : (fun x ↦ (f x).1) '' Tᶜ = e := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_contra hne
        exact hx ((hT x).mpr ⟨(f x).2, hne⟩)
      · intro hy
        refine ⟨f.symm ⟨y, subset_closure hy⟩, fun hx ↦ ?_, by simp⟩
        have := ((hT _).mp hx).2
        simp only [Homeomorph.apply_symm_apply] at this
        exact this hy
    have h := isConnectedNear_of_homeo f hY
    rw [himg, hp] at h
    exact h
  have hfinT : ∀ {X : Type} [TopologicalSpace X] (f : X ≃ₜ ↥(closure e)), ({x |
    (f x).1 ∈ tilde e}).Finite := by
    intro X _ f
    refine Set.Finite.of_injOn (f := fun x ↦ (f x).1) (t := tilde e) (fun x hx ↦ hx) ?_ hfin
    exact fun x _ y _ hxy ↦ f.injective (Subtype.ext hxy)
  rcases Γ.edge_shape e he with ⟨-, -, -, hends⟩ | ⟨-, -, ⟨φ⟩, hsub⟩
  · rw [← hends] at hv
    obtain ⟨w, f, hf₀, hf₁⟩ := hv
    refine hcore f (T := {x | (f x).1 ∈ tilde e}) (p := 0) hf₀ (fun _ ↦ Iff.rfl) ?_
    refine connected_near_extreme (C := Icc (0 : ℝ) 1) (convex_Icc _ _) ?_ (hfinT f) ?_
    · have heq : Icc (0 : ℝ) 1 \ {((0 : unitInterval) : ℝ)} = Ioc 0 1 := by
        ext x
        simp only [mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ioc, Set.Icc.coe_zero]
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          exact ⟨lt_of_le_of_ne h₁ (Ne.symm h₃), h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨⟨h₁.le, h₂⟩, h₁.ne'⟩
      exact heq ▸ convex_Ioc (0 : ℝ) 1
    · change (f 0).1 ∈ tilde e
      rw [hf₀, ← hends]
      exact ⟨w, f, hf₀, hf₁⟩
  · have hvb := hsub hv
    rw [disc_boundary (closure e) φ] at hvb
    obtain ⟨x, hx, hxv⟩ := hvb
    have : CompactSpace ClosedUnitDisc :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    refine hcore φ (T := {y | (φ y).1 ∈ tilde e}) (p := x) hxv (fun _ ↦ Iff.rfl) ?_
    refine connected_near_extreme (C := ClosedUnitDisc) (convex_closedBall _ _)
      (convex_disc_sdiff hx) (hfinT φ) ?_
    have hxv' : (φ x).1 = v := hxv
    change (φ x).1 ∈ tilde e
    rw [hxv']
    exact hv

end GraphMinor.GM19
