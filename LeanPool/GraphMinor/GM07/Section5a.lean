/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11
public import LeanPool.GraphMinor.GM07.Section11a
public import LeanPool.GraphMinor.GM07.Section11g
public import LeanPool.GraphMinor.GM07.AlphaExists
public import LeanPool.GraphMinor.Surface.CutOArc
public import LeanPool.GraphMinor.Surface.PasteDisc
public import LeanPool.GraphMinor.Surface.DiscsInSurface
public import LeanPool.GraphMinor.Surface.ModelCriterion
public import LeanPool.GraphMinor.GM11.Nice73
public import LeanPool.GraphMinor.GM11.PolarChart
import LeanPool.GraphMinor.GM19.Section6a

/-!
# Graph Minors VII, Section 5 (Part A): (5.2)–(5.4)

This file formalizes the first part of Section 5 of Robertson and Seymour,
*Graph Minors. VII. Disjoint Paths on a Surface*, J. Combin. Theory Ser. B **45** (1988), 212–254:
- `cappedCuff_homeo_model`: pasting a closed disc onto a cuff of `SurfaceModel a b c` yields a
  connected surface homeomorphic to `SurfaceModel a b (c - 1)` with `1 ≤ c`.
- `theorem_5_2`: (5.2) (page 230).
- `surroundsCuff_and_planarInCappedCuff_imp_cylinder`: if an `O`-arc surrounds a cuff `C` and is
  planar in `Σ + C'̂` for a cuff `C' ≠ C`, then `Σ ≅ Σ(0, 0, 2)`.
- `theorem_5_3`: (5.3) (page 231).
- `theorem_5_4`: (5.4) (page 231).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology unitInterval GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Capping a cuff of `SurfaceModel a b c` -/

/-- Every cuff of a surface `S` is a subset of `bd S`. -/
theorem cuff_subset_bd {C : Set S} (hC : C ∈ cuffs S) : C ⊆ bd S := by
  obtain ⟨x, _, rfl⟩ := hC
  exact connectedComponentIn_subset (bd S) x

/-- Every `O`-arc is nonempty. -/
theorem isOArc_nonempty {F : Set S} (hF : IsOArc F) : F.Nonempty := by
  obtain ⟨φ⟩ := id hF
  exact ⟨(φ 1).1, (φ 1).2⟩

/-- Every cuff of a surface `S` is an `O`-arc. -/
theorem cuff_isOArc (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) : IsOArc C :=
  (cuff_statement S hS).2.2 C hC

/-- Distinct cuffs of a surface `S` are disjoint. -/
theorem disjoint_cuffs {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C') :
    Disjoint C C' := by
  obtain ⟨x, _, rfl⟩ := hC
  obtain ⟨y, _, rfl⟩ := hC'
  refine disjoint_left.mpr fun z hzx hzy => hne ?_
  have h1 : connectedComponentIn (bd S) x = connectedComponentIn (bd S) z
    := connectedComponentIn_eq hzx
  have h2 : connectedComponentIn (bd S) y = connectedComponentIn (bd S) z
    := connectedComponentIn_eq hzy
  exact h1.trans h2.symm

/-- Being a surface is preserved under homeomorphism. -/
theorem isSurface_of_homeomorph {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : IsSurface Y) : IsSurface X := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  exact ⟨e.symm.surjective.compactSpace e.symm.continuous, e.isEmbedding.t2Space,
    fun x => (isManifoldPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mp (hY.2.2 (e x))⟩

/-- If `(S', ι, D)` is a capped cuff of a connected surface `S`, then `S'` is connected. -/
theorem IsCappedCuff.connectedSpace (hS : IsSurface S) [ConnectedSpace S]
    {C : Set S} {S' : Type u} [TopologicalSpace S'] {ι : S → S'} {D : Set S'}
    (hCap : IsCappedCuff C S' ι D) : ConnectedSpace S' := by
  have : T2Space S' := hCap.isSurface.2.1
  obtain ⟨x₀, hx₀⟩ := isOArc_nonempty (cuff_isOArc hS hCap.cuff)
  have hy : ι x₀ ∈ range ι ∩ D := hCap.inter_eq ▸ mem_image_of_mem ι hx₀
  have h1 : IsPreconnected (range ι) := isPreconnected_range hCap.isEmbedding.continuous
  have h2 : IsPreconnected D := hCap.isClosedDisc.isPathConnected.isConnected.isPreconnected
  have h3 := h1.union' ⟨ι x₀, hy.1, hy.2⟩ h2
  rw [hCap.union_eq] at h3
  exact { toPreconnectedSpace := ⟨h3⟩, toNonempty := ⟨ι x₀⟩ }

/-- Pasting a closed disc `D` onto a cuff `C` of `S ≃ₜ SurfaceModel a b c` produces a connected
surface `S'` with `1 ≤ c` and `Nonempty (S' ≃ₜ SurfaceModel a b (c - 1))`. -/
theorem cappedCuff_homeo_model
    (hS : IsSurface S) [ConnectedSpace S]
    {a b c : ℕ} (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    {C : Set S} (hC : C ∈ cuffs S)
    {S' : Type u} [TopologicalSpace S']
    {ι : S → S'} {D : Set S'} (hCap : IsCappedCuff C S' ι D) :
    1 ≤ c ∧ Nonempty (S' ≃ₜ SurfaceModel a b (c - 1)) := by
  classical
  obtain ⟨e₁₀⟩ := hmodel
  have hS' : IsSurface S' := hCap.isSurface
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := hCap.connectedSpace hS
  have hι : IsEmbedding ι := hCap.isEmbedding
  have hD : IsClosedDisc D := hCap.isClosedDisc
  have hdiscBdD : discBd D = ι '' C := hCap.discBd_eq
  have hmeet : range ι ∩ D = ι '' C := hCap.inter_eq
  have hcov : range ι ∪ D = univ := hCap.union_eq
  let Y := S ⊕ D
  let ψ : Y → S' := Sum.elim ι Subtype.val
  let F : Set S' := ι '' C
  let W₁ : Set Y := range Sum.inl
  let W₂ : Set Y := range Sum.inr
  let X : Set Y := Sum.inl '' C
  let X' : Set Y := Sum.inr '' {z : D | z.1 ∈ F}
  have hW₁ : IsClopen W₁ := isClopen_range_inl
  have hW₂ : IsClopen W₂ := isClopen_range_inr
  have hdW : Disjoint W₁ W₂ := isCompl_range_inl_range_inr.disjoint
  have hUW : W₁ ∪ W₂ = univ := isCompl_range_inl_range_inr.sup_eq_top
  obtain ⟨φD⟩ := id hD
  obtain ⟨eD₀⟩ := nonempty_disc_homeo
  have hD_surf : IsSurface D := isSurface_of_homeomorph (φD.symm.trans eD₀.symm)
    (isSurface_model 0 0 1).1
  have : CompactSpace D := hD_surf.1
  have : T2Space D := hD_surf.2.1
  have hY : IsSurface Y := by
    refine ⟨inferInstance, inferInstance, fun y => ?_⟩
    rcases y with s | d
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inl (hS.2.2 s)
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inr (hD_surf.2.2 d)
  have hbdY_inl : ∀ s ∈ bd S, (Sum.inl s : Y) ∈ bd Y := by
    intro s hs hint
    exact hs ((isInteriorPoint_iff_of_isOpenEmbedding IsOpenEmbedding.inl).mp hint)
  have hbdY_inr : ∀ d ∈ bd D, (Sum.inr d : Y) ∈ bd Y := by
    intro d hd hint
    exact hd ((isInteriorPoint_iff_of_isOpenEmbedding IsOpenEmbedding.inr).mp hint)
  have hbd_D_sub : {z : D | z.1 ∈ F} ⊆ bd D := by
    intro z hz
    have hz_bd : z.1 ∈ discBd D := hdiscBdD.symm ▸ hz
    rcases hz_bd with ⟨w, hw, hwz⟩
    exact (Subtype.ext hwz : w = z) ▸ hw
  have hψ_cont : Continuous ψ := continuous_sum_dom.mpr ⟨hι.continuous, continuous_subtype_val⟩
  have hψ_surj : Surjective ψ := by
    intro y
    have hy : y ∈ range ι ∪ D := hcov ▸ mem_univ y
    rcases hy with ⟨s, rfl⟩ | hyD
    · exact ⟨Sum.inl s, rfl⟩
    · exact ⟨Sum.inr ⟨y, hyD⟩, rfl⟩
  have hhun : X ∪ X' = ψ ⁻¹' F := by
    ext y
    rcases y with s | z
    · constructor
      · rintro (⟨s', hs', h⟩ | ⟨_, _, ⟨⟩⟩)
        exact Sum.inl.inj h ▸ mem_image_of_mem ι hs'
      · rintro ⟨s', hs', heq⟩
        exact Or.inl ⟨s', hs', congrArg Sum.inl (hι.injective heq)⟩
    · constructor
      · rintro (⟨_, _, ⟨⟩⟩ | ⟨z', hz', h⟩)
        exact Sum.inr.inj h ▸ hz'
      · intro hz
        exact Or.inr ⟨z, hz, rfl⟩
  have hψ_inj : InjOn ψ (ψ ⁻¹' Fᶜ) := by
    intro y₁ hy₁ y₂ hy₂ heq
    rcases y₁ with s₁ | z₁ <;> rcases y₂ with s₂ | z₂
    · exact congrArg Sum.inl (hι.injective heq)
    · exfalso
      change ι s₁ = z₂.1 at heq
      have : ι s₁ ∈ range ι ∩ D := ⟨mem_range_self s₁, heq.symm ▸ z₂.2⟩
      rw [hmeet] at this
      exact hy₁ this
    · exfalso
      change z₁.1 = ι s₂ at heq
      have : ι s₂ ∈ range ι ∩ D := ⟨mem_range_self s₂, heq ▸ z₁.2⟩
      rw [hmeet] at this
      exact hy₂ this
    · exact congrArg Sum.inr (Subtype.ext heq)
  have hψ_card : ∀ x ∈ F, (ψ ⁻¹' {x}).ncard = 2 := by
    rintro _ ⟨s, hs, rfl⟩
    have hD_mem : ι s ∈ D := (hmeet ▸ mem_image_of_mem ι hs).2
    have hpre : ψ ⁻¹' {ι s} = {Sum.inl s, Sum.inr ⟨ι s, hD_mem⟩} := by
      ext y
      rcases y with s' | z'
      · simp only [ψ, mem_preimage, mem_singleton_iff, Sum.elim_inl, mem_insert_iff,
          reduceCtorEq, or_false, hι.injective.eq_iff]
        exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
      · simp only [ψ, mem_preimage, mem_singleton_iff, Sum.elim_inr, mem_insert_iff,
          reduceCtorEq, false_or]
        exact ⟨fun h => congrArg Sum.inr (Subtype.ext h), fun h => congrArg Subtype.val
          (Sum.inr.inj h)⟩
    rw [hpre, ncard_pair Sum.inl_ne_inr]
  have ht₁ : X ⊆ bd Y := by
    rintro _ ⟨s, hs, rfl⟩
    exact hbdY_inl s (cuff_subset_bd hC hs)
  have ht₂ : X' ⊆ bd Y := by
    rintro _ ⟨z, hz, rfl⟩
    exact hbdY_inr z (hbd_D_sub hz)
  have hψ : IsCutting ψ F :=
    ⟨hψ_cont, hψ_surj, hψ_inj, hψ_card, hhun ▸ union_subset ht₁ ht₂⟩
  have b1 : BijOn ψ X F := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact mem_image_of_mem ι hs
    · rintro _ ⟨s₁, _, rfl⟩ _ ⟨s₂, _, rfl⟩ heq
      exact congrArg Sum.inl (hι.injective heq)
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨Sum.inl s, ⟨s, hs, rfl⟩, rfl⟩
  have b2 : BijOn ψ X' F := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · rintro _ ⟨z₁, _, rfl⟩ _ ⟨z₂, _, rfl⟩ heq
      exact congrArg Sum.inr (Subtype.ext heq)
    · rintro _ ⟨s, hs, rfl⟩
      have hD_mem : ι s ∈ D := (hmeet ▸ mem_image_of_mem ι hs).2
      exact ⟨Sum.inr ⟨ι s, hD_mem⟩, ⟨⟨ι s, hD_mem⟩, mem_image_of_mem ι hs, rfl⟩, rfl⟩
  have hC_oArc : IsOArc C := cuff_isOArc hS hC
  have hF_oArc : IsOArc F := isOArc_image hC_oArc hι.continuous.continuousOn hι.injective.injOn
  have hOX : IsOArc X :=
    isOArc_image hC_oArc continuous_inl.continuousOn Sum.inl_injective.injOn
  have hOX' : IsOArc X' := by
    have hsub_oArc : IsOArc {z : D | z.1 ∈ F} := by
      obtain ⟨φF⟩ := id hF_oArc
      refine ⟨Homeomorph.trans φF ?_⟩
      have : CompactSpace {z : D | z.1 ∈ F} :=
        isCompact_iff_compactSpace.mp
          (hF_oArc.isCompact.isClosed.preimage continuous_subtype_val).isCompact
      exact (Continuous.homeoOfEquivCompactToT2
        (f := {
          toFun := fun z => ⟨z.1.1, z.2⟩
          invFun := fun x => ⟨⟨x.1, by
            have hx : x.1 ∈ ι '' C := x.2
            rw [← hmeet] at hx
            exact hx.2⟩, x.2⟩
          left_inv := fun z => rfl
          right_inv := fun x => rfl })
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)).symm
    exact isOArc_image hsub_oArc continuous_inr.continuousOn Sum.inr_injective.injOn
  let eW₁ : W₁ ≃ₜ SurfaceModel a b c :=
    (IsOpenEmbedding.inl.toIsEmbedding.toHomeomorph).symm.trans e₁₀
  let eW₂ : W₂ ≃ₜ SurfaceModel 0 0 1 :=
    (IsOpenEmbedding.inr.toIsEmbedding.toHomeomorph).symm.trans (φD.symm.trans eD₀.symm)
  have s₁ : X ⊆ W₁ := image_subset_range _ _
  have s₂ : X' ⊆ W₂ := image_subset_range _ _
  obtain ⟨i, j, sig, f, -, -, hi, hj, hf, -⟩ :=
    loop_comps_aux hY hψ hhun b1 b2 hOX hOX' hW₁ hW₂ hdW hUW eW₁ eW₂ s₁ s₂ ht₁ ht₂
  obtain ⟨hN₁, hL₁⟩ := erase_facts c i
  obtain ⟨hN₂, hL₂⟩ := erase_facts 1 j
  obtain ⟨e'⟩ := homeo_of_two_loop hi hj hN₁ hN₂ hL₁ hL₂ hf
  rw [length_erase_range hi, length_erase_range hj] at e'
  have heq : 0 + a = a ∧ 0 + b = b ∧ 1 - 1 + (c - 1) = c - 1 := ⟨by omega, by omega, by omega⟩
  rw [heq.1, heq.2.1, heq.2.2] at e'
  exact ⟨by omega, ⟨e'⟩⟩

/-! ## 2. Proof of (5.2) -/

/-- If `bd S ≠ ∅`, any solid flat subset `X ⊆ S` of a connected surface `S` is planar (from (11.9)
and `solidFlat_boundarySurface_planar_core`). -/
theorem isPlanar_of_solid_flat_bd_ne_empty
    (hS : IsSurface S) (hbd : bd S ≠ ∅) [ConnectedSpace S] {X : Set S}
    (hX_solid : IsSolid X) (hX_flat : IsFlat X) :
    IsPlanar X := by
  obtain ⟨Y, hXY, hY_open, hY_sc, _⟩ :=
    theorem_11_9_proof hS hX_flat hX_solid.1 (Or.inl hX_solid.2)
  have : T2Space S := hS.2.1
  refine solidFlat_boundarySurface_planar_core hS hbd hX_solid.2 hXY hY_open
    (IsArcConnected.isPreconnected hY_sc.1) fun F hFY hF => ?_
  obtain ⟨Δ, hΔ, hΔ_bd, hΔY⟩ := hY_sc.2 F hF hFY
  exact ⟨Δ, hΔY, hΔ, hΔ_bd⟩

/-- Monotonicity of `IsPlanar`. -/
theorem IsPlanar.mono {X Y : Set S} (hY : IsPlanar Y) (hXY : X ⊆ Y) : IsPlanar X := by
  obtain ⟨Δ, hΔ, hYΔ⟩ := hY
  exact ⟨Δ, hΔ, hXY.trans hYΔ⟩

/-- Monotonicity of `IsPlanarInCappedCuff`. -/
theorem IsPlanarInCappedCuff.mono {C X Y : Set S}
    (hY : IsPlanarInCappedCuff C Y) (hXY : X ⊆ Y) : IsPlanarInCappedCuff C X := by
  refine ⟨hY.1, ?_, fun S' _ j D hCap => IsPlanar.mono (hY.2.2 S' j D hCap) (image_mono hXY)⟩
  obtain ⟨S', hTS', j, D, hCap, hpl⟩ := hY.2.1
  exact ⟨S', hTS', j, D, hCap, IsPlanar.mono hpl (image_mono hXY)⟩

/-- An `O`-arc `F` in a surface `S` is planar if and only if it is null-homotopic in `S`. -/
theorem isPlanar_iff_isNullHomotopicOArc_of_isOArc
    (hS : IsSurface S) {F : Set S} (hF : IsOArc F) :
    IsPlanar F ↔ IsNullHomotopicOArc F := by
  constructor
  · rintro ⟨Δ, hΔ, hFΔ⟩
    exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ Δ) hΔ hFΔ
  · intro h
    obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hS hF h
    have : T2Space S := hS.2.1
    exact ⟨Δ, hΔ, hbd ▸ Surface.discBd_subset Δ⟩

/-- Pullback of `IsSolid` along a closed embedding `j : S → T`. -/
theorem isSolid_of_isClosedEmbedding_aux [T2Space S] {T : Type u} [TopologicalSpace T]
    {j : S → T} (hj : IsClosedEmbedding j) {Z : Set S} (hZ : IsSolid (j '' Z)) :
    IsSolid Z := by
  refine ⟨fun z hz U hU hzU => ?_, ?_⟩
  · obtain ⟨U_T, hU_T_open, rfl⟩ := hj.isInducing.isOpen_iff.mp hU
    obtain ⟨V_T, hVT_sub, hjz_VT, hVT_open, h_arc⟩ :=
      hZ.1 (j z) ⟨z, hz, rfl⟩ U_T hU_T_open hzU
    refine ⟨j ⁻¹' V_T, preimage_mono hVT_sub, hjz_VT, hVT_open.preimage hj.continuous, ?_⟩
    intro a ha b hb hab
    have hja : j a ∈ j '' Z ∩ V_T := ⟨⟨a, ha.1, rfl⟩, ha.2⟩
    have hjb : j b ∈ j '' Z ∩ V_T := ⟨⟨b, hb.1, rfl⟩, hb.2⟩
    obtain ⟨F_T, hFT_sub, hFT_line⟩ := h_arc (j a) hja (j b) hjb (hj.injective.ne hab)
    have hFT_range : F_T ⊆ range j := fun y hy => by
      obtain ⟨w, _, rfl⟩ := (hFT_sub hy).1
      exact ⟨w, rfl⟩
    obtain ⟨a', b', ha', hb', h_line⟩ := hFT_line.pull hj.isEmbedding hFT_range
    obtain rfl : a' = a := hj.injective ha'
    obtain rfl : b' = b := hj.injective hb'
    refine ⟨j ⁻¹' F_T, fun x hx => ?_, h_line⟩
    obtain ⟨⟨w, hwZ, hjw⟩, hxVT⟩ := hFT_sub hx
    obtain rfl : w = x := hj.injective hjw
    exact ⟨hwZ, hxVT⟩
  · have h_pre : Z = j ⁻¹' (j '' Z) := (preimage_image_eq Z hj.injective).symm
    rw [h_pre]
    exact hZ.2.preimage hj.continuous

/-- A preconnected set meeting a clopen set is contained in it. -/
theorem subset_of_isPreconnected_isClopen {A : Type*} [TopologicalSpace A] {P U : Set A}
    (hP : IsPreconnected P) (hU : IsClopen U) (hne : (P ∩ U).Nonempty) : P ⊆ U :=
  hP.subset_left_of_subset_union hU.2 hU.compl.2 disjoint_compl_right (by simp) hne

/-- Image of a closed disc under a continuous injection into a Hausdorff space is a closed disc. -/
theorem isClosedDisc_image_of_injective {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [T2Space B] {f : A → B} (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    {Δ : Set A} (hΔ : IsClosedDisc Δ) : IsClosedDisc (f '' Δ) := by
  have : CompactSpace Δ := isCompact_iff_compactSpace.mp (IsClosedDisc.isCompact hΔ)
  obtain ⟨e⟩ := hΔ
  let g : Δ → f '' Δ := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  have hg_cont : Continuous g := Continuous.subtype_mk (hf_cont.comp continuous_subtype_val) _
  have hg_bij : Function.Bijective g := by
    refine ⟨fun x₁ x₂ h => Subtype.ext (hf_inj (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨e.trans (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij) hg_cont)⟩

/-- Preimage of a closed disc `Δ₀ ⊆ range f` under a continuous injection from a compact space is a
closed disc. -/
theorem isClosedDisc_preimage_of_subset_range {A B : Type*} [TopologicalSpace A] [TopologicalSpace
  B]
    [CompactSpace A] [T2Space B] {f : A → B} (hf_cont : Continuous f)
      (hf_inj : Function.Injective f)
    {Δ₀ : Set B} (hΔ₀ : IsClosedDisc Δ₀) (hsub : Δ₀ ⊆ range f) : IsClosedDisc (f ⁻¹' Δ₀) := by
  have : CompactSpace (f ⁻¹' Δ₀) := isCompact_iff_compactSpace.mp
    (((IsClosedDisc.isCompact hΔ₀).isClosed.preimage hf_cont).isCompact)
  obtain ⟨e⟩ := hΔ₀
  let g : f ⁻¹' Δ₀ → Δ₀ := fun x => ⟨f x.1, x.2⟩
  have hg_cont : Continuous g := Continuous.subtype_mk (hf_cont.comp continuous_subtype_val) _
  have hg_bij : Function.Bijective g := by
    refine ⟨fun x₁ x₂ h => Subtype.ext (hf_inj (congrArg Subtype.val h)), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hsub hy
    exact ⟨⟨a, hy⟩, rfl⟩
  exact ⟨e.trans (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)
    hg_cont).symm⟩

/-- Graph Minors VII, (5.2) (page 230):
"If $X \subseteq \Sigma$ is solid and $X$ is planar in $\Sigma + \hat{C}$, where $C$ is a cuff,
then $X$ surrounds $C$ in $\Sigma$ if and only if some $O$-arc included in $X$ surrounds $C$." -/
theorem theorem_5_2_proof
    (hS : IsSurface S) {X C : Set S}
    (hX_solid : IsSolid X) (hXC : IsPlanarInCappedCuff C X) :
    SurroundsCuff X C ↔ ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ SurroundsCuff F C := by
  constructor
  · intro hSurr
    have : CompactSpace S := hS.1
    have : T2Space S := hS.2.1
    have : LocallyConnectedSpace S := hS.locallyConnected
    have hC : C ∈ cuffs S := hXC.1
    obtain ⟨c₀, hc₀⟩ := isOArc_nonempty (cuff_isOArc hS hC)
    by_contra! hall
    obtain ⟨S', topS', j, D, hCap, Δ₀, hΔ₀, hXΔ₀⟩ := hXC.2.1
    have hS' : IsSurface S' := hCap.isSurface
    have : CompactSpace S' := hS'.1
    have : T2Space S' := hS'.2.1
    have hj_cont : Continuous j := hCap.isEmbedding.continuous
    have hj_inj : Function.Injective j := hCap.isEmbedding.injective
    let W : Set S := connectedComponent c₀
    have hW_clopen : IsClopen W := isClopen_connectedComponent
    have hW_surf : IsSurface W := isSurface_sub hS hW_clopen
    have : CompactSpace W := hW_surf.1
    have hW_conn : ConnectedSpace W :=
      isConnected_iff_connectedSpace.mp ⟨⟨c₀, mem_connectedComponent⟩,
        isPreconnected_connectedComponent⟩
    have hC_sub_W : C ⊆ W :=
      subset_of_isPreconnected_isClopen
        (IsArcConnected.isPreconnected (IsOArc.isArcConnected (cuff_isOArc hS hC)))
        hW_clopen ⟨c₀, hc₀, mem_connectedComponent⟩
    have hjWD_cl : IsClosed (j '' W ∪ D) :=
      (hW_clopen.1.isCompact.image hj_cont).isClosed.union hCap.isClosedDisc.isCompact.isClosed
    have hjWc_cl : IsClosed (j '' Wᶜ) :=
      (hW_clopen.2.isClosed_compl.isCompact.image hj_cont).isClosed
    have hjWD_compl_eq : (j '' W ∪ D)ᶜ = j '' Wᶜ := by
      ext y
      simp only [mem_compl_iff, mem_union, not_or]
      constructor
      · rintro ⟨hyW, hyD⟩
        rcases hCap.union_eq.symm ▸ mem_univ y with ⟨z, rfl⟩ | hyD'
        · exact ⟨z, fun hzW => hyW ⟨z, hzW, rfl⟩, rfl⟩
        · exact False.elim (hyD hyD')
      · rintro ⟨z, hzW, rfl⟩
        refine ⟨fun ⟨w, hwW, hjw⟩ => hzW (hj_inj hjw ▸ hwW), fun hyD => ?_⟩
        have : j z ∈ range j ∩ D := ⟨⟨z, rfl⟩, hyD⟩
        rw [hCap.inter_eq] at this
        obtain ⟨c, hcC, hjc⟩ := this
        exact hzW (hj_inj hjc ▸ hC_sub_W hcC)
    have hjWD_clopen : IsClopen (j '' W ∪ D) :=
      ⟨hjWD_cl, isClosed_compl_iff.mp (hjWD_compl_eq.symm ▸ hjWc_cl)⟩
    by_cases hXW : X ⊆ W
    · have hbdW : bd W ≠ ∅ := by
        refine Nonempty.ne_empty ⟨⟨c₀, hC_sub_W hc₀⟩, ?_⟩
        rw [mem_bd_sub hW_clopen.2]
        exact cuff_subset_bd hC hc₀
      let X_W : Set W := Subtype.val ⁻¹' X
      have hXW_img : Subtype.val '' X_W = X := by
        rw [Subtype.image_preimage_coe, inter_eq_right.mpr hXW]
      have hXW_solid : IsSolid X_W :=
        isSolid_of_isClosedEmbedding_aux hW_clopen.1.isClosedEmbedding_subtypeVal
          (hXW_img.symm ▸ hX_solid)
      have hXW_flat : IsFlat X_W := by
        refine isFlat_of_forall_isNullHomotopicOArc hW_surf fun F_W hFW_sub hFW_oarc => ?_
        let F : Set S := Subtype.val '' F_W
        have hF_oarc : IsOArc F :=
          isOArc_image hFW_oarc continuous_subtype_val.continuousOn Subtype.val_injective.injOn
        have hFX : F ⊆ X := by
          rw [← hXW_img]
          exact image_mono hFW_sub
        have hF_pl : IsPlanar F := by
          by_contra hF_npl
          exact hall F hF_oarc hFX ⟨hC, hXC.mono hFX, hF_npl⟩
        have hF_null : IsNullHomotopicOArc F :=
          (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hF_oarc).mp hF_pl
        obtain ⟨Δ_F, hΔ_F, hbd_F⟩ := nullHomotopicOArc_bounds_disc hS hF_oarc hF_null
        obtain ⟨y₀, hy₀F⟩ := isOArc_nonempty hF_oarc
        have hF_sub_ΔF : F ⊆ Δ_F := hbd_F ▸ Surface.discBd_subset Δ_F
        have hΔF_sub_W : Δ_F ⊆ W :=
          subset_of_isPreconnected_isClopen hΔ_F.isPathConnected.isConnected.isPreconnected
            hW_clopen
            ⟨y₀, hF_sub_ΔF hy₀F, hXW (hFX hy₀F)⟩
        have hΔFW_disc : IsClosedDisc (Subtype.val ⁻¹' Δ_F : Set W) :=
          isClosedDisc_preimage_of_subset_range continuous_subtype_val Subtype.val_injective hΔ_F
            (by rwa [Subtype.range_coe])
        refine isNullHomotopicOArcIn_of_subset_disc hFW_oarc
          (subset_univ (Subtype.val ⁻¹' Δ_F : Set W)) hΔFW_disc ?_
        intro z hz
        change z.1 ∈ Δ_F
        exact hF_sub_ΔF ⟨z, hz, rfl⟩
      obtain ⟨Δ_W, hΔ_W, hXW_Δ⟩ :=
        isPlanar_of_solid_flat_bd_ne_empty hW_surf hbdW hXW_solid hXW_flat
      refine hSurr.2.2 ⟨Subtype.val '' Δ_W,
        isClosedDisc_image_of_injective continuous_subtype_val Subtype.val_injective hΔ_W, ?_⟩
      rw [← hXW_img]
      exact image_mono hXW_Δ
    · obtain ⟨x₁, hx₁X, hx₁W⟩ := not_subset.mp hXW
      have hjWc_clopen : IsClopen (j '' Wᶜ) := by
        rw [← hjWD_compl_eq]
        exact hjWD_clopen.compl
      have hΔ₀_sub : Δ₀ ⊆ j '' Wᶜ :=
        subset_of_isPreconnected_isClopen hΔ₀.isPathConnected.isConnected.isPreconnected hjWc_clopen
          ⟨j x₁, hXΔ₀ ⟨x₁, hx₁X, rfl⟩, ⟨x₁, hx₁W, rfl⟩⟩
      have hΔ₀_range : Δ₀ ⊆ range j := hΔ₀_sub.trans (image_subset_range j Wᶜ)
      exact hSurr.2.2 ⟨j ⁻¹' Δ₀,
        isClosedDisc_preimage_of_subset_range hj_cont hj_inj hΔ₀ hΔ₀_range,
        fun x hx => hXΔ₀ ⟨x, hx, rfl⟩⟩
  · rintro ⟨F, _, hFX, hF_surr⟩
    exact ⟨hXC.1, hXC, fun hX_pl => hF_surr.2.2 (IsPlanar.mono hX_pl hFX)⟩

/-! ## 3. Proof of (5.3) -/

/-- If `C, C' ∈ cuffs S` are distinct (`C ≠ C'`) and `(S₁, ι₁, Δ₁)` is obtained by pasting a disc
onto `C`, then `ι₁ '' C'` is a cuff of `S₁`. -/
theorem image_cuff_of_cappedCuff
    {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {S₁ : Type u} [TopologicalSpace S₁] {ι₁ : S → S₁}
    (hι₁ : IsClosedEmbedding ι₁)
    (hbdS₁ : bd S₁ = ι₁ '' (bd S \ C)) :
    ι₁ '' C' ∈ cuffs S₁ := by
  have hdisj : Disjoint C C' := disjoint_cuffs hC hC' hne
  have hC'_sub : C' ⊆ bd S \ C :=
    subset_sdiff.mpr ⟨cuff_subset_bd hC', hdisj.symm⟩
  obtain ⟨x, hxbd, rfl⟩ := hC'
  have hxC' : x ∈ connectedComponentIn (bd S) x := mem_connectedComponentIn hxbd
  have hx_S₁ : ι₁ x ∈ bd S₁ := hbdS₁ ▸ mem_image_of_mem ι₁ (hC'_sub hxC')
  refine ⟨ι₁ x, hx_S₁, ?_⟩
  apply Subset.antisymm
  · intro y hy
    have hy_bd : y ∈ bd S₁ := connectedComponentIn_subset _ _ hy
    rw [hbdS₁] at hy_bd
    obtain ⟨z, ⟨hz_bd, _⟩, rfl⟩ := hy_bd
    refine mem_image_of_mem ι₁ ?_
    have hpre : IsPreconnected (ι₁ ⁻¹' connectedComponentIn (bd S₁) (ι₁ x)) := by
      refine hι₁.isInducing.isPreconnected_image.mp ?_
      have hsub_range : connectedComponentIn (bd S₁) (ι₁ x) ⊆ range ι₁ :=
        (connectedComponentIn_subset _ _).trans (hbdS₁ ▸ image_subset_range _ _)
      rw [image_preimage_eq_of_subset hsub_range]
      exact isPreconnected_connectedComponentIn
    have hsub_bd : ι₁ ⁻¹' connectedComponentIn (bd S₁) (ι₁ x) ⊆ bd S := by
      intro w hw
      have hw' : ι₁ w ∈ bd S₁ := connectedComponentIn_subset _ _ hw
      rw [hbdS₁] at hw'
      obtain ⟨w₀, ⟨hw₀, _⟩, heq⟩ := hw'
      exact hι₁.injective heq ▸ hw₀
    have hx_pre : x ∈ ι₁ ⁻¹' connectedComponentIn (bd S₁) (ι₁ x) :=
      mem_connectedComponentIn hx_S₁
    exact hpre.subset_connectedComponentIn hx_pre hsub_bd hy
  · have hconn : IsPreconnected (ι₁ '' connectedComponentIn (bd S) x) :=
      isPreconnected_connectedComponentIn.image ι₁ hι₁.continuous.continuousOn
    exact hconn.subset_connectedComponentIn (mem_image_of_mem ι₁ hxC')
      (hbdS₁ ▸ image_mono hC'_sub)

private theorem two_cap_domain_is_surface
    {S : Type u}
    [TopologicalSpace S]
    (hS : IsSurface S)
    {C : Set S}
    {C' : Set S}
    (hC' : C' ∈ cuffs S)
    [this : T2Space S]
    (S₁ : Type u)
    [TopologicalSpace S₁]
    (ι₁ : S → S₁)
    (hι₁ : IsClosedEmbedding ι₁)
    (S₂ : Type u)
    [TopologicalSpace S₂]
    (ι₂ : S₁ → S₂)
    (Δ₂ : Set S₂)
    (hS₂ : IsSurface S₂)
    (hι₂ : IsClosedEmbedding ι₂)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hmeet₂ : range ι₂ ∩ Δ₂ = ι₂ '' ι₁ '' C')
    [this : T2Space S₂]
    (D₁ : Set S₂)
    (hD₁_disc : IsClosedDisc D₁ ∧ discBd D₁ = ι₂ '' ι₁ '' C)
    (hdisj_D₁_Δ₂ : Disjoint D₁ Δ₂)
    (W₂ : Set S₂)
    (hW : W₂ = range (ι₂ ∘ ι₁) ∪ Δ₂)
    [CompactSpace W₂]
    (hW₂_eq_compl : W₂ = (discInt D₁)ᶜ)
    (j₂ : S → W₂)
    (hj : ∀ x, (j₂ x).1 = ι₂ (ι₁ x))
    (hj₂_emb : IsEmbedding j₂) :
    IsSurface ↑W₂ := by
  refine ⟨inferInstance, inferInstance, fun ⟨z, hzW₂⟩ => ?_⟩
  by_cases hzD₁ : z ∈ D₁
  · have hzW := hW ▸ hzW₂
    have hz_not_Δ₂ : z ∉ Δ₂ := disjoint_left.mp hdisj_D₁_Δ₂ hzD₁
    obtain ⟨x, rfl⟩ : z ∈ range (ι₂ ∘ ι₁) := hzW.resolve_right hz_not_Δ₂
    have hx_not_C' : x ∉ C' := fun hxC' =>
      hz_not_Δ₂ (hmeet₂ ▸ mem_image_of_mem ι₂ (mem_image_of_mem ι₁ hxC')).2
    have hU_S_open : IsOpen (C'ᶜ : Set S) := (cuff_isOArc hS hC').isCompact.isClosed.isOpen_compl
    let f_open : (C'ᶜ : Set S) → W₂ := fun w => j₂ w.1
    have hf_emb : IsEmbedding f_open :=
      hj₂_emb.comp hU_S_open.isOpenEmbedding_subtypeVal.toIsEmbedding
    have hf_range : range f_open = {w : W₂ | w.1 ∉ Δ₂} := by
      ext ⟨w, hwW₂⟩
      simp only [f_open, hj, mem_range, Subtype.ext_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨x', hx'⟩, rfl⟩ hwΔ₂
        have : ι₂ (ι₁ x') ∈ range ι₂ ∩ Δ₂ := ⟨mem_range_self _, hwΔ₂⟩
        rw [hmeet₂] at this
        obtain ⟨_, ⟨x₀, hx₀C', rfl⟩, heq⟩ := this
        exact hx' (hι₁.injective (hι₂.injective heq) ▸ hx₀C')
      · intro hw_not_Δ₂
        have hwW := hW ▸ hwW₂
        obtain ⟨x', rfl⟩ := hwW.resolve_right hw_not_Δ₂
        refine ⟨⟨x', fun hx'C' => hw_not_Δ₂ ?_⟩, rfl⟩
        exact (hmeet₂ ▸ mem_image_of_mem ι₂ (mem_image_of_mem ι₁ hx'C')).2
    have hf_open : IsOpenEmbedding f_open :=
      { toIsEmbedding := hf_emb
        isOpen_range := by
          rw [hf_range]
          exact (hΔ₂.isCompact.isClosed.preimage continuous_subtype_val).isOpen_compl }
    have hxj : j₂ x = ⟨(ι₂ ∘ ι₁) x, hzW₂⟩ := Subtype.ext (hj x)
    rw [← hxj]
    exact isManifoldPoint_of_isOpenEmbedding hf_open (x := ⟨x, hx_not_C'⟩)
      ((isManifoldPoint_iff_of_isOpenEmbedding hU_S_open.isOpenEmbedding_subtypeVal).mp
        (hS.2.2 x))
  · let U_W : Set W₂ := {w : W₂ | w.1 ∉ D₁}
    have hU_W_open : IsOpen U_W :=
      (hD₁_disc.1.isCompact.isClosed.preimage continuous_subtype_val).isOpen_compl
    let g_open : U_W → S₂ := fun w => w.1.1
    have hg_emb : IsEmbedding g_open :=
      IsEmbedding.subtypeVal.comp hU_W_open.isOpenEmbedding_subtypeVal.toIsEmbedding
    have hg_range : range g_open = D₁ᶜ := by
      ext w
      simp only [g_open, mem_range, mem_compl_iff]
      refine ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun hw => ?_⟩
      have hwW₂ : w ∈ W₂ := by
        rw [hW₂_eq_compl]
        exact fun h => hw h.1
      exact ⟨⟨⟨w, hwW₂⟩, hw⟩, rfl⟩
    have hg_open : IsOpenEmbedding g_open :=
      { toIsEmbedding := hg_emb
        isOpen_range := hg_range ▸ hD₁_disc.1.isCompact.isClosed.isOpen_compl }
    have hman_S₂ : IsManifoldPoint (g_open ⟨⟨z, hzW₂⟩, hzD₁⟩) := hS₂.2.2 z
    have hman_UW := (isManifoldPoint_iff_of_isOpenEmbedding hg_open).mp hman_S₂
    exact isManifoldPoint_of_isOpenEmbedding hU_W_open.isOpenEmbedding_subtypeVal hman_UW

private theorem second_cap_intersects_surface_in_cuff
    {S : Type u}
    {C' : Set S}
    (S₁ : Type u)
    (ι₁ : S → S₁)
    (S₂ : Type u)
    (ι₂ : S₁ → S₂)
    (Δ₂ : Set S₂)
    (hmeet₂ : range ι₂ ∩ Δ₂ = ι₂ '' ι₁ '' C')
    (W₂ : Set S₂)
    (j₂ : S → W₂)
    (hj : ∀ x, (j₂ x).1 = ι₂ (ι₁ x))
    : range j₂ ∩ Subtype.val ⁻¹' Δ₂ = j₂ '' C' := by
  ext ⟨z, hzW₂⟩
  simp only [mem_inter_iff, mem_range, Subtype.ext_iff, mem_preimage, mem_image, hj]
  constructor
  · rintro ⟨⟨x, rfl⟩, hzΔ₂⟩
    have : ι₂ (ι₁ x) ∈ range ι₂ ∩ Δ₂ := ⟨mem_range_self _, hzΔ₂⟩
    rw [hmeet₂] at this
    obtain ⟨_, ⟨x₀, hx₀C', rfl⟩, heq⟩ := this
    exact ⟨x₀, hx₀C', heq⟩
  · rintro ⟨x, hxC', rfl⟩
    exact ⟨⟨x, rfl⟩, (hmeet₂ ▸ mem_image_of_mem ι₂ (mem_image_of_mem ι₁ hxC')).2⟩

private theorem pulled_cap_boundary
    {S : Type u}
    {C' : Set S}
    (S₁ : Type u)
    (ι₁ : S → S₁)
    (S₂ : Type u)
    [TopologicalSpace S₂]
    (ι₂ : S₁ → S₂)
    (Δ₂ : Set S₂)
    (hbdΔ₂ : discBd Δ₂ = ι₂ '' ι₁ '' C')
    [T2Space S₂]
    (W₂ : Set S₂)
    (j₂ : S → W₂)
    (hj : ∀ x, (j₂ x).1 = ι₂ (ι₁ x))
    [Nonempty ↑W₂]
    (hΔ₂_sub_W₂ : Δ₂ ⊆ W₂)
    (hΔ₂'_disc : IsClosedDisc (Subtype.val ⁻¹' Δ₂ : Set W₂)) :
    discBd (Subtype.val ⁻¹' Δ₂ : Set W₂) = j₂ '' C' := by
  let Δ₂' : Set W₂ := Subtype.val ⁻¹' Δ₂
  have h_img : Subtype.val '' discBd Δ₂' = discBd Δ₂ := by
    obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn hΔ₂'_disc.isCompact
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn
    have h := (hΔ₂'_disc.image continuous_subtype_val.continuousOn hd'c hd'l).2
    have heq : Subtype.val '' Δ₂' = Δ₂ := Subtype.image_preimage_coe W₂ Δ₂ ▸ inter_eq_right.mpr
      hΔ₂_sub_W₂
    rw [heq] at h
    exact h.symm
  ext ⟨z, hzW₂⟩
  constructor
  · intro hz
    have hz' : z ∈ discBd Δ₂ := h_img ▸ mem_image_of_mem Subtype.val hz
    rw [hbdΔ₂] at hz'
    obtain ⟨_, ⟨x, hxC', rfl⟩, rfl⟩ := hz'
    exact ⟨x, hxC', Subtype.ext (hj x)⟩
  · rintro ⟨x, hxC', h⟩
    rw [← h]
    have hz' : ι₂ (ι₁ x) ∈ Subtype.val '' discBd Δ₂' := by
      rw [h_img, hbdΔ₂]
      exact mem_image_of_mem ι₂ (mem_image_of_mem ι₁ hxC')
    obtain ⟨w, hw, heq⟩ := hz'
    exact (Subtype.ext (heq.trans (hj x).symm) : w = j₂ x) ▸ hw

/-- If `C, C' ∈ cuffs S` are distinct (`C ≠ C'`) and `F ⊆ S` is an `O`-arc that surrounds `C`
and is planar in `Σ + C'̂`, then `Nonempty (S ≃ₜ SurfaceModel 0 0 2)`. -/
theorem surroundsCuff_and_planarInCappedCuff_imp_cylinder
    (hS : IsSurface S) [ConnectedSpace S] {C C' F : Set S}
    (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    (hF : IsOArc F) (hFC : SurroundsCuff F C) (hFC' : IsPlanarInCappedCuff C' F) :
    Nonempty (S ≃ₜ SurfaceModel 0 0 2) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hdisj_CC' : Disjoint C C' := disjoint_cuffs hC hC' hne
  obtain ⟨S₁, _, ι₁, Δ₁, hS₁, hι₁, hΔ₁, hcov₁, hmeet₁, hbdΔ₁, hbdS₁⟩ :=
    paste_disc S C hS hC
  have : T2Space S₁ := hS₁.2.1
  have hCap₁ : IsCappedCuff C S₁ ι₁ Δ₁ :=
    ⟨hC, hS₁, hι₁.toIsEmbedding, hΔ₁, hbdΔ₁, hcov₁, hmeet₁⟩
  have : ConnectedSpace S₁ := hCap₁.connectedSpace hS
  have hC'₁ : ι₁ '' C' ∈ cuffs S₁ :=
    image_cuff_of_cappedCuff hC hC' hne hι₁ hbdS₁
  obtain ⟨S₂, _, ι₂, Δ₂, hS₂, hι₂, hΔ₂, hcov₂, hmeet₂, hbdΔ₂, hbdS₂⟩ :=
    paste_disc S₁ (ι₁ '' C') hS₁ hC'₁
  have : CompactSpace S₂ := hS₂.1
  have : T2Space S₂ := hS₂.2.1
  have hCap₂ : IsCappedCuff (ι₁ '' C') S₂ ι₂ Δ₂ :=
    ⟨hC'₁, hS₂, hι₂.toIsEmbedding, hΔ₂, hbdΔ₂, hcov₂, hmeet₂⟩
  have : ConnectedSpace S₂ := hCap₂.connectedSpace hS₁
  have hF₁_oArc : IsOArc (ι₁ '' F) :=
    isOArc_image hF hι₁.continuous.continuousOn hι₁.injective.injOn
  have hF₁_pl : IsPlanar (ι₁ '' F) := hFC.2.1.2.2 S₁ ι₁ Δ₁ hCap₁
  have hF₁_null : IsNullHomotopicOArc (ι₁ '' F) :=
    (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS₁ hF₁_oArc).mp hF₁_pl
  obtain ⟨E₁', hE₁'_disc, hE₁'_bd⟩ :=
    nullHomotopicOArc_bounds_disc hS₁ hF₁_oArc hF₁_null
  have hdisj_int₁ : Disjoint (discInt Δ₁) (discBd E₁') := by
    rw [hE₁'_bd]
    refine disjoint_left.mpr ?_
    rintro _ ⟨hxΔ₁, hxbd⟩ ⟨x, _, rfl⟩
    have : ι₁ x ∈ range ι₁ ∩ Δ₁ := ⟨mem_range_self x, hxΔ₁⟩
    rw [hmeet₁, ← hbdΔ₁] at this
    exact hxbd this
  have h_int₁_sub : discInt Δ₁ ⊆ discInt E₁' := by
    rcases hE₁'_disc.side hS₁.2.2 hΔ₁.isPreconnected_discInt hdisj_int₁ with hsub | hdisj
    · exact hsub
    · exfalso
      have hE₁'_range : E₁' ⊆ range ι₁ := by
        intro y hy
        rcases (hcov₁ ▸ mem_univ y : y ∈ range ι₁ ∪ Δ₁) with hy_r | hy_Δ₁
        · exact hy_r
        · by_cases hy_bd : y ∈ discBd Δ₁
          · rw [hbdΔ₁, ← hmeet₁] at hy_bd
            exact hy_bd.1
          · exact (disjoint_right.mp hdisj hy ⟨hy_Δ₁, hy_bd⟩).elim
      obtain ⟨φE₁'⟩ := id hE₁'_disc
      have hpre_disc : IsClosedDisc (ι₁ ⁻¹' E₁') := by
        refine ⟨Homeomorph.trans φE₁' ?_⟩
        have h_inv_cont : Continuous (fun x : (ι₁ ⁻¹' E₁' : Set S) => (⟨ι₁ x.1, x.2⟩ : E₁')) :=
          Continuous.subtype_mk (hι₁.continuous.comp continuous_subtype_val) _
        have : CompactSpace (ι₁ ⁻¹' E₁' : Set S) :=
          isCompact_iff_compactSpace.mp (hE₁'_disc.isCompact.isClosed.preimage
            hι₁.continuous).isCompact
        exact (h_inv_cont.homeoOfEquivCompactToT2 (f := {
          toFun := fun x => ⟨ι₁ x.1, x.2⟩
          invFun := fun z => ⟨Classical.choose (hE₁'_range z.2), by
            have hspec := Classical.choose_spec (hE₁'_range z.2)
            simp [hspec]⟩
          left_inv := fun x => Subtype.ext (hι₁.injective
            (Classical.choose_spec (hE₁'_range x.2)))
          right_inv := fun z => Subtype.ext (Classical.choose_spec (hE₁'_range z.2)) })).symm
      have hF_sub : F ⊆ ι₁ ⁻¹' E₁' := by
        intro x hx
        have : ι₁ x ∈ discBd E₁' := hE₁'_bd ▸ mem_image_of_mem ι₁ hx
        exact Surface.discBd_subset E₁' this
      exact hFC.2.2 ⟨ι₁ ⁻¹' E₁', hpre_disc, hF_sub⟩
  let E₁ : Set S₂ := ι₂ '' E₁'
  let D₁ : Set S₂ := ι₂ '' Δ₁
  have hE₁_disc : IsClosedDisc E₁ ∧ discBd E₁ = ι₂ '' (ι₁ '' F) := by
    obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn hE₁'_disc.isCompact
      hι₂.continuous.continuousOn hι₂.injective.injOn
    have h := hE₁'_disc.image hι₂.continuous.continuousOn hd'c hd'l
    rwa [hE₁'_bd] at h
  have hD₁_disc : IsClosedDisc D₁ ∧ discBd D₁ = ι₂ '' (ι₁ '' C) := by
    obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn hΔ₁.isCompact
      hι₂.continuous.continuousOn hι₂.injective.injOn
    have h := hΔ₁.image hι₂.continuous.continuousOn hd'c hd'l
    rwa [hbdΔ₁] at h
  have hdisj_Δ₁_C' : Disjoint Δ₁ (ι₁ '' C') := by
    refine disjoint_left.mpr ?_
    rintro y hyΔ₁ ⟨x, hxC', rfl⟩
    have : ι₁ x ∈ range ι₁ ∩ Δ₁ := ⟨mem_range_self x, hyΔ₁⟩
    rw [hmeet₁] at this
    obtain ⟨z, hzC, heq⟩ := this
    exact disjoint_left.mp hdisj_CC' (hι₁.injective heq ▸ hzC) hxC'
  have hdisj_D₁_Δ₂ : Disjoint D₁ Δ₂ := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, hyΔ₁, rfl⟩ hyΔ₂
    have : ι₂ y ∈ range ι₂ ∩ Δ₂ := ⟨mem_range_self y, hyΔ₂⟩
    rw [hmeet₂] at this
    obtain ⟨w, hw, heq⟩ := this
    exact disjoint_left.mp hdisj_Δ₁_C' (hι₂.injective heq ▸ hyΔ₁) hw
  let W₂ : Set S₂ := range (ι₂ ∘ ι₁) ∪ Δ₂
  have hW₂_closed : IsClosed W₂ :=
    ((hι₂.comp hι₁).isClosed_range).union hΔ₂.isCompact.isClosed
  have : CompactSpace W₂ := isCompact_iff_compactSpace.mp hW₂_closed.isCompact
  have hW₂_eq_compl : W₂ = (discInt D₁)ᶜ := by
    ext z
    simp only [W₂, mem_union, mem_range, Function.comp_apply, mem_compl_iff, discInt, mem_sdiff,
      not_and, not_not]
    constructor
    · rintro (⟨x, rfl⟩ | hzΔ₂) hzD₁
      · obtain ⟨y, hyΔ₁, heq⟩ := hzD₁
        have hy : y = ι₁ x := hι₂.injective heq
        subst hy
        have : ι₁ x ∈ range ι₁ ∩ Δ₁ := ⟨mem_range_self x, hyΔ₁⟩
        rw [hmeet₁] at this
        rw [hD₁_disc.2]
        exact mem_image_of_mem ι₂ this
      · exact (disjoint_right.mp hdisj_D₁_Δ₂ hzΔ₂ hzD₁).elim
    · intro hz
      rcases (hcov₂ ▸ mem_univ z : z ∈ range ι₂ ∪ Δ₂) with ⟨y, rfl⟩ | hzΔ₂
      · rcases (hcov₁ ▸ mem_univ y : y ∈ range ι₁ ∪ Δ₁) with ⟨x, rfl⟩ | hyΔ₁
        · exact Or.inl ⟨x, rfl⟩
        · have hzD₁ : ι₂ y ∈ D₁ := mem_image_of_mem ι₂ hyΔ₁
          have hzbd := hz hzD₁
          rw [hD₁_disc.2] at hzbd
          obtain ⟨_, ⟨x, _, rfl⟩, heq⟩ := hzbd
          exact Or.inl ⟨x, heq⟩
      · exact Or.inr hzΔ₂
  let j₂ : S → W₂ := fun x => ⟨ι₂ (ι₁ x), Or.inl ⟨x, rfl⟩⟩
  have : Nonempty W₂ := ⟨j₂ (Classical.choice ‹ConnectedSpace S›.toNonempty)⟩
  have hj₂_emb : IsEmbedding j₂ :=
    IsEmbedding.of_comp (Continuous.subtype_mk (hι₂.continuous.comp hι₁.continuous) _)
      continuous_subtype_val (hι₂.comp hι₁).toIsEmbedding
  have hj₂_closed : IsClosed (range j₂) := by
    have heq : range j₂ = Subtype.val ⁻¹' range (ι₂ ∘ ι₁) := by
      ext ⟨z, hz⟩
      simp [j₂, Subtype.ext_iff]
    rw [heq]
    exact (hι₂.comp hι₁).isClosed_range.preimage continuous_subtype_val
  have hW₂_surf := two_cap_domain_is_surface hS hC' S₁ ι₁ hι₁ S₂ ι₂ Δ₂ hS₂ hι₂ hΔ₂ hmeet₂ D₁
    hD₁_disc hdisj_D₁_Δ₂ W₂ rfl hW₂_eq_compl j₂ (fun _ => rfl) hj₂_emb
  let Δ₂' : Set W₂ := Subtype.val ⁻¹' Δ₂
  have hΔ₂_sub_W₂ : Δ₂ ⊆ W₂ := subset_union_right
  have hΔ₂'_disc : IsClosedDisc Δ₂' := by
    obtain ⟨φΔ₂⟩ := id hΔ₂
    have : CompactSpace Δ₂ := isCompact_iff_compactSpace.mp hΔ₂.isCompact
    refine ⟨Homeomorph.trans φΔ₂ ?_⟩
    exact Continuous.homeoOfEquivCompactToT2
      (f := {
        toFun := fun z => ⟨⟨z.1, hΔ₂_sub_W₂ z.2⟩, z.2⟩
        invFun := fun w => ⟨w.1.1, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
      (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)
  have hcov_W₂ : range j₂ ∪ Δ₂' = univ := by
    ext ⟨z, hzW₂⟩
    simp only [j₂, Δ₂', mem_union, mem_range, Subtype.ext_iff, mem_preimage, mem_univ, iff_true]
    exact hzW₂
  have hbd_Δ₂' : discBd Δ₂' = j₂ '' C' := by
    exact pulled_cap_boundary S₁ ι₁ S₂ ι₂ Δ₂ hbdΔ₂ W₂ j₂ (fun _ => rfl)
      hΔ₂_sub_W₂ hΔ₂'_disc
  have hCap_W₂ : IsCappedCuff C' W₂ j₂ Δ₂' :=
    ⟨hC', hW₂_surf, hj₂_emb, hΔ₂'_disc, hbd_Δ₂', hcov_W₂,
      second_cap_intersects_surface_in_cuff S₁ ι₁ S₂ ι₂ Δ₂ hmeet₂ W₂ j₂ (fun _ => rfl)⟩
  have hF_W₂_oArc : IsOArc (j₂ '' F) :=
    isOArc_image hF hj₂_emb.continuous.continuousOn hj₂_emb.injective.injOn
  have hF_W₂_pl : IsPlanar (j₂ '' F) := hFC'.2.2 W₂ j₂ Δ₂' hCap_W₂
  have hF_W₂_null : IsNullHomotopicOArc (j₂ '' F) :=
    (isPlanar_iff_isNullHomotopicOArc_of_isOArc hW₂_surf hF_W₂_oArc).mp hF_W₂_pl
  obtain ⟨E₂', hE₂'_disc, hE₂'_bd⟩ :=
    nullHomotopicOArc_bounds_disc hW₂_surf hF_W₂_oArc hF_W₂_null
  let E₂ : Set S₂ := Subtype.val '' E₂'
  have hE₂_disc : IsClosedDisc E₂ ∧ discBd E₂ = ι₂ '' (ι₁ '' F) := by
    obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn hE₂'_disc.isCompact
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn
    have h := hE₂'_disc.image continuous_subtype_val.continuousOn hd'c hd'l
    rw [hE₂'_bd] at h
    refine ⟨h.1, h.2.trans ?_⟩
    ext z
    simp [j₂, mem_image]
  have hE₁_ne_E₂ : E₁ ≠ E₂ := by
    intro heq
    obtain ⟨z₀, hz₀⟩ := hΔ₁.nonempty_discInt
    have hz₀_E₁' : z₀ ∈ E₁' := (h_int₁_sub hz₀).1
    have hz₀_E₁ : ι₂ z₀ ∈ E₁ := mem_image_of_mem ι₂ hz₀_E₁'
    rw [heq] at hz₀_E₁
    obtain ⟨⟨w, hwW₂⟩, _, rfl⟩ := hz₀_E₁
    rw [hW₂_eq_compl] at hwW₂
    apply hwW₂
    refine ⟨mem_image_of_mem ι₂ hz₀.1, ?_⟩
    rw [hD₁_disc.2, ← hbdΔ₁]
    rintro ⟨y, hy, hyz₀⟩
    exact hz₀.2 (hι₂.injective hyz₀ ▸ hy)
  have hS₂_sph : IsSphere S₂ := by
    by_contra hns
    exact hE₁_ne_E₂ (eq_of_discBd_eq hS₂ hns hE₁_disc.1 hE₂_disc.1
      (hE₁_disc.2.trans hE₂_disc.2.symm))
  obtain ⟨a, b, c, hmodel⟩ := classification S hS ‹ConnectedSpace S›
  obtain ⟨hc1, hmodel₁⟩ := cappedCuff_homeo_model hS hmodel hC hCap₁
  obtain ⟨hc2, ⟨e₂⟩⟩ := cappedCuff_homeo_model hS₁ hmodel₁ hC'₁ hCap₂
  obtain ⟨e_sph⟩ := id hS₂_sph
  obtain ⟨e_m0⟩ := GraphMinor.GM19.isSphere_model
  have h_crit := (modelCriterion.2 a b (c - 1 - 1) 0 0 0).mp ⟨e₂.symm.trans (e_sph.trans e_m0.symm)⟩
  have ha : a = 0 ∧ b = 0 ∧ c = 2 := by
    have hb0 : b = 0 := h_crit.2.2.mpr rfl
    omega
  rcases ha with ⟨rfl, rfl, rfl⟩
  exact hmodel

/-- Graph Minors VII, (5.3) (page 231):
"If $\Sigma \not\cong \Sigma(0, 0, 2)$ and $G$ is a proper graph in $\Sigma$, and $C$, $C'$
are distinct cuffs and $r$, $r' \ge 0$ are integers with $r + r' < \alpha(G)$ then
$\mathscr{A}_r(C) \cap \mathscr{A}_{r'}(C') = \emptyset$." -/
theorem theorem_5_3_proof
    (hS : IsSurface S) [ConnectedSpace S]
    (hnot_cyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {r r' : ℕ} (hr : r + r' < alpha G) :
    scriptA G r C ∩ scriptA G r' C' = ∅ := by
  have : T2Space S := hS.2.1
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  simp only [scriptA, mem_sUnion, mem_ofPred_eq] at hx hx'
  obtain ⟨X, ⟨hX_sol, hX_conn, hX_norm, hX_surr, hX_card⟩, hxX⟩ := hx
  obtain ⟨X', ⟨hX'_sol, hX'_conn, hX'_norm, hX'_surr, hX'_card⟩, hxX'⟩ := hx'
  have hU_sol : IsSolid (X ∪ X') :=
    theorem_11_6_proof hS hX_sol hX'_sol
  have hU_conn : IsConnected (X ∪ X') :=
    ⟨⟨x, Or.inl hxX⟩, hX_conn.2.union' ⟨x, hxX, hxX'⟩ hX'_conn.2⟩
  have hU_norm : G.IsNormal (X ∪ X') := by
    rintro y ⟨hyX | hyX', hyU⟩
    · exact hX_norm ⟨hyX, hyU⟩
    · exact hX'_norm ⟨hyX', hyU⟩
  have hU_not_np : ¬ IsNearPlanar (X ∪ X') := by
    rintro (hpl | ⟨C'', hC'', hplC''⟩)
    · exact hX_surr.2.2 (IsPlanar.mono hpl subset_union_left)
    · rcases eq_or_ne C'' C with rfl | hC''C
      · have hne' : C' ≠ C'' := hne.symm
        obtain ⟨F', hF', hF'X', hF'_surr⟩ :=
          (theorem_5_2_proof hS hX'_sol hX'_surr.2.1).mp hX'_surr
        exact hnot_cyl (surroundsCuff_and_planarInCappedCuff_imp_cylinder
          hS hC' hC'' hne' hF' hF'_surr (hplC''.mono (hF'X'.trans subset_union_right)))
      · have hne' : C ≠ C'' := Ne.symm hC''C
        obtain ⟨F, hF, hFX, hF_surr⟩ :=
          (theorem_5_2_proof hS hX_sol hX_surr.2.1).mp hX_surr
        exact hnot_cyl (surroundsCuff_and_planarInCappedCuff_imp_cylinder
          hS hC hC'' hne' hF hF_surr (hplC''.mono (hFX.trans subset_union_left)))
  have hU_cand : IsAlphaCandidate G (X ∪ X') :=
    ⟨hU_sol, hU_conn, hU_norm, hU_not_np⟩
  have h_le_alpha : alpha G ≤ ((X ∪ X') ∩ G.V).ncard :=
    Nat.sInf_le ⟨X ∪ X', hU_cand, rfl⟩
  have h_card_union : ((X ∪ X') ∩ G.V).ncard ≤ r + r' := by
    have heq : (X ∪ X') ∩ G.V = (G.V ∩ X) ∪ (G.V ∩ X') := by
      ext z
      simp [and_comm, or_and_right]
    rw [heq]
    exact (ncard_union_le (G.V ∩ X) (G.V ∩ X')).trans (Nat.add_le_add hX_card hX'_card)
  omega

/-! ## 4. Proof of (5.4) -/

/-- If `B ∈ componentsIn (F₀ \ {x, y})` where `F₀` is an `O`-arc and `x ≠ y ∈ F₀`, then `x` and `y`
are joined by a path in `B ∪ {x, y} ⊆ F₀`. -/
theorem joinedIn_component_oArc_diff_pair
    {F₀ B : Set S} (hF₀ : IsOArc F₀) {x y : S} (hx : x ∈ F₀) (hy : y ∈ F₀) (hxy : x ≠ y)
    (hB : B ∈ componentsIn (F₀ \ {x, y})) :
    B ⊆ F₀ ∧ JoinedIn (B ∪ {x, y}) x y := by
  obtain ⟨φ⟩ := id hF₀
  have hB_sub : B ⊆ F₀ \ {x, y} := by
    obtain ⟨z, _, rfl⟩ := hB
    exact connectedComponentIn_subset _ _
  refine ⟨hB_sub.trans sdiff_subset, ?_⟩
  let a : Circle := φ.symm ⟨x, hx⟩
  let b : Circle := φ.symm ⟨y, hy⟩
  have hab : a ≠ b := by
    intro h
    have h' : (⟨x, hx⟩ : F₀) = ⟨y, hy⟩ := by simpa [a, b] using congrArg φ h
    exact hxy (congrArg Subtype.val h')
  let ι : Circle → S := fun w => (φ w).1
  have hι : Continuous ι := continuous_subtype_val.comp φ.continuous
  have hιinj : Injective ι := fun u w h => φ.injective (Subtype.ext h)
  have hιa : ι a = x := by simp [ι, a]
  have hιb : ι b = y := by simp [ι, b]
  have hsub_arc : ∀ c d : Circle, c ≠ d → (c = a ∧ d = b ∨ c = b ∧ d = a) →
      ι '' circleOpenArc c d ⊆ F₀ \ {x, y} := by
    rintro c d _ hor _ ⟨w, hw, rfl⟩
    refine ⟨(φ w).2, ?_⟩
    have h₁ : w ∈ ({a, b}ᶜ : Set Circle) := by
      rw [compl_pair_eq_union_circleOpenArc hab]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hw
      · exact Or.inr hw
    rintro (h | h)
    · exact h₁ (Or.inl (hιinj (h.trans hιa.symm)))
    · exact h₁ (Or.inr (hιinj (h.trans hιb.symm)))
  obtain ⟨z, hz, rfl⟩ := hB
  let w : Circle := φ.symm ⟨z, hz.1⟩
  have hιw : ι w = z := by simp [ι, w]
  have hwc : w ∈ ({a, b}ᶜ : Set Circle) := by
    rintro (h | h)
    · exact hz.2 (Or.inl (by rw [← hιw, h, hιa]))
    · exact hz.2 (Or.inr (mem_singleton_iff.mpr (by rw [← hιw, mem_singleton_iff.mp h, hιb])))
  rw [compl_pair_eq_union_circleOpenArc hab] at hwc
  rcases hwc with hwc | hwc
  · have hconn : IsPreconnected (ι '' circleOpenArc a b) :=
      (isPathConnected_circleOpenArc a b).isConnected.isPreconnected.image _ hι.continuousOn
    have hs := hconn.subset_connectedComponentIn ⟨w, hwc, hιw⟩
      (hsub_arc a b hab (Or.inl ⟨rfl, rfl⟩))
    refine ⟨⟨⟨fun t => ι (Circle.path a b t), hι.comp (Circle.path a b).continuous⟩,
      by simp [hιa], by simp [hιb]⟩, fun t => ?_⟩
    by_cases ht0 : t = 0
    · subst ht0; exact Or.inr (Or.inl (by simp))
    · by_cases ht1 : t = 1
      · subst ht1; exact Or.inr (Or.inr (by simp))
      · exact Or.inl (hs ⟨Circle.path a b t, ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
          unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩, rfl⟩)
  · have hconn : IsPreconnected (ι '' circleOpenArc b a) :=
      (isPathConnected_circleOpenArc b a).isConnected.isPreconnected.image _ hι.continuousOn
    have hs := hconn.subset_connectedComponentIn ⟨w, hwc, hιw⟩
      (hsub_arc b a hab.symm (Or.inr ⟨rfl, rfl⟩))
    have hj : JoinedIn (connectedComponentIn (F₀ \ {x, y}) z ∪ {x, y}) y x := by
      refine ⟨⟨⟨fun t => ι (Circle.path b a t), hι.comp (Circle.path b a).continuous⟩,
        by simp [hιb], by simp [hιa]⟩, fun t => ?_⟩
      by_cases ht0 : t = 0
      · subst ht0; exact Or.inr (Or.inr (by simp))
      · by_cases ht1 : t = 1
        · subst ht1; exact Or.inr (Or.inl (by simp))
        · exact Or.inl (hs ⟨Circle.path b a t, ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
            unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩, rfl⟩)
    exact hj.symm

/-- Helper for the final step of (5.4): if `Cl.mk γ_r = (Cl.mk π₀).trans ((Cl.mk q).trans (Cl.mk
πr).symm)`
with `vr = v₀`, `ur = u₀`, `q` null-homotopic, and `πr` equal to `π₀`, then `γ_r` is null-homotopic.
-/
theorem cl_conj_eq_refl {v₀ vr u₀ ur : S} (hv : v₀ = vr) (hu : u₀ = ur)
    (γ_r : Path v₀ vr) (π₀ : Path v₀ u₀) (πr : Path vr ur) (q : Path u₀ ur)
    (hq_eq : Cl.mk γ_r = (Cl.mk π₀).trans ((Cl.mk q).trans (Cl.mk πr).symm))
    (hq_null : (q.cast rfl hu).Homotopic (Path.refl u₀))
    (hπ_eq : πr.cast hv hu = π₀) :
    (γ_r.cast rfl hv).Homotopic (Path.refl v₀) := by
  subst hv; subst hu
  apply Path.Homotopic.Quotient.eq.mp
  change Cl.mk γ_r = Cl.rf v₀
  have hq : Cl.mk q = Cl.rf u₀ := Path.Homotopic.Quotient.eq.mpr hq_null
  have hπ : πr = π₀ := hπ_eq
  rw [hq_eq, hq, hπ, cl_refl_trans, cl_trans_symm]

private theorem paths_within_subdivision
    {S : Type u}
    [TopologicalSpace S]
    {F₀ : Set S}
    {r : ℕ}
    (v : ℕ → S)
    (u : ℕ → S)
    (P : ℕ → Set S)
    (hP : ∀ i ≤ r, IsLineWithEnds (P i) (v i) (u i) ∧ u i ∈ F₀)
    (v' : ℕ → S)
    (u' : ℕ → S)
    (hv'_eq : ∀ i ≤ r, v' i = v i)
    (hu'_eq : ∀ i ≤ r, u' i = u i) :
    ∀ i ≤ r, ∃ p : Path (v' i) (u' i), ∀ t, p t ∈ P i := by
  intro i hi
  obtain ⟨e, he0, he1⟩ := (hP i hi).1
  exact ⟨⟨⟨fun t => (e t).1, continuous_subtype_val.comp e.continuous⟩,
    he0.trans (hv'_eq i hi).symm, he1.trans (hu'_eq i hi).symm⟩, fun t => (e t).2⟩

private theorem subdivision_loop_is_null
    {S : Type u}
    [TopologicalSpace S]
    {r : ℕ}
    (s : ℕ → ↑I)
    (hsr : s r = 1)
    (f : C(Circle, S))
    (γ : Path (f ((arcParam 1) 0)) (f ((arcParam 1) 0)))
    (v' : ℕ → S)
    (hv' : ∀ i ≤ r, v' i = γ (s i))
    (hv'0 : v' 0 = γ 0)
    (hv'r : v' 0 = v' r)
    (hγ_cast : (((γ.subpath 0 (s r)).cast hv'0 (hv' r le_rfl)).cast rfl hv'r).Homotopic
      (Path.refl (v' 0))) :
    γ.Homotopic (Path.refl (f ((arcParam 1) 0))) := by
  have hsource := hv'0.trans γ.source
  have h1 := Path.Homotopic.pathCast hγ_cast hsource.symm hsource.symm
  have h2 : ((((γ.subpath 0 (s r)).cast hv'0 (hv' r le_rfl)).cast rfl hv'r).cast
      hsource.symm hsource.symm) = γ := by
    ext t
    change (γ.subpath 0 (s r)) t = γ t
    rw [hsr, Path.subpath_zero_one]
    rfl
  have h3 : (Path.refl (v' 0)).cast hsource.symm hsource.symm = Path.refl (f (arcParam 1 0)) := by
    ext t
    exact hv'0.trans γ.source
  rwa [h2, h3] at h1

private theorem loop_in_univ_is_null {S : Type u} [TopologicalSpace S] {x : S}
    (γ : Path x x) (hγ : γ.Homotopic (Path.refl x)) :
    let y : (univ : Set S) := ⟨x, mem_univ x⟩
    let γ' : Path y y :=
      ⟨⟨fun t => ⟨γ t, mem_univ _⟩, Continuous.subtype_mk γ.continuous _⟩,
        Subtype.ext γ.source, Subtype.ext γ.target⟩
    γ'.Homotopic (Path.refl y) :=
  by
    let incl : C(S, (univ : Set S)) := ⟨fun z => ⟨z, mem_univ z⟩,
      Continuous.subtype_mk continuous_id _⟩
    exact hγ.map incl

/-- Graph Minors VII, (5.4) (page 231):
"Let $F$, $F_0$ be $O$-arcs in $\Sigma$, where $F_0$ is null-homotopic. Let $r > 0$, and let
$v_1, \dots, v_r \in F$ be distinct, and in order on $F$. Let the components of $F - \{v_1,
\dots, v_r\}$ be $A_1, \dots, A_r$, where $\{v_{i-1}, v_i\} \subseteq \bar{A}_i$ ($1 \le i
\le r$). (Throughout, subscripts should be read modulo $r$.) Let $P_1, \dots, P_r$ be $[0,
1]$-arcs, such that for $1 \le i \le r$, $v_i$ is one end of $P_i$ and the other end ($u_i$
say) is in $F_0$. For $1 \le i \le r$, let $B_i = \emptyset$ if $u_{i-1} = u_i$, and be a
component of $F_0 - \{u_{i-1}, u_i\}$ if $u_{i-1} \ne u_i$. Suppose that $P_{i-1} \cup P_i
\cup A_i \cup B_i$ is planar ($1 \le i \le r$). Then $F$ is null-homotopic."

Here the cyclic order of $v_0, \dots, v_{r-1}$ on $F$ and the open arcs $A_0, \dots, A_{r-1}$ are
given by a homeomorphism $\phi \colon S^1 \cong F$ and a monotone partition
$0 = s_0 \le s_1 \le \dots \le s_r = 1$ of $[0, 1]$ under `arcParam 1` such that for each
$i < r$, $v_i = \phi(\text{arcParam } 1\ (s_{i+1}))$ and
$\phi(\text{arcParam } 1 '' (s_i, s_{i+1})) \subseteq A_i \subseteq F$. -/
theorem theorem_5_4_proof
    (hS : IsSurface S) {F F₀ : Set S}
    (_hF : IsOArc F) (hF₀ : IsOArc F₀) (hF₀_null : IsNullHomotopicOArc F₀)
    {r : ℕ} (hr : 0 < r)
    (φ : Circle ≃ₜ F) (s : ℕ → I) (hs0 : s 0 = 0) (hsr : s r = 1)
    (hs_mono : ∀ i < r, s i ≤ s (i + 1))
    (v u : ℕ → S) (A P B : ℕ → Set S)
    (hv : ∀ i ≤ r, v i = (φ (arcParam 1 (s i))).1)
    (hA : ∀ i < r, (fun t => (φ (arcParam 1 t)).1) '' Ioo (s i) (s (i + 1)) ⊆ A i ∧ A i ⊆ F)
    (hP : ∀ i ≤ r, IsLineWithEnds (P i) (v i) (u i) ∧ u i ∈ F₀)
    (hP_wrap : P 0 = P r ∧ u 0 = u r)
    (hB : ∀ i < r, (u i = u (i + 1) ∧ B i = ∅) ∨
      (u i ≠ u (i + 1) ∧ B i ∈ componentsIn (F₀ \ {u i, u (i + 1)})))
    (hPlanar : ∀ i < r, IsPlanar (P i ∪ P (i + 1) ∪ A i ∪ B i)) :
    IsNullHomotopicOArc F := by
  have : T2Space S := hS.2.1
  let f : C(Circle, S) := ⟨fun z => (φ z).1, continuous_subtype_val.comp φ.continuous⟩
  have hf01 : f (arcParam 1 0) = f (arcParam 1 1) := by simp [f]
  let γ : Path (f (arcParam 1 0)) (f (arcParam 1 0)) :=
    ⟨⟨fun t => f (arcParam 1 t), f.continuous.comp (arcParam 1).continuous⟩, rfl, hf01.symm⟩
  have hv0r : v 0 = v r := by
    rw [hv 0 (Nat.zero_le r), hv r le_rfl, hs0, hsr]
    exact hf01
  let v' : ℕ → S := fun i => if i = r then v 0 else v i
  let u' : ℕ → S := fun i => if i = r then u 0 else u i
  have hv'_eq : ∀ i ≤ r, v' i = v i := by
    intro i hi
    dsimp only [v']
    split_ifs with h
    · subst h; exact hv0r
    · rfl
  have hu'_eq : ∀ i ≤ r, u' i = u i := by
    intro i hi
    dsimp only [u']
    split_ifs with h
    · subst h; exact hP_wrap.2
    · rfl
  have hv' : ∀ i ≤ r, v' i = γ (s i) := fun i hi => (hv'_eq i hi).trans (hv i hi)
  have hv'0 : v' 0 = γ 0 := by
    rw [hv' 0 (Nat.zero_le r), hs0]
  -- For each `i ≤ r`, choose a path `π₀ i` in `P i` from `v' i` to `u' i`.
  have hπ_ex : ∀ i ≤ r, ∃ p : Path (v' i) (u' i), ∀ t, p t ∈ P i := by
    exact paths_within_subdivision (S := S) (F₀ := F₀) (r := r) v u P hP v' u' hv'_eq hu'_eq
  choose π₀ hπ₀ using hπ_ex
  let π : ∀ i, i ≤ r → Path (v' i) (u' i) := fun i hi =>
    if h : i = r then (π₀ 0 (Nat.zero_le r)).cast (by simp [v', h]) (by simp [u', h])
    else π₀ i hi
  -- For each `i < r`, choose a path `β i` in `B i ∪ {u i, u (i + 1)} ⊆ F₀` from `u' i` to `u' (i +
  -- 1)`.
  have hβ_ex : ∀ i < r, ∃ q : Path (u' i) (u' (i + 1)),
      (∀ t, q t ∈ B i ∪ {u i, u (i + 1)}) ∧ (∀ t, q t ∈ F₀) := by
    intro i hi
    rcases hB i hi with ⟨heq, _⟩ | ⟨hne, hB_comp⟩
    · refine ⟨(Path.refl (u i)).cast (hu'_eq i hi.le)
        ((hu'_eq (i + 1) (Nat.succ_le_of_lt hi)).trans heq.symm),
        fun t => Or.inr (Or.inl (by simp)),
        fun t => by simpa using (hP i hi.le).2⟩
    · obtain ⟨hBF₀, hj⟩ := joinedIn_component_oArc_diff_pair hF₀ (hP i hi.le).2
        (hP (i + 1) (Nat.succ_le_of_lt hi)).2 hne hB_comp
      refine ⟨hj.somePath.cast (hu'_eq i hi.le) (hu'_eq (i + 1) (Nat.succ_le_of_lt hi)),
        fun t => by simp, fun t => ?_⟩
      change hj.somePath t ∈ F₀
      rcases hj.somePath_mem t with ht | (h1 | h2)
      · exact hBF₀ ht
      · rw [mem_singleton_iff.mp h1]
        exact (hP i hi.le).2
      · rw [mem_singleton_iff.mp h2]
        exact (hP (i + 1) (Nat.succ_le_of_lt hi)).2
  choose β hβ_B hβ_F₀ using hβ_ex
  have h_step : ∀ i (hi : i < r),
      let α_i : Path (v' i) (v' (i + 1)) :=
        (γ.subpath (s i) (s (i + 1))).cast (hv' i hi.le) (hv' (i + 1) (Nat.succ_le_of_lt hi))
      Cl.mk α_i = (Cl.mk (π i hi.le)).trans
        ((Cl.mk (β i hi)).trans (Cl.mk (π (i + 1) (Nat.succ_le_of_lt hi))).symm) := by
    intro i hi α_i
    obtain ⟨Δ, hΔ, hsubΔ⟩ := hPlanar i hi
    have hP_i_Δ : P i ⊆ Δ :=
      ((subset_union_left.trans subset_union_left).trans subset_union_left).trans hsubΔ
    have hP_i1_Δ : P (i + 1) ⊆ Δ :=
      ((subset_union_right.trans subset_union_left).trans subset_union_left).trans hsubΔ
    have hA_i_Δ : A i ⊆ Δ :=
      (subset_union_right.trans subset_union_left).trans hsubΔ
    have hB_i_Δ : B i ⊆ Δ := subset_union_right.trans hsubΔ
    have hα_Δ : ∀ t, α_i t ∈ Δ := by
      intro t
      have ht_mem : (γ.subpath (s i) (s (i + 1))) t ∈ γ '' uIcc (s i) (s (i + 1)) := by
        rw [← Path.range_subpath]
        exact mem_range_self t
      obtain ⟨w, hw, htw⟩ := ht_mem
      rw [uIcc_of_le (hs_mono i hi)] at hw
      change (γ.subpath (s i) (s (i + 1))) t ∈ Δ
      rw [← htw]
      by_cases hw0 : w = s i
      · subst hw0
        have : γ (s i) = v i := (hv i hi.le).symm
        rw [this]
        obtain ⟨e, he0, _⟩ := (hP i hi.le).1
        exact hP_i_Δ (he0 ▸ (e 0).2)
      · by_cases hw1 : w = s (i + 1)
        · subst hw1
          have : γ (s (i + 1)) = v (i + 1) := (hv (i + 1) (Nat.succ_le_of_lt hi)).symm
          rw [this]
          obtain ⟨e, he0, _⟩ := (hP (i + 1) (Nat.succ_le_of_lt hi)).1
          exact hP_i1_Δ (he0 ▸ (e 0).2)
        · have hw_oo : w ∈ Ioo (s i) (s (i + 1)) :=
            ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), lt_of_le_of_ne hw.2 hw1⟩
          exact hA_i_Δ ((hA i hi).1 ⟨w, hw_oo, rfl⟩)
    have hπ_Δ : ∀ j (hj : j ≤ r), ∀ t, π j hj t ∈ P j := by
      intro j hj t
      dsimp only [π]
      split_ifs with hjr
      · change π₀ 0 (Nat.zero_le r) t ∈ P j
        rw [hjr, ← hP_wrap.1]
        exact hπ₀ 0 (Nat.zero_le r) t
      · exact hπ₀ j hj t
    have hπ_i_Δ : ∀ t, π i hi.le t ∈ Δ := fun t => hP_i_Δ (hπ_Δ i hi.le t)
    have hπ_i1_Δ : ∀ t, π (i + 1) (Nat.succ_le_of_lt hi) t ∈ Δ :=
      fun t => hP_i1_Δ (hπ_Δ (i + 1) (Nat.succ_le_of_lt hi) t)
    have hβ_i_Δ : ∀ t, β i hi t ∈ Δ := by
      intro t
      rcases hβ_B i hi t with htB | (htu | htu1)
      · exact hB_i_Δ htB
      · rw [htu]
        obtain ⟨e, _, he1⟩ := (hP i hi.le).1
        exact hP_i_Δ (he1 ▸ (e 1).2)
      · rw [htu1]
        obtain ⟨e, _, he1⟩ := (hP (i + 1) (Nat.succ_le_of_lt hi)).1
        exact hP_i1_Δ (he1 ▸ (e 1).2)
    have hflatΔ : Flat Δ := IsSimplyConnectedSet.flat hΔ.isSimplyConnectedSet
    refine hflatΔ.eq (Arw.of_path α_i hα_Δ) ?_
    exact (Arw.of_path (π i hi.le) hπ_i_Δ).trans
      ((Arw.of_path (β i hi) hβ_i_Δ).trans (Arw.of_path (π (i + 1) (Nat.succ_le_of_lt hi))
        hπ_i1_Δ).symm)
  have h_ind : ∀ k (hk : k ≤ r),
      ∃ q : Path (u' 0) (u' k), (∀ t, q t ∈ F₀) ∧
        Cl.mk ((γ.subpath 0 (s k)).cast hv'0 (hv' k hk)) =
          (Cl.mk (π 0 (Nat.zero_le r))).trans ((Cl.mk q).trans (Cl.mk (π k hk)).symm) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨Path.refl (u' 0), fun _ => hu'_eq 0 (Nat.zero_le r) ▸ (hP 0 (Nat.zero_le r)).2, ?_⟩
      have hsub0 : (γ.subpath 0 (s 0)).cast hv'0 (hv' 0 (Nat.zero_le r)) = Path.refl (v' 0) := by
        ext t
        change (γ.subpath 0 (s 0)) t = v' 0
        rw [hs0, Path.subpath_self, Path.refl_apply, hv'0]
      rw [hsub0]
      change Cl.rf (v' 0) =
        (Cl.mk (π 0 (Nat.zero_le r))).trans ((Cl.rf (u' 0)).trans (Cl.mk (π 0 hk)).symm)
      rw [cl_refl_trans, cl_trans_symm]
    | succ k ih =>
      obtain ⟨q, hqF₀, hq_eq⟩ := ih (Nat.le_of_succ_le hk)
      refine ⟨q.trans (β k hk), ?_, ?_⟩
      · intro t
        have : (q.trans (β k hk)) t ∈ range q ∪ range (β k hk) := by
          rw [← Path.trans_range]; exact mem_range_self t
        rcases this with ⟨w, hw⟩ | ⟨w, hw⟩
        · exact hw ▸ hqF₀ w
        · exact hw ▸ hβ_F₀ k hk w
      · let α_k : Path (v' k) (v' (k + 1)) :=
          (γ.subpath (s k) (s (k + 1))).cast (hv' k (Nat.le_of_succ_le hk)) (hv' (k + 1) hk)
        let γ_k : Path (v' 0) (v' k) :=
          (γ.subpath 0 (s k)).cast hv'0 (hv' k (Nat.le_of_succ_le hk))
        let γ_k1 : Path (v' 0) (v' (k + 1)) :=
          (γ.subpath 0 (s (k + 1))).cast hv'0 (hv' (k + 1) hk)
        have h_trans : γ_k1.Homotopic (γ_k.trans α_k) := by
          have h1 := Path.Homotopic.subpath_trans_subpath γ 0 (s k) (s (k + 1))
          have h2 := Path.Homotopic.pathCast h1 hv'0 (hv' (k + 1) hk)
          exact h2.symm.trans (by
            have heq : ((γ.subpath 0 (s k)).trans (γ.subpath (s k) (s (k + 1)))).cast
                hv'0 (hv' (k + 1) hk) = γ_k.trans α_k := by
              ext t
              simp [γ_k, α_k, Path.trans_apply]
            rw [heq])
        have h_cl_trans : Cl.mk γ_k1 = (Cl.mk γ_k).trans (Cl.mk α_k) := by
          rw [← Path.Homotopic.Quotient.mk_trans]
          exact Path.Homotopic.Quotient.eq.mpr h_trans
        have h_mk_qβ : Cl.mk (q.trans (β k hk)) = (Cl.mk q).trans (Cl.mk (β k hk)) :=
          (Path.Homotopic.Quotient.mk_trans q (β k hk)).symm
        rw [h_cl_trans, hq_eq, h_step k hk, h_mk_qβ]
        calc
          ((Cl.mk (π 0 (Nat.zero_le r))).trans ((Cl.mk q).trans (Cl.mk (π k
            (Nat.le_of_succ_le hk))).symm)).trans
              ((Cl.mk (π k (Nat.le_of_succ_le hk))).trans ((Cl.mk (β k hk)).trans (Cl.mk (π
                (k + 1) hk)).symm))
            = (Cl.mk (π 0 (Nat.zero_le r))).trans ((Cl.mk q).trans
                (((Cl.mk (π k (Nat.le_of_succ_le hk))).symm.trans (Cl.mk (π k
                  (Nat.le_of_succ_le hk)))).trans
                  ((Cl.mk (β k hk)).trans (Cl.mk (π (k + 1) hk)).symm))) := by
              simp only [cl_assoc]
          _ = (Cl.mk (π 0 (Nat.zero_le r))).trans (((Cl.mk q).trans (Cl.mk (β k hk))).trans (Cl.mk
            (π (k + 1) hk)).symm) := by
              rw [cl_symm_trans, cl_refl_trans, cl_assoc]
  obtain ⟨q, hqF₀, hq_eq⟩ := h_ind r le_rfl
  have hv'r : v' 0 = v' r := by simp [v']
  have hu'r : u' 0 = u' r := by simp [u']
  let q_loop : Path (⟨u' 0, mem_univ _⟩ : (univ : Set S)) ⟨u' 0, mem_univ _⟩ :=
    ⟨⟨fun t => ⟨q t, mem_univ _⟩, Continuous.subtype_mk q.continuous _⟩,
      Subtype.ext q.source, Subtype.ext (q.target.trans hu'r.symm)⟩
  have hq_null := homotopic_refl_of_null hF₀_null q_loop (fun t => hqF₀ t)
  have hq_null' : (q.cast rfl hu'r).Homotopic (Path.refl (u' 0)) := by
    let proj : C((univ : Set S), S) := ⟨Subtype.val, continuous_subtype_val⟩
    exact hq_null.map proj
  have hπ_r0 : (π r le_rfl).cast hv'r hu'r = π 0 (Nat.zero_le r) := by
    ext t
    simp [π]
  have hγ_cast := cl_conj_eq_refl hv'r hu'r
    ((γ.subpath 0 (s r)).cast hv'0 (hv' r le_rfl))
    (π 0 (Nat.zero_le r)) (π r le_rfl) q hq_eq hq_null' hπ_r0
  have hγ_null : γ.Homotopic (Path.refl (f (arcParam 1 0))) := by
    exact subdivision_loop_is_null (S := S) (r := r) s hsr f γ v' hv' hv'0 hv'r hγ_cast
  let a_univ : (univ : Set S) := ⟨f (arcParam 1 0), mem_univ _⟩
  let γ_univ : Path a_univ a_univ :=
    ⟨⟨fun t => ⟨γ t, mem_univ _⟩, Continuous.subtype_mk γ.continuous _⟩,
      Subtype.ext γ.source, Subtype.ext γ.target⟩
  refine ⟨φ, a_univ.1, a_univ.2, ?_⟩
  exact closedCurvesHomotopicIn_of_path 1 f (ContinuousMap.const _ a_univ.1)
    γ_univ (Path.refl a_univ) (fun _ => rfl) (fun _ => rfl) (loop_in_univ_is_null γ hγ_null)

end GraphMinor.GM07
