/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.GM07.Section11c
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.Circle
import Mathlib.Data.Set.Card

/-!
# Graph Minors VII, Section 11: Proof of (11.7) (Bridge Arc Between Arc-Components)

This file proves the bridge-arc step of Graph Minors VII, (11.7) (page 253):
in a connected surface `S`, if a solid flat subset `Z ⊆ S` has at least two arc-components
(`2 ≤ (arcComponentsIn Z).ncard`), then there is a `[0, 1]`-arc `T ⊆ S` with ends `a, b` in
distinct arc-components of `Z` and `T ∩ Z = {a, b}` such that `T` is solid, `Z ∪ T` is flat, and
`(arcComponentsIn (Z ∪ T)).ncard < (arcComponentsIn Z).ncard`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Basic Helper Lemmas on Solid Sets and Arc-Components -/

/-- Contrapositive of (11.2): a subset `Z ⊆ S` is flat if every `O`-arc `F ⊆ Z` is null-homotopic
in `S`. -/
theorem isFlat_of_forall_isNullHomotopicOArc (hS : IsSurface S) {Z : Set S}
    (h : ∀ F : Set S, F ⊆ Z → IsOArc F → IsNullHomotopicOArc F) :
    IsFlat Z := by
  intro φ hφZ
  by_contra hnot
  obtain ⟨F, hF_oarc, hF_range, hF_not_null⟩ := nonNullHomotopicOArc_in_curve hS φ hnot
  exact hF_not_null (h F (hF_range.trans hφZ) hF_oarc)

/-- Every `O`-arc `F` contained in a flat subset `Y ⊆ S` is null-homotopic in `S`. -/
theorem isNullHomotopicOArc_of_isFlat {Y F : Set S} (hY : IsFlat Y) (hFY : F ⊆ Y)
    (hF : IsOArc F) : IsNullHomotopicOArc F := by
  obtain ⟨φ⟩ := hF
  refine ⟨φ, hY ⟨fun x => (φ x).1, continuous_subtype_val.comp φ.continuous⟩ ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hFY (φ x).2

/-- `arcComponentsIn Z` is the image of `Z` under `pathComponentIn Z`. -/
theorem arcComponentsIn_eq_image_pathComponentIn (Z : Set S) :
    arcComponentsIn Z = (pathComponentIn Z) '' Z := by
  ext C
  constructor
  · rintro ⟨⟨x, hxC⟩, hCZ, hC_pc, hC_max⟩
    have hxZ : x ∈ Z := hCZ hxC
    refine ⟨x, hxZ, ?_⟩
    exact hC_max (pathComponentIn Z x) pathComponentIn_subset (isPathConnected_pathComponentIn hxZ)
      (hC_pc.subset_pathComponentIn hxC hCZ)
  · rintro ⟨x, hxZ, rfl⟩
    exact pathComponentIn_mem_arcComponentsIn hxZ

/-- Every solid subset of a surface has only finitely many arc-components. -/
theorem arcComponentsIn_finite_of_isSolid (hS : IsSurface S) {Z : Set S} (hZ : IsSolid Z) :
    (arcComponentsIn Z).Finite := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hZ_compact : IsCompact Z := hZ.2.isCompact
  have hex : ∀ z : S, ∃ A : Set S, IsOpen A ∧ z ∈ A ∧ (z ∈ Z → IsArcConnected (Z ∩ A)) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨A, _, hzA, hA_open, hZA_arc⟩ := hZ.1 z hz univ isOpen_univ (mem_univ z)
      exact ⟨A, hA_open, hzA, fun _ => hZA_arc⟩
    · exact ⟨univ, isOpen_univ, mem_univ z, fun hz' => absurd hz' hz⟩
  choose A hA_open hzA hZA_arc using hex
  have hcov : Z ⊆ ⋃ z ∈ Z, A z := fun z hz => mem_iUnion₂.mpr ⟨z, hz, hzA z⟩
  obtain ⟨t, htZ, ht_fin, ht_cov⟩ :=
    hZ_compact.elim_finite_subcover_image (fun z _ => hA_open z) hcov
  rw [arcComponentsIn_eq_image_pathComponentIn]
  refine (ht_fin.image (pathComponentIn Z)).subset ?_
  rintro _ ⟨y, hyZ, rfl⟩
  obtain ⟨z, hzt, hyAz⟩ := mem_iUnion₂.mp (ht_cov hyZ)
  have hzZ : z ∈ Z := htZ hzt
  have hj : JoinedIn (Z ∩ A z) z y :=
    isArcConnected_iff_joinedIn.mp (hZA_arc z hzZ) z ⟨hzZ, hzA z⟩ y ⟨hyZ, hyAz⟩
  have hjZ : JoinedIn Z z y := hj.mono inter_subset_left
  exact ⟨z, hzt, (pathComponentIn_congr hjZ).symm⟩

/-- In a surface `S`, if `Z` is solid and `z₀ ∈ Z`, then both `A := pathComponentIn Z z₀` and
`B := Z \ A` are closed in `S`. -/
theorem isClosed_pathComponentIn_and_sdiff_of_isSolid (hS : IsSurface S) {Z : Set S}
    (hZ : IsSolid Z) {z₀ : S} :
    IsClosed (pathComponentIn Z z₀) ∧ IsClosed (Z \ pathComponentIn Z z₀) := by
  have : T2Space S := hS.2.1
  set A : Set S := pathComponentIn Z z₀
  set B : Set S := Z \ A
  have hA_sub : A ⊆ Z := pathComponentIn_subset
  have hA_open_in_Z : ∀ x ∈ A, ∃ C : Set S, IsOpen C ∧ x ∈ C ∧ Z ∩ C ⊆ A := by
    intro x hxA
    obtain ⟨C, _, hxC, hC_open, hZC_arc⟩ := hZ.1 x (hA_sub hxA) univ isOpen_univ (mem_univ x)
    refine ⟨C, hC_open, hxC, fun y hy => ?_⟩
    have hj : JoinedIn (Z ∩ C) x y :=
      isArcConnected_iff_joinedIn.mp hZC_arc x ⟨hA_sub hxA, hxC⟩ y hy
    exact JoinedIn.trans hxA (hj.mono inter_subset_left)
  have hB_open_in_Z : ∀ x ∈ B, ∃ C : Set S, IsOpen C ∧ x ∈ C ∧ Z ∩ C ⊆ B := by
    intro x hxB
    obtain ⟨C, _, hxC, hC_open, hZC_arc⟩ := hZ.1 x hxB.1 univ isOpen_univ (mem_univ x)
    refine ⟨C, hC_open, hxC, fun y hy => ⟨hy.1, fun hyA => hxB.2 ?_⟩⟩
    have hj : JoinedIn (Z ∩ C) y x :=
      isArcConnected_iff_joinedIn.mp hZC_arc y hy x ⟨hxB.1, hxC⟩
    exact JoinedIn.trans hyA (hj.mono inter_subset_left)
  set U_A : Set S := ⋃ (x : S) (hx : x ∈ A), (hA_open_in_Z x hx).choose
  set U_B : Set S := ⋃ (x : S) (hx : x ∈ B), (hB_open_in_Z x hx).choose
  have hUA_open : IsOpen U_A :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx => (hA_open_in_Z x hx).choose_spec.1
  have hUB_open : IsOpen U_B :=
    isOpen_iUnion fun x => isOpen_iUnion fun hx => (hB_open_in_Z x hx).choose_spec.1
  have hA_eq : A = Z \ U_B := by
    ext y
    constructor
    · intro hyA
      refine ⟨hA_sub hyA, ?_⟩
      rintro hyUB
      obtain ⟨x, hx, hyC⟩ := mem_iUnion₂.mp hyUB
      exact ((hB_open_in_Z x hx).choose_spec.2.2 ⟨hA_sub hyA, hyC⟩).2 hyA
    · rintro ⟨hyZ, hynotUB⟩
      by_contra hynotA
      have hyB : y ∈ B := ⟨hyZ, hynotA⟩
      exact hynotUB (mem_iUnion₂.mpr ⟨y, hyB, (hB_open_in_Z y hyB).choose_spec.2.1⟩)
  have hB_eq : B = Z \ U_A := by
    ext y
    constructor
    · rintro ⟨hyZ, hynotA⟩
      refine ⟨hyZ, ?_⟩
      rintro hyUA
      obtain ⟨x, hx, hyC⟩ := mem_iUnion₂.mp hyUA
      exact hynotA ((hA_open_in_Z x hx).choose_spec.2.2 ⟨hyZ, hyC⟩)
    · rintro ⟨hyZ, hynotUA⟩
      refine ⟨hyZ, fun hyA => ?_⟩
      exact hynotUA (mem_iUnion₂.mpr ⟨y, hyA, (hA_open_in_Z y hyA).choose_spec.2.1⟩)
  exact ⟨hA_eq ▸ hZ.2.sdiff hUB_open, hB_eq ▸ hZ.2.sdiff hUA_open⟩

/-- A connected surface `S` is arc-connected (`IsArcConnected (univ : Set S)`). -/
theorem isArcConnected_univ_of_isSurface (hS : IsSurface S) [ConnectedSpace S] :
    IsArcConnected (univ : Set S) := by
  have : T2Space S := hS.2.1
  have hlac : IsLocallyArcConnected (univ : Set S) := by
    intro x _ A hA hxA
    obtain ⟨W, hWA, hxW, hW_open, hW_arc, _⟩ := exists_chart_ball_subset hS x hA hxA
    exact ⟨W, hWA, hxW, hW_open, by rwa [univ_inter]⟩
  obtain ⟨z₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨hA_closed, hB_closed⟩ :=
    isClosed_pathComponentIn_and_sdiff_of_isSolid hS ⟨hlac, isClosed_univ⟩ (z₀ := z₀)
  set A : Set S := pathComponentIn univ z₀
  set B : Set S := univ \ A
  have hz₀A : z₀ ∈ A := mem_pathComponentIn_self (mem_univ z₀)
  have hA_open : IsOpen A := by
    have : A = Bᶜ := by ext x; simp [B]
    rw [this]
    exact hB_closed.isOpen_compl
  have hA_clopen : IsClopen A := ⟨hA_closed, hA_open⟩
  have hA_univ : A = univ := hA_clopen.eq_univ ⟨z₀, hz₀A⟩
  rw [← hA_univ]
  exact IsPathConnected.isArcConnected (isPathConnected_pathComponentIn (mem_univ z₀))

/-- Every `[0, 1]`-arc `T` in a surface `S` is solid (`IsSolid T`). -/
theorem isSolid_of_isLineWithEnds (hS : IsSurface S) {T : Set S} {a b : S}
    (hT : IsLineWithEnds T a b) : IsSolid T := by
  have : T2Space S := hS.2.1
  obtain ⟨f, _, _⟩ := hT
  let e : unitInterval → S := fun t => (f t).1
  have he_cont : Continuous e := continuous_subtype_val.comp f.continuous
  have hT_range : T = range e := by
    ext x
    exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, by simp [e]⟩, by rintro ⟨t, rfl⟩; exact (f t).2⟩
  have hT_closed : IsClosed T := hT_range ▸ (isCompact_range he_cont).isClosed
  refine ⟨?_, hT_closed⟩
  intro z hz A hA_open hzA
  let t₀ : unitInterval := f.symm ⟨z, hz⟩
  have ht₀_mem : t₀ ∈ e ⁻¹' A := by
    change (f (f.symm ⟨z, hz⟩)).1 ∈ A
    simpa using hzA
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp (hA_open.preimage he_cont) t₀ ht₀_mem
  have hball_open_T : IsOpen (f '' Metric.ball t₀ r) :=
    f.isOpenMap _ Metric.isOpen_ball
  obtain ⟨W₀, hW₀_open, hW₀_eq⟩ := isOpen_induced_iff.mp hball_open_T
  let A' : Set S := W₀ ∩ A
  have hT_inter : T ∩ A' = e '' Metric.ball t₀ r := by
    ext x
    constructor
    · rintro ⟨hxT, hxW₀, _⟩
      have hx_mem : (⟨x, hxT⟩ : T) ∈ Subtype.val ⁻¹' W₀ := hxW₀
      rw [hW₀_eq] at hx_mem
      obtain ⟨t, ht, hft⟩ := hx_mem
      exact ⟨t, ht, congrArg Subtype.val hft⟩
    · rintro ⟨t, ht, rfl⟩
      have hft_mem : f t ∈ f '' Metric.ball t₀ r := mem_image_of_mem f ht
      rw [← hW₀_eq] at hft_mem
      exact ⟨(f t).2, hft_mem, hr_sub ht⟩
  have hzA' : z ∈ A' := by
    have : z ∈ T ∩ A' := by
      rw [hT_inter]
      refine ⟨t₀, Metric.mem_ball_self hr_pos, ?_⟩
      change (f (f.symm ⟨z, hz⟩)).1 = z
      simp
    exact this.2
  have hball_pc : IsPathConnected (Metric.ball t₀ r) := by
    have hconv : Convex ℝ (Subtype.val '' Metric.ball t₀ r) := by
      have heq : Subtype.val '' Metric.ball t₀ r = Icc (0 : ℝ) 1 ∩ Metric.ball (t₀ : ℝ) r := by
        ext x
        simp only [mem_image, Metric.mem_ball, Subtype.exists, Subtype.dist_eq, mem_inter_iff]
        exact ⟨fun ⟨u, huI, hur, hux⟩ => hux ▸ ⟨huI, hur⟩,
          fun ⟨hxI, hxr⟩ => ⟨x, hxI, hxr, rfl⟩⟩
      rw [heq]
      exact (convex_Icc 0 1).inter (convex_ball (t₀ : ℝ) r)
    rw [IsInducing.subtypeVal.isPathConnected_iff]
    exact hconv.isPathConnected ⟨(t₀ : ℝ), mem_image_of_mem Subtype.val
      (Metric.mem_ball_self hr_pos)⟩
  have hTA'_arc : IsArcConnected (T ∩ A') := by
    rw [hT_inter]
    exact IsPathConnected.isArcConnected (hball_pc.image he_cont)
  exact ⟨A', inter_subset_right, hzA', hW₀_open.inter hA_open, hTA'_arc⟩

/-- Every nonempty open subset `W` of `Circle` contains at least two distinct points. -/
private theorem exists_ne_of_isOpen_circle {W : Set Circle} (hW : IsOpen W) {z₁ : Circle}
    (hz₁ : z₁ ∈ W) : ∃ z₂ ∈ W, z₂ ≠ z₁ := by
  by_contra! h
  have hW_eq : W = {z₁} := Subset.antisymm h (singleton_subset_iff.mpr hz₁)
  have hW_clopen : IsClopen W := ⟨hW_eq ▸ isClosed_singleton, hW⟩
  have hW_univ : W = univ := hW_clopen.eq_univ ⟨z₁, hz₁⟩
  have hneg : -z₁ ∈ ({z₁} : Set Circle) := by rw [← hW_eq, hW_univ]; exact mem_univ _
  exact Circle.neg_ne_self z₁ (mem_singleton_iff.mp hneg)

/-- Any `O`-arc `F` contained in a `[0, 1]`-arc `T` is null-homotopic in `S`. -/
private theorem isNullHomotopicOArc_of_subset_line {T F : Set S} {a b : S}
    (hT : IsLineWithEnds T a b) (hFT : F ⊆ T) (hF : IsOArc F) :
    IsNullHomotopicOArc F := by
  obtain ⟨f, _, _⟩ := hT
  obtain ⟨φ⟩ := hF
  let lift : Circle → unitInterval := fun z => f.symm ⟨(φ z).1, hFT (φ z).2⟩
  have hlift_cont : Continuous lift := by
    dsimp [lift]
    fun_prop
  let H : Circle × unitInterval → unitInterval := fun p =>
    ⟨(1 - (p.2 : ℝ)) * (lift p.1 : ℝ),
      mul_nonneg (sub_nonneg.mpr p.2.2.2) (lift p.1).2.1,
      by nlinarith [p.2.2.1, p.2.2.2, (lift p.1).2.1, (lift p.1).2.2]⟩
  have hH_cont : Continuous H := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_subtype_val.comp (hlift_cont.comp continuous_fst))
  refine ⟨φ, (f 0).1, mem_univ _, ⟨⟨fun p => (f (H p)).1,
    continuous_subtype_val.comp (f.continuous.comp hH_cont)⟩, fun _ => mem_univ _, ?_, ?_⟩⟩
  · intro z
    have h0 : H (z, 0) = lift z := by ext; simp [H]
    change (f (H (z, 0))).1 = (φ z).1
    rw [h0]
    change (f (f.symm ⟨(φ z).1, hFT (φ z).2⟩)).1 = (φ z).1
    simp
  · intro z
    have h1 : H (z, 1) = 0 := by ext; simp [H]
    change (f (H (z, 1))).1 = (f 0).1
    rw [h1]

/-! ## Proof of (11.7): Bridge Arc (`solid_bridge_arc`) -/

private theorem flat_union_of_bridge_arc (hS : IsSurface S) {Z A : Set S}
    (hZ_closed : IsClosed Z) (hZ_flat : IsFlat Z) (hA_sub : A ⊆ Z)
    (hA_closed : IsClosed A) (hB_closed : IsClosed (Z \ A))
    {e : unitInterval → S} (he_cont : Continuous e) (he_inj : Injective e)
    {a b : S} (he0 : e 0 = a) (he1 : e 1 = b)
    (ha_A : a ∈ A) (hb_B : b ∈ Z \ A)
    (he_mem_A : ∀ t : unitInterval, e t ∈ A ↔ t = 0)
    (he_mem_B : ∀ t : unitInterval, e t ∈ Z \ A ↔ t = 1)
    (hT_line : IsLineWithEnds (range e) a b) : IsFlat (Z ∪ range e) := by
  have : T2Space S := hS.2.1
  let B := Z \ A
  let T := range e
  refine isFlat_of_forall_isNullHomotopicOArc hS fun F hF_sub hF_oarc => ?_
  -- For any interior point `t ∈ Ioo 0 1` with `e t ∈ F`, `F` is contained in
  -- `K₁ t := A ∪ e '' Iic t` or `K₂ t := B ∪ e '' Ici t`.
  let K₁ : unitInterval → Set S := fun t => A ∪ e '' Iic t
  let K₂ : unitInterval → Set S := fun t => B ∪ e '' Ici t
  have hK₁_closed : ∀ t, IsClosed (K₁ t) := fun t =>
    hA_closed.union (isClosed_Iic.isCompact.image he_cont).isClosed
  have hK₂_closed : ∀ t, IsClosed (K₂ t) := fun t =>
    hB_closed.union (isClosed_Ici.isCompact.image he_cont).isClosed
  have hK_union : ∀ t, Z ∪ T ⊆ K₁ t ∪ K₂ t := by
    intro t x hx
    rcases hx with hxZ | ⟨s, rfl⟩
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl ⟨hxZ, hxA⟩)
    · rcases le_total s t with hst | hts
      · exact Or.inl (Or.inr ⟨s, hst, rfl⟩)
      · exact Or.inr (Or.inr ⟨s, hts, rfl⟩)
  have hK_inter : ∀ t ∈ Ioo (0 : unitInterval) 1, K₁ t ∩ K₂ t = {e t} := by
    intro t ⟨ht0, ht1⟩
    ext x
    constructor
    · rintro (⟨hxA | ⟨s₁, hs₁, rfl⟩, hxB | ⟨s₂, hs₂, heq⟩⟩)
      · exact False.elim (hxB.2 hxA)
      · exfalso
        have hs₂0 : s₂ = 0 := (he_mem_A s₂).mp (heq ▸ hxA)
        exact ht0.not_ge (hs₂0 ▸ hs₂)
      · exfalso
        have hs₁1 : s₁ = 1 := (he_mem_B s₁).mp hxB
        exact ht1.not_ge (hs₁1 ▸ hs₁)
      · have hs_eq : s₁ = s₂ := he_inj heq.symm
        have hst : s₁ = t := le_antisymm hs₁ (hs_eq ▸ hs₂)
        exact mem_singleton_iff.mpr (hst ▸ rfl)
    · rintro rfl
      exact ⟨Or.inr ⟨t, le_refl t, rfl⟩, Or.inr ⟨t, le_refl t, rfl⟩⟩
  have hF_dichotomy : ∀ t ∈ Ioo (0 : unitInterval) 1, e t ∈ F → F ⊆ K₁ t ∨ F ⊆ K₂ t := by
    intro t ht hetF
    obtain ⟨φ⟩ := hF_oarc
    let z_t : Circle := φ.symm ⟨e t, hetF⟩
    have hcompl_pc : IsPathConnected ({z_t}ᶜ : Set Circle) :=
      Circle.isPathConnected_compl_singleton z_t
    have hF_minus_eq : F \ {e t} = (Subtype.val ∘ φ) '' ({z_t}ᶜ : Set Circle) := by
      ext x
      constructor
      · rintro ⟨hxF, hxne⟩
        refine ⟨φ.symm ⟨x, hxF⟩, ?_, by simp⟩
        intro hzeq
        have h1 : (φ (φ.symm ⟨x, hxF⟩)).1 = (φ z_t).1 := congrArg (fun z => (φ z).1) hzeq
        simp only [z_t, Homeomorph.apply_symm_apply] at h1
        exact hxne h1
      · rintro ⟨z, hzne, rfl⟩
        refine ⟨(φ z).2, ?_⟩
        intro hxeq
        apply hzne
        change z = φ.symm ⟨e t, hetF⟩
        have : φ z = ⟨e t, hetF⟩ := Subtype.ext hxeq
        rw [← this, φ.symm_apply_apply]
    have hF_minus_pre : IsPreconnected (F \ {e t}) := by
      rw [hF_minus_eq]
      exact (hcompl_pc.image (continuous_subtype_val.comp φ.continuous)).isConnected.isPreconnected
    let V₁ : Set S := (K₂ t)ᶜ
    let V₂ : Set S := (K₁ t)ᶜ
    have hsub_V : F \ {e t} ⊆ V₁ ∪ V₂ := by
      rintro x ⟨_, hxne⟩
      by_cases hx1 : x ∈ K₁ t
      · by_cases hx2 : x ∈ K₂ t
        · exfalso
          have hx_inter : x ∈ K₁ t ∩ K₂ t := ⟨hx1, hx2⟩
          rw [hK_inter t ht] at hx_inter
          exact hxne hx_inter
        · exact Or.inl hx2
      · exact Or.inr hx1
    have hdisj_V : (F \ {e t}) ∩ (V₁ ∩ V₂) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨⟨hxF, _⟩, hxV₁, hxV₂⟩
      rcases hK_union t (hF_sub hxF) with hx1 | hx2
      · exact hxV₂ hx1
      · exact hxV₁ hx2
    rcases isPreconnected_iff_subset_of_disjoint.mp hF_minus_pre V₁ V₂
      (hK₂_closed t).isOpen_compl (hK₁_closed t).isOpen_compl hsub_V hdisj_V with h₁ | h₂
    · left
      intro x hxF
      by_cases hxt : x = e t
      · rw [hxt]; exact Or.inr ⟨t, le_refl t, rfl⟩
      · have hxV₁ : x ∉ K₂ t := h₁ ⟨hxF, hxt⟩
        exact (hK_union t (hF_sub hxF)).resolve_right hxV₁
    · right
      intro x hxF
      by_cases hxt : x = e t
      · rw [hxt]; exact Or.inr ⟨t, le_refl t, rfl⟩
      · have hxV₂ : x ∉ K₁ t := h₂ ⟨hxF, hxt⟩
        exact (hK_union t (hF_sub hxF)).resolve_left hxV₂
  by_cases hFZ : F ⊆ Z
  · exact isNullHomotopicOArc_of_isFlat hZ_flat hFZ hF_oarc
  · obtain ⟨x₁, hx₁F, hx₁Z⟩ := not_subset.mp hFZ
    obtain ⟨φ⟩ := id hF_oarc
    let W : Set Circle := {z : Circle | (φ z).1 ∉ Z}
    have hW_open : IsOpen W :=
      hZ_closed.isOpen_compl.preimage (continuous_subtype_val.comp φ.continuous)
    let z₁ : Circle := φ.symm ⟨x₁, hx₁F⟩
    have hz₁W : z₁ ∈ W := by change (φ (φ.symm ⟨x₁, hx₁F⟩)).1 ∉ Z; simpa using hx₁Z
    obtain ⟨z₂, hz₂W, hz_ne⟩ := exists_ne_of_isOpen_circle hW_open hz₁W
    let x₂ : S := (φ z₂).1
    have hx₂F : x₂ ∈ F := (φ z₂).2
    have hx₂Z : x₂ ∉ Z := hz₂W
    have hx_ne : x₁ ≠ x₂ := by
      intro heq
      apply hz_ne
      have : φ z₂ = ⟨x₁, hx₁F⟩ := Subtype.ext heq.symm
      dsimp [z₁]
      rw [← this, φ.symm_apply_apply]
    have hx₁T : x₁ ∈ T := (hF_sub hx₁F).resolve_left hx₁Z
    have hx₂T : x₂ ∈ T := (hF_sub hx₂F).resolve_left hx₂Z
    obtain ⟨t₁', ht₁'⟩ := hx₁T
    obtain ⟨t₂', ht₂'⟩ := hx₂T
    have ht₁'_Ioo : t₁' ∈ Ioo (0 : unitInterval) 1 := by
      refine ⟨lt_of_le_of_ne t₁'.2.1 ?_, lt_of_le_of_ne t₁'.2.2 ?_⟩
      · intro h0; exact hx₁Z (ht₁' ▸ h0 ▸ he0 ▸ hA_sub ha_A)
      · intro h1; exact hx₁Z (ht₁' ▸ h1 ▸ he1 ▸ hb_B.1)
    have ht₂'_Ioo : t₂' ∈ Ioo (0 : unitInterval) 1 := by
      refine ⟨lt_of_le_of_ne t₂'.2.1 ?_, lt_of_le_of_ne t₂'.2.2 ?_⟩
      · intro h0; exact hx₂Z (ht₂' ▸ h0 ▸ he0 ▸ hA_sub ha_A)
      · intro h1; exact hx₂Z (ht₂' ▸ h1 ▸ he1 ▸ hb_B.1)
    have ht'_ne : t₁' ≠ t₂' := fun h => hx_ne (ht₁' ▸ ht₂' ▸ congrArg e h)
    have hFT : F ⊆ T := by
      have h_ord : ∀ u₁ u₂ : unitInterval, u₁ ∈ Ioo 0 1 → u₂ ∈ Ioo 0 1 →
          u₁ < u₂ → e u₁ ∈ F → e u₂ ∈ F → F ⊆ T := by
        intro u₁ u₂ hu₁ hu₂ hlt heu₁ heu₂
        have h1 : F ⊆ K₁ u₂ := by
          refine (hF_dichotomy u₂ hu₂ heu₂).resolve_right fun hsub2 => ?_
          rcases hsub2 heu₁ with hB1 | ⟨s, hs, heq⟩
          · exact (lt_irrefl (1 : unitInterval)) ((he_mem_B u₁).mp hB1 ▸ hu₁.2)
          · have : u₁ = s := he_inj heq.symm
            exact hlt.not_ge (this ▸ hs)
        have h2 : F ⊆ K₂ u₁ := by
          refine (hF_dichotomy u₁ hu₁ heu₁).resolve_left fun hsub1 => ?_
          rcases hsub1 heu₂ with hA2 | ⟨s, hs, heq⟩
          · exact (lt_irrefl (0 : unitInterval)) ((he_mem_A u₂).mp hA2 ▸ hu₂.1)
          · have : u₂ = s := he_inj heq.symm
            exact hlt.not_ge (this ▸ hs)
        intro x hxF
        rcases h1 hxF with hxA | ⟨s, _, rfl⟩
        · rcases h2 hxF with hxB | ⟨s, hs, heq⟩
          · exact False.elim (hxB.2 hxA)
          · exact ⟨s, heq⟩
        · exact mem_range_self s
      rcases lt_or_gt_of_ne ht'_ne with hlt | hgt
      · exact h_ord t₁' t₂' ht₁'_Ioo ht₂'_Ioo hlt (ht₁' ▸ hx₁F) (ht₂' ▸ hx₂F)
      · exact h_ord t₂' t₁' ht₂'_Ioo ht₁'_Ioo hgt (ht₂' ▸ hx₂F) (ht₁' ▸ hx₁F)
    exact isNullHomotopicOArc_of_subset_line hT_line hFT hF_oarc

/-- The bridge-arc step in the proof of Graph Minors VII, (11.7) (page 253):
in a connected surface `S`, if a solid flat subset `Z ⊆ S` has at least two arc-components, there
is a `[0, 1]`-arc `T ⊆ S` meeting `Z` only at its two ends in distinct arc-components of `Z`, such
that `T` is solid, `Z ∪ T` is flat, and `Z ∪ T` has strictly fewer arc-components than `Z`. -/
theorem solid_bridge_arc (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) (h2 : 2 ≤ (arcComponentsIn Z).ncard) :
    ∃ (T : Set S) (a b : S), IsLineWithEnds T a b ∧ T ∩ Z = {a, b} ∧
      IsSolid T ∧ IsFlat (Z ∪ T) ∧ (arcComponentsIn (Z ∪ T)).ncard < (arcComponentsIn Z).ncard := by
  have : T2Space S := hS.2.1
  -- Step 1: Pick two distinct arc-components `A = pathComponentIn Z z₀` and `C₂ = pathComponentIn Z
  -- z₁`.
  have hfin : (arcComponentsIn Z).Finite := arcComponentsIn_finite_of_isSolid hS hZ_solid
  obtain ⟨C₁, C₂, hC₁, hC₂, hC_ne⟩ :=
    (Set.one_lt_ncard_iff hfin).mp (by omega : 1 < (arcComponentsIn Z).ncard)
  rw [arcComponentsIn_eq_image_pathComponentIn] at hC₁ hC₂
  obtain ⟨z₀, hz₀Z, rfl⟩ := hC₁
  obtain ⟨z₁, hz₁Z, rfl⟩ := hC₂
  set A : Set S := pathComponentIn Z z₀
  set B : Set S := Z \ A
  have hA_sub : A ⊆ Z := pathComponentIn_subset
  have hz₀A : z₀ ∈ A := mem_pathComponentIn_self hz₀Z
  have hz₁B : z₁ ∈ B := by
    refine ⟨hz₁Z, fun hz₁A => hC_ne ?_⟩
    exact (pathComponentIn_congr hz₁A).symm
  obtain ⟨hA_closed, hB_closed⟩ :=
    isClosed_pathComponentIn_and_sdiff_of_isSolid hS hZ_solid (z₀ := z₀)
  -- Step 2: Connect `z₀ ∈ A` to `z₁ ∈ B` in `S`, trim to first hit of `B` and last hit of `A`,
  -- and extract an injective `[0, 1]`-arc `T` via (11.1).
  obtain ⟨γ₀, _, hγ₀_0, hγ₀_1⟩ :=
    exists_path_of_isArcConnected (isArcConnected_univ_of_isSurface hS) (mem_univ z₀) (mem_univ z₁)
  let PreB : Set unitInterval := γ₀ ⁻¹' B
  have hPreB_closed : IsClosed PreB := hB_closed.preimage γ₀.continuous
  have h1_PreB : (1 : unitInterval) ∈ PreB := by change γ₀ 1 ∈ B; rw [hγ₀_1]; exact hz₁B
  let t₁ : unitInterval := sInf PreB
  have ht₁_mem : γ₀ t₁ ∈ B := hPreB_closed.csInf_mem ⟨1, h1_PreB⟩ (OrderBot.bddBelow PreB)
  have ht₁_le : ∀ t ∈ PreB, t₁ ≤ t := fun t ht => csInf_le (OrderBot.bddBelow PreB) ht
  have ht₁_pos : 0 < (t₁ : ℝ) := by
    refine lt_of_le_of_ne t₁.2.1 ?_
    intro heq
    have ht₁0 : t₁ = 0 := Subtype.ext heq.symm
    rw [ht₁0, hγ₀_0] at ht₁_mem
    exact ht₁_mem.2 hz₀A
  let γ₁ : C(unitInterval, S) := subPathSeg γ₀ 0 t₁
  have hγ₁_0 : γ₁ 0 = z₀ := by rw [subPathSeg_zero, hγ₀_0]
  have hγ₁_1 : γ₁ 1 = γ₀ t₁ := subPathSeg_one γ₀ 0 t₁
  have hγ₁_B : ∀ t : unitInterval, γ₁ t ∈ B → t = 1 := by
    intro t htB
    have hmem : (⟨(1 - (t : ℝ)) * (0 : ℝ) + (t : ℝ) * (t₁ : ℝ), by
        rw [mul_zero, zero_add]
        exact ⟨mul_nonneg t.2.1 t₁.2.1,
          (mul_le_of_le_one_left t₁.2.1 t.2.2).trans t₁.2.2⟩⟩ : unitInterval) ∈ PreB := htB
    have hle := ht₁_le _ hmem
    change (t₁ : ℝ) ≤ (1 - (t : ℝ)) * 0 + (t : ℝ) * (t₁ : ℝ) at hle
    ext
    change (t : ℝ) = 1
    nlinarith [t.2.2, ht₁_pos]
  let PreA : Set unitInterval := γ₁ ⁻¹' A
  have hPreA_closed : IsClosed PreA := hA_closed.preimage γ₁.continuous
  have h0_PreA : (0 : unitInterval) ∈ PreA := by change γ₁ 0 ∈ A; rw [hγ₁_0]; exact hz₀A
  let s₀ : unitInterval := sSup PreA
  have hs₀_mem : γ₁ s₀ ∈ A := hPreA_closed.csSup_mem ⟨0, h0_PreA⟩ (OrderTop.bddAbove PreA)
  have hs₀_ge : ∀ s ∈ PreA, s ≤ s₀ := fun s hs => le_csSup (OrderTop.bddAbove PreA) hs
  have hs₀_lt1 : (s₀ : ℝ) < 1 := by
    refine lt_of_le_of_ne s₀.2.2 ?_
    intro heq
    have hs₀1 : s₀ = 1 := Subtype.ext heq
    rw [hs₀1, hγ₁_1] at hs₀_mem
    exact ht₁_mem.2 hs₀_mem
  let γ₂ : C(unitInterval, S) := subPathSeg γ₁ s₀ 1
  set a : S := γ₂ 0
  set b : S := γ₂ 1
  have ha_A : a ∈ A := by change γ₂ 0 ∈ A; rw [subPathSeg_zero]; exact hs₀_mem
  have hb_B : b ∈ B := by change γ₂ 1 ∈ B; rw [subPathSeg_one, hγ₁_1]; exact ht₁_mem
  have hab_ne : a ≠ b := fun h => hb_B.2 (h ▸ ha_A)
  have hγ₂_A : ∀ t : unitInterval, γ₂ t ∈ A → t = 0 := by
    intro t htA
    let u : unitInterval := ⟨(1 - (t : ℝ)) * (s₀ : ℝ) + (t : ℝ) * 1,
      by nlinarith [t.2.1, t.2.2, s₀.2.1], by nlinarith [t.2.1, t.2.2, s₀.2.2]⟩
    have hle : (u : ℝ) ≤ (s₀ : ℝ) := hs₀_ge u htA
    change (1 - (t : ℝ)) * (s₀ : ℝ) + (t : ℝ) * 1 ≤ (s₀ : ℝ) at hle
    ext
    change (t : ℝ) = 0
    nlinarith [t.2.1, hs₀_lt1]
  have hγ₂_B : ∀ t : unitInterval, γ₂ t ∈ B → t = 1 := by
    intro t htB
    let u : unitInterval := ⟨(1 - (t : ℝ)) * (s₀ : ℝ) + (t : ℝ) * 1,
      by nlinarith [t.2.1, t.2.2, s₀.2.1], by nlinarith [t.2.1, t.2.2, s₀.2.2]⟩
    have hu1 : u = 1 := hγ₁_B u htB
    have hu1' : (1 - (t : ℝ)) * (s₀ : ℝ) + (t : ℝ) * 1 = 1 := congrArg Subtype.val hu1
    ext
    change (t : ℝ) = 1
    nlinarith [t.2.2, hs₀_lt1]
  obtain ⟨e, he_cont, he_inj, he0, he1, he_sub⟩ := exists_arc_of_path γ₂.continuous hab_ne
  let T : Set S := range e
  have he_emb : IsEmbedding e := (he_cont.isClosedEmbedding he_inj).isEmbedding
  have hT_line : IsLineWithEnds T a b := ⟨he_emb.toHomeomorph, he0, he1⟩
  have he_mem_A : ∀ t : unitInterval, e t ∈ A ↔ t = 0 := by
    intro t
    refine ⟨fun h => ?_, fun h => h ▸ he0 ▸ ha_A⟩
    obtain ⟨u, hu⟩ := he_sub (mem_range_self t)
    have hu0 : u = 0 := hγ₂_A u (hu ▸ h)
    have het : e t = e 0 := by rw [← hu, hu0, ← he0]
    exact he_inj het
  have he_mem_B : ∀ t : unitInterval, e t ∈ B ↔ t = 1 := by
    intro t
    refine ⟨fun h => ?_, fun h => h ▸ he1 ▸ hb_B⟩
    obtain ⟨u, hu⟩ := he_sub (mem_range_self t)
    have hu1 : u = 1 := hγ₂_B u (hu ▸ h)
    have het : e t = e 1 := by rw [← hu, hu1, ← he1]
    exact he_inj het
  have hTZ_eq : T ∩ Z = {a, b} := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hxZ⟩
      by_cases hxA : e t ∈ A
      · rw [(he_mem_A t).mp hxA, he0]; exact Or.inl rfl
      · have hxB : e t ∈ B := ⟨hxZ, hxA⟩
        rw [(he_mem_B t).mp hxB, he1]; exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨0, he0⟩, hA_sub ha_A⟩
      · exact ⟨⟨1, he1⟩, hb_B.1⟩
  -- Step 3: Prove `IsSolid T`.
  have hT_solid : IsSolid T := isSolid_of_isLineWithEnds hS hT_line
  have hZT_flat : IsFlat (Z ∪ T) :=
    flat_union_of_bridge_arc hS hZ_solid.2 hZ_flat hA_sub hA_closed hB_closed
      he_cont he_inj he0 he1 ha_A hb_B he_mem_A he_mem_B hT_line
  -- Step 5: Prove `(arcComponentsIn (Z ∪ T)).ncard < (arcComponentsIn Z).ncard`.
  have hncard_lt : (arcComponentsIn (Z ∪ T)).ncard < (arcComponentsIn Z).ncard := by
    let g : Set S → Set S := fun C => ⋃ x ∈ C, pathComponentIn (Z ∪ T) x
    have hg_eq : ∀ z ∈ Z, g (pathComponentIn Z z) = pathComponentIn (Z ∪ T) z := by
      intro z hz
      ext y
      simp only [g, mem_iUnion₂]
      constructor
      · rintro ⟨x, hx, hy⟩
        exact JoinedIn.trans (hx.mono subset_union_left) hy
      · intro hy
        exact ⟨z, mem_pathComponentIn_self hz, hy⟩
    have haZ : a ∈ Z := hA_sub ha_A
    have hbZ : b ∈ Z := hb_B.1
    let C_a : Set S := pathComponentIn Z a
    let C_b : Set S := pathComponentIn Z b
    have hCa_mem : C_a ∈ arcComponentsIn Z := pathComponentIn_mem_arcComponentsIn haZ
    have hCb_mem : C_b ∈ arcComponentsIn Z := pathComponentIn_mem_arcComponentsIn hbZ
    have hCa_ne_Cb : C_a ≠ C_b := by
      intro heq
      have hCa_eq_A : C_a = A := pathComponentIn_congr ha_A
      have hb_in_A : b ∈ A := by
        rw [← hCa_eq_A, heq]
        exact mem_pathComponentIn_self hbZ
      exact hb_B.2 hb_in_A
    have hI_pc : IsPathConnected (univ : Set unitInterval) := by
      rw [IsInducing.subtypeVal.isPathConnected_iff, image_univ, Subtype.range_coe]
      exact (convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, left_mem_Icc.mpr zero_le_one⟩
    have hT_pc : IsPathConnected T := by
      dsimp [T]
      rw [← image_univ]
      exact hI_pc.image he_cont
    have hj_ab : JoinedIn (Z ∪ T) a b :=
      (hT_pc.joinedIn a ⟨0, he0⟩ b ⟨1, he1⟩).mono subset_union_right
    have hg_ab : g C_a = g C_b := by
      rw [hg_eq a haZ, hg_eq b hbZ]
      exact (pathComponentIn_congr hj_ab).symm
    have hsub_img : arcComponentsIn (Z ∪ T) ⊆ g '' (arcComponentsIn Z \ {C_b}) := by
      rw [arcComponentsIn_eq_image_pathComponentIn]
      rintro _ ⟨y, hyZT, rfl⟩
      have hex_z : ∃ z ∈ Z, pathComponentIn (Z ∪ T) y = pathComponentIn (Z ∪ T) z := by
        rcases hyZT with hyZ | hyT
        · exact ⟨y, hyZ, rfl⟩
        · have hj_ay : JoinedIn (Z ∪ T) a y :=
            (hT_pc.joinedIn a ⟨0, he0⟩ y hyT).mono subset_union_right
          exact ⟨a, haZ, pathComponentIn_congr hj_ay⟩
      obtain ⟨z, hzZ, hzy⟩ := hex_z
      rw [hzy, ← hg_eq z hzZ]
      by_cases hzb : pathComponentIn Z z = C_b
      · rw [hzb, ← hg_ab]
        exact ⟨C_a, ⟨hCa_mem, hCa_ne_Cb⟩, rfl⟩
      · exact ⟨pathComponentIn Z z, ⟨pathComponentIn_mem_arcComponentsIn hzZ, hzb⟩, rfl⟩
    have hfin_diff : (arcComponentsIn Z \ {C_b}).Finite := hfin.sdiff
    have h1 : (arcComponentsIn (Z ∪ T)).ncard ≤ (g '' (arcComponentsIn Z \ {C_b})).ncard :=
      Set.ncard_le_ncard hsub_img (hfin_diff.image g)
    have h2 : (g '' (arcComponentsIn Z \ {C_b})).ncard ≤ (arcComponentsIn Z \ {C_b}).ncard :=
      Set.ncard_image_le hfin_diff
    have h3 : (arcComponentsIn Z \ {C_b}).ncard < (arcComponentsIn Z).ncard :=
      Set.ncard_lt_ncard ⟨sdiff_subset, fun h => (h hCb_mem).2 rfl⟩ hfin
    omega
  exact ⟨T, a, b, hT_line, hTZ_eq, hT_solid, hZT_flat, hncard_lt⟩

end GraphMinor.GM07
