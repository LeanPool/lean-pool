/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.MoveCuff
import LeanPool.GraphMinor.Surface.OpenDisc

/-!
# Graph Minors VII, (11.10) Boundary-Surface Case (`bd S ≠ ∅`): Interior Merging and Collar Charts

This file develops the first half of the boundary-surface case of Graph Minors VII, (11.10)
(page 253, "If $\operatorname{bd}(\Sigma) \ne \emptyset$, similar slightly more complicated
arguments yield the result, and we omit the details"):
1. In a connected surface `S` with `bd S ≠ ∅`, `¬ IsSphere S`, and for any open arc-connected
   `Y ⊆ S` in which every `O`-arc bounds a closed disc, `Y \ bd S` is open, nonempty, and
   preconnected, every `O`-arc `F ⊆ Y \ bd S` bounds a closed disc `Δ ⊆ Y \ bd S`, and any compact
   `K ⊆ Y \ bd S` is contained in `discInt D` for a closed disc `D ⊆ Y \ bd S`
   (`exists_disc_compact_interior`).
2. If some cuff `C ∈ cuffs S` satisfies `C ⊆ Y`, then `C` bounds a closed disc `Δ = univ`, so
   `IsPlanar Z` (`isPlanar_of_cuff_subset`).
3. Interval merging (`mergeOne`, `mergeList`) and the explicit homeomorphisms `stretchTo` and
   `psiShift` (`Ψ(z) = ⟨z.re - capH52 z.im, z.im⟩`) for boundary collar charts when no cuff of `S`
   is contained in `Y`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric Filter OnePoint GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Basic Boundary and Collar Facts -/

/-- A surface `S` with `bd S ≠ ∅` is not a 2-sphere. -/
theorem not_isSphere_of_bd_ne_empty (hbd : bd S ≠ ∅) : ¬ IsSphere S := by
  rintro ⟨e⟩
  refine hbd (eq_empty_iff_forall_notMem.mpr fun x hx => hx ?_)
  obtain ⟨q, hq⟩ : ∃ q : OnePoint EuclideanPlane, q ≠ e x := by
    by_cases hp : e x = ∞
    · exact ⟨sph 0, hp ▸ sph_ne_infty 0⟩
    · exact ⟨∞, Ne.symm hp⟩
  obtain ⟨H, hH⟩ := exists_homeomorph_onePoint q
  rcases eq_infty_or_sph (H (e x)) with h | ⟨z, hz⟩
  · exact absurd (H.injective (h.trans hH.symm)) (Ne.symm hq)
  · have hemb : IsOpenEmbedding (fun w : ℂ => e.symm (H.symm (sph w))) :=
      e.symm.isOpenEmbedding.comp (H.symm.isOpenEmbedding.comp isOpenEmbedding_sph)
    have hxz : e.symm (H.symm (sph z)) = x := by
      rw [← hz, H.symm_apply_apply, e.symm_apply_apply]
    rw [← hxz]
    exact isInteriorPoint_of_isOpenEmbedding hemb
      ⟨ball z 1, isOpen_ball, mem_ball_self one_pos, exists_homeomorph_ball z one_pos⟩

/-- Every cuff `C ∈ cuffs S` is closed in `S`, and `bd S \ C` is closed in `S`. -/
theorem isClosed_bd_diff_cuff (hS : IsSurface S) {C : Set S} (hC : IsCuff C) :
    IsClosed (bd S \ C) := by
  have hfin := (cuff_statement.{u} S hS).2.1
  have hcov : bd S \ C = ⋃ C' ∈ {C' ∈ cuffs S | C' ≠ C}, C' := by
    ext x
    simp only [Set.mem_sdiff, mem_iUnion, exists_prop, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hxC⟩
      refine ⟨connectedComponentIn (bd S) x, ⟨⟨x, hx, rfl⟩, fun h => hxC ?_⟩,
        mem_connectedComponentIn hx⟩
      rw [← h]
      exact mem_connectedComponentIn hx
    · rintro ⟨C', ⟨⟨y, hy, rfl⟩, hne⟩, hxC'⟩
      refine ⟨connectedComponentIn_subset (bd S) y hxC', fun hxC => hne ?_⟩
      obtain ⟨z, hz, rfl⟩ := hC
      have h1 := connectedComponentIn_eq hxC'
      have h2 := connectedComponentIn_eq hxC
      exact h1.trans h2.symm
  rw [hcov]
  have hfin' : {C' ∈ cuffs S | C' ≠ C}.Finite := hfin.subset fun _ hC' => hC'.1
  refine hfin'.isClosed_biUnion fun C' hC' => ?_
  have : T2Space S := hS.2.1
  exact ((cuff_statement.{u} S hS).2.2 C' hC'.1).isCompact.isClosed

/-- For a cuff `C`, there is a collar `b : Circle × 𝕀 → S` inside `U` that misses all other cuffs,
so `b (w, t) ∈ bd S ↔ t = 0`. -/
theorem exists_isolated_collar (hS : IsSurface S) {C U : Set S} (hC : IsCuff C)
    (φ : Circle ≃ₜ C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ b : Circle × 𝕀 → S, Continuous b ∧ Function.Injective b ∧ range b ⊆ U ∧
      (∀ w, b (w, 0) = (φ w).1) ∧ IsOpen (range b \ b '' {x | x.2 = 1}) ∧
      (∀ w t, b (w, t) ∈ bd S ↔ t = 0) := by
  have : T2Space S := hS.2.1
  have hU' : IsOpen (U \ (bd S \ C)) := hU.sdiff (isClosed_bd_diff_cuff hS hC)
  have hCU' : C ⊆ U \ (bd S \ C) := fun x hx => ⟨hCU hx, fun h => h.2 hx⟩
  obtain ⟨b, hbc, hbi, hbU', hb0, hopen⟩ := exists_collar hS hC φ hU' hCU'
  have hCb : C ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  refine ⟨b, hbc, hbi, hbU'.trans sdiff_subset, hb0, hopen, fun w t => ?_⟩
  constructor
  · intro hbd
    have hmemU' : b (w, t) ∈ U \ (bd S \ C) := hbU' (mem_range_self _)
    have hmemC : b (w, t) ∈ C := by
      by_contra hnotC
      exact hmemU'.2 ⟨hbd, hnotC⟩
    let w' : Circle := φ.symm ⟨b (w, t), hmemC⟩
    have heq : b (w, t) = b (w', 0) := by
      rw [hb0 w']
      exact (congrArg Subtype.val (φ.apply_symm_apply ⟨b (w, t), hmemC⟩)).symm
    exact (Prod.ext_iff.mp (hbi heq)).2
  · rintro rfl
    rw [hb0]
    exact hCb (φ w).2

/-- The open collar `b '' {x : Circle × 𝕀 | x.2 < 1}` is open in `S`, and `b` maps open subsets of
`{x : Circle × 𝕀 | x.2 < 1}` to open subsets of `S`. -/
theorem isOpen_image_of_collar [T2Space S] {b : Circle × 𝕀 → S}
    (hbc : Continuous b) (hbi : Function.Injective b)
    (hopen : IsOpen (range b \ b '' {x | x.2 = 1}))
    {V : Set (Circle × 𝕀)} (hV : IsOpen V) (hV1 : ∀ x ∈ V, x.2 < 1) :
    IsOpen (b '' V) := by
  have hemb : IsClosedEmbedding b := hbc.isClosedEmbedding hbi
  have hsub : b '' V ⊆ range b \ b '' {x | x.2 = 1} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_range_self x, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxy := hbi he
    subst hxy
    exact (hV1 y hx).ne hy
  obtain ⟨U, hU, hUeq⟩ := hemb.isInducing.isOpen_iff.mp hV
  have h1 : b '' V = (range b \ b '' {x | x.2 = 1}) ∩ U := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxU : x ∈ b ⁻¹' U := by rwa [hUeq]
      exact ⟨hsub ⟨x, hx, rfl⟩, hxU⟩
    · rintro ⟨⟨⟨x, rfl⟩, _⟩, hxU⟩
      have hxV : x ∈ V := by rwa [← hUeq]
      exact ⟨x, hxV, rfl⟩
  rw [h1]
  exact hopen.inter hU

/-! ## 2. Case 1: A Cuff Contained in `Y` -/

/-- If some cuff `C ∈ cuffs S` is contained in `Y`, then `Y = univ` is a closed disc and `IsPlanar
Z`. -/
theorem isPlanar_of_cuff_subset (hS : IsSurface S) [ConnectedSpace S] {Z Y : Set S}
    (_hZY : Z ⊆ Y)
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {C : Set S} (hC : IsCuff C) (hCY : C ⊆ Y) :
    IsPlanar Z := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hCO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
  obtain ⟨Δ, hΔY, hΔ, hΔb⟩ := H C hCY hCO
  obtain ⟨φ⟩ := id hCO
  obtain ⟨b, hbc, hbi, _, hb0, hopen, hbd_iff⟩ :=
    exists_isolated_collar hS hC φ isOpen_univ (subset_univ _)
  let W : Set S := range b \ b '' {x | x.2 = 1}
  have hWC_eq : W \ C = b '' (univ ×ˢ Ioo (0 : 𝕀) 1) := by
    ext y
    constructor
    · rintro ⟨⟨⟨⟨w, t⟩, rfl⟩, hy1⟩, hyC⟩
      have ht1 : t ≠ 1 := fun h => hy1 ⟨(w, t), h, rfl⟩
      have ht0 : t ≠ 0 := by
        intro h
        apply hyC
        rw [h, hb0]
        exact (φ w).2
      refine ⟨(w, t), ⟨trivial, lt_of_le_of_ne t.2.1 ht0.symm, lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
    · rintro ⟨⟨w, t⟩, ⟨_, ht0, ht1⟩, rfl⟩
      refine ⟨⟨⟨(w, t), rfl⟩, ?_⟩, ?_⟩
      · rintro ⟨⟨w', t'⟩, ht'1, he⟩
        have h := (Prod.ext_iff.mp (hbi he)).2
        exact ht1.ne (h.symm.trans ht'1)
      · intro hyC
        have hCb : C ⊆ bd S := by
          obtain ⟨x, hx, rfl⟩ := hC
          exact connectedComponentIn_subset _ _
        have ht0' := (hbd_iff w t).mp (hCb hyC)
        exact ht0.ne' ht0'
  have hWC_pre : IsPreconnected (W \ C) := by
    rw [hWC_eq]
    have h1 : IsPreconnected (univ : Set Circle) := isPreconnected_univ
    have h2 : IsPreconnected (Ioo (0 : 𝕀) 1) := ordConnected_Ioo.isPreconnected
    exact (h1.prod h2).image b hbc.continuousOn
  have hWC_disj : Disjoint (W \ C) (discBd Δ) := by
    rw [hΔb]
    exact disjoint_sdiff_left
  have hb10_W : b (1, 0) ∈ W := by
    refine ⟨⟨(1, 0), rfl⟩, ?_⟩
    rintro ⟨⟨w, t⟩, ht1, he⟩
    have h := (Prod.ext_iff.mp (hbi he)).2
    exact zero_ne_one (h.symm.trans ht1)
  have hb10_cl : b (1, 0) ∈ closure (discInt Δ) := by
    refine hΔ.subset_closure_discInt (discBd_subset Δ ?_)
    rw [hΔb, hb0]
    exact (φ 1).2
  obtain ⟨z, hzW, hzInt⟩ := mem_closure_iff.mp hb10_cl W hopen hb10_W
  have hz_notC : z ∉ C := by
    rw [← hΔb]
    exact hzInt.2
  have hWC_sub : W \ C ⊆ discInt Δ := by
    rcases hΔ.side hS.2.2 hWC_pre hWC_disj with hsub | hdisj
    · exact hsub
    · exact False.elim (Set.disjoint_left.mp hdisj ⟨hzW, hz_notC⟩ hzInt.1)
  have hW_sub : W ⊆ Δ := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact discBd_subset Δ (hΔb ▸ hxC)
    · exact discInt_subset Δ (hWC_sub ⟨hx, hxC⟩)
  have hΔ_eq : Δ = discInt Δ ∪ W := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxb : x ∈ discBd Δ
      · right
        rw [hΔb] at hxb
        let w : Circle := φ.symm ⟨x, hxb⟩
        have hbw : b (w, 0) = x := by
          rw [hb0]
          exact congrArg Subtype.val (φ.apply_symm_apply ⟨x, hxb⟩)
        rw [← hbw]
        refine ⟨⟨(w, 0), rfl⟩, ?_⟩
        rintro ⟨⟨w', t'⟩, ht'1, he⟩
        have h := (Prod.ext_iff.mp (hbi he)).2
        exact zero_ne_one (h.symm.trans ht'1)
      · exact Or.inl ⟨hx, hxb⟩
    · exact union_subset (discInt_subset Δ) hW_sub
  have hΔ_open : IsOpen Δ := by
    rw [hΔ_eq]
    exact (hΔ.isOpen_discInt hS.2.2).union hopen
  have hΔ_univ : Δ = univ := IsClopen.eq_univ ⟨hΔ.isClosed, hΔ_open⟩ ⟨b (1, 0), hW_sub hb10_W⟩
  exact ⟨Δ, hΔ, hΔ_univ.symm ▸ subset_univ Z⟩

/-! ## 3. Compact Subsets of `Y \ bd S` lie in Closed Discs in `Y \ bd S` -/

/-- Every `O`-arc `F ⊆ Y \ bd S` bounds a closed disc `Δ ⊆ Y \ bd S`. -/
theorem disc_subset_diff_bd_of_oArc (hS : IsSurface S) {Y : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {F : Set S} (hF : F ⊆ Y \ bd S) (hFO : IsOArc F) :
    ∃ Δ : Set S, Δ ⊆ Y \ bd S ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
  have : T2Space S := hS.2.1
  obtain ⟨Δ, hΔY, hΔ, hΔb⟩ := H F (hF.trans sdiff_subset) hFO
  refine ⟨Δ, fun x hx => ⟨hΔY hx, ?_⟩, hΔ, hΔb⟩
  by_cases hxb : x ∈ discBd Δ
  · rw [hΔb] at hxb
    exact (hF hxb).2
  · exact fun hbd => hbd (isInteriorPoint_of_mem_discInt hS.2.2 hΔ ⟨hx, hxb⟩)

/-- If `Y ⊆ S` is open and preconnected, then `Y \ bd S` is preconnected. -/
theorem isPreconnected_diff_bd (hS : IsSurface S) {Y : Set S} (hYo : IsOpen Y)
    (hYc : IsPreconnected Y) : IsPreconnected (Y \ bd S) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  intro U V hU hV hcov hU_ne hV_ne
  have hbd_cl : IsClosed (bd S) := (cuff_statement.{u} S hS).1
  have hY'o : IsOpen (Y \ bd S) := hYo.sdiff hbd_cl
  let U₀ : Set S := (Y \ bd S) ∩ U
  let V₀ : Set S := (Y \ bd S) ∩ V
  have hU₀ : IsOpen U₀ := hY'o.inter hU
  have hV₀ : IsOpen V₀ := hY'o.inter hV
  by_contra hdisj_UV
  have hdisj : Disjoint U₀ V₀ := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    exact hdisj_UV ⟨x, hxU.1, hxU.2, hxV.2⟩
  -- Every open neighborhood `W ⊆ Y` of `y ∈ Y` contains an open neighborhood `N ⊆ W` of `y` such
  -- that `N \ bd S` is nonempty and preconnected, hence contained in `U₀` or `V₀`.
  have hloc : ∀ y ∈ Y, ∀ W : Set S, IsOpen W → y ∈ W → W ⊆ Y →
      ∃ N : Set S, IsOpen N ∧ y ∈ N ∧ N ⊆ W ∧
        (N \ bd S).Nonempty ∧ IsPreconnected (N \ bd S) := by
    intro y _ W hWo hyW hWY
    by_cases hyb : y ∈ bd S
    · let C := connectedComponentIn (bd S) y
      have hC : IsCuff C := ⟨y, hyb, rfl⟩
      have hCO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
      obtain ⟨φ⟩ := id hCO
      obtain ⟨b, hbc, hbi, _, hb0, hopen, hbd_iff⟩ :=
        exists_isolated_collar hS hC φ isOpen_univ (subset_univ _)
      have hyC : y ∈ C := mem_connectedComponentIn hyb
      let w₀ : Circle := φ.symm ⟨y, hyC⟩
      have hbw₀ : b (w₀, 0) = y := by
        rw [hb0]
        exact congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyC⟩)
      obtain ⟨θ₀, _, hθ₀⟩ := exists_circle_angle 1 w₀
      rw [one_mul] at hθ₀
      have hpre_open : IsOpen (b ⁻¹' W) := hWo.preimage hbc
      have hw₀_mem : (w₀, (0 : 𝕀)) ∈ b ⁻¹' W := by
        change b (w₀, 0) ∈ W
        rw [hbw₀]
        exact hyW
      obtain ⟨A, B, hAo, hBo, hw₀A, h0B, hAB_sub⟩ :=
        isOpen_prod_iff.mp hpre_open w₀ 0 hw₀_mem
      have hθ₀_pre : θ₀ ∈ Circle.exp ⁻¹' A := by
        change Circle.exp θ₀ ∈ A
        rwa [← hθ₀]
      obtain ⟨δ, hδ, hδ_sub⟩ :=
        Metric.isOpen_iff.mp (hAo.preimage Circle.exp.continuous) θ₀ hθ₀_pre
      obtain ⟨ε₀, hε₀, hε₀_sub⟩ := Metric.isOpen_iff.mp hBo 0 h0B
      let ε : 𝕀 := ⟨min (ε₀ / 2) (1 / 2), le_min (by positivity) (by norm_num),
        (min_le_right _ _).trans (by norm_num)⟩
      have hε_pos : (0 : 𝕀) < ε := by
        change (0 : ℝ) < min (ε₀ / 2) (1 / 2)
        exact lt_min (by positivity) (by norm_num)
      have hε_lt1 : ε < (1 : 𝕀) := by
        change min (ε₀ / 2) (1 / 2) < 1
        exact (min_le_right _ _).trans_lt (by norm_num)
      let Vw : Set Circle := Circle.exp '' Ioo (θ₀ - δ) (θ₀ + δ)
      have hVw_open : IsOpen Vw := isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
      have hw₀_Vw : w₀ ∈ Vw := ⟨θ₀, ⟨by linarith, by linarith⟩, hθ₀.symm⟩
      have hVw_sub : Vw ⊆ A := by
        rintro _ ⟨θ, hθ, rfl⟩
        refine hδ_sub ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      let Vt : Set 𝕀 := Iio ε
      have hVt_open : IsOpen Vt := isOpen_Iio
      have hVt_sub : Vt ⊆ B := by
        intro t ht
        refine hε₀_sub ?_
        rw [Metric.mem_ball, Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero,
          abs_of_nonneg t.2.1]
        have ht' : t.1 < min (ε₀ / 2) (1 / 2) := ht
        linarith [min_le_left (ε₀ / 2) (1 / 2)]
      let R : Set (Circle × 𝕀) := Vw ×ˢ Vt
      have hR_open : IsOpen R := hVw_open.prod hVt_open
      have hR_lt1 : ∀ x ∈ R, x.2 < 1 := fun x hx => hx.2.trans hε_lt1
      have hN_open : IsOpen (b '' R) := isOpen_image_of_collar hbc hbi hopen hR_open hR_lt1
      have hy_N : y ∈ b '' R := ⟨(w₀, 0), ⟨hw₀_Vw, hε_pos⟩, hbw₀⟩
      have hN_sub : b '' R ⊆ W := by
        rintro _ ⟨x, hx, rfl⟩
        exact hAB_sub ⟨hVw_sub hx.1, hVt_sub hx.2⟩
      have hN_diff : (b '' R) \ bd S = b '' (Vw ×ˢ Ioo (0 : 𝕀) ε) := by
        ext z
        constructor
        · rintro ⟨⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩, hzb⟩
          have ht0 : t ≠ 0 := fun h => hzb ((hbd_iff w t).mpr h)
          exact ⟨(w, t), ⟨hw, lt_of_le_of_ne t.2.1 ht0.symm, ht⟩, rfl⟩
        · rintro ⟨⟨w, t⟩, ⟨hw, ht0, htε⟩, rfl⟩
          exact ⟨⟨(w, t), ⟨hw, htε⟩, rfl⟩, fun hzb => ht0.ne' ((hbd_iff w t).mp hzb)⟩
      let t_mid : 𝕀 := ⟨ε.1 / 2, by positivity, by linarith [ε.2.2]⟩
      have ht_mid : t_mid ∈ Ioo (0 : 𝕀) ε := by
        change (0 : ℝ) < ε.1 / 2 ∧ ε.1 / 2 < ε.1
        have hpos : (0 : ℝ) < ε.1 := hε_pos
        exact ⟨by positivity, by linarith⟩
      refine ⟨b '' R, hN_open, hy_N, hN_sub, ?_, ?_⟩
      · rw [hN_diff]
        exact ⟨b (w₀, t_mid), (w₀, t_mid), ⟨hw₀_Vw, ht_mid⟩, rfl⟩
      · rw [hN_diff]
        have hVw_pre : IsPreconnected Vw :=
          isPreconnected_Ioo.image Circle.exp Circle.exp.continuous.continuousOn
        have hIoo_pre : IsPreconnected (Ioo (0 : 𝕀) ε) := ordConnected_Ioo.isPreconnected
        exact (hVw_pre.prod hIoo_pre).image b hbc.continuousOn
    · have hy' : IsInteriorPoint y := by
        by_contra hni
        exact hyb hni
      have hW'o : IsOpen (W \ bd S) := hWo.sdiff hbd_cl
      obtain ⟨U_c, h_c, g_c, c, hUW, hg0⟩ :=
        hy'.exists_ballChart hW'o ⟨hyW, hyb⟩ (R := 3) (by norm_num)
      have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
      let N := g_c '' ball 0 1
      have hN_open : IsOpen N := c.isOpen_image isOpen_ball hb
      have hy_N : y ∈ N := ⟨0, by simp, hg0⟩
      have hN_sub : N ⊆ W \ bd S :=
        (image_subset_iff.mpr fun z hz => c.gm (hb hz)).trans hUW
      have hN_diff : N \ bd S = N :=
        sdiff_eq_left.mpr (Set.disjoint_left.mpr fun z hz => (hN_sub hz).2)
      refine ⟨N, hN_open, hy_N, hN_sub.trans sdiff_subset, ?_, ?_⟩
      · rw [hN_diff]
        exact ⟨y, hy_N⟩
      · rw [hN_diff]
        exact (convex_ball (0 : ℂ) 1).isPreconnected.image g_c (c.gc.mono hb)
  let U₁ : Set S := ⋃₀ {N : Set S | IsOpen N ∧ N ⊆ Y ∧ N \ bd S ⊆ U₀}
  let V₁ : Set S := ⋃₀ {N : Set S | IsOpen N ∧ N ⊆ Y ∧ N \ bd S ⊆ V₀}
  have hU₁ : IsOpen U₁ := isOpen_sUnion fun _ h => h.1
  have hV₁ : IsOpen V₁ := isOpen_sUnion fun _ h => h.1
  have hY_cov : Y ⊆ U₁ ∪ V₁ := by
    intro y hy
    obtain ⟨N, hNo, hyN, hNY, _, hN_pre⟩ := hloc y hy Y hYo hy Subset.rfl
    have hz_cov : N \ bd S ⊆ U₀ ∪ V₀ := by
      intro x hx
      rcases hcov ⟨hNY hx.1, hx.2⟩ with hxU | hxV
      · exact Or.inl ⟨⟨hNY hx.1, hx.2⟩, hxU⟩
      · exact Or.inr ⟨⟨hNY hx.1, hx.2⟩, hxV⟩
    rcases hN_pre.subset_or_subset hU₀ hV₀ hdisj hz_cov with hsubU | hsubV
    · exact Or.inl (mem_sUnion.mpr ⟨N, ⟨hNo, hNY, hsubU⟩, hyN⟩)
    · exact Or.inr (mem_sUnion.mpr ⟨N, ⟨hNo, hNY, hsubV⟩, hyN⟩)
  obtain ⟨u₀, hu₀Y, hu₀U⟩ := hU_ne
  obtain ⟨v₀, hv₀Y, hv₀V⟩ := hV_ne
  have hu₀_U₁ : u₀ ∈ Y ∩ U₁ := by
    refine ⟨hu₀Y.1, mem_sUnion.mpr ⟨U₀, ⟨hU₀, inter_subset_left.trans sdiff_subset, ?_⟩,
      ⟨hu₀Y, hu₀U⟩⟩⟩
    exact sdiff_subset
  have hv₀_V₁ : v₀ ∈ Y ∩ V₁ := by
    refine ⟨hv₀Y.1, mem_sUnion.mpr ⟨V₀, ⟨hV₀, inter_subset_left.trans sdiff_subset, ?_⟩,
      ⟨hv₀Y, hv₀V⟩⟩⟩
    exact sdiff_subset
  obtain ⟨w, hwY, ⟨N₁, hN₁, hwN₁⟩, ⟨N₂, hN₂, hwN₂⟩⟩ :=
    hYc U₁ V₁ hU₁ hV₁ hY_cov ⟨u₀, hu₀_U₁⟩ ⟨v₀, hv₀_V₁⟩
  obtain ⟨N_w, _, _, hNw_sub, ⟨x₀, hx₀N, hx₀b⟩, _⟩ :=
    hloc w hwY (N₁ ∩ N₂) (hN₁.1.inter hN₂.1) ⟨hwN₁, hwN₂⟩ (inter_subset_left.trans hN₁.2.1)
  have hx₀12 := hNw_sub hx₀N
  exact Set.disjoint_left.mp hdisj (hN₁.2.2 ⟨hx₀12.1, hx₀b⟩) (hN₂.2.2 ⟨hx₀12.2, hx₀b⟩)

/-- Auxiliary disc-chart merging lemma in an open interior subset `Y' ⊆ S \ bd S` when `¬ IsSphere
S`. -/
theorem exists_disc_merge_interior_aux (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S}
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {D : Set S} (hDY : D ⊆ Y') (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y')
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) {r ρ : ℝ} (hr2 : 2 < r) (hr3 : r < 3) (hρ : 0 < ρ)
    (hfree : ∀ z ∈ ball (r : ℂ) ρ, g z ∉ discBd D) :
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' closedBall 0 2 ⊆ D' := by
  exact exists_disc_merge_in_chart_aux hS H' (fun h => hns h.1)
    hDY hD c hUY hz hr2 hr3 hρ hfree

/-- Merging a closed disc `D ⊆ Y'` with an overlapping `BallChart 3 U h g` in `Y'`. -/
theorem exists_disc_merge_interior (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S}
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {D : Set S} (hDY : D ⊆ Y') (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y')
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) :
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' closedBall 0 2 ⊆ D' := by
  exact exists_disc_merge_in_chart hS H' (fun h => hns h.1) hDY hD c hUY hz

/-- If a closed disc in `Y'` overlaps the unit ball of a chart in `Y'`, a larger closed disc in `Y'`
contains that unit ball in its inside. -/
theorem exists_disc_of_overlap_interior (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S} (hint : ∀ x ∈ Y', IsInteriorPoint x)
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {D : Set S} (hDY : D ⊆ Y') (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart 3 U h g) (hUY : U ⊆ Y')
    (hz : (discInt D ∩ g '' ball 0 1).Nonempty) :
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ g '' ball 0 1 ⊆ discInt D' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨D', h1, h2, h3, h4⟩ := exists_disc_merge_interior hS hns H' hDY hD c hUY hz
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  have hsub2 : g '' ball 0 1 ⊆ D' :=
    (image_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by norm_num)))).trans h4
  refine ⟨D', h1, h2, h3,
    subset_discInt_of_isOpen (fun x hx => hint x (h1 (hsub2 hx)))
      (c.isOpen_image isOpen_ball hb) hsub2⟩

/-- Every point of `Y'` lies in the inside of a closed disc of `Y'` that contains a given closed
disc of `Y'`. -/
theorem exists_disc_mem_interior (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S} (hint : ∀ x ∈ Y', IsInteriorPoint x)
    (hYo : IsOpen Y') (hYc : IsPreconnected Y')
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {D : Set S} (hDY : D ⊆ Y') (hD : IsClosedDisc D) {y : S} (hy : y ∈ Y') :
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ y ∈ discInt D' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  let A : Set S := {y | ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ y ∈ discInt D'}
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨D', h1, h2, h3, h4⟩
    filter_upwards [(h2.isOpen_discInt hman).mem_nhds h4] with z hz
    exact ⟨D', h1, h2, h3, hz⟩
  have hBo : IsOpen (Y' \ A) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨hxY, hxA⟩
    obtain ⟨U, h, g, c, hUY, hg0⟩ := (hint x hxY).exists_ballChart hYo hxY (R := 3) (by norm_num)
    have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
    have hV := c.isOpen_image isOpen_ball hb
    have hx : x ∈ g '' ball 0 1 := ⟨0, by simp, hg0⟩
    filter_upwards [hV.mem_nhds hx] with z hz
    obtain ⟨w, hw, rfl⟩ := id hz
    refine ⟨hUY (c.gm (hb hw)), ?_⟩
    rintro ⟨D', h1, h2, h3, h4⟩
    obtain ⟨E, h5, h6, h7, h8⟩ :=
      exists_disc_of_overlap_interior hS hns hint H' h1 h2 c hUY ⟨_, h4, hz⟩
    exact hxA ⟨E, h5, h6, h3.trans h7, h8 hx⟩
  by_contra hcon
  obtain ⟨z, hz⟩ := hD.nonempty_discInt
  obtain ⟨w, -, hw1, hw2⟩ := hYc A (Y' \ A) hAo hBo
    (fun x hx => by
      by_cases hxA : x ∈ A
      · exact .inl hxA
      · exact .inr ⟨hx, hxA⟩)
    ⟨z, hDY (discInt_subset D hz), D, hDY, hD, Subset.rfl, hz⟩ ⟨y, hy, hy, hcon⟩
  exact hw2.2 hw1

/-- Around every point of `Y'` there is a neighbourhood that the inside of a closed disc swallows,
starting from any closed disc of `Y'`. -/
theorem exists_disc_nhds_interior (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S} (hint : ∀ x ∈ Y', IsInteriorPoint x)
    (hYo : IsOpen Y') (hYc : IsPreconnected Y')
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {y : S} (hy : y ∈ Y') : ∃ V ∈ 𝓝 y, ∀ D : Set S, D ⊆ Y' → IsClosedDisc D →
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ V ⊆ discInt D' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨U, h, g, c, hUY, hg0⟩ := (hint y hy).exists_ballChart hYo hy (R := 3) (by norm_num)
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  have hy' : y ∈ g '' ball 0 1 := ⟨0, by simp, hg0⟩
  refine ⟨g '' ball 0 1, (c.isOpen_image isOpen_ball hb).mem_nhds hy', fun D hDY hD => ?_⟩
  obtain ⟨D₁, h1, h2, h3, h4⟩ := exists_disc_mem_interior hS hns hint hYo hYc H' hDY hD hy
  obtain ⟨D₂, h5, h6, h7, h8⟩ :=
    exists_disc_of_overlap_interior hS hns hint H' h1 h2 c hUY ⟨y, h4, hy'⟩
  exact ⟨D₂, h5, h6, h3.trans h7, h8⟩

/-- The inside of a closed disc of `Y'` swallows any compact subset of `Y'` and any given closed
disc of `Y'`. -/
theorem exists_disc_compact_interior (hS : IsSurface S) [ConnectedSpace S]
    (hns : ¬ IsSphere S) {Y' : Set S} (hint : ∀ x ∈ Y', IsInteriorPoint x)
    (hYo : IsOpen Y') (hYc : IsPreconnected Y')
    (H' : ∀ F : Set S, F ⊆ Y' → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y' ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {K : Set S} (hK : IsCompact K) (hKY : K ⊆ Y') {D : Set S} (hDY : D ⊆ Y')
    (hD : IsClosedDisc D) :
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ K ⊆ discInt D' := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  refine hK.induction_on (p := fun K => ∀ D : Set S, D ⊆ Y' → IsClosedDisc D →
    ∃ D' : Set S, D' ⊆ Y' ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ K ⊆ discInt D') ?_ ?_ ?_ ?_ D hDY hD
  · exact fun D hDY hD => ⟨D, hDY, hD, Subset.rfl, empty_subset _⟩
  · intro s t hst hp D hDY hD
    obtain ⟨D', h1, h2, h3, h4⟩ := hp D hDY hD
    exact ⟨D', h1, h2, h3, hst.trans h4⟩
  · intro s t hs ht D hDY hD
    obtain ⟨D₁, h1, h2, h3, h4⟩ := hs D hDY hD
    obtain ⟨D₂, h5, h6, h7, h8⟩ := ht D₁ h1 h2
    exact ⟨D₂, h5, h6, h3.trans h7,
      union_subset (h4.trans (discInt_mono hman h2 h7)) h8⟩
  · intro x hx
    obtain ⟨V, hV, hp⟩ := exists_disc_nhds_interior hS hns hint hYo hYc H' (hKY hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hp⟩

/-- Every nonempty open `Y ⊆ S` has a closed disc `D₀ ⊆ Y \ bd S`. -/
theorem exists_initial_disc_interior (hS : IsSurface S) {Y : Set S} (hYo : IsOpen Y)
    (hYne : Y.Nonempty) :
    ∃ D₀ : Set S, D₀ ⊆ Y \ bd S ∧ IsClosedDisc D₀ := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hbd_cl : IsClosed (bd S) := (cuff_statement.{u} S hS).1
  have hY'o : IsOpen (Y \ bd S) := hYo.sdiff hbd_cl
  -- First find a point `x₀ ∈ Y \ bd S`.
  have hY'_ne : (Y \ bd S).Nonempty := by
    obtain ⟨y, hy⟩ := hYne
    by_cases hyb : y ∈ bd S
    · let C := connectedComponentIn (bd S) y
      have hC : IsCuff C := ⟨y, hyb, rfl⟩
      have hCO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
      obtain ⟨φ⟩ := id hCO
      obtain ⟨b, hbc, _, _, hb0, _, hbd_iff⟩ :=
        exists_isolated_collar hS hC φ isOpen_univ (subset_univ _)
      have hyC : y ∈ C := mem_connectedComponentIn hyb
      let w₀ : Circle := φ.symm ⟨y, hyC⟩
      have hbw₀ : b (w₀, 0) = y := by
        rw [hb0]
        exact congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyC⟩)
      have hw₀_mem : (w₀, (0 : 𝕀)) ∈ b ⁻¹' Y := by
        change b (w₀, 0) ∈ Y
        rw [hbw₀]
        exact hy
      obtain ⟨A, B, _, hBo, hw₀A, h0B, hAB_sub⟩ :=
        isOpen_prod_iff.mp (hYo.preimage hbc) w₀ 0 hw₀_mem
      obtain ⟨ε₀, hε₀, hε₀_sub⟩ := Metric.isOpen_iff.mp hBo 0 h0B
      let t₀ : 𝕀 := ⟨min (ε₀ / 2) (1 / 2), le_min (by positivity) (by norm_num),
        (min_le_right _ _).trans (by norm_num)⟩
      have ht₀_pos : (0 : ℝ) < t₀.1 := lt_min (by positivity) (by norm_num)
      have ht₀_B : t₀ ∈ B := by
        refine hε₀_sub ?_
        rw [Metric.mem_ball, Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero,
          abs_of_nonneg t₀.2.1]
        linarith [min_le_left (ε₀ / 2) (1 / 2)]
      refine ⟨b (w₀, t₀), hAB_sub ⟨hw₀A, ht₀_B⟩, fun hzb => ?_⟩
      have ht0 := (hbd_iff w₀ t₀).mp hzb
      exact ht₀_pos.ne' (congrArg Subtype.val ht0)
    · exact ⟨y, hy, hyb⟩
  obtain ⟨x₀, hx₀Y, hx₀b⟩ := hY'_ne
  have hx₀' : IsInteriorPoint x₀ := by
    by_contra hni
    exact hx₀b hni
  obtain ⟨U, h, g, c, hUY, _⟩ := hx₀'.exists_ballChart hY'o ⟨hx₀Y, hx₀b⟩ (R := 3) (by norm_num)
  have hb13 : closedBall (0 : ℂ) 1 ⊆ ball 0 3 := closedBall_subset_ball (by norm_num)
  refine ⟨g '' closedBall 0 1, ?_, ?_⟩
  · exact (image_subset_iff.mpr fun z hz => c.gm (hb13 hz)).trans hUY
  · exact (c.image_disc isClosedDisc_closedBall.1 hb13).1

/-! ## 4. Interval Merging and Explicit Boundary Chart Homeomorphisms -/

/-- Insert an interval `(a, b)` into a list of pairwise disjoint intervals, merging any that
overlap `[a, b]`. -/
noncomputable def mergeOne (a b : ℝ) : List (ℝ × ℝ) → (ℝ × ℝ) × List (ℝ × ℝ)
  | [] => ((a, b), [])
  | p :: rest =>
    let q := mergeOne a b rest
    if q.1.2 < p.1 ∨ p.2 < q.1.1 then (q.1, p :: q.2)
    else ((min q.1.1 p.1, max q.1.2 p.2), q.2)

/-- Merge a list of intervals into a list of pairwise disjoint closed intervals. -/
noncomputable def mergeList : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | p :: rest =>
    let q := mergeOne p.1 p.2 (mergeList rest)
    q.1 :: q.2

/-- The union of the open intervals `(p.1, p.2)` in a list `L`. -/
def unionIoo : List (ℝ × ℝ) → Set ℝ
  | [] => ∅
  | p :: rest => Ioo p.1 p.2 ∪ unionIoo rest

/-- The union of the closed intervals `[p.1, p.2]` in a list `L`. -/
def unionIcc : List (ℝ × ℝ) → Set ℝ
  | [] => ∅
  | p :: rest => Icc p.1 p.2 ∪ unionIcc rest

theorem mem_unionIoo {x : ℝ} {L : List (ℝ × ℝ)} :
    x ∈ unionIoo L ↔ ∃ p ∈ L, x ∈ Ioo p.1 p.2 := by
  induction L with
  | nil => simp [unionIoo]
  | cons p rest ih => simp [unionIoo, ih]

theorem mem_unionIcc {x : ℝ} {L : List (ℝ × ℝ)} :
    x ∈ unionIcc L ↔ ∃ p ∈ L, x ∈ Icc p.1 p.2 := by
  induction L with
  | nil => simp [unionIcc]
  | cons p rest ih => simp [unionIcc, ih]

theorem mergeOne_properties (a b : ℝ) (L : List (ℝ × ℝ))
    (hab : a < b) (hL : ∀ p ∈ L, p.1 < p.2)
    (hpw : L.Pairwise (fun p q => p.2 < q.1 ∨ q.2 < p.1)) :
    let q := mergeOne a b L
    q.1.1 ≤ a ∧ b ≤ q.1.2 ∧ q.1.1 < q.1.2 ∧
    (∀ p ∈ q.2, p ∈ L ∧ p.1 < p.2 ∧ (q.1.2 < p.1 ∨ p.2 < q.1.1)) ∧
    q.2.Pairwise (fun p1 p2 => p1.2 < p2.1 ∨ p2.2 < p1.1) ∧
    (Ioo a b ∪ unionIoo L ⊆ Ioo q.1.1 q.1.2 ∪ unionIoo q.2) ∧
    (Icc q.1.1 q.1.2 ∪ unionIcc q.2 ⊆ Icc a b ∪ unionIcc L) ∧
    (∀ c d : ℝ, c ≤ a → b ≤ d → (∀ p ∈ L, c ≤ p.1 ∧ p.2 ≤ d) →
      c ≤ q.1.1 ∧ q.1.2 ≤ d ∧ ∀ p ∈ q.2, c ≤ p.1 ∧ p.2 ≤ d) := by
  induction L with
  | nil =>
    dsimp [mergeOne, unionIoo, unionIcc]
    refine ⟨le_rfl, le_rfl, hab, by simp, List.Pairwise.nil, Subset.rfl, Subset.rfl, ?_⟩
    intro c d hca hbd _
    exact ⟨hca, hbd, by simp⟩
  | cons p rest ih =>
    have hrest : ∀ r ∈ rest, r.1 < r.2 := fun r hr => hL r (List.mem_cons_of_mem p hr)
    have hp_lt : p.1 < p.2 := hL p List.mem_cons_self
    obtain ⟨hp_rest, hpw_rest⟩ := List.pairwise_cons.mp hpw
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7, ih8⟩ := ih hrest hpw_rest
    set q := mergeOne a b rest
    dsimp only [mergeOne]
    change (if q.1.2 < p.1 ∨ p.2 < q.1.1 then (q.1, p :: q.2)
      else ((min q.1.1 p.1, max q.1.2 p.2), q.2)).1.1 ≤ a ∧ _
    split_ifs with hsep
    · refine ⟨ih1, ih2, ih3, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨List.mem_cons_self, hp_lt, hsep⟩
        · obtain ⟨h1, h2, h3⟩ := ih4 r hr'
          exact ⟨List.mem_cons_of_mem p h1, h2, h3⟩
      · refine List.pairwise_cons.mpr ⟨fun r hr => ?_, ih5⟩
        exact hp_rest r (ih4 r hr).1
      · intro x hx
        dsimp only [unionIoo] at hx ⊢
        rcases hx with hxab | hxp | hxrest
        · rcases ih6 (Or.inl hxab) with hq1 | hq2
          · exact Or.inl hq1
          · exact Or.inr (Or.inr hq2)
        · exact Or.inr (Or.inl hxp)
        · rcases ih6 (Or.inr hxrest) with hq1 | hq2
          · exact Or.inl hq1
          · exact Or.inr (Or.inr hq2)
      · intro x hx
        dsimp only [unionIcc] at hx ⊢
        rcases hx with hq1 | hxp | hq2
        · rcases ih7 (Or.inl hq1) with hxab | hxrest
          · exact Or.inl hxab
          · exact Or.inr (Or.inr hxrest)
        · exact Or.inr (Or.inl hxp)
        · rcases ih7 (Or.inr hq2) with hxab | hxrest
          · exact Or.inl hxab
          · exact Or.inr (Or.inr hxrest)
      · intro c d hca hbd hcd
        have hcd_p := hcd p List.mem_cons_self
        obtain ⟨hc1, hd1, hcd_q2⟩ := ih8 c d hca hbd fun r hr =>
          hcd r (List.mem_cons_of_mem p hr)
        refine ⟨hc1, hd1, fun r hr => ?_⟩
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hcd_p
        · exact hcd_q2 r hr'
    · push Not at hsep
      refine ⟨(min_le_left _ _).trans ih1, ih2.trans (le_max_left _ _),
        (min_le_left _ _).trans_lt (ih3.trans_le (le_max_left _ _)), ?_, ih5, ?_, ?_, ?_⟩
      · intro r hr
        obtain ⟨h1, h2, h3⟩ := ih4 r hr
        refine ⟨List.mem_cons_of_mem p h1, h2, ?_⟩
        rcases hp_rest r h1 with hpr | hrp <;> rcases h3 with hqr | hrq
        · exact Or.inl (max_lt hqr hpr)
        · linarith [h2]
        · linarith [h2]
        · exact Or.inr (lt_min hrq hrp)
      · intro x hx
        dsimp only [unionIoo] at hx ⊢
        have hsub_q1 : Ioo q.1.1 q.1.2 ⊆ Ioo (min q.1.1 p.1) (max q.1.2 p.2) :=
          Ioo_subset_Ioo (min_le_left _ _) (le_max_left _ _)
        have hsub_p : Ioo p.1 p.2 ⊆ Ioo (min q.1.1 p.1) (max q.1.2 p.2) :=
          Ioo_subset_Ioo (min_le_right _ _) (le_max_right _ _)
        rcases hx with hxab | hxp | hxrest
        · rcases ih6 (Or.inl hxab) with hq1 | hq2
          · exact Or.inl (hsub_q1 hq1)
          · exact Or.inr hq2
        · exact Or.inl (hsub_p hxp)
        · rcases ih6 (Or.inr hxrest) with hq1 | hq2
          · exact Or.inl (hsub_q1 hq1)
          · exact Or.inr hq2
      · intro x hx
        dsimp only [unionIcc] at hx ⊢
        have hcov : Icc (min q.1.1 p.1) (max q.1.2 p.2) ⊆ Icc q.1.1 q.1.2 ∪ Icc p.1 p.2 := by
          intro y hy
          by_cases hyq : y ∈ Icc q.1.1 q.1.2
          · exact Or.inl hyq
          · right
            rcases le_or_gt q.1.1 y with h1 | h1
            · have hy_gt : q.1.2 < y := not_le.mp fun h2 => hyq ⟨h1, h2⟩
              rcases max_cases q.1.2 p.2 with ⟨hmax, _⟩ | ⟨hmax, _⟩
              · linarith [hy.2]
              · exact ⟨by linarith [hsep.1], by linarith [hy.2]⟩
            · rcases min_cases q.1.1 p.1 with ⟨hmin, _⟩ | ⟨hmin, _⟩
              · linarith [hy.1]
              · exact ⟨by linarith [hy.1], by linarith [hsep.2]⟩
        rcases hx with hqp | hq2
        · rcases hcov hqp with hq1 | hxp
          · rcases ih7 (Or.inl hq1) with hxab | hxrest
            · exact Or.inl hxab
            · exact Or.inr (Or.inr hxrest)
          · exact Or.inr (Or.inl hxp)
        · rcases ih7 (Or.inr hq2) with hxab | hxrest
          · exact Or.inl hxab
          · exact Or.inr (Or.inr hxrest)
      · intro c d hca hbd hcd
        have hcd_p := hcd p List.mem_cons_self
        obtain ⟨hc1, hd1, hcd_q2⟩ := ih8 c d hca hbd fun r hr =>
          hcd r (List.mem_cons_of_mem p hr)
        exact ⟨le_min hc1 hcd_p.1, max_le hd1 hcd_p.2, hcd_q2⟩

theorem mergeList_properties (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, p.1 < p.2)
    (c d : ℝ) (hcd : ∀ p ∈ L, c ≤ p.1 ∧ p.2 ≤ d) :
    (∀ p ∈ mergeList L, p.1 < p.2 ∧ c ≤ p.1 ∧ p.2 ≤ d) ∧
    (mergeList L).Pairwise (fun p q => p.2 < q.1 ∨ q.2 < p.1) ∧
    (unionIoo L ⊆ unionIoo (mergeList L)) ∧
    (unionIcc (mergeList L) ⊆ unionIcc L) := by
  induction L with
  | nil =>
    simp [mergeList, unionIoo, unionIcc]
  | cons p rest ih =>
    have hrest : ∀ r ∈ rest, r.1 < r.2 := fun r hr => hL r (List.mem_cons_of_mem p hr)
    have hcd_rest : ∀ r ∈ rest, c ≤ r.1 ∧ r.2 ≤ d := fun r hr => hcd r (List.mem_cons_of_mem p hr)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hrest hcd_rest
    have hp_lt : p.1 < p.2 := hL p List.mem_cons_self
    have hp_cd : c ≤ p.1 ∧ p.2 ≤ d := hcd p List.mem_cons_self
    have hprops := mergeOne_properties p.1 p.2 (mergeList rest) hp_lt
      (fun r hr => (ih1 r hr).1) ih2
    set q := mergeOne p.1 p.2 (mergeList rest)
    obtain ⟨_, _, hq_lt, hq2, hq_pw, hq_Ioo, hq_Icc, hq_cd⟩ := hprops
    obtain ⟨hc_q1, hd_q1, hcd_q2⟩ := hq_cd c d hp_cd.1 hp_cd.2 fun r hr =>
      ⟨(ih1 r hr).2.1, (ih1 r hr).2.2⟩
    dsimp [mergeList, unionIoo, unionIcc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨hq_lt, hc_q1, hd_q1⟩
      · exact ⟨(hq2 r hr').2.1, (hcd_q2 r hr').1, (hcd_q2 r hr').2⟩
    · refine List.pairwise_cons.mpr ⟨fun r hr => (hq2 r hr).2.2, hq_pw⟩
    · intro x hx
      rcases hx with hxp | hxrest
      · exact hq_Ioo (Or.inl hxp)
      · exact hq_Ioo (Or.inr (ih3 hxrest))
    · intro x hx
      rcases hq_Icc hx with hxp | hxrest
      · exact Or.inl hxp
      · exact Or.inr (ih4 hxrest)

theorem exists_head_gap (p : ℝ × ℝ) (L : List (ℝ × ℝ)) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsep : ∀ q ∈ L, p.2 < q.1 ∨ q.2 < p.1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧
      ∀ q ∈ L, p.2 + 2 * δ < q.1 - 2 * δ ∨ q.2 + 2 * δ < p.1 - 2 * δ := by
  induction L with
  | nil => exact ⟨δ₀, hδ₀, le_rfl, by simp⟩
  | cons q rest ih =>
    obtain ⟨δ₁, hδ₁_pos, hδ₁_le, hδ₁_rest⟩ :=
      ih fun r hr => hsep r (List.mem_cons_of_mem q hr)
    rcases hsep q List.mem_cons_self with hpq | hqp
    · let δ₂ := min δ₁ ((q.1 - p.2) / 5)
      have hδ₂_pos : 0 < δ₂ := lt_min hδ₁_pos (by linarith)
      refine ⟨δ₂, hδ₂_pos, (min_le_left _ _).trans hδ₁_le, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · left
        have : δ₂ ≤ (r.1 - p.2) / 5 := min_le_right _ _
        linarith
      · have : δ₂ ≤ δ₁ := min_le_left _ _
        rcases hδ₁_rest r hr' with h1 | h1
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
    · let δ₂ := min δ₁ ((p.1 - q.2) / 5)
      have hδ₂_pos : 0 < δ₂ := lt_min hδ₁_pos (by linarith)
      refine ⟨δ₂, hδ₂_pos, (min_le_left _ _).trans hδ₁_le, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · right
        have : δ₂ ≤ (p.1 - r.2) / 5 := min_le_right _ _
        linarith
      · have : δ₂ ≤ δ₁ := min_le_left _ _
        rcases hδ₁_rest r hr' with h1 | h1
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)

theorem exists_min_gap (L : List (ℝ × ℝ)) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hpw : L.Pairwise (fun p q => p.2 < q.1 ∨ q.2 < p.1)) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < δ₀ ∧
      L.Pairwise (fun p q => p.2 + 2 * δ < q.1 - 2 * δ ∨ q.2 + 2 * δ < p.1 - 2 * δ) := by
  induction L with
  | nil =>
    exact ⟨δ₀ / 3, by positivity, by linarith, List.Pairwise.nil⟩
  | cons p rest ih =>
    obtain ⟨hp_rest, hpw_rest⟩ := List.pairwise_cons.mp hpw
    obtain ⟨δ₁, hδ₁_pos, hδ₁_lt, hδ₁_pw⟩ := ih hpw_rest
    obtain ⟨δ₂, hδ₂_pos, hδ₂_le, hδ₂_head⟩ := exists_head_gap p rest hδ₁_pos hp_rest
    refine ⟨δ₂, hδ₂_pos, by linarith, List.pairwise_cons.mpr ⟨hδ₂_head, ?_⟩⟩
    refine hδ₁_pw.imp ?_
    intro q1 q2 hq
    rcases hq with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- Piecewise-linear homeomorphism of `ℝ` mapping `[-1, 1]` onto `[a, d]` and `[-3, 3]` onto
`[a - 2δ, d + 2δ]`. -/
noncomputable def stretchTo (a d δ x : ℝ) : ℝ :=
  (a + d) / 2 + ((d - a) / 2) * max (-1) (min 1 x) + δ * (min 0 (x + 1) + max 0 (x - 1))

/-- Explicit inverse of `stretchTo a d δ`. -/
noncomputable def unstretchFrom (a d δ y : ℝ) : ℝ :=
  (max a (min d y) - (a + d) / 2) / ((d - a) / 2) + (min 0 (y - a) + max 0 (y - d)) / δ

theorem stretchTo_of_lt_neg_one {a d δ x : ℝ} (hx : x ≤ -1) :
    stretchTo a d δ x = a + δ * (x + 1) := by
  have h1 : min 1 x = x := min_eq_right (by linarith)
  have h2 : max (-1) x = -1 := max_eq_left hx
  have h3 : min 0 (x + 1) = x + 1 := min_eq_right (by linarith)
  have h4 : max 0 (x - 1) = 0 := max_eq_left (by linarith)
  simp only [stretchTo, h1, h2, h3, h4]
  ring

theorem stretchTo_of_mem_Icc {a d δ x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    stretchTo a d δ x = (a + d) / 2 + ((d - a) / 2) * x := by
  have h1 : min 1 x = x := min_eq_right hx.2
  have h2 : max (-1) x = x := max_eq_right hx.1
  have h3 : min 0 (x + 1) = 0 := min_eq_left (by linarith [hx.1])
  have h4 : max 0 (x - 1) = 0 := max_eq_left (by linarith [hx.2])
  simp only [stretchTo, h1, h2, h3, h4]
  ring

theorem stretchTo_of_one_le {a d δ x : ℝ} (hx : 1 ≤ x) :
    stretchTo a d δ x = d + δ * (x - 1) := by
  have h1 : min 1 x = 1 := min_eq_left hx
  have h2 : max (-1 : ℝ) 1 = 1 := max_eq_right (by norm_num)
  have h3 : min 0 (x + 1) = 0 := min_eq_left (by linarith)
  have h4 : max 0 (x - 1) = x - 1 := max_eq_right (by linarith)
  simp only [stretchTo, h1, h2, h3, h4]
  ring

theorem unstretchFrom_of_le {a d δ y : ℝ} (had : a < d) (hy : y ≤ a) :
    unstretchFrom a d δ y = -1 + (y - a) / δ := by
  have h1 : min d y = y := min_eq_right (by linarith)
  have h2 : max a y = a := max_eq_left hy
  have h3 : min 0 (y - a) = y - a := min_eq_right (by linarith)
  have h4 : max 0 (y - d) = 0 := max_eq_left (by linarith)
  have hne : (d - a) / 2 ≠ 0 := by linarith
  simp only [unstretchFrom, h1, h2, h3, h4, add_zero]
  have h5 : (a - (a + d) / 2) / ((d - a) / 2) = -1 := by
    rw [div_eq_iff hne]
    ring
  rw [h5]

theorem unstretchFrom_of_mem_Icc {a d δ y : ℝ} (hy : y ∈ Icc a d) :
    unstretchFrom a d δ y = (y - (a + d) / 2) / ((d - a) / 2) := by
  have h1 : min d y = y := min_eq_right hy.2
  have h2 : max a y = y := max_eq_right hy.1
  have h3 : min 0 (y - a) = 0 := min_eq_left (by linarith [hy.1])
  have h4 : max 0 (y - d) = 0 := max_eq_left (by linarith [hy.2])
  simp [unstretchFrom, h1, h2, h3, h4]

theorem unstretchFrom_of_ge {a d δ y : ℝ} (had : a < d) (hy : d ≤ y) :
    unstretchFrom a d δ y = 1 + (y - d) / δ := by
  have h1 : min d y = d := min_eq_left hy
  have h2 : max a d = d := max_eq_right had.le
  have h3 : min 0 (y - a) = 0 := min_eq_left (by linarith)
  have h4 : max 0 (y - d) = y - d := max_eq_right (by linarith)
  have hne : (d - a) / 2 ≠ 0 := by linarith
  simp only [unstretchFrom, h1, h2, h3, h4, zero_add]
  have h5 : (d - (a + d) / 2) / ((d - a) / 2) = 1 := by
    rw [div_eq_iff hne]
    ring
  rw [h5]

theorem unstretchFrom_stretchTo {a d δ : ℝ} (had : a < d) (hδ : 0 < δ) (x : ℝ) :
    unstretchFrom a d δ (stretchTo a d δ x) = x := by
  have hne : (d - a) / 2 ≠ 0 := by linarith
  have hδne : δ ≠ 0 := hδ.ne'
  rcases le_total x (-1) with hx1 | hx1
  · rw [stretchTo_of_lt_neg_one hx1]
    have hle : a + δ * (x + 1) ≤ a := by nlinarith
    rw [unstretchFrom_of_le had hle]
    field_simp
    ring
  · rcases le_total x 1 with hx2 | hx2
    · rw [stretchTo_of_mem_Icc ⟨hx1, hx2⟩]
      have hmem : (a + d) / 2 + (d - a) / 2 * x ∈ Icc a d := ⟨by nlinarith, by nlinarith⟩
      rw [unstretchFrom_of_mem_Icc hmem, add_sub_cancel_left, mul_div_cancel_left₀ _ hne]
    · rw [stretchTo_of_one_le hx2]
      have hge : d ≤ d + δ * (x - 1) := by nlinarith
      rw [unstretchFrom_of_ge had hge]
      field_simp
      ring

theorem stretchTo_unstretchFrom {a d δ : ℝ} (had : a < d) (hδ : 0 < δ) (y : ℝ) :
    stretchTo a d δ (unstretchFrom a d δ y) = y := by
  have hne : (d - a) / 2 ≠ 0 := by linarith
  have hδne : δ ≠ 0 := hδ.ne'
  rcases le_total y a with hy1 | hy1
  · rw [unstretchFrom_of_le had hy1]
    have hle : -1 + (y - a) / δ ≤ -1 := by
      have : (y - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      linarith
    rw [stretchTo_of_lt_neg_one hle]
    field_simp
    ring
  · rcases le_total y d with hy2 | hy2
    · rw [unstretchFrom_of_mem_Icc ⟨hy1, hy2⟩]
      have hmem : (y - (a + d) / 2) / ((d - a) / 2) ∈ Icc (-1 : ℝ) 1 := by
        rw [mem_Icc, le_div_iff₀ (by linarith), div_le_iff₀ (by linarith)]
        exact ⟨by linarith, by linarith⟩
      rw [stretchTo_of_mem_Icc hmem, mul_div_cancel₀ _ hne]
      ring
    · rw [unstretchFrom_of_ge had hy2]
      have hge : 1 ≤ 1 + (y - d) / δ := by
        have : 0 ≤ (y - d) / δ := div_nonneg (by linarith) hδ.le
        linarith
      rw [stretchTo_of_one_le hge]
      field_simp
      ring

/-- Homeomorphism of `ℝ` stretching `[-1, 1]` to `[a, d]` and `[-3, 3]` to `[a - 2δ, d + 2δ]`. -/
noncomputable def stretchHomeomorph {a d δ : ℝ} (had : a < d) (hδ : 0 < δ) : ℝ ≃ₜ ℝ where
  toFun := stretchTo a d δ
  invFun := unstretchFrom a d δ
  left_inv := unstretchFrom_stretchTo had hδ
  right_inv := stretchTo_unstretchFrom had hδ
  continuous_toFun := by unfold stretchTo; fun_prop
  continuous_invFun := by unfold unstretchFrom; fun_prop

theorem stretchTo_strictMono {a d δ : ℝ} (had : a < d) (hδ : 0 < δ) :
    StrictMono (stretchTo a d δ) := by
  intro x₁ x₂ hlt
  rcases le_total x₂ (-1) with hx₂1 | hx₂1
  · rw [stretchTo_of_lt_neg_one (hlt.le.trans hx₂1), stretchTo_of_lt_neg_one hx₂1]
    nlinarith
  · rcases le_total x₁ (-1) with hx₁1 | hx₁1
    · have ha1 : stretchTo a d δ x₁ ≤ a := by
        rw [stretchTo_of_lt_neg_one hx₁1]; nlinarith
      rcases le_total x₂ 1 with hx₂2 | hx₂2
      · have ha2 : a ≤ stretchTo a d δ x₂ := by
          rw [stretchTo_of_mem_Icc ⟨hx₂1, hx₂2⟩]; nlinarith
        rcases eq_or_lt_of_le hx₁1 with rfl | hlt1
        · rw [stretchTo_of_lt_neg_one le_rfl, stretchTo_of_mem_Icc ⟨hx₂1, hx₂2⟩]
          nlinarith
        · have : stretchTo a d δ x₁ < a := by rw [stretchTo_of_lt_neg_one hx₁1]; nlinarith
          linarith
      · have hd2 : d ≤ stretchTo a d δ x₂ := by
          rw [stretchTo_of_one_le hx₂2]; nlinarith
        linarith
    · rcases le_total x₂ 1 with hx₂2 | hx₂2
      · rw [stretchTo_of_mem_Icc ⟨hx₁1, hlt.le.trans hx₂2⟩, stretchTo_of_mem_Icc ⟨hx₂1, hx₂2⟩]
        nlinarith
      · rcases le_total x₁ 1 with hx₁2 | hx₁2
        · have hd1 : stretchTo a d δ x₁ ≤ d := by
            rw [stretchTo_of_mem_Icc ⟨hx₁1, hx₁2⟩]; nlinarith
          rcases eq_or_lt_of_le hx₂2 with rfl | hlt2
          · rw [stretchTo_of_mem_Icc ⟨hx₁1, hx₁2⟩, stretchTo_of_one_le le_rfl]
            nlinarith
          · have : d < stretchTo a d δ x₂ := by rw [stretchTo_of_one_le hx₂2]; nlinarith
            linarith
        · rw [stretchTo_of_one_le hx₁2, stretchTo_of_one_le hx₂2]
          nlinarith

theorem stretchTo_eval_pts (a d δ : ℝ) :
    stretchTo a d δ (-3) = a - 2 * δ ∧
    stretchTo a d δ (-5 / 2) = a - (3 / 2) * δ ∧
    stretchTo a d δ (-1) = a ∧
    stretchTo a d δ 1 = d ∧
    stretchTo a d δ (5 / 2) = d + (3 / 2) * δ ∧
    stretchTo a d δ 3 = d + 2 * δ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stretchTo_of_lt_neg_one (by norm_num)]; ring
  · rw [stretchTo_of_lt_neg_one (by norm_num)]; ring
  · rw [stretchTo_of_lt_neg_one (by norm_num)]; ring
  · rw [stretchTo_of_one_le (by norm_num)]; ring
  · rw [stretchTo_of_one_le (by norm_num)]; ring
  · rw [stretchTo_of_one_le (by norm_num)]; ring

/-- The upper semicircle profile `√(max 0 ((5/2)² - y²))` at radius `5 / 2`. -/
noncomputable def capH52 (y : ℝ) : ℝ :=
  Real.sqrt (max 0 ((5 / 2) ^ 2 - y ^ 2))

theorem continuous_capH52 : Continuous capH52 := by
  unfold capH52
  fun_prop

theorem capH52_nonneg (y : ℝ) : 0 ≤ capH52 y := Real.sqrt_nonneg _

theorem capH52_le (y : ℝ) : capH52 y ≤ 5 / 2 := by
  unfold capH52
  have h1 : max 0 ((5 / 2) ^ 2 - y ^ 2) ≤ (5 / 2) ^ 2 :=
    max_le (by norm_num) (by nlinarith [sq_nonneg y])
  exact (Real.sqrt_le_sqrt h1).trans (by rw [Real.sqrt_sq (by norm_num)])

theorem sq_capH52 {y : ℝ} (hy : y ∈ Icc (-5 / 2 : ℝ) (5 / 2)) :
    (capH52 y) ^ 2 = (5 / 2) ^ 2 - y ^ 2 := by
  unfold capH52
  have hnonneg : 0 ≤ (5 / 2) ^ 2 - y ^ 2 := by nlinarith [hy.1, hy.2]
  rw [max_eq_right hnonneg, Real.sq_sqrt hnonneg]

theorem two_le_capH52 {y : ℝ} (hy : y ∈ Icc (-3 / 2 : ℝ) (3 / 2)) :
    2 ≤ capH52 y := by
  unfold capH52
  have h1 : (2 : ℝ) ^ 2 ≤ max 0 ((5 / 2) ^ 2 - y ^ 2) :=
    le_trans (by nlinarith [hy.1, hy.2]) (le_max_right 0 _)
  exact (by rw [Real.sqrt_sq (by norm_num)] : (2 : ℝ) = Real.sqrt (2 ^ 2)).trans_le
    (Real.sqrt_le_sqrt h1)

/-- The horizontal shear homeomorphism `Ψ(z) = ⟨z.re - capH52 z.im, z.im⟩` of `ℂ`, which maps the
right semicircle `{z ∈ sphere 0 (5/2) | 0 ≤ z.re}` to `{0} ×ℂ [-5/2, 5/2]` and `{z ∈ ball 0 3 | z.re
≤ capH52 z.im}` into `[-6, 0] ×ℂ (-3, 3)`. -/
noncomputable def psiShift : ℂ ≃ₜ ℂ where
  toFun z := ⟨z.re - capH52 z.im, z.im⟩
  invFun w := ⟨w.re + capH52 w.im, w.im⟩
  left_inv z := Complex.ext (by simp) (by simp)
  right_inv w := Complex.ext (by simp) (by simp)
  continuous_toFun := by
    refine Continuous.comp Complex.equivRealProdCLM.symm.continuous (Continuous.prodMk ?_ ?_)
    · exact Complex.continuous_re.sub (continuous_capH52.comp Complex.continuous_im)
    · exact Complex.continuous_im
  continuous_invFun := by
    refine Continuous.comp Complex.equivRealProdCLM.symm.continuous (Continuous.prodMk ?_ ?_)
    · exact Complex.continuous_re.add (continuous_capH52.comp Complex.continuous_im)
    · exact Complex.continuous_im

@[simp] theorem psiShift_re (z : ℂ) : (psiShift z).re = z.re - capH52 z.im := rfl
@[simp] theorem psiShift_im (z : ℂ) : (psiShift z).im = z.im := rfl
@[simp] theorem psiShift_symm_re (w : ℂ) : (psiShift.symm w).re = w.re + capH52 w.im := rfl
@[simp] theorem psiShift_symm_im (w : ℂ) : (psiShift.symm w).im = w.im := rfl

theorem psiShift_right_semicircle {z : ℂ} (hz : ‖z‖ = 5 / 2) (hre : 0 ≤ z.re) :
    (psiShift z).re = 0 ∧ (psiShift z).im ∈ Icc (-5 / 2 : ℝ) (5 / 2) := by
  have hsq : z.re ^ 2 + z.im ^ 2 = (5 / 2) ^ 2 := by
    have h1 : Complex.normSq z = (5 / 2) ^ 2 := by
      rw [← Complex.sq_norm, hz]
    rw [Complex.normSq_apply] at h1
    nlinarith
  have him : z.im ∈ Icc (-5 / 2 : ℝ) (5 / 2) := by
    have h2 : z.im ^ 2 ≤ (5 / 2) ^ 2 := by nlinarith [sq_nonneg z.re]
    have h3 : |z.im| ≤ 5 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
      exact h2
    exact ⟨by linarith [ neg_le_of_abs_le h3 ], le_of_abs_le h3⟩
  have hcap : capH52 z.im = z.re := by
    unfold capH52
    have h1 : (5 / 2) ^ 2 - z.im ^ 2 = z.re ^ 2 := by linarith
    rw [h1, max_eq_right (sq_nonneg _), Real.sqrt_sq hre]
  exact ⟨by rw [psiShift_re, hcap, sub_self], him⟩

theorem psiShift_symm_mem_closedBall {w : ℂ} (hre : w.re ∈ Icc (-2 : ℝ) 0)
    (him : w.im ∈ Icc (-3 / 2 : ℝ) (3 / 2)) :
    ‖psiShift.symm w‖ ≤ 5 / 2 ∧ 0 ≤ (psiShift.symm w).re := by
  have hcap2 : 2 ≤ capH52 w.im := two_le_capH52 him
  have him52 : w.im ∈ Icc (-5 / 2 : ℝ) (5 / 2) := ⟨by linarith [him.1], by linarith [him.2]⟩
  have hre_pos : 0 ≤ (psiShift.symm w).re := by
    simp only [psiShift_symm_re]
    linarith [hre.1]
  have hre_le : (psiShift.symm w).re ≤ capH52 w.im := by
    simp only [psiShift_symm_re]
    linarith [hre.2]
  refine ⟨?_, hre_pos⟩
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have hsq := sq_capH52 him52
  have hsq_re : (psiShift.symm w).re * (psiShift.symm w).re ≤ (capH52 w.im) ^ 2 := by
    nlinarith [hre_pos, hre_le]
  rw [psiShift_symm_im]
  linarith

theorem psiShift_ball3_bounds {z : ℂ} (hz : z ∈ ball (0 : ℂ) 3) (hle : z.re ≤ capH52 z.im) :
    (psiShift z).re ∈ Icc (-6 : ℝ) 0 ∧ (psiShift z).im ∈ Ioo (-3 : ℝ) 3 := by
  have hnorm : ‖z‖ < 3 := mem_ball_zero_iff.mp hz
  have hre_gt : -3 < z.re := by
    have := Complex.abs_re_le_norm z
    linarith [(abs_lt.mp (this.trans_lt hnorm)).1]
  have him_mem : z.im ∈ Ioo (-3 : ℝ) 3 := by
    have := Complex.abs_im_le_norm z
    exact abs_lt.mp (this.trans_lt hnorm)
  have hcap : capH52 z.im ≤ 5 / 2 := capH52_le z.im
  rw [psiShift_re, psiShift_im]
  exact ⟨⟨by linarith, by linarith⟩, him_mem⟩

end GraphMinor.GM07
