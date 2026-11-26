/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.RegionLocal
public import LeanPool.GraphMinor.GM06.Section2Dual
public import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.Surface.JordanDomain
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.Surface.DiscArcs
import Mathlib.Analysis.Convex.PathConnected

/-!
# Regions and Edges of a Proper Drawing on a Closed Disc Space

This file adapts the edge-side and region-connectivity lemmas of `GraphMinor.GM11` (`EdgeSides`,
`Regions`, `Section5`, `Section5b`) from closed surfaces to proper drawings on a closed disc space
`S` (`IsClosedDiscSpace S`), with zero unproved hypotheses.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- `bd S` is closed in `S` when `IsClosedDiscSpace S`. -/
theorem isClosed_bd_of_isClosedDiscSpace (hS : IsClosedDiscSpace S) :
    IsClosed (bd S) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  obtain ⟨φ⟩ := hS
  have hbd := image_bd_homeomorph φ
  rw [bd_closedUnitDisc] at hbd
  rw [← hbd]
  have hcl : IsClosed {x : ClosedUnitDisc | x.1 ∈ UnitCircle} :=
    isClosed_sphere.preimage continuous_subtype_val
  exact hcl.isCompact.image φ.continuous |>.isClosed

/-- Small closed disc neighborhoods around an interior point `p ∈ O \ bd S` of a closed disc
space `S`. -/
theorem disc_exists_closedDisc_nbhd (hS : IsClosedDiscSpace S) {O : Set S} (hO : IsOpen O)
    {p : S} (hpO : p ∈ O) (hpbd : p ∉ bd S) :
    ∃ D D' : Set S,
      IsClosedDisc D ∧ IsOpen D' ∧ p ∈ D' ∧ D' ⊆ D ∧ D ⊆ O ∧ D \ D' = discBd D := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  obtain ⟨φ⟩ := hS
  have hbd_img := image_bd_homeomorph φ
  rw [bd_closedUnitDisc] at hbd_img
  let c : ClosedUnitDisc := φ.symm p
  have hc_open : (c : EuclideanPlane) ∈ OpenUnitDisc := by
    have hle : ‖(c : EuclideanPlane)‖ ≤ 1 := mem_closedBall_zero_iff.mp c.2
    have hne : ‖(c : EuclideanPlane)‖ ≠ 1 := by
      intro h1
      apply hpbd
      rw [← hbd_img]
      exact ⟨c, by simpa [UnitCircle] using h1, φ.apply_symm_apply p⟩
    simpa [OpenUnitDisc] using lt_of_le_of_ne hle hne
  let P : Set ClosedUnitDisc := φ ⁻¹' (O \ bd S)
  have hP_open : IsOpen P := (hO.sdiff hbd_cl).preimage φ.continuous
  rw [isOpen_induced_iff] at hP_open
  obtain ⟨W, hW_open, hW_eq⟩ := hP_open
  have hcW : (c : EuclideanPlane) ∈ W ∩ OpenUnitDisc := by
    refine ⟨?_, hc_open⟩
    have hcP : c ∈ P := by
      change φ c ∈ O \ bd S
      rw [φ.apply_symm_apply]
      exact ⟨hpO, hpbd⟩
    rw [← hW_eq] at hcP
    exact hcP
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp (hW_open.inter Metric.isOpen_ball) c.1 hcW
  let ρ : ℝ := ρ' / 2
  have hρ : 0 < ρ := half_pos hρ'
  have hclosed : Metric.closedBall (c : EuclideanPlane) ρ ⊆ W ∩ OpenUnitDisc :=
    (Metric.closedBall_subset_ball (half_lt_self hρ')).trans hball
  have hto : Metric.closedBall (c : EuclideanPlane) ρ ⊆ ClosedUnitDisc :=
    fun x hx => Metric.ball_subset_closedBall (hclosed hx).2
  let g : EuclideanPlane → EuclideanPlane := fun x => (c : EuclideanPlane) + ρ • x
  have hg : Continuous g := by fun_prop
  have hgin : ∀ x : EuclideanPlane,
      g x ∈ Metric.closedBall (c : EuclideanPlane) ρ ↔ x ∈ ClosedUnitDisc := by
    intro x
    simp only [g, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ClosedUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => le_of_mul_le_mul_left (by simpa using h') hρ, fun h' => by nlinarith⟩
  have hgball : ∀ x : EuclideanPlane,
      g x ∈ Metric.ball (c : EuclideanPlane) ρ ↔ x ∈ OpenUnitDisc := by
    intro x
    simp only [g, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, OpenUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => lt_of_mul_lt_mul_left (by simpa using h') hρ.le, fun h' => by nlinarith⟩
  let k : ClosedUnitDisc → S := fun x => φ ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩
  have hk : Continuous k := φ.continuous.comp (Continuous.subtype_mk (hg.comp
    continuous_subtype_val) _)
  have hkinj : Function.Injective k := by
    intro x y hxy
    have h₁ : g x.1 = g y.1 := congrArg Subtype.val (φ.injective hxy)
    have h₂ : ρ • x.1 = ρ • y.1 := add_left_cancel h₁
    exact Subtype.ext (smul_right_injective _ hρ.ne' h₂)
  let D : Set S := range k
  let E : ClosedUnitDisc ≃ₜ D :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective k hkinj) hk.rangeFactorization
  have hE_val : ∀ x : ClosedUnitDisc, (E x).1 = k x := fun _ => rfl
  let B_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) ρ
  have hB_open : IsOpen B_sub := Metric.isOpen_ball.preimage continuous_subtype_val
  let D' : Set S := φ '' B_sub
  have hD'open : IsOpen D' := φ.isOpenMap _ hB_open
  have hkD' : ∀ x : ClosedUnitDisc, k x ∈ D' ↔ x.1 ∈ OpenUnitDisc := by
    intro x
    constructor
    · rintro ⟨y, hy, hyk⟩
      have heq : ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩ = y := φ.injective hyk.symm
      have hgy : g x.1 = y.1 := congrArg Subtype.val heq
      rw [← hgball, hgy]
      exact hy
    · intro hx
      refine ⟨⟨g x.1, hto ((hgin x.1).mpr x.2)⟩, ?_, rfl⟩
      exact (hgball x.1).mpr hx
  have hbd := disc_boundary D E
  refine ⟨D, D', ⟨E⟩, hD'open, ⟨c, by simp [B_sub, hρ], φ.apply_symm_apply p⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : EuclideanPlane) ∈ Metric.ball (c : EuclideanPlane) ρ := hy
    let x : EuclideanPlane := ρ⁻¹ • ((y : EuclideanPlane) - c.1)
    have hgx : g x = (y : EuclideanPlane) := by
      simp only [g, x, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
    have hxm : x ∈ OpenUnitDisc := by
      rw [← hgball, hgx]
      exact hy'
    refine ⟨⟨x, Metric.ball_subset_closedBall hxm⟩, ?_⟩
    change φ ⟨g x, _⟩ = φ y
    congr 1
    exact Subtype.ext hgx
  · rintro _ ⟨x, rfl⟩
    have hxW : g x.1 ∈ W := (hclosed ((hgin x.1).mpr x.2)).1
    have hxP : (⟨g x.1, hto ((hgin x.1).mpr x.2)⟩ : ClosedUnitDisc) ∈ P := by
      rw [← hW_eq]
      exact hxW
    exact hxP.1
  · rw [hbd]
    ext q
    constructor
    · rintro ⟨⟨x, rfl⟩, hq⟩
      refine ⟨x, ?_, hE_val x⟩
      have hle : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
      have hne : ¬ ‖x.1‖ < 1 := fun hlt => hq ((hkD' x).mpr (by simpa [OpenUnitDisc] using hlt))
      have : ‖x.1‖ = 1 := le_antisymm hle (not_lt.mp hne)
      simpa [UnitCircle] using this
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, (hE_val x).symm⟩, fun hin => ?_⟩
      have h₁ : ‖x.1‖ < 1 := by simpa [OpenUnitDisc] using (hkD' x).mp hin
      have h₂ : ‖x.1‖ = 1 := by simpa [UnitCircle] using hx
      linarith

/-- Small punctured neighborhoods in a closed disc space `S`. -/
theorem disc_exists_punctured_nbhd (hS : IsClosedDiscSpace S) {O : Set S} (hO : IsOpen O)
    {x : S} (hx : x ∈ O) :
    ∃ Z : Set S, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ O ∧ IsPreconnected (Z \ {x}) ∧ x ∈ closure (Z \ {x}) := by
  obtain ⟨φ⟩ := hS
  let c : ClosedUnitDisc := φ.symm x
  have hφc : φ c = x := φ.apply_symm_apply x
  have hbd_img := image_bd_homeomorph φ
  rw [bd_closedUnitDisc] at hbd_img
  by_cases h_int : (c : EuclideanPlane) ∈ OpenUnitDisc
  · let P : Set ClosedUnitDisc := φ ⁻¹' O
    have hP_open : IsOpen P := hO.preimage φ.continuous
    rw [isOpen_induced_iff] at hP_open
    obtain ⟨W, hW_open, hW_eq⟩ := hP_open
    have hcW : (c : EuclideanPlane) ∈ W ∩ OpenUnitDisc := by
      refine ⟨?_, h_int⟩
      have hcP : c ∈ P := by simp [P, hφc, hx]
      rw [← hW_eq] at hcP
      exact hcP
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hW_open.inter Metric.isOpen_ball) c.1 hcW
    have hsub : Metric.ball (c : EuclideanPlane) δ ⊆ ClosedUnitDisc :=
      fun y hy => Metric.ball_subset_closedBall (hball hy).2
    let B : Set ClosedUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) δ
    have hdiff : φ '' B \ {x} =
        φ '' (Subtype.val ⁻¹' (Metric.ball (c : EuclideanPlane) δ \ {(c : EuclideanPlane)})) := by
      ext q
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hne⟩
        refine ⟨y, ⟨hy, fun hyc => hne ?_⟩, rfl⟩
        have : y = c := Subtype.ext hyc
        rw [this, hφc]
        rfl
      · rintro ⟨y, ⟨hy, hne⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, fun hq => hne ?_⟩
        have : y = c := φ.injective (hq.trans hφc.symm)
        rw [this]
        rfl
    refine ⟨φ '' B, φ.isOpenMap _ (Metric.isOpen_ball.preimage continuous_subtype_val),
      ⟨c, by simp [B, hδ], hφc⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyW : (y : EuclideanPlane) ∈ W := (hball hy).1
      have hyP : y ∈ P := by rw [← hW_eq]; exact hyW
      exact hyP
    · rw [hdiff]
      refine IsPreconnected.image ?_ _ φ.continuous.continuousOn
      refine (IsInducing.subtypeVal :
        IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hsub)]
      exact isPreconnected_ball_sdiff _ hδ
    · rw [hdiff, ← hφc]
      refine image_closure_subset_closure_image φ.continuous ⟨c, ?_, rfl⟩
      rw [closure_subtype, Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hsub)]
      refine Metric.mem_closure_iff.mpr fun ε hε => ?_
      have hr : 0 < min ε δ / 2 := by positivity
      obtain ⟨b, hb⟩ := (NormedSpace.sphere_nonempty (x := (c : EuclideanPlane))).mpr hr.le
      have hbd : dist b (c : EuclideanPlane) = min ε δ / 2 := hb
      have hlt₁ : min ε δ / 2 < δ := by
        have := min_le_right ε δ
        linarith
      have hlt₂ : min ε δ / 2 < ε := by
        have := min_le_left ε δ
        linarith
      refine ⟨b, ⟨?_, ?_⟩, ?_⟩
      · simpa [hbd] using hlt₁
      · intro hbc
        rw [hbc, dist_self] at hbd
        exact hr.ne hbd
      · rw [dist_comm]
        simpa [hbd] using hlt₂
  · let P : Set ClosedUnitDisc := φ ⁻¹' O
    have hP_open : IsOpen P := hO.preimage φ.continuous
    rw [isOpen_induced_iff] at hP_open
    obtain ⟨W, hW_open, hW_eq⟩ := hP_open
    have hcW : (c : EuclideanPlane) ∈ W := by
      have hcP : c ∈ P := by simp [P, hφc, hx]
      rw [← hW_eq] at hcP
      exact hcP
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW_open c.1 hcW
    let B : Set ClosedUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) δ
    let U_open : Set EuclideanPlane := Metric.ball (c : EuclideanPlane) δ ∩ OpenUnitDisc
    have hU_sub : U_open ⊆ ClosedUnitDisc :=
      fun y hy => Metric.ball_subset_closedBall hy.2
    let B_open : Set ClosedUnitDisc := Subtype.val ⁻¹' U_open
    have hB_open_conn : IsPreconnected B_open := by
      refine (IsInducing.subtypeVal :
        IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hU_sub]
      exact ((convex_ball _ _).inter convex_openUnitDisc).isPreconnected
    have hB_sub_diff : B_open ⊆ B \ {c} := by
      intro y hy
      refine ⟨hy.1, fun hyc => ?_⟩
      rw [mem_singleton_iff] at hyc
      subst hyc
      exact h_int hy.2
    have hB_sub_cl : B ⊆ closure B_open := by
      intro y hy
      rw [closure_subtype, Subtype.image_preimage_coe, inter_eq_right.mpr hU_sub]
      have hcl : (y : EuclideanPlane) ∈ closure (OpenUnitDisc : Set EuclideanPlane) := by
        rw [show closure (OpenUnitDisc : Set EuclideanPlane) = ClosedUnitDisc from
          closure_ball _ one_ne_zero]
        exact y.2
      exact Metric.isOpen_ball.inter_closure ⟨hy, hcl⟩
    have hB_diff_conn : IsPreconnected (B \ {c}) :=
      hB_open_conn.subset_closure hB_sub_diff (sdiff_subset.trans hB_sub_cl)
    have hc_cl : c ∈ closure (B \ {c}) :=
      closure_mono hB_sub_diff (hB_sub_cl (Metric.mem_ball_self hδ))
    have hdiff_eq : φ '' B \ {x} = φ '' (B \ {c}) := by
      ext q
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hne⟩
        refine ⟨y, ⟨hy, fun hyc => hne ?_⟩, rfl⟩
        rw [mem_singleton_iff] at hyc
        rw [hyc, hφc]
        rfl
      · rintro ⟨y, ⟨hy, hne⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, fun hq => hne ?_⟩
        exact φ.injective (hq.trans hφc.symm)
    refine ⟨φ '' B, φ.isOpenMap _ (Metric.isOpen_ball.preimage continuous_subtype_val),
      ⟨c, Metric.mem_ball_self hδ, hφc⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyW : (y : EuclideanPlane) ∈ W := hball hy
      have hyP : y ∈ P := by rw [← hW_eq]; exact hyW
      exact hyP
    · rw [hdiff_eq]
      exact hB_diff_conn.image _ φ.continuous.continuousOn
    · rw [hdiff_eq, ← hφc]
      exact image_closure_subset_closure_image φ.continuous ⟨c, hc_cl, rfl⟩

private theorem exists_edge_side_neighborhood {Y Δ A₀ D D' F : Set S}
    {Γ : Drawing S} {e : Set S} {p : S}
    (hY : IsClosed Y) (hpY : p ∉ Y) (hpF : p ∈ F)
    (hYcover : Γ.U \ e ⊆ Y) (hFU : F ⊆ Γ.U)
    (hFsub : ∀ x ∈ e, x ∉ Y → x ∈ F)
    (hbdD : D \ D' = discBd D) (hΔ : IsClosedDisc Δ)
    (hbdΔ : discBd Δ = A₀ ∪ F) (hA₀ : A₀ ⊆ discBd D) :
    ∃ A W : Set S, IsOpen W ∧ p ∈ W ∧ IsPreconnected A ∧ Disjoint A Γ.U ∧
      (∀ x ∈ W, x ∈ D' → x ∈ Δ → x ∉ Γ.U → x ∈ A) ∧
      (∀ x ∈ W, x ∈ e → x ∉ Y → x ∈ closure A) := by
  have hpbd : p ∈ discBd Δ := by rw [hbdΔ]; exact Or.inr hpF
  obtain ⟨A, W, hW, hpW, hconn, -, hAbd, hAY, hin, hcl⟩ :=
    exists_half_nbhd hΔ hY hpbd hpY
  refine ⟨A, W, hW, hpW, hconn, ?_, ?_, ?_⟩
  · refine disjoint_left.mpr fun x hxA hxU => ?_
    have hxY : x ∉ Y := disjoint_left.mp hAY hxA
    have hxe : x ∈ e := by
      by_contra hxe
      exact hxY (hYcover ⟨hxU, hxe⟩)
    refine disjoint_left.mp hAbd hxA ?_
    rw [hbdΔ]
    exact Or.inr (hFsub x hxe hxY)
  · intro x hxW hxD' hxΔ hxU
    refine hin ⟨⟨hxW, hxΔ⟩, ?_⟩
    rw [hbdΔ]
    rintro (h | h)
    · have hx' := hA₀ h
      rw [← hbdD] at hx'
      exact hx'.2 hxD'
    · exact hxU (hFU h)
  · intro x hxW hxe hxY
    refine hcl ⟨hxW, ?_⟩
    rw [hbdΔ]
    exact Or.inr (hFsub x hxe hxY)

/-- Two sides of an edge of a proper drawing on a closed disc space `S`. -/
theorem disc_exists_edge_sides (hS : IsClosedDiscSpace S) (Γ : Drawing S) (hprop : Γ.IsProper)
    {e : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e) :
    ∃ W A₁ A₂ : Set S, IsOpen W ∧ p ∈ W ∧ W ∩ Γ.U ⊆ e ∧ W \ Γ.U ⊆ A₁ ∪ A₂ ∧
      IsPreconnected A₁ ∧ IsPreconnected A₂ ∧ Disjoint A₁ Γ.U ∧ Disjoint A₂ Γ.U ∧
      e ∩ W ⊆ closure A₁ ∧ e ∩ W ⊆ closure A₂ := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
  have hX₀ := isClosed_U_sdiff_edge Γ he
  have hpX₀ : p ∉ Γ.U \ e := fun h => h.2 hp
  have hpbd : p ∉ bd S := fun hbd => (he.2.1 hp).2 (hprop ⟨hbd, (he.2.1 hp).1⟩)
  obtain ⟨D, D', hD, hD', hpD', hD'D, hDO, hbdD⟩ :=
    disc_exists_closedDisc_nbhd hS hX₀.isOpen_compl hpX₀ hpbd
  have hVout : ∀ x ∈ Γ.V, x ∉ D := fun x hx hxD =>
    hDO hxD ⟨Γ.V_subset_U hx, fun hxe => (he.2.1 hxe).2 hx⟩
  obtain ⟨t₀, ⟨ht₀0, ht₀1⟩, rfl⟩ : p ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hp
  obtain ⟨a, b, hat', htb', hIcc, hIoo, hFline, hFD, hFcap, hst⟩ :=
    GM11.exists_edge_piece_in_disc hD hD' hD'D hbdD hγ hinj
      (hVout _ hγ0) (hVout _ hγ1) hpD'
  let F := γ '' Icc a b
  have hFmem : ∀ x, x ∈ F ↔ ∃ t ∈ Icc a b, γ t = x := fun _ ↦ Iff.rfl
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, hΔ₂, hunion, -, hbd₁, hbd₂, -⟩ :=
    disc_iArc D F (γ a) (γ b) hD hFD hst hFline hFcap
  have hAsub : ∀ A ∈ componentsIn (discBd D \ {γ a, γ b}), A ⊆ discBd D := by
    rintro _ ⟨x, -, rfl⟩
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hA₁ : A₁ ⊆ discBd D := hAsub _ (by rw [hcomp]; simp)
  have hA₂ : A₂ ⊆ discBd D := hAsub _ (by rw [hcomp]; simp)
  have hFU : F ⊆ Γ.U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hFmem x).mp hx
    have hmem : γ t ∈ e := by rw [← hγe]; exact ⟨t, hIcc ht, rfl⟩
    exact (he.2.1 hmem).1
  let Y : Set S := D'ᶜ ∪ (Γ.U \ e) ∪ γ '' {t | t ≤ a ∨ b ≤ t}
  have hY : IsClosed Y := by
    refine (hD'.isClosed_compl.union hX₀).union ?_
    exact ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY : γ t₀ ∉ Y := by
    rintro ((h | h) | ⟨t, ht, hteq⟩)
    · exact h hpD'
    · exact h.2 hp
    · have hpV : t ∈ Ioo (0 : unitInterval) 1 := by
        refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ0)
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ1)
      have := hinj hpV ⟨ht₀0, ht₀1⟩ hteq
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr hat')
      · exact absurd h (not_le.mpr htb')
  have hpF : γ t₀ ∈ F := (hFmem _).mpr ⟨t₀, ⟨hat'.le, htb'.le⟩, rfl⟩
  have hFsub : ∀ x ∈ e, x ∉ Y → x ∈ F := by
    intro x hx hxY
    obtain ⟨t, -, rfl⟩ : x ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hx
    refine (hFmem _).mpr ⟨t, ?_, rfl⟩
    have hn : ¬ (t ≤ a ∨ b ≤ t) := fun h => hxY (Or.inr ⟨t, h, rfl⟩)
    push Not at hn
    exact ⟨hn.1.le, hn.2.le⟩
  have hYcover : Γ.U \ e ⊆ Y := fun _ h => Or.inl (Or.inr h)
  obtain ⟨S₁, W₁, hW₁, hpW₁, hconn₁, hdis₁, hin₁, hcl₁⟩ :=
    exists_edge_side_neighborhood hY hpY hpF hYcover hFU hFsub hbdD hΔ₁ hbd₁ hA₁
  obtain ⟨S₂, W₂, hW₂, hpW₂, hconn₂, hdis₂, hin₂, hcl₂⟩ :=
    exists_edge_side_neighborhood hY hpY hpF hYcover hFU hFsub hbdD hΔ₂ hbd₂ hA₂
  refine ⟨W₁ ∩ W₂ ∩ Yᶜ, S₁, S₂, (hW₁.inter hW₂).inter hY.isOpen_compl, ⟨⟨hpW₁, hpW₂⟩, hpY⟩,
    ?_, ?_, hconn₁, hconn₂, hdis₁, hdis₂, ?_, ?_⟩
  · rintro x ⟨⟨-, hxY⟩, hxU⟩
    by_contra hxe
    exact hxY (Or.inl (Or.inr ⟨hxU, hxe⟩))
  · rintro x ⟨⟨⟨hx₁, hx₂⟩, hxY⟩, hxU⟩
    have hxD' : x ∈ D' := by
      by_contra h
      exact hxY (Or.inl (Or.inl h))
    have hxD : x ∈ Δ₁ ∪ Δ₂ := by rw [hunion]; exact hD'D hxD'
    rcases hxD with h | h
    · exact Or.inl (hin₁ x hx₁ hxD' h hxU)
    · exact Or.inr (hin₂ x hx₂ hxD' h hxU)
  · rintro x ⟨hxe, ⟨hx₁, -⟩, hxY⟩
    exact hcl₁ x hx₁ hxe hxY
  · rintro x ⟨hxe, ⟨-, hx₂⟩, hxY⟩
    exact hcl₂ x hx₂ hxe hxY

/-- If a region of a proper drawing on `S` has a point of an edge `e` in its closure, then all of
`e` lies in its closure. -/
theorem disc_edge_subset_closure_of_incident (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e r : Set S} (he : e ∈ Γ.E) (hr : r ∈ Γ.R)
    (hinc : (e ∩ closure r).Nonempty) : e ⊆ closure r :=
  GM11.edge_subset_closure_of_local_sides
    (fun _ hp => disc_exists_edge_sides hS Γ hprop he hp) he hr hinc

/-- Every edge of a proper drawing on `S` is incident with a region. -/
theorem disc_exists_region_incident (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) :
    ∃ r ∈ Γ.R, e ⊆ closure r :=
  GM11.exists_region_incident_of_local_sides
    (fun _ hp => disc_exists_edge_sides hS Γ hprop he hp) he

/-- An edge of a proper drawing on `S` is incident with at most two regions. -/
theorem disc_region_incident_two (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e r₁ r₂ r₃ : Set S} (he : e ∈ Γ.E) (h₁ : r₁ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R)
    (h₃ : r₃ ∈ Γ.R) (i₁ : e ⊆ closure r₁) (i₂ : e ⊆ closure r₂) (i₃ : e ⊆ closure r₃) :
    r₁ = r₂ ∨ r₁ = r₃ ∨ r₂ = r₃ :=
  GM11.region_incident_two_of_local_sides
    (fun _ hp => disc_exists_edge_sides hS Γ hprop he hp) he h₁ h₂ h₃ i₁ i₂ i₃

/-- Either an edge of a proper drawing on `S` is incident with a region, or it misses the closure
of the region. -/
theorem disc_edge_incident_or_disjoint (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e r : Set S} (he : e ∈ Γ.E) (hr : r ∈ Γ.R) :
    e ⊆ closure r ∨ Disjoint e (closure r) := by
  by_cases h : (e ∩ closure r).Nonempty
  · exact Or.inl (disc_edge_subset_closure_of_incident hS hprop he hr h)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h))

/-- An open connected subset of a closed disc space `S` stays connected when finitely many points
are removed. -/
theorem disc_isPreconnected_sdiff_finite (hS : IsClosedDiscSpace S) {G F : Set S} (hG : IsOpen G)
    (hGc : IsPreconnected G) (hF : F.Finite) : IsPreconnected (G \ F) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  exact isPreconnected_sdiff_finite_of_punctured_nbhd
    (fun {_} hO {_} hx => disc_exists_punctured_nbhd hS hO hx) hG hGc hF

/-- A point in any nonempty open subset of `S` lies off `U(Γ)` for a proper drawing `Γ`. -/
theorem disc_exists_notMem_U (hS : IsClosedDiscSpace S) {Γ : Drawing S} (hprop : Γ.IsProper)
    {O : Set S} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y ∈ O, y ∉ Γ.U := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyO, hyV⟩ : ∃ y ∈ O, y ∉ Γ.V := by
    have hF : IsOpen (O ∩ (Γ.V \ {x})ᶜ) :=
      hO.inter (Γ.finite_V.subset sdiff_subset).isClosed.isOpen_compl
    obtain ⟨Z, -, -, hZsub, -, hZcl⟩ :=
      disc_exists_punctured_nbhd hS hF ⟨hx, fun h => h.2 rfl⟩
    obtain ⟨y, hy⟩ : (Z \ {x}).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      rw [hcon, closure_empty] at hZcl
      exact hZcl
    exact ⟨y, (hZsub hy.1).1, fun hyV => (hZsub hy.1).2 ⟨hyV, hy.2⟩⟩
  by_cases hyU : y ∈ Γ.U
  · obtain ⟨e, he, hye⟩ := Γ.exists_edge_of_mem hyU hyV
    obtain ⟨W, A₁, A₂, hW, hyW, -, -, -, -, d₁, -, c₁, -⟩ :=
      disc_exists_edge_sides hS Γ hprop he hye
    obtain ⟨a, ⟨haW, haO⟩, ha⟩ := mem_closure_iff.mp (c₁ ⟨hye, hyW⟩) _ (hW.inter hO) ⟨hyW, hyO⟩
    exact ⟨a, haO, disjoint_left.mp d₁ ha⟩
  · exact ⟨y, hyO, hyU⟩

/-- Deleting an edge from a proper drawing on `S` preserves properness. -/
theorem deleteEdge_isProper {Γ : Drawing S} [T2Space S] (hprop : Γ.IsProper) (e : Set S) :
    (Γ.deleteEdge e).IsProper := by
  have hsub := deleteEdge_isSubdrawing Γ e
  rintro x ⟨hxbd, hxU⟩
  rw [deleteEdge_V]
  exact hprop ⟨hxbd, hsub.U_subset hxU⟩

/-- Closed-disc version of Graph Minors XI, (5.1): if `Γ' ⊆ Γ` is a subdrawing of a proper drawing
`Γ` on a closed disc space `S`, `r' ∈ Γ'.R`, and `r₁ ∈ Z`, `r₂ ∈ Γ.R \ Z` satisfy `r₁, r₂ ⊆ r'`,
then there is an edge `e ∈ Γ.E \ Γ'.E` incident with a region in `Z` and a region outside `Z` inside
`r'`. -/
theorem disc_theorem_5_1 (hS : IsClosedDiscSpace S) {Γ Γ' : Drawing S} (hprop : Γ.IsProper)
    (hsub : Γ'.IsSubdrawing Γ) {Z : Set (Set S)}
    {r' r₁ r₂ : Set S} (hr' : r' ∈ Γ'.R) (h₁ : r₁ ∈ Γ.R) (hz₁ : r₁ ∈ Z) (h₂ : r₂ ∈ Γ.R)
    (hz₂ : r₂ ∉ Z) (hs₁ : r₁ ⊆ r') (hs₂ : r₂ ⊆ r') :
    ∃ e ∈ Γ.E, e ∉ Γ'.E ∧ ∃ a b : Set S, a ∈ Z ∧ b ∉ Z ∧ a ⊆ r' ∧ b ⊆ r' ∧
      Γ.EdgeRegionIncident e a ∧ Γ.EdgeRegionIncident e b := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  exact exists_separating_region_edge Drawing.IsProper
    (fun {_} hp e => deleteEdge_isProper hp e)
    (fun {_} hp {_ _} he hr => disc_edge_incident_or_disjoint hS hp he hr)
    (fun {G} hp {_} he {_} hx => disc_exists_edge_sides hS G hp he hx)
    (disc_isPreconnected_sdiff_finite hS) hprop hsub hr' h₁ hz₁ h₂ hz₂ hs₁ hs₂

/-- A proper drawing on a closed disc space `S` has finitely many regions. -/
theorem disc_finite_R (hS : IsClosedDiscSpace S) (Γ : Drawing S) (hprop : Γ.IsProper) :
    Γ.R.Finite := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected
      ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ.surjective.connectedSpace φ.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ⟩
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    by_cases hE : Γ.E.Nonempty
    · obtain ⟨e, he⟩ := hE
      have hlt : (Γ.deleteEdge e).E.ncard < n := by
        rw [deleteEdge_E, ← hn]
        exact ncard_sdiff_singleton_lt_of_mem he Γ.finite_edges
      have h₁ := ih _ hlt (Γ.deleteEdge e) (deleteEdge_isProper hprop e) rfl
      have h₂ : {r ∈ Γ.R | e ⊆ closure r}.Finite := by
        by_contra hinf
        obtain ⟨T, hT, hcard⟩ := (Set.not_finite.mp hinf |> Set.Infinite.exists_subset_ncard_eq) 3
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp hcard.2
        have ha := hT (show a ∈ _ by simp)
        have hb := hT (show b ∈ _ by simp)
        have hc := hT (show c ∈ _ by simp)
        rcases disc_region_incident_two hS hprop he ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 with h | h | h
        · exact hab h
        · exact hac h
        · exact hbc h
      refine (h₁.union h₂).subset fun r hr => ?_
      rcases disc_edge_incident_or_disjoint hS hprop he hr with h | h
      · exact Or.inr ⟨hr, h⟩
      · exact Or.inl (region_deleteEdge_of_not_incident he hr h)
    · have hU : Γ.U = Γ.V := by
        rw [Γ.U_eq, not_nonempty_iff_eq_empty.mp hE]
        simp
      have hc : IsPreconnected (univ \ Γ.U) := by
        rw [hU]
        exact disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ Γ.finite_V
      refine Set.Subsingleton.finite fun r₁ h₁ r₂ h₂ => ?_
      obtain ⟨x, hx⟩ := region_nonempty h₁
      obtain ⟨y, hy⟩ := region_nonempty h₂
      refine region_eq_of_mem h₁ h₂ (subset_region h₁ hc ?_ ⟨mem_univ _, region_subset h₁ hx⟩ hx
        ⟨mem_univ _, region_subset h₂ hy⟩) hy
      exact disjoint_left.mpr fun q hq => hq.2

/-- A subdrawing `Γ' ⊆ Γ` of a proper drawing `Γ` on `S` has at most as many regions as `Γ`. -/
theorem disc_region_ncard_le_of_isSubdrawing (hS : IsClosedDiscSpace S) {Γ Γ' : Drawing S}
    (hprop : Γ.IsProper) (hsub : Γ'.IsSubdrawing Γ) :
    Γ'.R.ncard ≤ Γ.R.ncard := by
  classical
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have hfin : Γ.R.Finite := disc_finite_R hS Γ hprop
  let f : Set S → Set S := fun r =>
    if hr : r.Nonempty then connectedComponentIn (univ \ Γ'.U) hr.some else ∅
  have hf_surj : Γ'.R ⊆ f '' Γ.R := by
    intro r' hr'
    obtain ⟨z, hz, hzU⟩ := disc_exists_notMem_U hS hprop (region_isOpen hr') (region_nonempty hr')
    obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
    refine ⟨r, hr, ?_⟩
    have hr_ne : r.Nonempty := ⟨z, hzr⟩
    dsimp only [f]
    simp only [hr_ne, ↓reduceDIte]
    have hsub_r : r ⊆ r' := subset_region hr' (region_isPreconnected hr)
      (disjoint_left.mpr fun y hy h => region_subset hr hy (hsub.U_subset h)) hzr hz
    have hx_r' : hr_ne.some ∈ r' := hsub_r hr_ne.some_mem
    obtain ⟨x₀, -, rfl⟩ := (mem_R_iff Γ').mp hr'
    exact (connectedComponentIn_eq hx_r').symm
  exact (Set.ncard_le_ncard hf_surj (hfin.image f)).trans (Set.ncard_image_le hfin)

/-! ## 2. One-Way Duality and Proof of Theorem (3.1) -/

/-- `IsClosedDiscSpace S` implies `IsClosedDisc (univ : Set S)`. -/
theorem IsClosedDiscSpace.isClosedDisc_univ (hS : IsClosedDiscSpace S) :
    IsClosedDisc (univ : Set S) := by
  obtain ⟨φ⟩ := hS
  exact ⟨φ.trans (Homeomorph.Set.univ S).symm⟩

/-- `discBd (univ : Set S) = bd S`. -/
theorem discBd_univ (S : Type u) [TopologicalSpace S] :
    discBd (univ : Set S) = bd S :=
  image_bd_homeomorph (Homeomorph.Set.univ S)

/-- For a closed disc space `S`, `bd S` is an `O`-arc. -/
theorem IsClosedDiscSpace.isOArc_bd (hS : IsClosedDiscSpace S) : IsOArc (bd S) := by
  rw [← discBd_univ]
  exact hS.isClosedDisc_univ.isOArc_discBd

/-- Symmetry of `IsDualPointSet` on any `O`-arc `C`. -/
theorem isDualPointSet_symm {C V U : Set S} (hC : IsOArc C) (hV : V.Finite) (hV_sub : V ⊆ C)
    (hU : IsDualPointSet C V U) : IsDualPointSet C U V := by
  obtain ⟨φ⟩ := hC
  have hU_sub : U ⊆ C := (isDualPointSet_subset_diff hU).trans sdiff_subset
  have hV_eq : oArcMap φ '' (oArcMap φ ⁻¹' V) = V :=
    image_preimage_eq_of_subset (hV_sub.trans (range_oArcMap φ).symm.subset)
  have hU_eq : oArcMap φ '' (oArcMap φ ⁻¹' U) = U :=
    image_preimage_eq_of_subset (hU_sub.trans (range_oArcMap φ).symm.subset)
  have hV₀ : (oArcMap φ ⁻¹' V).Finite :=
    Finite.of_finite_image (by rwa [hV_eq]) (injective_oArcMap φ).injOn
  rw [← hV_eq, ← hU_eq, isDualPointSet_oArcMap_iff] at hU ⊢
  exact isDualPointSet_univ_symm hV₀ hU

/-- Every edge `e ∈ Γ.E` has a parameterization `γ : unitInterval → S` with `closure e = range γ`
and `Γ.toGraph.IsLink e (γ 0) (γ 1)`. -/
theorem exists_edge_param_isLink [T2Space S] (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) :
    ∃ γ : unitInterval → S, Continuous γ ∧ γ 0 ∈ Γ.V ∧ γ 1 ∈ Γ.V ∧
      InjOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 = e ∧ closure e = range γ ∧
      Γ.toGraph.IsLink e (γ 0) (γ 1) := by
  obtain ⟨γ, hγ, h0, h1, hinj, himg⟩ := exists_edge_param Γ he
  have hrange : range γ = e ∪ {γ 0, γ 1} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      by_cases ht0 : t = 0
      · subst ht0; exact Or.inr (Or.inl rfl)
      · by_cases ht1 : t = 1
        · subst ht1; exact Or.inr (Or.inr rfl)
        · left
          rw [← himg]
          exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
            unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩
    · rintro (hxe | rfl | rfl)
      · rw [← himg] at hxe
        obtain ⟨t, -, rfl⟩ := hxe
        exact mem_range_self t
      · exact mem_range_self 0
      · exact mem_range_self 1
  have hcl : closure e = range γ := by
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ (isCompact_range hγ).isClosed
      rw [hrange]
      exact subset_union_left
    · rintro _ ⟨t, rfl⟩
      have ht_cl : t ∈ closure (Ioo (0 : unitInterval) 1) := by
        rw [closure_Ioo (zero_ne_one : (0 : unitInterval) ≠ 1)]
        exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩
      rw [← himg]
      exact image_closure_subset_closure_image hγ ⟨t, ht_cl, rfl⟩
  refine ⟨γ, hγ, h0, h1, hinj, himg, hcl, he, h0, h1, ?_⟩
  rw [hcl, hrange]
  ext x
  simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxe | rfl | rfl, hxV⟩
    · exact ((he.2.1 hxe).2 hxV).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), h0⟩
    · exact ⟨Or.inr (Or.inr rfl), h1⟩

/-- If `IsDiscDualDrawing G G_dual`, then `G.V` is disjoint from `G_dual.U`. -/
theorem IsDiscDualDrawing.disjoint_V_dual_U {G G_dual : Drawing S}
    (hDual : IsDiscDualDrawing G G_dual) : Disjoint G.V G_dual.U := by
  refine disjoint_left.mpr fun v hv hvU => ?_
  by_cases hvVd : v ∈ G_dual.V
  · obtain ⟨r, hr, hvr⟩ := hDual.2.2.2.1 v hvVd
    exact region_subset hr hvr (G.V_subset_U hv)
  · obtain ⟨e', he', hve'⟩ := G_dual.exists_edge_of_mem hvU hvVd
    obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
    let e := edgeEquiv.symm ⟨e', he'⟩
    have he_eq : (edgeEquiv e).1 = e' := congrArg Subtype.val (edgeEquiv.apply_symm_apply ⟨e', he'⟩)
    have hmem : v ∈ (edgeEquiv e).1 ∩ G.U := ⟨he_eq ▸ hve', G.V_subset_U hv⟩
    rw [(hedge e).1] at hmem
    exact (e.2.2.1 hmem.2).2 hv

/-- If `IsDiscDualDrawing G G_dual`, then `G.V ∩ G_dual.V = ∅`. -/
theorem IsDiscDualDrawing.V_inter_dual_V_eq_empty {G G_dual : Drawing S}
    (hDual : IsDiscDualDrawing G G_dual) : G.V ∩ G_dual.V = ∅ := by
  ext v
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hv hvVd
  exact disjoint_left.mp hDual.disjoint_V_dual_U hv (G_dual.V_subset_U hvVd)

/-- For every `v ∈ G.V`, `connectedComponentIn (univ \ G_dual.U) v` is a region of `G_dual`
containing `v`. -/
theorem IsDiscDualDrawing.connectedComponentIn_mem_dual_R {G G_dual : Drawing S}
    (hDual : IsDiscDualDrawing G G_dual) {v : S} (hv : v ∈ G.V) :
    connectedComponentIn (univ \ G_dual.U) v ∈ G_dual.R ∧
      v ∈ connectedComponentIn (univ \ G_dual.U) v := by
  have hv_compl : v ∈ univ \ G_dual.U :=
    ⟨mem_univ v, disjoint_left.mp hDual.disjoint_V_dual_U hv⟩
  exact ⟨⟨v, hv_compl, rfl⟩, mem_connectedComponentIn hv_compl⟩

/-- Each primal edge `e ∈ G.E` is split by its dual edge `e' ∈ G_dual.E` into two half-edges
lying in the dual regions of the ends `u, v ∈ G.V` of `e`, and `e'` is incident in `G_dual` with
precisely those two dual regions. -/
theorem IsDiscDualDrawing.edge_half_regions (hS : IsClosedDiscSpace S) {G G_dual : Drawing S}
    (hDual : IsDiscDualDrawing G G_dual) {e e' : Set S} (he : e ∈ G.E) (he' : e' ∈ G_dual.E)
    (he2 : e ∩ G_dual.U = e ∩ e') (he3 : (e' ∩ e).ncard = 1)
    (he4 : ∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident e' r' → (r' ∩ e).Nonempty) :
    (∃ u ∈ G.V, ∃ v ∈ G.V,
      G.toGraph.IsLink e u v ∧
      e \ G_dual.U ⊆ connectedComponentIn (univ \ G_dual.U) u ∪
        connectedComponentIn (univ \ G_dual.U) v ∧
      G_dual.EdgeRegionIncident e' (connectedComponentIn (univ \ G_dual.U) u) ∧
      G_dual.EdgeRegionIncident e' (connectedComponentIn (univ \ G_dual.U) v) ∧
      ∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident e' r' →
        r' = connectedComponentIn (univ \ G_dual.U) u ∨
        r' = connectedComponentIn (univ \ G_dual.U) v) ∧
    (∀ r₁' ∈ G_dual.R, ∀ r₂' ∈ G_dual.R, ∀ v₁ ∈ r₁' ∩ G.V, ∀ v₂ ∈ r₂' ∩ G.V,
      G.toGraph.IsLink e v₁ v₂ ↔
        G_dual.EdgeRegionIncident e' r₁' ∧ G_dual.EdgeRegionIncident e' r₂' ∧
        ∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident e' r' → r' = r₁' ∨ r' = r₂') := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨γ, hγ, h0, h1, hinj, himg, _, hlink⟩ := exists_edge_param_isLink G he
  obtain ⟨p, hp_eq⟩ := ncard_eq_one.mp he3
  have hp_mem : p ∈ e' ∩ e := by rw [hp_eq]; exact mem_singleton p
  have hp_e' : p ∈ e' := hp_mem.1
  have hp_e : p ∈ e := hp_mem.2
  have he_GdU : e ∩ G_dual.U = {p} := by rw [he2, inter_comm, hp_eq]
  rw [← himg] at hp_e
  obtain ⟨t₀, ht₀, rfl⟩ := hp_e
  let u := γ 0
  let v := γ 1
  have hIco_sub : γ '' Ico 0 t₀ ⊆ univ \ G_dual.U := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨mem_univ _, fun htU => ?_⟩
    by_cases ht0 : t = 0
    · subst ht0
      exact disjoint_left.mp hDual.disjoint_V_dual_U h0 htU
    · have ht_Ioo : t ∈ Ioo (0 : unitInterval) 1 :=
        ⟨unitInterval.pos_iff_ne_zero.mpr ht0, ht.2.trans ht₀.2⟩
      have hmem : γ t ∈ e ∩ G_dual.U := ⟨himg ▸ mem_image_of_mem γ ht_Ioo, htU⟩
      rw [he_GdU, mem_singleton_iff] at hmem
      exact ht.2.ne (hinj ht_Ioo ht₀ hmem)
  have hIco_comp : γ '' Ico 0 t₀ ⊆ connectedComponentIn (univ \ G_dual.U) u :=
    (isPreconnected_Ico.image γ hγ.continuousOn).subset_connectedComponentIn
      ⟨0, left_mem_Ico.mpr ht₀.1, rfl⟩ hIco_sub
  have hp_cl_u : γ t₀ ∈ closure (connectedComponentIn (univ \ G_dual.U) u) :=
    closure_mono hIco_comp (image_closure_subset_closure_image hγ
      ⟨t₀, by rw [closure_Ico ht₀.1.ne]; exact ⟨ht₀.1.le, le_rfl⟩, rfl⟩)
  have hinc_u : G_dual.EdgeRegionIncident e' (connectedComponentIn (univ \ G_dual.U) u) :=
    ⟨he', (hDual.connectedComponentIn_mem_dual_R h0).1, γ t₀, hp_e', hp_cl_u⟩
  have hIoc_sub : γ '' Ioc t₀ 1 ⊆ univ \ G_dual.U := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨mem_univ _, fun htU => ?_⟩
    by_cases ht1 : t = 1
    · subst ht1
      exact disjoint_left.mp hDual.disjoint_V_dual_U h1 htU
    · have ht_Ioo : t ∈ Ioo (0 : unitInterval) 1 :=
        ⟨ht₀.1.trans ht.1, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
      have hmem : γ t ∈ e ∩ G_dual.U := ⟨himg ▸ mem_image_of_mem γ ht_Ioo, htU⟩
      rw [he_GdU, mem_singleton_iff] at hmem
      exact ht.1.ne' (hinj ht_Ioo ht₀ hmem)
  have hIoc_comp : γ '' Ioc t₀ 1 ⊆ connectedComponentIn (univ \ G_dual.U) v :=
    (isPreconnected_Ioc.image γ hγ.continuousOn).subset_connectedComponentIn
      ⟨1, right_mem_Ioc.mpr ht₀.2, rfl⟩ hIoc_sub
  have hp_cl_v : γ t₀ ∈ closure (connectedComponentIn (univ \ G_dual.U) v) :=
    closure_mono hIoc_comp (image_closure_subset_closure_image hγ
      ⟨t₀, by rw [closure_Ioc ht₀.2.ne]; exact ⟨le_rfl, ht₀.2.le⟩, rfl⟩)
  have hinc_v : G_dual.EdgeRegionIncident e' (connectedComponentIn (univ \ G_dual.U) v) :=
    ⟨he', (hDual.connectedComponentIn_mem_dual_R h1).1, γ t₀, hp_e', hp_cl_v⟩
  have he_diff_sub : e \ G_dual.U ⊆
      connectedComponentIn (univ \ G_dual.U) u ∪ connectedComponentIn (univ \ G_dual.U) v := by
    rintro x ⟨hxe, hxU⟩
    rw [← himg] at hxe
    obtain ⟨t, ht, rfl⟩ := hxe
    have hne : t ≠ t₀ := fun h => hxU (h ▸ (he'.2.1 hp_e').1)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hIco_comp ⟨t, ⟨unitInterval.nonneg t, hlt⟩, rfl⟩)
    · exact Or.inr (hIoc_comp ⟨t, ⟨hgt, unitInterval.le_one t⟩, rfl⟩)
  have hall_r' : ∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident e' r' →
      r' = connectedComponentIn (univ \ G_dual.U) u ∨
      r' = connectedComponentIn (univ \ G_dual.U) v := by
    intro r' hr' hinc
    obtain ⟨x, hx_r', hx_e⟩ := he4 r' hr' hinc
    have hx_diff : x ∈ e \ G_dual.U := ⟨hx_e, region_subset hr' hx_r'⟩
    rcases he_diff_sub hx_diff with hxu | hxv
    · exact Or.inl (region_eq_of_mem hr' (hDual.connectedComponentIn_mem_dual_R h0).1 hx_r' hxu)
    · exact Or.inr (region_eq_of_mem hr' (hDual.connectedComponentIn_mem_dual_R h1).1 hx_r' hxv)
  refine ⟨⟨u, h0, v, h1, hlink, he_diff_sub, hinc_u, hinc_v, hall_r'⟩, ?_⟩
  intro r₁' hr₁' r₂' hr₂' v₁ hv₁ v₂ hv₂
  have hr₁_eq : r₁' = connectedComponentIn (univ \ G_dual.U) v₁ := by
    obtain ⟨z, -, rfl⟩ := (mem_R_iff G_dual).mp hr₁'
    exact connectedComponentIn_eq hv₁.1
  have hr₂_eq : r₂' = connectedComponentIn (univ \ G_dual.U) v₂ := by
    obtain ⟨z, -, rfl⟩ := (mem_R_iff G_dual).mp hr₂'
    exact connectedComponentIn_eq hv₂.1
  constructor
  · intro hlink'
    have hpair : ({v₁, v₂} : Set S) = {u, v} := hlink'.2.2.2.symm.trans hlink.2.2.2
    have hv₁_mem : v₁ = u ∨ v₁ = v := by
      have : v₁ ∈ ({v₁, v₂} : Set S) := mem_insert v₁ {v₂}
      rwa [hpair, mem_insert_iff, mem_singleton_iff] at this
    have hv₂_mem : v₂ = u ∨ v₂ = v := by
      have : v₂ ∈ ({v₁, v₂} : Set S) := mem_insert_of_mem v₁ (mem_singleton v₂)
      rwa [hpair, mem_insert_iff, mem_singleton_iff] at this
    have hu_mem : u = v₁ ∨ u = v₂ := by
      have : u ∈ ({u, v} : Set S) := mem_insert u {v}
      rwa [← hpair, mem_insert_iff, mem_singleton_iff] at this
    have hv_mem : v = v₁ ∨ v = v₂ := by
      have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u (mem_singleton v)
      rwa [← hpair, mem_insert_iff, mem_singleton_iff] at this
    refine ⟨?_, ?_, fun r' hr' hinc => ?_⟩
    · rw [hr₁_eq]
      rcases hv₁_mem with rfl | rfl <;> assumption
    · rw [hr₂_eq]
      rcases hv₂_mem with rfl | rfl <;> assumption
    · rcases hall_r' r' hr' hinc with rfl | rfl
      · rcases hu_mem with rfl | rfl
        · exact Or.inl hr₁_eq.symm
        · exact Or.inr hr₂_eq.symm
      · rcases hv_mem with rfl | rfl
        · exact Or.inl hr₁_eq.symm
        · exact Or.inr hr₂_eq.symm
  · rintro ⟨hinc1, hinc2, hall⟩
    have hv₁_uv : v₁ = u ∨ v₁ = v := by
      rcases hall_r' r₁' hr₁' hinc1 with heq | heq
      · exact Or.inl (hDual.2.2.2.2.2.1 v₁ hv₁.2 u h0 (hr₁_eq.symm.trans heq))
      · exact Or.inr (hDual.2.2.2.2.2.1 v₁ hv₁.2 v h1 (hr₁_eq.symm.trans heq))
    have hv₂_uv : v₂ = u ∨ v₂ = v := by
      rcases hall_r' r₂' hr₂' hinc2 with heq | heq
      · exact Or.inl (hDual.2.2.2.2.2.1 v₂ hv₂.2 u h0 (hr₂_eq.symm.trans heq))
      · exact Or.inr (hDual.2.2.2.2.2.1 v₂ hv₂.2 v h1 (hr₂_eq.symm.trans heq))
    have hu_12 : u = v₁ ∨ u = v₂ := by
      rcases hall _ (hDual.connectedComponentIn_mem_dual_R h0).1 hinc_u with heq | heq
      · exact Or.inl (hDual.2.2.2.2.2.1 u h0 v₁ hv₁.2 (heq.trans hr₁_eq))
      · exact Or.inr (hDual.2.2.2.2.2.1 u h0 v₂ hv₂.2 (heq.trans hr₂_eq))
    have hv_12 : v = v₁ ∨ v = v₂ := by
      rcases hall _ (hDual.connectedComponentIn_mem_dual_R h1).1 hinc_v with heq | heq
      · exact Or.inl (hDual.2.2.2.2.2.1 v h1 v₁ hv₁.2 (heq.trans hr₁_eq))
      · exact Or.inr (hDual.2.2.2.2.2.1 v h1 v₂ hv₂.2 (heq.trans hr₂_eq))
    refine ⟨he, hv₁.2, hv₂.2, ?_⟩
    rw [hlink.2.2.2]
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact hu_12
      · exact hv_12
    · rintro (rfl | rfl)
      · exact hv₁_uv
      · exact hv₂_uv

/-- If `A` is preconnected, `B` is open, `(A ∩ B).Nonempty`, and `A` is disjoint from
`closure B \ B`, then `A ⊆ B`. -/
private theorem subset_of_isPreconnected_of_inter_open {A B : Set S}
    (hA : IsPreconnected A) (hB : IsOpen B) (hAB : (A ∩ B).Nonempty)
    (hfront : Disjoint A (closure B \ B)) : A ⊆ B := by
  intro x hx
  by_contra hxB
  by_cases hxcl : x ∈ closure B
  · exact disjoint_left.mp hfront hx ⟨hxcl, hxB⟩
  · obtain ⟨w, hwA, hwB, hwcl⟩ := hA B (closure B)ᶜ hB isClosed_closure.isOpen_compl
      (fun y hy => by
        by_cases hyB : y ∈ B
        · exact Or.inl hyB
        · exact Or.inr fun hycl => disjoint_left.mp hfront hy ⟨hycl, hyB⟩)
      hAB ⟨x, hx, hxcl⟩
    exact hwcl (subset_closure hwB)

/-- For any region `r ∈ Γ.R` on a locally path-connected space `S`, `closure r \ r ⊆ Γ.U`. -/
private theorem closure_region_sdiff_subset_U [LocallyPathConnectedSpace S]
    {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R) :
    closure r \ r ⊆ Γ.U := by
  rintro y ⟨hy_cl, hy_not_r⟩
  by_contra hyU
  obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem hyU
  obtain ⟨w, hwr', hwr⟩ := mem_closure_iff.mp hy_cl r' (region_isOpen hr') hyr'
  exact hy_not_r (region_eq_of_mem hr' hr hwr' hwr ▸ hyr')

/-- Every region `r_dual ∈ G_dual.R` contains a unique vertex `v ∈ G.V` when `G` is connected. -/
theorem IsDiscDualDrawing.exists_unique_vertex_in_dual_region (hS : IsClosedDiscSpace S)
    {G G_dual : Drawing S} (hConn : IsGraphConnected G.toGraph)
    (hDual : IsDiscDualDrawing G G_dual) {r_dual : Set S} (hr_dual : r_dual ∈ G_dual.R) :
    ∃! v, v ∈ r_dual ∧ v ∈ G.V := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected
      ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ.surjective.connectedSpace φ.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ⟩
  have huniq : ∀ v₁ v₂, v₁ ∈ r_dual ∧ v₁ ∈ G.V → v₂ ∈ r_dual ∧ v₂ ∈ G.V → v₁ = v₂ := by
    rintro v₁ v₂ ⟨hv₁_r, hv₁_V⟩ ⟨hv₂_r, hv₂_V⟩
    obtain ⟨z, -, rfl⟩ := (mem_R_iff G_dual).mp hr_dual
    have h1 : connectedComponentIn (univ \ G_dual.U) v₁ = connectedComponentIn (univ \ G_dual.U) z
      :=
      (connectedComponentIn_eq hv₁_r).symm
    have h2 : connectedComponentIn (univ \ G_dual.U) v₂ = connectedComponentIn (univ \ G_dual.U) z
      :=
      (connectedComponentIn_eq hv₂_r).symm
    exact hDual.2.2.2.2.2.1 v₁ hv₁_V v₂ hv₂_V (h1.trans h2.symm)
  by_cases hex : ∃ e' ∈ G_dual.E, G_dual.EdgeRegionIncident e' r_dual
  · obtain ⟨e', he', hinc⟩ := hex
    obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
    let e := edgeEquiv.symm ⟨e', he'⟩
    have he_eq : (edgeEquiv e).1 = e' := congrArg Subtype.val (edgeEquiv.apply_symm_apply ⟨e', he'⟩)
    obtain ⟨he1, he2, he3, he4, _⟩ := hedge e
    rw [he_eq] at he1 he2 he3 he4
    obtain ⟨⟨u, hu, v, hv, _, _, _, _, hall⟩, _⟩ :=
      hDual.edge_half_regions hS e.2 he' he2 he3 he4
    rcases hall r_dual hr_dual hinc with rfl | rfl
    · exact ⟨u, ⟨(hDual.connectedComponentIn_mem_dual_R hu).2, hu⟩,
        fun y hy => huniq y u hy ⟨(hDual.connectedComponentIn_mem_dual_R hu).2, hu⟩⟩
    · exact ⟨v, ⟨(hDual.connectedComponentIn_mem_dual_R hv).2, hv⟩,
        fun y hy => huniq y v hy ⟨(hDual.connectedComponentIn_mem_dual_R hv).2, hv⟩⟩
  · have hsub_all : univ \ G_dual.V ⊆ r_dual := by
      refine subset_of_isPreconnected_of_inter_open
        (disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ G_dual.finite_V)
        (region_isOpen hr_dual) ?_ ?_
      · obtain ⟨x₀, hx₀⟩ := region_nonempty hr_dual
        exact ⟨x₀, ⟨mem_univ x₀, fun hxV => region_subset hr_dual hx₀ (G_dual.V_subset_U hxV)⟩, hx₀⟩
      · refine disjoint_left.mpr fun y hy hfront => ?_
        have hyU : y ∈ G_dual.U := closure_region_sdiff_subset_U hr_dual hfront
        obtain ⟨e', he', hye'⟩ := G_dual.exists_edge_of_mem hyU hy.2
        exact hex ⟨e', he', he', hr_dual, y, hye', hfront.1⟩
    obtain ⟨v₀, hv₀⟩ := hConn.1
    have hv₀_r : v₀ ∈ r_dual := hsub_all ⟨mem_univ v₀,
      fun hvVd => disjoint_left.mp hDual.disjoint_V_dual_U hv₀ (G_dual.V_subset_U hvVd)⟩
    exact ⟨v₀, ⟨hv₀_r, hv₀⟩, fun y hy => huniq y v₀ hy ⟨hv₀_r, hv₀⟩⟩

/-- **Graph Minors VI, (3.1)**: if `G` is connected and properly drawn on a closed disc `S` and
`IsDiscDualDrawing G G_dual`, then `IsDiscDualDrawing G_dual G`. -/
theorem IsDiscDualDrawing.symm_of_connected (hS : IsClosedDiscSpace S) {G G_dual : Drawing S}
    (hConn : IsGraphConnected G.toGraph) (hDual : IsDiscDualDrawing G G_dual) :
    IsDiscDualDrawing G_dual G := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
  refine ⟨hDual.2.1, hDual.1,
    fun r_dual hr_dual => hDual.exists_unique_vertex_in_dual_region hS hConn hr_dual,
    fun v hv => ⟨_, (hDual.connectedComponentIn_mem_dual_R hv).1,
      (hDual.connectedComponentIn_mem_dual_R hv).2⟩,
    isDualPointSet_symm hS.isOArc_bd (G.finite_V.subset inter_subset_left)
      inter_subset_right hDual.2.2.2.2.1,
    ?_, edgeEquiv.symm, ?_⟩
  · intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨r₁, hr₁, hw₁_r⟩ := hDual.2.2.2.1 w₁ hw₁
    obtain ⟨r₂, hr₂, hw₂_r⟩ := hDual.2.2.2.1 w₂ hw₂
    have hr₁_eq : r₁ = connectedComponentIn (univ \ G.U) w₁ := by
      obtain ⟨z, -, rfl⟩ := (mem_R_iff G).mp hr₁
      exact connectedComponentIn_eq hw₁_r
    have hr₂_eq : r₂ = connectedComponentIn (univ \ G.U) w₂ := by
      obtain ⟨z, -, rfl⟩ := (mem_R_iff G).mp hr₂
      exact connectedComponentIn_eq hw₂_r
    have hw₂_r₁ : w₂ ∈ r₁ := by
      rw [hr₁_eq, heq, ← hr₂_eq]
      exact hw₂_r
    exact (hDual.2.2.1 r₁ hr₁).unique ⟨hw₁_r, hw₁⟩ ⟨hw₂_r₁, hw₂⟩
  · intro e'
    let e := edgeEquiv.symm e'
    have he_eq : edgeEquiv e = e' := edgeEquiv.apply_symm_apply e'
    obtain ⟨he1, he2, he3, he4, he5⟩ := hedge e
    rw [he_eq] at he1 he2 he3 he4 he5
    refine ⟨he2, he1, by rw [inter_comm, he3], ?_,
      (hDual.edge_half_regions hS e.2 e'.2 he2 he3 he4).2⟩
    intro r hr hinc
    obtain ⟨γ', hγ', h0', h1', _, _, hcl', hlink'⟩ := exists_edge_param_isLink G_dual e'.2
    obtain ⟨r₁, hr₁, hw₁⟩ := hDual.2.2.2.1 (γ' 0) h0'
    obtain ⟨r₂, hr₂, hw₂⟩ := hDual.2.2.2.1 (γ' 1) h1'
    have hall := ((he5 r₁ hr₁ r₂ hr₂ (γ' 0) ⟨hw₁, h0'⟩ (γ' 1) ⟨hw₂, h1'⟩).mp hlink').2.2
    rcases hall r hr hinc with hr_eq | hr_eq
    · subst hr_eq
      have h0_cl : γ' 0 ∈ closure e'.1 := by rw [hcl']; exact mem_range_self 0
      exact mem_closure_iff.mp h0_cl r (region_isOpen hr) hw₁
    · subst hr_eq
      have h1_cl : γ' 1 ∈ closure e'.1 := by rw [hcl']; exact mem_range_self 1
      exact mem_closure_iff.mp h1_cl r (region_isOpen hr) hw₂

/-- One-way vertex-region incidence transposition: if `w ∈ closure r_dual`, then `v ∈ closure r`. -/
theorem IsDiscDualDrawing.mem_closure_region_of_mem_closure_dual (hS : IsClosedDiscSpace S)
    {G G_dual : Drawing S} (hDual : IsDiscDualDrawing G G_dual)
    {v : S} (hv : v ∈ G.V) {r : Set S} (hr : r ∈ G.R) {w : S} (hw : w ∈ r ∩ G_dual.V)
    {r_dual : Set S} (hr_dual : r_dual ∈ G_dual.R) (hv_rd : v ∈ r_dual)
    (hw_cl : w ∈ closure r_dual) : v ∈ closure r := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have h_inter : (r_dual ∩ r).Nonempty := by
    rw [inter_comm]
    exact mem_closure_iff.mp hw_cl r (region_isOpen hr) hw.1
  have h_not_sub : ¬ (r_dual ⊆ r) := fun hsub =>
    region_subset hr (hsub hv_rd) (G.V_subset_U hv)
  have h_not_disj : ¬ Disjoint r_dual (closure r \ r) := fun hdisj =>
    h_not_sub (subset_of_isPreconnected_of_inter_open (region_isPreconnected hr_dual)
      (region_isOpen hr) h_inter hdisj)
  rw [not_disjoint_iff] at h_not_disj
  obtain ⟨z, hz_rd, hz_cl, hz_not_r⟩ := h_not_disj
  have hz_U : z ∈ G.U := closure_region_sdiff_subset_U hr ⟨hz_cl, hz_not_r⟩
  have hrd_eq : r_dual = connectedComponentIn (univ \ G_dual.U) v := by
    obtain ⟨x₀, -, rfl⟩ := (mem_R_iff G_dual).mp hr_dual
    exact connectedComponentIn_eq hv_rd
  by_cases hzV : z ∈ G.V
  · have hzv : z = v := by
      have hz_eq : r_dual = connectedComponentIn (univ \ G_dual.U) z := by
        obtain ⟨x₀, -, rfl⟩ := (mem_R_iff G_dual).mp hr_dual
        exact connectedComponentIn_eq hz_rd
      exact hDual.2.2.2.2.2.1 z hzV v hv (hz_eq.symm.trans hrd_eq)
    exact hzv ▸ hz_cl
  · obtain ⟨e₀, he₀, hze₀⟩ := G.exists_edge_of_mem hz_U hzV
    have he₀_inc : e₀ ⊆ closure r :=
      disc_edge_subset_closure_of_incident hS hDual.1 he₀ hr ⟨z, hze₀, hz_cl⟩
    obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
    let e : G.E := ⟨e₀, he₀⟩
    obtain ⟨_, he2, he3, he4, _⟩ := hedge e
    obtain ⟨⟨u₁, hu₁, u₂, hu₂, hlink, he_diff, _, _, _⟩, _⟩ :=
      hDual.edge_half_regions hS he₀ (edgeEquiv e).2 he2 he3 he4
    have hz_diff : z ∈ e₀ \ G_dual.U := ⟨hze₀, region_subset hr_dual hz_rd⟩
    rcases he_diff hz_diff with hzu₁ | hzu₂
    · have h_eq : r_dual = connectedComponentIn (univ \ G_dual.U) u₁ :=
        region_eq_of_mem hr_dual (hDual.connectedComponentIn_mem_dual_R hu₁).1 hz_rd hzu₁
      have hvu₁ : v = u₁ := hDual.2.2.2.2.2.1 v hv u₁ hu₁ (hrd_eq.symm.trans h_eq)
      have hu₁_cl : u₁ ∈ closure e₀ := by
        have : u₁ ∈ closure e₀ ∩ G.V := by rw [hlink.2.2.2]; exact mem_insert u₁ {u₂}
        exact this.1
      simpa only [closure_closure] using closure_mono he₀_inc (hvu₁ ▸ hu₁_cl)
    · have h_eq : r_dual = connectedComponentIn (univ \ G_dual.U) u₂ :=
        region_eq_of_mem hr_dual (hDual.connectedComponentIn_mem_dual_R hu₂).1 hz_rd hzu₂
      have hvu₂ : v = u₂ := hDual.2.2.2.2.2.1 v hv u₂ hu₂ (hrd_eq.symm.trans h_eq)
      have hu₂_cl : u₂ ∈ closure e₀ := by
        have : u₂ ∈ closure e₀ ∩ G.V := by rw [hlink.2.2.2]; exact mem_insert_of_mem u₁ rfl
        exact this.1
      simpa only [closure_closure] using closure_mono he₀_inc (hvu₂ ▸ hu₂_cl)

/-- Upgrade a one-way `IsDiscDualDrawing G G_dual` to the two-way `IsDiscDualDrawingPair G G_dual`
when `G` is connected and drawn on a closed disc space `S`. -/
theorem IsDiscDualDrawing.to_pair (hS : IsClosedDiscSpace S) {G G_dual : Drawing S}
    (hConn : IsGraphConnected G.toGraph) (hDual : IsDiscDualDrawing G G_dual) :
    IsDiscDualDrawingPair G G_dual := by
  have hSymm := hDual.symm_of_connected hS hConn
  obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
  refine ⟨hDual.1, hDual.2.1, hDual.V_inter_dual_V_eq_empty,
    hDual.2.2.1, hDual.2.2.2.1,
    hSymm.2.2.1, hSymm.2.2.2.1,
    ?_, hDual.2.2.2.2.1, hSymm.2.2.2.2.1, edgeEquiv, ?_⟩
  · intro v hv r hr w hw r_dual hr_dual hv_rd
    exact ⟨fun hv_cl => hSymm.mem_closure_region_of_mem_closure_dual hS hw.2 hr_dual
      ⟨hv_rd, hv⟩ hr hw.1 hv_cl,
      fun hw_cl => hDual.mem_closure_region_of_mem_closure_dual hS hv hr hw hr_dual hv_rd hw_cl⟩
  · intro e
    obtain ⟨he1, he2, he3, he4, he5⟩ := hedge e
    exact ⟨he1, he2, he3, he5, (hDual.edge_half_regions hS e.2 (edgeEquiv e).2 he2 he3 he4).2⟩

/-- Symmetry of `IsDiscDualDrawingPair`. -/
theorem IsDiscDualDrawingPair.symm {G G_dual : Drawing S}
    (h : IsDiscDualDrawingPair G G_dual) : IsDiscDualDrawingPair G_dual G := by
  rcases h with ⟨hG_prop, hGd_prop, hV_disj, hR_uniq, hVd_R, hRd_uniq, hV_Rd,
    hinc, hU1, hU2, edgeEquiv, hedge⟩
  refine ⟨hGd_prop, hG_prop, by rw [inter_comm, hV_disj],
    hRd_uniq, hV_Rd, hR_uniq, hVd_R, ?_, hU2, hU1, edgeEquiv.symm, ?_⟩
  · intro w hw r_dual hr_dual v hv r hr hw_r
    exact (hinc v hv.2 r hr w ⟨hw_r, hw⟩ r_dual hr_dual hv.1).symm
  · intro e'
    let e := edgeEquiv.symm e'
    have he' : edgeEquiv e = e' := edgeEquiv.apply_symm_apply e'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hedge e
    rw [he'] at h1 h2 h3 h4 h5
    refine ⟨h2, h1, by rw [inter_comm, h3], h5, h4⟩

end GraphMinor.GM06
