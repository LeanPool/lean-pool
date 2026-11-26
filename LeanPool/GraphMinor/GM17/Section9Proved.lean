/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved
import LeanPool.GraphMinor.GM17.Section7Proved
import LeanPool.GraphMinor.GM17.Section8Proved

public import LeanPool.GraphMinor.GM17.Section8
public import LeanPool.GraphMinor.Menger.Basic
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.GM17.RegionBoundary

/-!
# Graph Minors XVII: proved deductions of Section9

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section9`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

/-! ## 1. Internal Cell Connectivity: (9.1) (Page 183) -/

private theorem norm_convex_combo_eq {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (u : ℝ) :
    ‖(1 - (u : ℂ)) * z + (u : ℂ) * w‖ ^ 2 + u * (1 - u) * ‖z - w‖ ^ 2 = 1 := by
  have h1 : ∀ a : ℂ, ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← h1 z, hz, one_pow]
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by rw [← h1 w, hw, one_pow]
  rw [h1, h1]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (1 - u) * hz2 + u * hw2

private theorem exists_chord_in_closedDisc {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {s t : S} (hs : s ∈ discBd D) (ht : t ∈ discBd D)
    (hst : s ≠ t) :
    ∃ F : Set S, F ⊆ D ∧ IsLineWithEnds F s t ∧ F ∩ discBd D = {s, t} ∧
      IsConnected (F \ {t}) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hs_D : s ∈ D := discBd_subset D hs
  have ht_D : t ∈ D := discBd_subset D ht
  have hzs : h s ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h hs
  have hzt : h t ∈ sphere (0 : ℂ) 1 := by rw [← c.bd]; exact mem_image_of_mem h ht
  have hzs_norm : ‖h s‖ = 1 := mem_sphere_zero_iff_norm.mp hzs
  have hzt_norm : ‖h t‖ = 1 := mem_sphere_zero_iff_norm.mp hzt
  have hz_ne : h s ≠ h t := fun hEq => hst (c.gh.injOn hs_D ht_D hEq)
  let ℓ : 𝕀 → ℂ := fun u => (1 - (u : ℝ) : ℂ) * h s + (u : ℝ) * h t
  have hℓ_cont : Continuous ℓ :=
    ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      continuous_const).add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  have hℓ_ball : ∀ u : 𝕀, ℓ u ∈ closedBall (0 : ℂ) 1 := fun u => by
    rw [mem_closedBall_zero_iff]
    have hid := norm_convex_combo_eq hzs_norm hzt_norm (u : ℝ)
    have hnonneg : 0 ≤ (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 :=
      mul_nonneg (mul_nonneg u.2.1 (sub_nonneg.mpr u.2.2)) (sq_nonneg _)
    have hsq : ‖ℓ u‖ ^ 2 ≤ 1 ^ 2 := by dsimp [ℓ]; linarith
    exact (abs_le_of_sq_le_sq' hsq zero_le_one).2
  have hℓ_sphere : ∀ u : 𝕀, ℓ u ∈ sphere (0 : ℂ) 1 → u = 0 ∨ u = 1 := fun u hu => by
    have hn : ‖ℓ u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hid := norm_convex_combo_eq hzs_norm hzt_norm (u : ℝ)
    change ‖ℓ u‖ ^ 2 + (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 = 1 at hid
    rw [hn, one_pow] at hid
    have hdiff_ne : ‖h s - h t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz_ne)
    have hmul : (u : ℝ) * (1 - (u : ℝ)) = 0 := by
      have h0 : (u : ℝ) * (1 - (u : ℝ)) * ‖h s - h t‖ ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp h0).resolve_right (pow_ne_zero 2 hdiff_ne)
    rcases mul_eq_zero.mp hmul with hu0 | hu1
    · exact Or.inl (Subtype.ext hu0)
    · have h1 : (u : ℝ) = 1 := by linarith
      exact Or.inr (Subtype.ext h1)
  have hℓ_inj : Function.Injective ℓ := fun u₁ u₂ hEq => by
    have hsub : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (h t - h s) = 0 := by
      calc ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (h t - h s)
        _ = ℓ u₁ - ℓ u₂ := by dsimp [ℓ]; ring
        _ = 0 := sub_eq_zero.mpr hEq
    have hdiff : h t - h s ≠ 0 := sub_ne_zero.mpr hz_ne.symm
    have hu : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) = 0 := (mul_eq_zero.mp hsub).resolve_right hdiff
    have hu' : (u₁ : ℝ) - (u₂ : ℝ) = 0 := Complex.ofReal_eq_zero.mp (by simpa using hu)
    exact Subtype.ext (sub_eq_zero.mp hu')
  let φ : 𝕀 → S := fun u => g (ℓ u)
  have hφ_cont : Continuous φ := c.gc.comp_continuous hℓ_cont hℓ_ball
  have hφ_inj : Function.Injective φ := fun u₁ u₂ hEq =>
    hℓ_inj (c.injOn (hℓ_ball u₁) (hℓ_ball u₂) hEq)
  have hφ0 : φ 0 = s := by
    change g (ℓ 0) = s
    simp only [ℓ, Icc.coe_zero, Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact c.gh hs_D
  have hφ1 : φ 1 = t := by
    change g (ℓ 1) = t
    simp only [ℓ, Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
    exact c.gh ht_D
  set F := range φ
  have hF_sub : F ⊆ D := by
    rintro _ ⟨u, rfl⟩
    exact c.gm (hℓ_ball u)
  let ev : 𝕀 ≃ₜ F :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective φ hφ_inj)
      hφ_cont.rangeFactorization
  have hF_line : IsLineWithEnds F s t := ⟨ev, hφ0, hφ1⟩
  have hF_bd : F ∩ discBd D = {s, t} := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨u, rfl⟩, hbd⟩
      have hlu_sphere : ℓ u ∈ sphere (0 : ℂ) 1 := by
        rw [← c.bd, ← c.hg (hℓ_ball u)]
        exact mem_image_of_mem h hbd
      rcases hℓ_sphere u hlu_sphere with rfl | rfl
      · exact Or.inl hφ0
      · exact Or.inr hφ1
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, hφ0⟩, hs⟩
      · exact ⟨⟨1, hφ1⟩, ht⟩
  have hF_conn : IsConnected (F \ {t}) := by
    have hEq : F \ {t} = φ '' {u : 𝕀 | (u : ℝ) < 1} := by
      ext x
      simp only [F, mem_sdiff, mem_range, mem_singleton_iff, mem_image, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨u, rfl⟩, hne⟩
        have hu1 : u ≠ 1 := fun h => hne (h ▸ hφ1)
        exact ⟨u, lt_of_le_of_ne u.2.2 (Subtype.ext_iff.not.mp hu1), rfl⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨u, rfl⟩, fun hEq => ?_⟩
        have hu1 : u = 1 := hφ_inj (hEq.trans hφ1.symm)
        exact hu.ne (congrArg Subtype.val hu1)
    rw [hEq]
    have hpre : IsConnected {u : 𝕀 | (u : ℝ) < 1} := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      exact isPreconnected_iff_preconnectedSpace.mpr (Subtype.preconnectedSpace (by
        have hconv : Convex ℝ (Ico (0 : ℝ) 1) := convex_Ico 0 1
        have hEq2 : {u : 𝕀 | (u : ℝ) < 1} = Subtype.val ⁻¹' Ico (0 : ℝ) 1 := by
          ext u; simp [u.2.1]
        rw [hEq2]
        exact (IsInducing.subtypeVal.isPreconnected_image.mp (by
          rw [Subtype.image_preimage_coe]
          have hinter : (Icc (0 : ℝ) 1) ∩ Ico 0 1 = Ico 0 1 :=
            inter_eq_right.mpr Ico_subset_Icc_self
          rw [hinter]
          exact hconv.isPreconnected))))
    exact hpre.image φ hφ_cont.continuousOn
  exact ⟨F, hF_sub, hF_line, hF_bd, hF_conn⟩

private theorem exists_two_discs_touching_at_point {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {n₁ n₂ n₃ : S}
    (hn₁ : n₁ ∈ discBd D) (hn₂ : n₂ ∈ discBd D) (hn₃ : n₃ ∈ discBd D)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ D ∧ Δ₂ ⊆ D ∧
      n₁ ∈ Δ₁ ∧ n₃ ∈ Δ₁ ∧ n₂ ∉ Δ₁ ∧
      n₂ ∈ Δ₂ ∧ n₃ ∈ Δ₂ ∧ n₁ ∉ Δ₂ ∧
      Δ₁ ∩ Δ₂ = {n₃} := by
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, hF₁_conn⟩ :=
    exists_chord_in_closedDisc hD hn₁ hn₃ h13
  obtain ⟨A₁, A₂, E₁, E₂, -, -, hE₁_disc, hE₂_disc, hE_union, hE_inter, hE₁_bd, hE₂_bd, -⟩ :=
    disc_iArc D F₁ n₁ n₃ hD hF₁_sub h13 hF₁_line hF₁_bd
  have hn₁_F₁ : n₁ ∈ F₁ := by
    have : n₁ ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₁ : n₃ ∈ F₁ := by
    have : n₃ ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hn₂_not_F₁ : n₂ ∉ F₁ := by
    intro hmem
    have : n₂ ∈ F₁ ∩ discBd D := ⟨hmem, hn₂⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact h12 hEq.symm
    · exact h23 hEq
  have hn₂_D : n₂ ∈ E₁ ∪ E₂ := hE_union.symm ▸ discBd_subset D hn₂
  have hhalf : ∃ Δ₁ D' : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc D' ∧
      Δ₁ ⊆ D ∧ D' ⊆ D ∧ Δ₁ ∩ D' = F₁ ∧ F₁ ⊆ Δ₁ ∧ F₁ ⊆ discBd D' ∧
      n₂ ∉ Δ₁ ∧ n₂ ∈ discBd D' := by
    rcases hn₂_D with hn₂_E₁ | hn₂_E₂
    · have hn₂_not_E₂ : n₂ ∉ E₂ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨hn₂_E₁, h⟩)
      have hE₁_sub : E₁ ⊆ D := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ D := hE_union ▸ subset_union_right
      refine ⟨E₂, E₁, hE₂_disc, hE₁_disc, hE₂_sub, hE₁_sub, ?_, ?_, ?_, hn₂_not_E₂, ?_⟩
      · rw [Set.inter_comm, hE_inter]
      · rw [← hE_inter]; exact inter_subset_right
      · rw [hE₁_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₁_disc hE₁_sub ⟨hn₂_E₁, hn₂⟩
    · have hn₂_not_E₁ : n₂ ∉ E₁ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨h, hn₂_E₂⟩)
      have hE₁_sub : E₁ ⊆ D := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ D := hE_union ▸ subset_union_right
      refine ⟨E₁, E₂, hE₁_disc, hE₂_disc, hE₁_sub, hE₂_sub, hE_inter, ?_, ?_, hn₂_not_E₁, ?_⟩
      · rw [← hE_inter]; exact inter_subset_left
      · rw [hE₂_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₂_disc hE₂_sub ⟨hn₂_E₂, hn₂⟩
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub, hΔ₁D'_inter, hF₁_Δ₁,
    hF₁_bdD', hn₂_not_Δ₁, hn₂_bdD'⟩ := hhalf
  have hn₃_bdD' : n₃ ∈ discBd D' := hF₁_bdD' hn₃_F₁
  obtain ⟨F₂, hF₂_sub, hF₂_line, hF₂_bd, -⟩ :=
    exists_chord_in_closedDisc hD'_disc hn₂_bdD' hn₃_bdD' h23
  obtain ⟨B₁, B₂, G₁, G₂, hB_ne, hB_comp, hG₁_disc, hG₂_disc, hG_union, hG_inter,
    hG₁_bd, hG₂_bd, -⟩ :=
    disc_iArc D' F₂ n₂ n₃ hD'_disc hF₂_sub h23 hF₂_line hF₂_bd
  have hn₂_F₂ : n₂ ∈ F₂ := by
    have : n₂ ∈ F₂ ∩ discBd D' := by rw [hF₂_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₂ : n₃ ∈ F₂ := by
    have : n₃ ∈ F₂ ∩ discBd D' := by rw [hF₂_bd]; exact Or.inr rfl
    exact this.1
  have hF₁_sub_bdD' : F₁ \ {n₃} ⊆ discBd D' \ {n₂, n₃} := by
    rintro x ⟨hxF₁, hxn₃⟩
    refine ⟨hF₁_bdD' hxF₁, ?_⟩
    rintro (rfl | rfl)
    · exact hn₂_not_F₁ hxF₁
    · exact hxn₃ rfl
  have hn₁_mem_diff : n₁ ∈ discBd D' \ {n₂, n₃} := hF₁_sub_bdD' ⟨hn₁_F₁, h13⟩
  have hcomp_mem : connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ ∈ ({B₁, B₂} : Set (Set S)) := by
    rw [← hB_comp]
    exact ⟨n₁, hn₁_mem_diff, rfl⟩
  have hF₁_in_comp : F₁ \ {n₃} ⊆ connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ :=
    hF₁_conn.isPreconnected.subset_connectedComponentIn ⟨hn₁_F₁, h13⟩ hF₁_sub_bdD'
  have hB₁_mem : B₁ ∈ componentsIn (discBd D' \ {n₂, n₃}) := by rw [hB_comp]; exact Or.inl rfl
  have hB₂_mem : B₂ ∈ componentsIn (discBd D' \ {n₂, n₃}) := by rw [hB_comp]; exact Or.inr rfl
  have hB_disj : Disjoint B₁ B₂ := by
    rcases hB₁_mem with ⟨x₁, hx₁, rfl⟩
    rcases hB₂_mem with ⟨x₂, hx₂, rfl⟩
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hB_ne ?_
    rw [connectedComponentIn_eq hz₁, connectedComponentIn_eq hz₂]
  have hchoose_G : ∃ B Δ₂ : Set S, IsClosedDisc Δ₂ ∧ Δ₂ ⊆ D' ∧ F₂ ⊆ Δ₂ ∧
      discBd Δ₂ = B ∪ F₂ ∧ Disjoint B (F₁ \ {n₃}) := by
    rcases hcomp_mem with hEq | hEq
    · refine ⟨B₂, G₂, hG₂_disc, hG_union ▸ subset_union_right, ?_, hG₂_bd, ?_⟩
      · rw [← hG_inter]; exact inter_subset_right
      · exact hB_disj.symm.mono_right (hEq ▸ hF₁_in_comp)
    · have hEq' : connectedComponentIn (discBd D' \ {n₂, n₃}) n₁ = B₂ := hEq
      refine ⟨B₁, G₁, hG₁_disc, hG_union ▸ subset_union_left, ?_, hG₁_bd, ?_⟩
      · rw [← hG_inter]; exact inter_subset_left
      · exact hB_disj.mono_right (hEq' ▸ hF₁_in_comp)
  obtain ⟨B, Δ₂, hΔ₂_disc, hΔ₂_sub', hF₂_Δ₂, hΔ₂_bd, hB_disj_F₁⟩ := hchoose_G
  have hΔ₂_sub : Δ₂ ⊆ D := hΔ₂_sub'.trans hD'_sub
  have hinter : Δ₁ ∩ Δ₂ = {n₃} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁, hx₂⟩
      have hxF₁ : x ∈ F₁ := by
        rw [← hΔ₁D'_inter]
        exact ⟨hx₁, hΔ₂_sub' hx₂⟩
      by_cases hxn₃ : x = n₃
      · exact hxn₃
      · exfalso
        have hx_bdΔ₂ : x ∈ discBd Δ₂ :=
          disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hx₂, hF₁_bdD' hxF₁⟩
        rw [hΔ₂_bd] at hx_bdΔ₂
        rcases hx_bdΔ₂ with hxB | hxF₂
        · exact Set.disjoint_left.mp hB_disj_F₁ hxB ⟨hxF₁, hxn₃⟩
        · have hx_bd : x ∈ F₂ ∩ discBd D' := ⟨hxF₂, hF₁_bdD' hxF₁⟩
          rw [hF₂_bd] at hx_bd
          rcases hx_bd with rfl | rfl
          · exact hn₂_not_F₁ hxF₁
          · exact hxn₃ rfl
    · rintro x rfl
      exact ⟨hF₁_Δ₁ hn₃_F₁, hF₂_Δ₂ hn₃_F₂⟩
  have hn₁_not_Δ₂ : n₁ ∉ Δ₂ := by
    intro h
    have : n₁ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₁_F₁, h⟩
    rw [hinter] at this
    exact h13 this
  exact ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
    hF₁_Δ₁ hn₁_F₁, hF₁_Δ₁ hn₃_F₁, hn₂_not_Δ₁,
    hF₂_Δ₂ hn₂_F₂, hF₂_Δ₂ hn₃_F₂, hn₁_not_Δ₂, hinter⟩

private theorem exists_third_point_in_discBd {S : Type*} [TopologicalSpace S]
    {D : Set S} (hD : IsClosedDisc D) (n₁ n₂ : S) :
    ∃ n₃ ∈ discBd D, n₁ ≠ n₃ ∧ n₂ ≠ n₃ := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have h1_sp : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hm1_sp : (-1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hI_sp : Complex.I ∈ sphere (0 : ℂ) 1 := by simp
  have h1_ball : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall h1_sp
  have hm1_ball : (-1 : ℂ) ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hm1_sp
  have hI_ball : Complex.I ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hI_sp
  have hg_bd : ∀ z ∈ sphere (0 : ℂ) 1, g z ∈ discBd D := by
    intro z hz
    have hzD : g z ∈ D := c.gm (sphere_subset_closedBall hz)
    have hhz : h (g z) ∈ h '' discBd D := by
      rw [c.bd, c.hg (sphere_subset_closedBall hz)]
      exact hz
    rcases hhz with ⟨x, hx_bd, hEq⟩
    rwa [c.gh.injOn hzD (discBd_subset D hx_bd) hEq.symm]
  have hne_1_m1 : g 1 ≠ g (-1) := fun hEq => by
    have : (1 : ℂ) = -1 := c.injOn h1_ball hm1_ball hEq
    norm_num at this
  have hne_1_I : g 1 ≠ g Complex.I := fun hEq => by
    have : (1 : ℂ) = Complex.I := c.injOn h1_ball hI_ball hEq
    have := congrArg Complex.im this
    norm_num at this
  have hne_m1_I : g (-1) ≠ g Complex.I := fun hEq => by
    have : (-1 : ℂ) = Complex.I := c.injOn hm1_ball hI_ball hEq
    have := congrArg Complex.im this
    norm_num at this
  by_cases h1 : n₁ ≠ g 1 ∧ n₂ ≠ g 1
  · exact ⟨g 1, hg_bd 1 h1_sp, h1.1, h1.2⟩
  by_cases hm1 : n₁ ≠ g (-1) ∧ n₂ ≠ g (-1)
  · exact ⟨g (-1), hg_bd (-1) hm1_sp, hm1.1, hm1.2⟩
  refine ⟨g Complex.I, hg_bd Complex.I hI_sp, ?_, ?_⟩
  · intro hEq1
    rcases not_and_or.mp h1 with h1' | h1' <;> rcases not_and_or.mp hm1 with hm1' | hm1'
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
    · push Not at h1'; exact hne_1_I (h1'.symm.trans hEq1)
    · push Not at hm1'; exact hne_m1_I (hm1'.symm.trans hEq1)
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
  · intro hEq2
    rcases not_and_or.mp h1 with h1' | h1' <;> rcases not_and_or.mp hm1 with hm1' | hm1'
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')
    · push Not at hm1'; exact hne_m1_I (hm1'.symm.trans hEq2)
    · push Not at h1'; exact hne_1_I (h1'.symm.trans hEq2)
    · push Not at h1' hm1'; exact hne_1_m1 (h1'.symm.trans hm1')

private theorem exists_two_disjoint_discs {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {n₁ n₂ : S}
    (hn₁ : n₁ ∈ discBd D) (hn₂ : n₂ ∈ discBd D) (h12 : n₁ ≠ n₂) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ D ∧ Δ₂ ⊆ D ∧
      n₁ ∈ Δ₁ ∧ n₂ ∉ Δ₁ ∧
      n₂ ∈ Δ₂ ∧ n₁ ∉ Δ₂ ∧
      Δ₁ ∩ Δ₂ = ∅ := by
  obtain ⟨p₃, hp₃, h13, h23⟩ := exists_third_point_in_discBd hD n₁ n₂
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub,
    hn₁_Δ₁, _, hn₂_not_Δ₁, hn₂_D', hp₃_D', hn₁_not_D', hinter1⟩ :=
    exists_two_discs_touching_at_point hD hn₁ hn₂ hp₃ h12 h13 h23
  have hn₂_bdD' : n₂ ∈ discBd D' :=
    disc_inter_discBd_subset_discBd hD hD'_disc hD'_sub ⟨hn₂_D', hn₂⟩
  have hp₃_bdD' : p₃ ∈ discBd D' :=
    disc_inter_discBd_subset_discBd hD hD'_disc hD'_sub ⟨hp₃_D', hp₃⟩
  obtain ⟨p₄, hp₄, h24, h34⟩ := exists_third_point_in_discBd hD'_disc n₂ p₃
  obtain ⟨Δ₂, _, hΔ₂_disc, _, hΔ₂_sub', _,
    hn₂_Δ₂, _, hp₃_not_Δ₂, _, _, _, _⟩ :=
    exists_two_discs_touching_at_point hD'_disc hn₂_bdD' hp₃_bdD' hp₄ h23 h24 h34
  have hΔ₂_sub : Δ₂ ⊆ D := hΔ₂_sub'.trans hD'_sub
  have hn₁_not_Δ₂ : n₁ ∉ Δ₂ := fun h => hn₁_not_D' (hΔ₂_sub' h)
  have hinter : Δ₁ ∩ Δ₂ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx₁, hx₂⟩
    have hxp₃ : x ∈ Δ₁ ∩ D' := ⟨hx₁, hΔ₂_sub' hx₂⟩
    rw [hinter1] at hxp₃
    exact hp₃_not_Δ₂ (hxp₃ ▸ hx₂)
  exact ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
    hn₁_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₁_not_Δ₂, hinter⟩

private noncomputable def splitInternalCellWithCells {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₀ Δ₁ Δ₂ N' : Set S} (hc₀ : c₀ ∈ Γ.C) (hint₀ : ¬ (c₀ ∩ bd S).Nonempty)
    (hΔ₁_disc : IsClosedDisc Δ₁) (hΔ₂_disc : IsClosedDisc Δ₂)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀) (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hN_sub : Γ.N ⊆ N') (hN'_fin : N'.Finite) (hN'_diff : N' \ Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_bd : Δ₁ ∩ N' ⊆ discBd Δ₁) (hΔ₂_bd : Δ₂ ∩ N' ⊆ discBd Δ₂)
    (hΔ₁_card : (Δ₁ ∩ N').ncard ≤ 3) (hΔ₂_card : (Δ₂ ∩ N').ncard ≤ 3) :
    {Γ' : Painting S // Γ'.C = insert (Δ₁ \ N') (insert (Δ₂ \ N') (Γ.C \ {c₀}))} := by
  classical
  let c₁ : Set S := Δ₁ \ N'
  let c₂ : Set S := Δ₂ \ N'
  let U' : Set S := (Γ.U \ c₀) ∪ Δ₁ ∪ Δ₂
  let I₀ : Set (Set S) := Γ.C \ {c₀}
  let I : Set (Set S) := insert c₁ (insert c₂ I₀)
  have hI₀_fin : I₀.Finite := Γ.finite_cells.subset sdiff_subset
  have hI_fin : I.Finite := (hI₀_fin.insert c₂).insert c₁
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₁, hxN'⟩ => ⟨hΔ₁_sub hx₁, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hx₂, hxN'⟩ => ⟨hΔ₂_sub hx₂, fun hxN => hxN' (hN_sub hxN)⟩
  have hc₁_diff_fin : (Δ₁ \ c₁).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₂_diff_fin : (Δ₂ \ c₂).Finite :=
    hN'_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩
  have hc₁_pc : IsPathConnected c₁ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hc₂_pc : IsPathConnected c₂ :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have hcl_c₁ : closure c₁ = Δ₁ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset hc₁_diff_fin
  have hcl_c₂ : closure c₂ = Δ₂ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset hc₂_diff_fin
  have htc₁ : tilde c₁ = Δ₁ ∩ N' :=
    tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin
  have htc₂ : tilde c₂ = Δ₂ ∩ N' :=
    tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin
  have hc₁_disj_c₂ : Disjoint c₁ c₂ := by
    refine Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter ⟨hx₁, hx₂⟩)
  have hcell_disj_N' : ∀ c ∈ I₀, ∀ x ∈ c, x ∉ N' := by
    rintro c ⟨hc, hne⟩ x hxc hxN'
    by_cases hxN : x ∈ Γ.N
    · exact (Γ.cell_subset_diff hc hxc).2 hxN
    · have hx_c₀ : x ∈ c₀ := by
        rw [← Γ.closure_cell_diff_N hc₀]
        exact ⟨hΔ₁_sub (hN'_diff ⟨hxN', hxN⟩).1, hxN⟩
      exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc hx_c₀
  have hcl_sub_I₀ : ∀ c ∈ I₀, closure c ⊆ Γ.U \ c₀ := by
    rintro c ⟨hc, hne⟩ x hxcl
    refine ⟨Γ.closure_cell_subset_U hc hxcl, fun hxc₀ => ?_⟩
    by_cases hxc : x ∈ c
    · exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc hxc₀
    · exact (Γ.cell_subset_diff hc₀ hxc₀).2 (Γ.tilde_subset_N hc ⟨hxcl, hxc⟩)
  have hU₀_eq : Γ.U \ c₀ = Γ.N ∪ ⋃ c ∈ I₀, closure c := by
    ext x
    simp only [I₀, mem_sdiff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hxU, hx_not_c₀⟩
      rw [Γ.U_eq_N_union_biUnion_closure] at hxU
      rcases hxU with hxN | hcl
      · exact Or.inl hxN
      · rw [mem_iUnion₂] at hcl
        rcases hcl with ⟨c, hc, hxcl⟩
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          exact Or.inl (Γ.tilde_subset_N hc₀ ⟨hxcl, hx_not_c₀⟩)
        · exact Or.inr ⟨c, ⟨hc, hcc₀⟩, hxcl⟩
    · rintro (hxN | ⟨c, hcI, hxcl⟩)
      · exact ⟨Γ.N_subset hxN, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩
      · exact hcl_sub_I₀ c hcI hxcl
  have hU'_closed : IsClosed U' := by
    have hU₀_cl : IsClosed (Γ.U \ c₀) := by
      rw [hU₀_eq]
      exact Γ.finite_N.isClosed.union (hI₀_fin.isClosed_biUnion fun _ _ => isClosed_closure)
    exact (hU₀_cl.union (isClosed_of_isClosedDisc hΔ₁_disc)).union (isClosed_of_isClosedDisc
      hΔ₂_disc)
  have hcov : ⋃₀ I = U' \ N' := by
    ext x
    simp only [I, U', sUnion_insert, mem_union, mem_sUnion, mem_sdiff]
    constructor
    · rintro (hxc₁ | hxc₂ | ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact ⟨Or.inl (Or.inr hxc₁.1), hxc₁.2⟩
      · exact ⟨Or.inr hxc₂.1, hxc₂.2⟩
      · exact ⟨Or.inl (Or.inl ⟨Γ.cell_subset_U hc hxc,
          Set.disjoint_left.mp (Γ.cell_disjoint hc hc₀ hne) hxc⟩),
          hcell_disj_N' c ⟨hc, hne⟩ x hxc⟩
    · rintro ⟨((⟨hxU, hx_not_c₀⟩ | hxΔ₁) | hxΔ₂), hx_not_N'⟩
      · have hx_not_N : x ∉ Γ.N := fun hxN => hx_not_N' (hN_sub hxN)
        have hx_cells : x ∈ ⋃₀ Γ.C := Γ.sUnion_cells.symm ▸ ⟨hxU, hx_not_N⟩
        rcases hx_cells with ⟨c, hc, hxc⟩
        have hne : c ≠ c₀ := fun h => hx_not_c₀ (h ▸ hxc)
        exact Or.inr (Or.inr ⟨c, ⟨hc, hne⟩, hxc⟩)
      · exact Or.inl ⟨hxΔ₁, hx_not_N'⟩
      · exact Or.inr (Or.inl ⟨hxΔ₂, hx_not_N'⟩)
  have hC'_eq : arcComponentsIn (U' \ N') = I := by
    apply arcComponentsIn_eq_of_finite_cover hI_fin hcov
    · rintro c (rfl | rfl | hcI)
      · exact hc₁_pc.nonempty
      · exact hc₂_pc.nonempty
      · exact Γ.cell_nonempty hcI.1
    · rintro c (rfl | rfl | hcI)
      · exact hc₁_pc
      · exact hc₂_pc
      · exact Γ.cell_isPathConnected hcI.1
    · rintro c (rfl | rfl | hcI) c' (rfl | rfl | hc'I) hne
      · exact (hne rfl).elim
      · exact hc₁_disj_c₂
      · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₁_sub_c₀
      · exact hc₁_disj_c₂.symm
      · exact (hne rfl).elim
      · exact (Γ.cell_disjoint hc'I.1 hc₀ hc'I.2).symm.mono_left hc₂_sub_c₀
      · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₁_sub_c₀
      · exact (Γ.cell_disjoint hcI.1 hc₀ hcI.2).mono_right hc₂_sub_c₀
      · exact Γ.cell_disjoint hcI.1 hc'I.1 hne
    · intro c hcI_all
      refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI_all, hxc⟩⟩)
      rintro x ⟨hxcl, hxUN⟩
      rcases hcI_all with rfl | rfl | hcI
      · rw [hcl_c₁] at hxcl
        exact ⟨hxcl, hxUN.2⟩
      · rw [hcl_c₂] at hxcl
        exact ⟨hxcl, hxUN.2⟩
      · rw [← Γ.closure_cell_diff_N hcI.1]
        exact ⟨hxcl, fun hxN => hxUN.2 (hN_sub hxN)⟩
  refine ⟨?_, ?_⟩
  · refine
      { U := U'
        N := N'
        isClosed_U := hU'_closed
        finite_N := hN'_fin
        N_subset := fun x hxN' => by
          by_cases hxN : x ∈ Γ.N
          · exact Or.inl (Or.inl ⟨Γ.N_subset hxN,
              fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩)
          · exact Or.inl (Or.inr (hN'_diff ⟨hxN', hxN⟩).1)
        finite_cells := hC'_eq ▸ hI_fin
        cell_disc := ?_
        bd_subset := fun x hxbd => Or.inl (Or.inl ⟨Γ.bd_subset hxbd,
          fun hxc₀ => hint₀ ⟨x, hxc₀, hxbd⟩⟩)
        border_cell := ?_ }
    · intro c hc
      rw [hC'_eq] at hc
      rcases hc with rfl | rfl | hcI
      · rw [hcl_c₁, htc₁]
        exact ⟨hΔ₁_disc, hΔ₁_bd, hN'_fin.inter_of_right Δ₁, hΔ₁_card⟩
      · rw [hcl_c₂, htc₂]
        exact ⟨hΔ₂_disc, hΔ₂_bd, hN'_fin.inter_of_right Δ₂, hΔ₂_card⟩
      · exact Γ.cell_disc c hcI.1
    · intro c hc hbd
      rw [hC'_eq] at hc
      rcases hc with rfl | rfl | hcI
      · exact False.elim (hint₀ (hbd.mono (inter_subset_inter_left _ hc₁_sub_c₀)))
      · exact False.elim (hint₀ (hbd.mono (inter_subset_inter_left _ hc₂_sub_c₀)))
      · exact Γ.border_cell c hcI.1 hbd
  · exact hC'_eq

private noncomputable def splitInternalCell {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₀ Δ₁ Δ₂ N' : Set S} (hc₀ : c₀ ∈ Γ.C) (hint₀ : ¬ (c₀ ∩ bd S).Nonempty)
    (hΔ₁_disc : IsClosedDisc Δ₁) (hΔ₂_disc : IsClosedDisc Δ₂)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀) (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hN_sub : Γ.N ⊆ N') (hN'_fin : N'.Finite) (hN'_diff : N' \ Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_bd : Δ₁ ∩ N' ⊆ discBd Δ₁) (hΔ₂_bd : Δ₂ ∩ N' ⊆ discBd Δ₂)
    (hΔ₁_card : (Δ₁ ∩ N').ncard ≤ 3) (hΔ₂_card : (Δ₂ ∩ N').ncard ≤ 3) :
    Painting S :=
  (splitInternalCellWithCells Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
    hN_sub hN'_fin hN'_diff hΔ_inter hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card).1

private theorem splitInternalCell_C {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₀ Δ₁ Δ₂ N' : Set S} (hc₀ : c₀ ∈ Γ.C) (hint₀ : ¬ (c₀ ∩ bd S).Nonempty)
    (hΔ₁_disc : IsClosedDisc Δ₁) (hΔ₂_disc : IsClosedDisc Δ₂)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀) (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hN_sub : Γ.N ⊆ N') (hN'_fin : N'.Finite) (hN'_diff : N' \ Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_bd : Δ₁ ∩ N' ⊆ discBd Δ₁) (hΔ₂_bd : Δ₂ ∩ N' ⊆ discBd Δ₂)
    (hΔ₁_card : (Δ₁ ∩ N').ncard ≤ 3) (hΔ₂_card : (Δ₂ ∩ N').ncard ≤ 3) :
    (splitInternalCell Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card).C =
      insert (Δ₁ \ N') (insert (Δ₂ \ N') (Γ.C \ {c₀})) :=
  (splitInternalCellWithCells Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
    hN_sub hN'_fin hN'_diff hΔ_inter hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card).2

private theorem exists_discs_for_splitInternalCell {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.C)
    (htc₀_ge2 : 2 ≤ (tilde c₀).ncard)
    {n₁ n₂ : S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ closure c₀ ∧ Δ₂ ⊆ closure c₀ ∧
      Δ₁ ∩ Δ₂ = tilde c₀ \ {n₁, n₂} ∧
      tilde (Δ₁ \ Γ.N) = tilde c₀ \ {n₂} ∧
      tilde (Δ₂ \ Γ.N) = tilde c₀ \ {n₁} := by
  have hD : IsClosedDisc (closure c₀) := Γ.isClosedDisc_closure_cell hc₀
  have htc₀_bd : tilde c₀ ⊆ discBd (closure c₀) := (Γ.cell_disc c₀ hc₀).2.1
  have htc₀_fin : (tilde c₀).Finite := Γ.finite_tilde_cell hc₀
  have htc₀_le3 : (tilde c₀).ncard ≤ 3 := Γ.ncard_tilde_cell_le hc₀
  have htc_diff : ∀ Δ : Set S, IsClosedDisc Δ → Δ ⊆ closure c₀ → tilde (Δ \ Γ.N) = Δ ∩ tilde c₀
    := by
    intro Δ hΔ hΔ_sub
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ Γ.finite_N]
    ext x
    simp only [mem_inter_iff, tilde, mem_sdiff]
    exact ⟨fun ⟨hxΔ, hxN⟩ => ⟨hxΔ, hΔ_sub hxΔ, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩,
      fun ⟨hxΔ, hxtc₀⟩ => ⟨hxΔ, Γ.tilde_subset_N hc₀ hxtc₀⟩⟩
  by_cases hex₃ : (tilde c₀ \ {n₁, n₂}).Nonempty
  · obtain ⟨n₃, hn₃_tc, hn₃_not_pair⟩ := hex₃
    have h13 : n₁ ≠ n₃ := fun h => hn₃_not_pair (Or.inl h.symm)
    have h23 : n₂ ≠ n₃ := fun h => hn₃_not_pair (Or.inr h.symm)
    have hsub3 : ({n₁, n₂, n₃} : Set S) ⊆ tilde c₀ := by
      rintro x (rfl | rfl | rfl) <;> assumption
    have hcard3 : ({n₁, n₂, n₃} : Set S).ncard = 3 := by
      rw [ncard_insert_of_notMem, ncard_pair h23]
      rintro (rfl | rfl)
      · exact hne rfl
      · exact h13 rfl
    have htc₀_eq : tilde c₀ = {n₁, n₂, n₃} :=
      (eq_of_subset_of_ncard_le hsub3 (by omega) htc₀_fin).symm
    obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
      hn₁_Δ₁, hn₃_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₃_Δ₂, hn₁_not_Δ₂, hinter⟩ :=
      exists_two_discs_touching_at_point hD (htc₀_bd hn₁) (htc₀_bd hn₂) (htc₀_bd hn₃_tc) hne h13 h23
    refine ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, ?_, ?_, ?_⟩
    · rw [hinter, htc₀_eq]
      ext x
      simp only [mem_singleton_iff, mem_sdiff, mem_insert_iff]
      constructor
      · rintro rfl
        refine ⟨Or.inr (Or.inr rfl), ?_⟩
        rintro (rfl | rfl)
        · exact h13 rfl
        · exact h23 rfl
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact (hnot (Or.inl rfl)).elim
        · exact (hnot (Or.inr rfl)).elim
        · rfl
    · rw [htc_diff Δ₁ hΔ₁_disc hΔ₁_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₁, rfl | rfl | rfl⟩
        · exact ⟨Or.inl rfl, hne⟩
        · exact (hn₂_not_Δ₁ hxΔ₁).elim
        · exact ⟨Or.inr (Or.inr rfl), h23.symm⟩
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact ⟨hn₁_Δ₁, Or.inl rfl⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₃_Δ₁, Or.inr (Or.inr rfl)⟩
    · rw [htc_diff Δ₂ hΔ₂_disc hΔ₂_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₂, rfl | rfl | rfl⟩
        · exact (hn₁_not_Δ₂ hxΔ₂).elim
        · exact ⟨Or.inr (Or.inl rfl), hne.symm⟩
        · exact ⟨Or.inr (Or.inr rfl), h13.symm⟩
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₂_Δ₂, Or.inr (Or.inl rfl)⟩
        · exact ⟨hn₃_Δ₂, Or.inr (Or.inr rfl)⟩
  · have htc₀_diff_empty : tilde c₀ \ {n₁, n₂} = ∅ := not_nonempty_iff_eq_empty.mp hex₃
    have htc₀_eq : tilde c₀ = {n₁, n₂} := by
      refine Subset.antisymm (sdiff_eq_empty.mp htc₀_diff_empty) ?_
      rintro x (rfl | rfl) <;> assumption
    obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub,
      hn₁_Δ₁, hn₂_not_Δ₁, hn₂_Δ₂, hn₁_not_Δ₂, hinter⟩ :=
      exists_two_disjoint_discs hD (htc₀_bd hn₁) (htc₀_bd hn₂) hne
    refine ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, ?_, ?_, ?_⟩
    · rw [hinter, htc₀_diff_empty]
    · rw [htc_diff Δ₁ hΔ₁_disc hΔ₁_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₁, rfl | rfl⟩
        · exact ⟨Or.inl rfl, hne⟩
        · exact (hn₂_not_Δ₁ hxΔ₁).elim
      · rintro ⟨rfl | rfl, hnot⟩
        · exact ⟨hn₁_Δ₁, Or.inl rfl⟩
        · exact (hnot rfl).elim
    · rw [htc_diff Δ₂ hΔ₂_disc hΔ₂_sub, htc₀_eq]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_sdiff]
      constructor
      · rintro ⟨hxΔ₂, rfl | rfl⟩
        · exact (hn₁_not_Δ₂ hxΔ₂).elim
        · exact ⟨Or.inr rfl, hne.symm⟩
      · rintro ⟨rfl | rfl, hnot⟩
        · exact (hnot rfl).elim
        · exact ⟨hn₂_Δ₂, Or.inr rfl⟩

private theorem internal_cell_attachments_le_three {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G) {c : Set π.S}
    (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    (attachments G (π.cellGraph c)).ncard ≤ 3 := by
  have : T2Space π.S := π.isSurface.2.1
  have hsub : attachments G (π.cellGraph c) ⊆ π.nodeVertex '' (tilde c ∩ π.domγ) := by
    intro v hv
    obtain ⟨hvc, hvother⟩ := π.attachments_cellGraph_subset_otherVertices hc hv
    exact π.p5 c hc hint v hvc hvother
  have hfinite := π.Γ.finite_tilde_cell hc
  have hdomfin := hfinite.inter_of_left π.domγ
  exact (ncard_le_ncard hsub (hdomfin.image _)).trans <|
    (ncard_image_le hdomfin).trans <|
      (ncard_le_ncard inter_subset_left hfinite).trans (π.Γ.ncard_tilde_cell_le hc)

open Classical in
private noncomputable abbrev split_internal_cell_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C)
    (hint₀ : ¬(c₀ ∩ bd π.S).Nonempty)
    (htc₀_ge2 : 2 ≤ (tilde c₀).ncard)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁ : n₁ ∈ tilde c₀)
    (hn₂ : n₂ ∈ tilde c₀)
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    (hA₁_le : A₁ ≤ π.cellGraph c₀)
    (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA_union_V : A₁.vertexSet ∪ A₂.vertexSet = (π.cellGraph c₀).vertexSet)
    (hA_union_E : A₁.edgeSet ∪ A₂.edgeSet = (π.cellGraph c₀).edgeSet)
    (hA_disj_E : Disjoint A₁.edgeSet A₂.edgeSet)
    (hA₁_tc : ∀ n ∈ tilde c₀ \ {n₂}, π.nodeVertex n ∈ A₁.vertexSet)
    (hA₂_tc : ∀ n ∈ tilde c₀ \ {n₁}, π.nodeVertex n ∈ A₂.vertexSet)
    (hA_inter_V : A₁.vertexSet ∩ A₂.vertexSet ⊆ π.nodeVertex '' (tilde c₀ \ {n₁, n₂}))
    (Δ₁ : Set π.S)
    (Δ₂ : Set π.S)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀)
    (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hΔ_inter : Δ₁ ∩ Δ₂ = tilde c₀ \ {n₁, n₂})
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (htc₂ : tilde c₂ = tilde c₀ \ {n₁})
    (htc₁ : tilde c₁ = tilde c₀ \ {n₂})
    (hΔ₁_N_eq : Δ₁ ∩ π.Γ.N = tilde c₀ \ {n₂})
    (hΔ₂_N_eq : Δ₂ ∩ π.Γ.N = tilde c₀ \ {n₁})
    (Γ' : Painting π.S)
    (hΓN : Γ'.N = π.Γ.N)
    (hC' : Γ'.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (hc₁_sub_c₀ : c₁ ⊆ c₀)
    (hc₂_sub_c₀ : c₂ ⊆ c₀)
    (hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁)
    (hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂)
    (hint₁ : ¬(c₁ ∩ bd π.S).Nonempty)
    (hint₂ : ¬(c₂ ∩ bd π.S).Nonempty)
    (hc₁_C' : c₁ ∈ Γ'.C)
    (hc₂_C' : c₂ ∈ Γ'.C)
    (cellG : Set π.S → Hypergraph α β)
    (hcellG_c₁ : cellG c₁ = A₁)
    (hcellG_c₂ : cellG c₂ = A₂)
    (hcellG_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG d = π.cellGraph d)
    (hcellG_le : ∀ c ∈ Γ'.C, cellG c ≤ G)
    (hp5_aux : ∀ c ∈ Γ'.C, ¬(c ∩ bd π.S).Nonempty → ∀ v ∈ (cellG c).vertexSet, (∃ d ∈ Γ'.C, d ≠ c
      ∧ v ∈ (cellG d).vertexSet) → v ∈ π.nodeVertex '' (tilde c ∩ π.domγ)) : Portrayal G :=
  { S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ'
    cellGraph := cellG
    borderSet := π.borderSet
    domγ := π.domγ
    nodeVertex := π.nodeVertex
    cellGraph_le := hcellG_le
    borderSet_subset := fun n hn => π.borderSet_subset n (hΓN ▸ hn)
    domγ_subset := hΓN.symm ▸ π.domγ_subset
    nodeVertex_mem := π.nodeVertex_mem
    nodeVertex_injOn := π.nodeVertex_injOn
    p1_vertex := fun v hv => by
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      by_cases hcc₀ : c = c₀
      · subst hcc₀
        rw [← hA_union_V] at hvc
        rcases hvc with hv₁ | hv₂
        · exact ⟨c₁, hc₁_C', hcellG_c₁.symm ▸ hv₁⟩
        · exact ⟨c₂, hc₂_C', hcellG_c₂.symm ▸ hv₂⟩
      · exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
          (hcellG_other c ⟨hc, hcc₀⟩).symm ▸ hvc⟩
    p1_edge := fun e he => by
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      by_cases hcc₀ : c = c₀
      · subst hcc₀
        rw [← hA_union_E] at hec
        rcases hec with he₁ | he₂
        · exact ⟨c₁, hc₁_C', hcellG_c₁.symm ▸ he₁⟩
        · exact ⟨c₂, hc₂_C', hcellG_c₂.symm ▸ he₂⟩
      · exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
          (hcellG_other c ⟨hc, hcc₀⟩).symm ▸ hec⟩
    p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
      rw [hC'] at hd₁ hd₂
      rcases hd₁ with rfl | rfl | hd₁I <;> rcases hd₂ with rfl | rfl | hd₂I
      · exact (hne rfl).elim
      · rw [hcellG_c₁, hcellG_c₂]; exact hA_disj_E
      · rw [hcellG_c₁, hcellG_other d₂ hd₂I]
        exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₁_le.2
      · rw [hcellG_c₂, hcellG_c₁]; exact hA_disj_E.symm
      · exact (hne rfl).elim
      · rw [hcellG_c₂, hcellG_other d₂ hd₂I]
        exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₂_le.2
      · rw [hcellG_other d₁ hd₁I, hcellG_c₁]
        exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₁_le.2
      · rw [hcellG_other d₁ hd₁I, hcellG_c₂]
        exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₂_le.2
      · rw [hcellG_other d₁ hd₁I, hcellG_other d₂ hd₂I]
        exact π.p1_disjoint d₁ hd₁I.1 d₂ hd₂I.1 hne
    p2 := fun c hc n hn => by
      rw [hC'] at hc
      rcases hc with rfl | rfl | hcI
      · rw [hcellG_c₁]
        exact hA₁_tc n (htc₁ ▸ hn.1)
      · rw [hcellG_c₂]
        exact hA₂_tc n (htc₂ ▸ hn.1)
      · rw [hcellG_other c hcI]
        exact π.p2 c hcI.1 n hn
    p3_notMem := π.p3_notMem
    p3_subset := fun c hc hbd n hn => by
      rw [hC'] at hc
      rcases hc with rfl | rfl | hcI
      · exact (hint₁ hbd).elim
      · exact (hint₂ hbd).elim
      · rw [hcellG_other c hcI]
        exact π.p3_subset c hcI.1 hbd n hn
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ hm₁ m₂ hm₂ =>
      π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ (hΓN ▸ hm₁) m₂ (hΓN ▸ hm₂)
    p4_notMem := fun Θ hΘ m₁ hm₁ m₂ hm₂ hne =>
      π.p4_notMem Θ hΘ m₁ (hΓN ▸ hm₁) m₂ hm₂ hne
    p5 := hp5_aux
    p6 := fun c hc hbd v hvc ⟨d, hd, hne_dc, hvd⟩ => by
      rw [hC'] at hc hd
      rcases hc with rfl | rfl | hcI
      · exact (hint₁ hbd).elim
      · exact (hint₂ hbd).elim
      · rw [hcellG_other c hcI] at hvc
        rcases hd with rfl | rfl | hdI
        · rw [hcellG_c₁] at hvd
          exact π.p6 c hcI.1 hbd v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁_le.1 hvd⟩
        · rw [hcellG_c₂] at hvd
          exact π.p6 c hcI.1 hbd v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hvd⟩
        · rw [hcellG_other d hdI] at hvd
          exact π.p6 c hcI.1 hbd v hvc ⟨d, hdI.1, hne_dc, hvd⟩
    p7 := fun Θ hΘ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃ =>
      π.p7 Θ hΘ m₁ (hΓN ▸ hm₁) m₂ (hΓN ▸ hm₂) m₃ (hΓN ▸ hm₃) m₄ (hΓN ▸ hm₄) hord w hw₁ hw₃ }

private theorem split_cell_shared_vertices_correspond_to_nodes
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (hdom : π.domγ = π.Γ.N)
    {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C)
    (hint₀ : ¬(c₀ ∩ bd π.S).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    (hA₁_le : A₁ ≤ π.cellGraph c₀)
    (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA₁_not_n₂ : π.nodeVertex n₂ ∉ A₁.vertexSet)
    (hA₂_not_n₁ : π.nodeVertex n₁ ∉ A₂.vertexSet)
    (hA_inter_V : A₁.vertexSet ∩ A₂.vertexSet ⊆ π.nodeVertex '' (tilde c₀ \ {n₁, n₂}))
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (htc₂ : tilde c₂ = tilde c₀ \ {n₁})
    (htc₁ : tilde c₁ = tilde c₀ \ {n₂})
    (Γ' : Painting π.S)
    (hC' : Γ'.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (cellG : Set π.S → Hypergraph α β)
    (hcellG_c₁ : cellG c₁ = A₁)
    (hcellG_c₂ : cellG c₂ = A₂)
    (hcellG_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG d = π.cellGraph d) :
    ∀ c ∈ Γ'.C, ¬(c ∩ bd π.S).Nonempty → ∀ v ∈ (cellG c).vertexSet, (∃ d ∈ Γ'.C, d ≠ c ∧ v ∈
      (cellG d).vertexSet) → v ∈ π.nodeVertex '' (tilde c ∩ π.domγ) := by
  intro c hc hint v hvc ⟨d, hd, hne_dc, hvd⟩
  rw [hC'] at hc hd
  rcases hc with hc_eq₁ | hc_eq₂ | hcI
  · subst c
    rw [hcellG_c₁] at hvc
    change v ∈ π.nodeVertex '' (tilde c₁ ∩ π.domγ)
    rw [htc₁, hdom, inter_eq_left.mpr (sdiff_subset.trans (π.Γ.tilde_subset_N hc₀))]
    rcases hd with rfl | rfl | hdI
    · exact (hne_dc rfl).elim
    · rw [hcellG_c₂] at hvd
      obtain ⟨n, ⟨hn_tc, hn_not_pair⟩, rfl⟩ := hA_inter_V ⟨hvc, hvd⟩
      exact ⟨n, ⟨hn_tc, fun h => hn_not_pair (Or.inr h)⟩, rfl⟩
    · rw [hcellG_other d hdI] at hvd
      obtain ⟨n, ⟨hn_tc, _⟩, rfl⟩ :=
        π.p5 c₀ hc₀ hint₀ v (hA₁_le.1 hvc) ⟨d, hdI.1, hdI.2, hvd⟩
      have hnn₂ : n ≠ n₂ := fun h => hA₁_not_n₂ (h ▸ hvc)
      exact ⟨n, ⟨hn_tc, hnn₂⟩, rfl⟩
  · subst c
    rw [hcellG_c₂] at hvc
    change v ∈ π.nodeVertex '' (tilde c₂ ∩ π.domγ)
    rw [htc₂, hdom, inter_eq_left.mpr (sdiff_subset.trans (π.Γ.tilde_subset_N hc₀))]
    rcases hd with rfl | rfl | hdI
    · rw [hcellG_c₁] at hvd
      obtain ⟨n, ⟨hn_tc, hn_not_pair⟩, rfl⟩ := hA_inter_V ⟨hvd, hvc⟩
      exact ⟨n, ⟨hn_tc, fun h => hn_not_pair (Or.inl h)⟩, rfl⟩
    · exact (hne_dc rfl).elim
    · rw [hcellG_other d hdI] at hvd
      obtain ⟨n, ⟨hn_tc, _⟩, rfl⟩ :=
        π.p5 c₀ hc₀ hint₀ v (hA₂_le.1 hvc) ⟨d, hdI.1, hdI.2, hvd⟩
      have hnn₁ : n ≠ n₁ := fun h => hA₂_not_n₁ (h ▸ hvc)
      exact ⟨n, ⟨hn_tc, hnn₁⟩, rfl⟩
  · rw [hcellG_other c hcI] at hvc
    rcases hd with rfl | rfl | hdI
    · rw [hcellG_c₁] at hvd
      exact π.p5 c hcI.1 hint v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁_le.1 hvd⟩
    · rw [hcellG_c₂] at hvd
      exact π.p5 c hcI.1 hint v hvc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hvd⟩
    · rw [hcellG_other d hdI] at hvd
      exact π.p5 c hcI.1 hint v hvc ⟨d, hdI.1, hne_dc, hvd⟩

private theorem disc_inside_cell_has_its_nodes_on_boundary {S : Type}
    [TopologicalSpace S] (Γ : Painting S) {c Δ : Set S} (hc : c ∈ Γ.C)
    (hΔ : IsClosedDisc Δ) (hsub : Δ ⊆ closure c) (hN : Δ ∩ Γ.N ⊆ tilde c) :
    Δ ∩ Γ.N ⊆ discBd Δ := by
  intro x hx
  exact disc_inter_discBd_subset_discBd (Γ.isClosedDisc_closure_cell hc) hΔ hsub
    ⟨hx.1, (Γ.cell_disc c hc).2.1 (hN hx)⟩

private theorem exists_truer_of_splitInternalCell
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hdom : π.domγ = π.Γ.N)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    (htc₀_ge2 : 2 ≤ (tilde c₀).ncard)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂)
    {A₁ A₂ : Hypergraph α β} (hA₁_le : A₁ ≤ π.cellGraph c₀) (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA_union_V : A₁.vertexSet ∪ A₂.vertexSet = (π.cellGraph c₀).vertexSet)
    (hA_union_E : A₁.edgeSet ∪ A₂.edgeSet = (π.cellGraph c₀).edgeSet)
    (hA_disj_E : Disjoint A₁.edgeSet A₂.edgeSet)
    (hA₁_tc : ∀ n ∈ tilde c₀ \ {n₂}, π.nodeVertex n ∈ A₁.vertexSet)
    (hA₂_tc : ∀ n ∈ tilde c₀ \ {n₁}, π.nodeVertex n ∈ A₂.vertexSet)
    (hA₁_not_n₂ : π.nodeVertex n₂ ∉ A₁.vertexSet)
    (hA₂_not_n₁ : π.nodeVertex n₁ ∉ A₂.vertexSet)
    (hA_inter_V : A₁.vertexSet ∩ A₂.vertexSet ⊆ π.nodeVertex '' (tilde c₀ \ {n₁, n₂})) :
    ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.Resembles π ∧ π'.IsTruer π ∧
      ((tilde c₀).ncard = 3 → π'.truth 0 < π.truth 0 ∧
        ∀ w : Set π.S → ℕ, (∀ Θ ∈ cuffs π.S, π.warpAt Θ = w Θ) →
          ∃ ψ : π'.S ≃ₜ π.S, ∀ Θ ∈ cuffs π'.S, π'.warpAt Θ = w (ψ '' Θ)) := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hΔ_inter, htc₁, htc₂⟩ :=
    exists_discs_for_splitInternalCell π.Γ hc₀ htc₀_ge2 hn₁ hn₂ hne
  have hΔ_inter_N : Δ₁ ∩ Δ₂ ⊆ π.Γ.N := by
    rw [hΔ_inter]
    exact sdiff_subset.trans (π.Γ.tilde_subset_N hc₀)
  let c₁ : Set π.S := Δ₁ \ π.Γ.N
  let c₂ : Set π.S := Δ₂ \ π.Γ.N
  have hΔ₁_N_eq : Δ₁ ∩ π.Γ.N = tilde c₀ \ {n₂} := by
    rw [← tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc π.Γ.finite_N, htc₁]
  have hΔ₂_N_eq : Δ₂ ∩ π.Γ.N = tilde c₀ \ {n₁} := by
    rw [← tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc π.Γ.finite_N, htc₂]
  have hΔ₁_bd : Δ₁ ∩ π.Γ.N ⊆ discBd Δ₁ :=
    disc_inside_cell_has_its_nodes_on_boundary π.Γ hc₀ hΔ₁_disc hΔ₁_sub (hΔ₁_N_eq ▸ sdiff_subset)
  have hΔ₂_bd : Δ₂ ∩ π.Γ.N ⊆ discBd Δ₂ :=
    disc_inside_cell_has_its_nodes_on_boundary π.Γ hc₀ hΔ₂_disc hΔ₂_sub (hΔ₂_N_eq ▸ sdiff_subset)
  have hΔ₁_card : (Δ₁ ∩ π.Γ.N).ncard ≤ 3 := by
    rw [hΔ₁_N_eq]
    exact (ncard_le_ncard sdiff_subset (π.Γ.finite_tilde_cell hc₀)).trans
      (π.Γ.ncard_tilde_cell_le hc₀)
  have hΔ₂_card : (Δ₂ ∩ π.Γ.N).ncard ≤ 3 := by
    rw [hΔ₂_N_eq]
    exact (ncard_le_ncard sdiff_subset (π.Γ.finite_tilde_cell hc₀)).trans
      (π.Γ.ncard_tilde_cell_le hc₀)
  let Γ' : Painting π.S :=
    splitInternalCell π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      Subset.rfl π.Γ.finite_N (by simp) hΔ_inter_N hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card
  have hC' : Γ'.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})) :=
    splitInternalCell_C π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      Subset.rfl π.Γ.finite_N (by simp) hΔ_inter_N hΔ₁_bd hΔ₂_bd hΔ₁_card hΔ₂_card
  have hc₁_sub_c₀ : c₁ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact sdiff_le_sdiff_right hΔ₁_sub
  have hc₂_sub_c₀ : c₂ ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact sdiff_le_sdiff_right hΔ₂_sub
  have hc₁_ne : c₁.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₁_disc sdiff_subset
      (π.Γ.finite_N.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₂_ne : c₂.Nonempty :=
    (isPathConnected_of_isClosedDisc_finite_diff hΔ₂_disc sdiff_subset
      (π.Γ.finite_N.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  have hc₁_disj_c₂ : Disjoint c₁ c₂ :=
    Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter_N ⟨hx₁, hx₂⟩)
  have hc₁_ne_c₂ : c₁ ≠ c₂ := by
    rcases hc₁_ne with ⟨x, hx⟩
    exact fun h => Set.disjoint_left.mp hc₁_disj_c₂ hx (h ▸ hx)
  have hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₁_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₁_sub_c₀ hx)
  have hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂ := by
    rintro d ⟨hd, hne₀⟩ rfl
    rcases hc₂_ne with ⟨x, hx⟩
    exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hc₂_sub_c₀ hx)
  have hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₁_sub_c₀))
  have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty :=
    fun h => hint₀ (h.mono (inter_subset_inter_left _ hc₂_sub_c₀))
  have hc₁_C' : c₁ ∈ Γ'.C := hC'.symm ▸ Or.inl rfl
  have hc₂_C' : c₂ ∈ Γ'.C := hC'.symm ▸ Or.inr (Or.inl rfl)
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c₁ then A₁ else if c = c₂ then A₂ else π.cellGraph c
  have hcellG_c₁ : cellG c₁ = A₁ := by simp [cellG]
  have hcellG_c₂ : cellG c₂ = A₂ := by simp [cellG, hc₁_ne_c₂.symm]
  have hcellG_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG d = π.cellGraph d := fun d hd => by
    simp [cellG, hc₁_not_I₀ d hd, hc₂_not_I₀ d hd]
  have hcellG_le : ∀ c ∈ Γ'.C, cellG c ≤ G := by
    intro c hc
    rw [hC'] at hc
    rcases hc with rfl | rfl | hd
    · rw [hcellG_c₁]; exact hA₁_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG_c₂]; exact hA₂_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG_other c hd]; exact π.cellGraph_le c hd.1
  have hp5_aux : ∀ c ∈ Γ'.C, ¬ (c ∩ bd π.S).Nonempty → ∀ v ∈ (cellG c).vertexSet,
      (∃ d ∈ Γ'.C, d ≠ c ∧ v ∈ (cellG d).vertexSet) → v ∈ π.nodeVertex '' (tilde c ∩ π.domγ) := by
    exact split_cell_shared_vertices_correspond_to_nodes (α := α) (β := β) (G := G) π hdom (c₀ :=
      c₀) hc₀ hint₀ (n₁ := n₁) (n₂ := n₂) (A₁ := A₁) (A₂ := A₂) hA₁_le hA₂_le hA₁_not_n₂
      hA₂_not_n₁ hA_inter_V c₁ c₂ htc₂ htc₁ Γ' hC' cellG hcellG_c₁ hcellG_c₂ hcellG_other
  let π' : Portrayal G :=
    split_internal_cell_portrayal (α := α) (β := β) (G := G) π (c₀ := c₀) hc₀ hint₀ htc₀_ge2 (n₁
      := n₁) (n₂ := n₂) hn₁ hn₂ (A₁ := A₁) (A₂ := A₂) hA₁_le hA₂_le hA_union_V hA_union_E
      hA_disj_E hA₁_tc hA₂_tc hA_inter_V Δ₁ Δ₂ hΔ₁_sub hΔ₂_sub hΔ_inter c₁ c₂ htc₂ htc₁ hΔ₁_N_eq
        hΔ₂_N_eq Γ' rfl hC' hc₁_sub_c₀
      hc₂_sub_c₀ hc₁_not_I₀ hc₂_not_I₀ hint₁ hint₂ hc₁_C' hc₂_C' cellG hcellG_c₁ hcellG_c₂
      hcellG_other hcellG_le hp5_aux
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG c)
    have hcases : c ∈ insert c₁ (insert c₂ (π.Γ.C \ {c₀})) := hC' ▸ hc
    rcases hcases with rfl | rfl | hcI
    · have hatt_le := internal_cell_attachments_le_three π' hc₁_C' hint₁
      have hatt_lt : (attachments G (cellG c₁)).ncard < θ := hatt_le.trans_lt (by omega)
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG_c₁ ▸ hA₁_le) hatt_lt
    · have hatt_le := internal_cell_attachments_le_three π' hc₂_C' hint₂
      have hatt_lt : (attachments G (cellG c₂)).ncard < θ := hatt_le.trans_lt (by omega)
      exact IsSmallWrt.mono h𝒯 (hcentral c₀ hc₀) (hcellG_c₂ ▸ hA₂_le) hatt_lt
    · rw [hcellG_other c hcI]
      exact hcentral c hcI.1
  have hπ'_warpAt : ∀ Θ ∈ cuffs π.S, π'.warpAt Θ = π.warpAt Θ := by
    intro Θ hΘ
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hcw_eq : ∀ c ∈ π.Γ.C \ {c₀}, (c ∩ Θ).Nonempty → π'.cellWarp c = π.cellWarp c := by
      intro c hcI _
      change sInf {q | π'.CellWarpLE c q} = sInf {q | π.CellWarpLE c q}
      congr 1; ext q
      change (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
          (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
          ((π.borderPlus n₁).ncard = q + 1 → (π.borderPlus n₂).ncard = q + 1 →
            Portrayal.LinkagePairs (cellG c).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
              (q + 1) (π.nodeVertex n₁) (π.nodeVertex n₂))) ↔ _
      rw [hcellG_other c hcI]
      rfl
    change sSup {p | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    congr 1; ext q
    constructor
    · rintro ⟨c, hc', hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      rw [hC'] at hc'
      rcases hc' with rfl | rfl | hcI
      · exact (hint₁ hbd_c).elim
      · exact (hint₂ hbd_c).elim
      · exact ⟨c, hcI.1, hcΘ, hcw_eq c hcI hcΘ⟩
    · rintro ⟨c, hc_C, hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      have hcc₀ : c ≠ c₀ := fun h => hint₀ (h ▸ hbd_c)
      exact ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc_C, hcc₀⟩), hcΘ, (hcw_eq c ⟨hc_C, hcc₀⟩ hcΘ).symm⟩
  have hπ'_res : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    exact hπ'_warpAt Θ hΘ
  have htc₀_le3 : (tilde c₀).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₀
  let k₀ : Fin 6 := ⟨3 - (tilde c₀).ncard, by omega⟩
  have hk₀_lt : π'.truth k₀ < π.truth k₀ := by
    have htc₁_card : (tilde c₁).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₁ = tilde c₀ \ {n₂} from htc₁, ncard_sdiff_singleton_of_mem hn₂]
    have htc₂_card : (tilde c₂).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₂ = tilde c₀ \ {n₁} from htc₂, ncard_sdiff_singleton_of_mem hn₁]
    have hk₀_lt4 : k₀.1 < 4 := by dsimp [k₀]; omega
    simp only [Portrayal.truth, π', hk₀_lt4, ↓reduceIte]
    have hm_eq : 3 - k₀.1 = (tilde c₀).ncard := by dsimp [k₀]; omega
    have hset_eq :
        {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} =
        {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} := by
      rw [hC']
      ext d
      simp only [mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · omega
        · omega
        · exact ⟨hdI, hint_d, hcard_d⟩
      · rintro ⟨hdI, hint_d, hcard_d⟩
        exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    rw [hset_eq]
    have hssub : {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} ⊂
        {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} := by
      refine ⟨fun d hd => ⟨hd.1.1, hd.2⟩, fun h => ?_⟩
      have hc₀_mem : c₀ ∈ {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} :=
        ⟨hc₀, hint₀, hm_eq.symm⟩
      exact (h hc₀_mem).1.2 rfl
    exact ncard_lt_ncard hssub (π.Γ.finite_cells.subset fun _ hd => hd.1)
  have hπ'_truer : π'.IsTruer π := by
    have htc₁_card : (tilde c₁).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₁ = tilde c₀ \ {n₂} from htc₁, ncard_sdiff_singleton_of_mem hn₂]
    have htc₂_card : (tilde c₂).ncard = (tilde c₀).ncard - 1 := by
      rw [show tilde c₂ = tilde c₀ \ {n₁} from htc₂, ncard_sdiff_singleton_of_mem hn₁]
    have hset_eq : ∀ m : ℕ, (tilde c₀).ncard ≤ m →
        {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = m} =
        {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = m} := by
      intro m hm
      rw [hC']
      ext d
      simp only [mem_sep_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
        · omega
        · omega
        · exact ⟨hdI, hint_d, hcard_d⟩
      · rintro ⟨hdI, hint_d, hcard_d⟩
        exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
    refine ⟨k₀, fun i hi => ?_, hk₀_lt⟩
    have hi_lt : i.1 < 3 - (tilde c₀).ncard := hi
    have hi4 : i.1 < 4 := by omega
    simp only [Portrayal.truth, π', hi4, ↓reduceIte]
    rw [hset_eq (3 - i.1) (by omega)]
    congr 1; ext d
    simp only [mem_sep_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hd, _⟩, h⟩ => ⟨hd, h⟩,
      fun ⟨hd, hint_d, hcard_d⟩ => ⟨⟨hd, fun hEq => by subst hEq; omega⟩, hint_d, hcard_d⟩⟩
  refine ⟨π', hπ'_central, hπ'_res, hπ'_truer, fun h3 => ⟨?_, fun w hw => ?_⟩⟩
  · have hk0 : k₀ = 0 := by ext; simp [k₀, h3]
    exact hk0 ▸ hk₀_lt
  · refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    rw [Homeomorph.refl_apply, image_id, hπ'_warpAt Θ hΘ, hw Θ hΘ]

/-- **Graph Minors XVII, (9.1)** (page 183):
"Let $c_0$ be an internal cell, and let $v_1, v_2 \in \gamma(\tilde{c}_0)$. Then there is a path in
$\alpha(c_0)^*$ from $v_1$ to $v_2$ with no other vertex in $\gamma(\tilde{c}_0)$." -/
theorem theorem_9_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    ∃ L : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
      ∀ z ∈ L.walk.support, z ∈ π.nodeVertex '' tilde c₀ →
        z = π.nodeVertex n₁ ∨ z = π.nodeVertex n₂ := by
  classical
  by_contra hno_path
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  obtain ⟨_, h82_card, _⟩ :=
    theorem_8_2_proof h𝒯 π htrue hred hwarp hθ
  have htc₀_ge2 : 2 ≤ (tilde c₀).ncard := h82_card c₀ hc₀
  have htc₀_dom : tilde c₀ ⊆ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀
  set v₁ := π.nodeVertex n₁
  set v₂ := π.nodeVertex n₂
  have hv₁_mem : v₁ ∈ (π.cellGraph c₀).vertexSet :=
    π.p2 c₀ hc₀ n₁ ⟨hn₁, htc₀_dom hn₁⟩
  have hv₂_mem : v₂ ∈ (π.cellGraph c₀).vertexSet :=
    π.p2 c₀ hc₀ n₂ ⟨hn₂, htc₀_dom hn₂⟩
  let H₀ := π.cellGraph c₀
  let K : Set α := (π.nodeVertex '' tilde c₀) \ {v₁, v₂}
  have hK_sub : K ⊆ H₀.vertexSet := by
    rintro _ ⟨⟨n, hn_tc, rfl⟩, _⟩
    exact π.p2 c₀ hc₀ n ⟨hn_tc, htc₀_dom hn_tc⟩
  let X₁ : Set α :=
    {z ∈ H₀.vertexSet \ K | ∃ w : H₀.skeleton.Walk v₁ z, ∀ u ∈ w.support, u ∉ K}
  have hv₁_not_K : v₁ ∉ K := fun h => h.2 (Or.inl rfl)
  have hv₂_not_K : v₂ ∉ K := fun h => h.2 (Or.inr rfl)
  have hv₁_X₁ : v₁ ∈ X₁ := by
    refine ⟨⟨hv₁_mem, hv₁_not_K⟩, SimpleGraph.Walk.nil, ?_⟩
    intro u hu
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    subst hu
    exact hv₁_not_K
  have hv₂_not_X₁ : v₂ ∉ X₁ := by
    rintro ⟨_, w, hw⟩
    apply hno_path
    refine ⟨⟨v₁, v₂, w.toPath, w.toPath.2, rfl, rfl⟩, ?_⟩
    intro z hz hz_img
    by_contra hnot
    exact hw z (SimpleGraph.Walk.support_toPath_subset_support w hz) ⟨hz_img, hnot⟩
  have hedge_X₁ : ∀ e ∈ H₀.edgeSet, (∃ x ∈ X₁, H₀.Inc e x) →
      ∀ y, H₀.Inc e y → y ∈ X₁ ∪ K := by
    rintro e _ ⟨x, ⟨⟨hxV, hx_not_K⟩, w, hw⟩, hx_inc⟩ y hy_inc
    have hyV : y ∈ H₀.vertexSet := H₀.vertex_mem_of_inc hy_inc
    by_cases hyK : y ∈ K
    · exact Or.inr hyK
    · left
      by_cases hyx : y = x
      · subst hyx; exact ⟨⟨hxV, hx_not_K⟩, w, hw⟩
      · have hadj : H₀.skeleton.Adj x y := ⟨Ne.symm hyx, e, hx_inc, hy_inc⟩
        refine ⟨⟨hyV, hyK⟩, w.concat hadj, ?_⟩
        intro u hu
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
        rcases hu with huw | rfl
        · exact hw u huw
        · exact hyK
  let A₁ : Hypergraph α β :=
    { vertexSet := X₁ ∪ K
      edgeSet := {e ∈ H₀.edgeSet | ∃ x ∈ X₁, H₀.Inc e x}
      Inc := fun e y => (e ∈ H₀.edgeSet ∧ ∃ x ∈ X₁, H₀.Inc e x) ∧ H₀.Inc e y
      vertex_mem_of_inc := fun e y ⟨⟨he, hx⟩, hy⟩ => hedge_X₁ e he hx y hy
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := H₀.vertexSet_finite.subset (union_subset (fun _ hx => hx.1.1) hK_sub)
      edgeSet_finite := H₀.edgeSet_finite.subset (sep_subset _ _) }
  let A₂ : Hypergraph α β :=
    { vertexSet := H₀.vertexSet \ X₁
      edgeSet := {e ∈ H₀.edgeSet | ¬ ∃ x ∈ X₁, H₀.Inc e x}
      Inc := fun e y => (e ∈ H₀.edgeSet ∧ ¬ ∃ x ∈ X₁, H₀.Inc e x) ∧ H₀.Inc e y
      vertex_mem_of_inc := fun _ y ⟨⟨_, hnot⟩, hy⟩ => ⟨H₀.vertex_mem_of_inc hy, fun hyX₁
        => hnot ⟨y, hyX₁, hy⟩⟩
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := H₀.vertexSet_finite.subset sdiff_subset
      edgeSet_finite := H₀.edgeSet_finite.subset (sep_subset _ _) }
  have hA₁_le : A₁ ≤ H₀ :=
    ⟨union_subset (fun _ hx => hx.1.1) hK_sub, sep_subset _ _, fun e he => by
      ext y; exact ⟨fun hy => ⟨he, hy⟩, fun hy => hy.2⟩⟩
  have hA₂_le : A₂ ≤ H₀ :=
    ⟨sdiff_subset, sep_subset _ _, fun e he => by
      ext y; exact ⟨fun hy => ⟨he, hy⟩, fun hy => hy.2⟩⟩
  have hA_union_V : A₁.vertexSet ∪ A₂.vertexSet = H₀.vertexSet := by
    refine Subset.antisymm (union_subset hA₁_le.1 hA₂_le.1) fun v hv => ?_
    by_cases hvX₁ : v ∈ X₁
    · exact Or.inl (Or.inl hvX₁)
    · exact Or.inr ⟨hv, hvX₁⟩
  have hA_union_E : A₁.edgeSet ∪ A₂.edgeSet = H₀.edgeSet := by
    ext e
    simp only [A₁, A₂, mem_union, mem_sep_iff]
    refine ⟨fun h => h.elim And.left And.left, fun he => ?_⟩
    by_cases h : ∃ x ∈ X₁, H₀.Inc e x
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  have hA_disj_E : Disjoint A₁.edgeSet A₂.edgeSet :=
    Set.disjoint_left.mpr fun _ he₁ he₂ => he₂.2 he₁.2
  have hA₁_tc : ∀ n ∈ tilde c₀ \ {n₂}, π.nodeVertex n ∈ A₁.vertexSet := by
    rintro n ⟨hn_tc, hnn₂⟩
    by_cases hnn₁ : n = n₁
    · subst hnn₁; exact Or.inl hv₁_X₁
    · right
      refine ⟨⟨n, hn_tc, rfl⟩, ?_⟩
      rintro (hEq | hEq)
      · exact hnn₁ (π.nodeVertex_injOn (htc₀_dom hn_tc) (htc₀_dom hn₁) hEq)
      · exact hnn₂ (π.nodeVertex_injOn (htc₀_dom hn_tc) (htc₀_dom hn₂) hEq)
  have hA₂_tc : ∀ n ∈ tilde c₀ \ {n₁}, π.nodeVertex n ∈ A₂.vertexSet := by
    rintro n ⟨hn_tc, hnn₁⟩
    by_cases hnn₂ : n = n₂
    · subst hnn₂; exact ⟨hv₂_mem, hv₂_not_X₁⟩
    · have hnK : π.nodeVertex n ∈ K := by
        refine ⟨⟨n, hn_tc, rfl⟩, ?_⟩
        rintro (hEq | hEq)
        · exact hnn₁ (π.nodeVertex_injOn (htc₀_dom hn_tc) (htc₀_dom hn₁) hEq)
        · exact hnn₂ (π.nodeVertex_injOn (htc₀_dom hn_tc) (htc₀_dom hn₂) hEq)
      exact ⟨hK_sub hnK, fun hX₁ => hX₁.1.2 hnK⟩
  have hA₁_not_n₂ : π.nodeVertex n₂ ∉ A₁.vertexSet := by
    rintro (hX₁ | hK)
    · exact hv₂_not_X₁ hX₁
    · exact hv₂_not_K hK
  have hA₂_not_n₁ : π.nodeVertex n₁ ∉ A₂.vertexSet := fun h => h.2 hv₁_X₁
  have hA_inter_V : A₁.vertexSet ∩ A₂.vertexSet ⊆ π.nodeVertex '' (tilde c₀ \ {n₁, n₂}) := by
    rintro z ⟨hX₁ | ⟨⟨n, hn_tc, rfl⟩, hnot_pair⟩, _, hnot_X₁⟩
    · exact (hnot_X₁ hX₁).elim
    · refine ⟨n, ⟨hn_tc, ?_⟩, rfl⟩
      rintro (rfl | rfl)
      · exact hnot_pair (Or.inl rfl)
      · exact hnot_pair (Or.inr rfl)
  obtain ⟨π', hπ'_central, hπ'_res, hπ'_truer, _⟩ :=
    exists_truer_of_splitInternalCell h𝒯 (by omega) π htrue.1 hdom hc₀ hint₀ htc₀_ge2
      hn₁ hn₂ hne hA₁_le hA₂_le hA_union_V hA_union_E hA_disj_E
      hA₁_tc hA₂_tc hA₁_not_n₂ hA₂_not_n₁ hA_inter_V
  exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res

/-! ## 2. Three-Ended Internal Cell Separation: (9.2) (Page 184) -/

private theorem exists_subdisc_inter_discBd_eq_pair {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {s t : S}
    (hs : s ∈ discBd D) (ht : t ∈ discBd D) (hst : s ≠ t) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ D ∧ s ∈ Δ ∧ t ∈ Δ ∧ Δ ∩ discBd D = {s, t} := by
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, _⟩ :=
    exists_chord_in_closedDisc hD hs ht hst
  obtain ⟨B₁, B₂, G₁, G₂, _, hB_comp, hG₁_disc, _, hG_union, hG_inter, hG₁_bd, _, _⟩ :=
    disc_iArc D F₁ s t hD hF₁_sub hst hF₁_line hF₁_bd
  have hG₁_sub : G₁ ⊆ D := hG_union ▸ subset_union_left
  have hF₁_G₁ : F₁ ⊆ G₁ := hG_inter ▸ inter_subset_left
  have hs_F₁ : s ∈ F₁ := by
    have : s ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have ht_F₁ : t ∈ F₁ := by
    have : t ∈ F₁ ∩ discBd D := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hs_bdG₁ : s ∈ discBd G₁ := hG₁_bd ▸ Or.inr hs_F₁
  have ht_bdG₁ : t ∈ discBd G₁ := hG₁_bd ▸ Or.inr ht_F₁
  have hB₁_mem : B₁ ∈ componentsIn (discBd D \ {s, t}) := by rw [hB_comp]; exact Or.inl rfl
  rcases hB₁_mem with ⟨x₁, hx₁_diff, hB₁_eq⟩
  have hB₁_sub_diff : B₁ ⊆ discBd G₁ \ {s, t} := by
    intro x hxB₁
    have hx_bdD : x ∈ discBd D \ {s, t} := by
      rw [← hB₁_eq] at hxB₁
      exact connectedComponentIn_subset (discBd D \ {s, t}) x₁ hxB₁
    exact ⟨hG₁_bd ▸ Or.inl hxB₁, hx_bdD.2⟩
  have hx₁_B₁ : x₁ ∈ B₁ := hB₁_eq ▸ mem_connectedComponentIn hx₁_diff
  have hB₁_preconn : IsPreconnected B₁ := hB₁_eq ▸ isPreconnected_connectedComponentIn
  obtain ⟨F₂, hF₂_sub, hF₂_line, hF₂_bd, _⟩ :=
    exists_chord_in_closedDisc hG₁_disc hs_bdG₁ ht_bdG₁ hst
  obtain ⟨C₁, C₂, H₁, H₂, hC_ne, hC_comp, hH₁_disc, hH₂_disc, hH_union, hH_inter,
    hH₁_bd, hH₂_bd, _⟩ :=
    disc_iArc G₁ F₂ s t hG₁_disc hF₂_sub hst hF₂_line hF₂_bd
  have hs_F₂ : s ∈ F₂ := by
    have : s ∈ F₂ ∩ discBd G₁ := by rw [hF₂_bd]; exact Or.inl rfl
    exact this.1
  have ht_F₂ : t ∈ F₂ := by
    have : t ∈ F₂ ∩ discBd G₁ := by rw [hF₂_bd]; exact Or.inr rfl
    exact this.1
  have hx₁_diffG₁ : x₁ ∈ discBd G₁ \ {s, t} := hB₁_sub_diff hx₁_B₁
  have hcomp_mem : connectedComponentIn (discBd G₁ \ {s, t}) x₁ ∈ ({C₁, C₂} : Set (Set S)) := by
    rw [← hC_comp]
    exact ⟨x₁, hx₁_diffG₁, rfl⟩
  have hB₁_in_comp : B₁ ⊆ connectedComponentIn (discBd G₁ \ {s, t}) x₁ :=
    hB₁_preconn.subset_connectedComponentIn hx₁_B₁ hB₁_sub_diff
  have hC₁_mem : C₁ ∈ componentsIn (discBd G₁ \ {s, t}) := by rw [hC_comp]; exact Or.inl rfl
  have hC₂_mem : C₂ ∈ componentsIn (discBd G₁ \ {s, t}) := by rw [hC_comp]; exact Or.inr rfl
  have hC_disj : Disjoint C₁ C₂ := by
    rcases hC₁_mem with ⟨y₁, hy₁, rfl⟩
    rcases hC₂_mem with ⟨y₂, hy₂, rfl⟩
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => hC_ne ?_
    rw [connectedComponentIn_eq hz₁, connectedComponentIn_eq hz₂]
  have hchoose_H : ∃ C Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ G₁ ∧ F₂ ⊆ Δ ∧
      discBd Δ = C ∪ F₂ ∧ Disjoint C B₁ := by
    rcases hcomp_mem with hEq | hEq
    · refine ⟨C₂, H₂, hH₂_disc, hH_union ▸ subset_union_right, ?_, hH₂_bd, ?_⟩
      · rw [← hH_inter]; exact inter_subset_right
      · exact hC_disj.symm.mono_right (hEq ▸ hB₁_in_comp)
    · have hEq' : connectedComponentIn (discBd G₁ \ {s, t}) x₁ = C₂ := hEq
      refine ⟨C₁, H₁, hH₁_disc, hH_union ▸ subset_union_left, ?_, hH₁_bd, ?_⟩
      · rw [← hH_inter]; exact inter_subset_left
      · exact hC_disj.mono_right (hEq' ▸ hB₁_in_comp)
  obtain ⟨C, Δ, hΔ_disc, hΔ_sub_G₁, hF₂_Δ, hΔ_bd, hC_disj_B₁⟩ := hchoose_H
  have hΔ_sub : Δ ⊆ D := hΔ_sub_G₁.trans hG₁_sub
  refine ⟨Δ, hΔ_disc, hΔ_sub, hF₂_Δ hs_F₂, hF₂_Δ ht_F₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxΔ, hx_bdD⟩
    have hx_bdG₁ : x ∈ discBd G₁ :=
      disc_inter_discBd_subset_discBd hD hG₁_disc hG₁_sub ⟨hΔ_sub_G₁ hxΔ, hx_bdD⟩
    have hx_bdΔ : x ∈ discBd Δ :=
      disc_inter_discBd_subset_discBd hD hΔ_disc hΔ_sub ⟨hxΔ, hx_bdD⟩
    rw [hΔ_bd] at hx_bdΔ
    rcases hx_bdΔ with hxC | hxF₂
    · have hxF₁ : x ∈ F₁ := by
        rw [hG₁_bd] at hx_bdG₁
        exact hx_bdG₁.resolve_left (Set.disjoint_left.mp hC_disj_B₁ hxC)
      have : x ∈ F₁ ∩ discBd D := ⟨hxF₁, hx_bdD⟩
      rwa [hF₁_bd] at this
    · have : x ∈ F₂ ∩ discBd G₁ := ⟨hxF₂, hx_bdG₁⟩
      rwa [hF₂_bd] at this
  · rintro x (rfl | rfl)
    · exact ⟨hF₂_Δ hs_F₂, hs⟩
    · exact ⟨hF₂_Δ ht_F₂, ht⟩

private theorem exists_discs_for_9_2 {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₀ : Set S} (hc₀ : c₀ ∈ Γ.C)
    {n₁ n₂ n₃ : S} (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃) :
    ∃ n₀ ∈ c₀, ∃ Δ₁ Δ₂ : Set S,
      IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ⊆ closure c₀ ∧ Δ₂ ⊆ closure c₀ ∧
      Δ₁ ∩ Δ₂ = {n₀} ∧
      Δ₁ ∩ insert n₀ Γ.N = {n₀, n₁, n₃} ∧
      Δ₂ ∩ insert n₀ Γ.N = {n₀, n₂} ∧
      Δ₁ ∩ insert n₀ Γ.N ⊆ discBd Δ₁ ∧
      Δ₂ ∩ insert n₀ Γ.N ⊆ discBd Δ₂ := by
  have hD : IsClosedDisc (closure c₀) := Γ.isClosedDisc_closure_cell hc₀
  have htc₀_bd : tilde c₀ ⊆ discBd (closure c₀) := (Γ.cell_disc c₀ hc₀).2.1
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have hn₁_bd : n₁ ∈ discBd (closure c₀) := htc₀_bd hn₁_tc
  have hn₂_bd : n₂ ∈ discBd (closure c₀) := htc₀_bd hn₂_tc
  have hn₃_bd : n₃ ∈ discBd (closure c₀) := htc₀_bd hn₃_tc
  obtain ⟨F₁, hF₁_sub, hF₁_line, hF₁_bd, _⟩ :=
    exists_chord_in_closedDisc hD hn₁_bd hn₃_bd h13
  obtain ⟨ev, hev0, hev1⟩ := hF₁_line
  let u₀ : 𝕀 := ⟨1 / 2, by constructor <;> norm_num⟩
  let n₀ : S := (ev u₀).1
  have hn₀_F₁ : n₀ ∈ F₁ := (ev u₀).2
  have hn₀_ne_n₁ : n₀ ≠ n₁ := fun h => by
    have hEq : ev u₀ = ev 0 := Subtype.ext (h.trans hev0.symm)
    have hval := congrArg Subtype.val (ev.injective hEq)
    norm_num [u₀] at hval
  have hn₀_ne_n₃ : n₀ ≠ n₃ := fun h => by
    have hEq : ev u₀ = ev 1 := Subtype.ext (h.trans hev1.symm)
    have hval := congrArg Subtype.val (ev.injective hEq)
    norm_num [u₀] at hval
  have hn₀_not_bd : n₀ ∉ discBd (closure c₀) := by
    intro hbd
    have : n₀ ∈ F₁ ∩ discBd (closure c₀) := ⟨hn₀_F₁, hbd⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact hn₀_ne_n₁ hEq
    · exact hn₀_ne_n₃ hEq
  have hn₀_c₀ : n₀ ∈ c₀ := by
    have hcl : n₀ ∈ closure c₀ := hF₁_sub hn₀_F₁
    by_contra hnot
    exact hn₀_not_bd (htc₀_bd ⟨hcl, hnot⟩)
  obtain ⟨A₁, A₂, E₁, E₂, _, _, hE₁_disc, hE₂_disc, hE_union, hE_inter, hE₁_bd, hE₂_bd, _⟩ :=
    disc_iArc (closure c₀) F₁ n₁ n₃ hD hF₁_sub h13 ⟨ev, hev0, hev1⟩ hF₁_bd
  have hn₁_F₁ : n₁ ∈ F₁ := by
    have : n₁ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inl rfl
    exact this.1
  have hn₃_F₁ : n₃ ∈ F₁ := by
    have : n₃ ∈ F₁ ∩ discBd (closure c₀) := by rw [hF₁_bd]; exact Or.inr rfl
    exact this.1
  have hn₂_not_F₁ : n₂ ∉ F₁ := by
    intro hmem
    have : n₂ ∈ F₁ ∩ discBd (closure c₀) := ⟨hmem, hn₂_bd⟩
    rw [hF₁_bd] at this
    rcases this with hEq | hEq
    · exact h12 hEq.symm
    · exact h23 hEq
  have hn₂_D : n₂ ∈ E₁ ∪ E₂ := hE_union.symm ▸ discBd_subset (closure c₀) hn₂_bd
  have hhalf : ∃ Δ₁ D' : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc D' ∧
      Δ₁ ⊆ closure c₀ ∧ D' ⊆ closure c₀ ∧ Δ₁ ∩ D' = F₁ ∧
      F₁ ⊆ discBd Δ₁ ∧ F₁ ⊆ discBd D' ∧
      n₂ ∉ Δ₁ ∧ n₂ ∈ discBd D' := by
    rcases hn₂_D with hn₂_E₁ | hn₂_E₂
    · have hn₂_not_E₂ : n₂ ∉ E₂ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨hn₂_E₁, h⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₂, E₁, hE₂_disc, hE₁_disc, hE₂_sub, hE₁_sub, ?_, ?_, ?_, hn₂_not_E₂, ?_⟩
      · rw [Set.inter_comm, hE_inter]
      · rw [hE₂_bd]; exact subset_union_right
      · rw [hE₁_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₁_disc hE₁_sub ⟨hn₂_E₁, hn₂_bd⟩
    · have hn₂_not_E₁ : n₂ ∉ E₁ := fun h => hn₂_not_F₁ (hE_inter ▸ ⟨h, hn₂_E₂⟩)
      have hE₁_sub : E₁ ⊆ closure c₀ := hE_union ▸ subset_union_left
      have hE₂_sub : E₂ ⊆ closure c₀ := hE_union ▸ subset_union_right
      refine ⟨E₁, E₂, hE₁_disc, hE₂_disc, hE₁_sub, hE₂_sub, hE_inter, ?_, ?_, hn₂_not_E₁, ?_⟩
      · rw [hE₁_bd]; exact subset_union_right
      · rw [hE₂_bd]; exact subset_union_right
      · exact disc_inter_discBd_subset_discBd hD hE₂_disc hE₂_sub ⟨hn₂_E₂, hn₂_bd⟩
  obtain ⟨Δ₁, D', hΔ₁_disc, hD'_disc, hΔ₁_sub, hD'_sub, hΔ₁D'_inter, hF₁_bdΔ₁,
    hF₁_bdD', hn₂_not_Δ₁, hn₂_bdD'⟩ := hhalf
  have hF₁_Δ₁ : F₁ ⊆ Δ₁ := hF₁_bdΔ₁.trans (discBd_subset Δ₁)
  have hn₀_bdD' : n₀ ∈ discBd D' := hF₁_bdD' hn₀_F₁
  have h20 : n₂ ≠ n₀ := fun h => hn₀_not_bd (h ▸ hn₂_bd)
  obtain ⟨Δ₂, hΔ₂_disc, hΔ₂_sub', hn₂_Δ₂, hn₀_Δ₂, hΔ₂_bdD'_inter⟩ :=
    exists_subdisc_inter_discBd_eq_pair hD'_disc hn₂_bdD' hn₀_bdD' h20
  have hΔ₂_sub : Δ₂ ⊆ closure c₀ := hΔ₂_sub'.trans hD'_sub
  have hinter : Δ₁ ∩ Δ₂ = {n₀} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁, hx₂⟩
      have hxF₁ : x ∈ F₁ := hΔ₁D'_inter ▸ ⟨hx₁, hΔ₂_sub' hx₂⟩
      have hx_pair : x ∈ ({n₂, n₀} : Set S) := hΔ₂_bdD'_inter ▸ ⟨hx₂, hF₁_bdD' hxF₁⟩
      rcases hx_pair with rfl | rfl
      · exact (hn₂_not_Δ₁ hx₁).elim
      · rfl
    · rintro x rfl
      exact ⟨hF₁_Δ₁ hn₀_F₁, hn₀_Δ₂⟩
  have hcl_inter_N : closure c₀ ∩ Γ.N = {n₁, n₂, n₃} := by
    rw [← htc₀]
    ext x
    simp only [mem_inter_iff, tilde, mem_sdiff]
    exact ⟨fun ⟨hxcl, hxN⟩ => ⟨hxcl, fun hxc₀ => (Γ.cell_subset_diff hc₀ hxc₀).2 hxN⟩,
      fun hxtc₀ => ⟨hxtc₀.1, Γ.tilde_subset_N hc₀ hxtc₀⟩⟩
  have hΔ₁_N' : Δ₁ ∩ insert n₀ Γ.N = {n₀, n₁, n₃} := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, rfl | hxN⟩
      · exact Or.inl rfl
      · have hx3 : x ∈ ({n₁, n₂, n₃} : Set S) := hcl_inter_N ▸ ⟨hΔ₁_sub hx₁, hxN⟩
        rcases hx3 with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact (hn₂_not_Δ₁ hx₁).elim
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨hF₁_Δ₁ hn₀_F₁, Or.inl rfl⟩
      · exact ⟨hF₁_Δ₁ hn₁_F₁, Or.inr (Γ.tilde_subset_N hc₀ hn₁_tc)⟩
      · exact ⟨hF₁_Δ₁ hn₃_F₁, Or.inr (Γ.tilde_subset_N hc₀ hn₃_tc)⟩
  have hΔ₂_N' : Δ₂ ∩ insert n₀ Γ.N = {n₀, n₂} := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx₂, hxn₀ | hxN⟩
      · exact Or.inl hxn₀
      · have hx3 : x ∈ ({n₁, n₂, n₃} : Set S) := hcl_inter_N ▸ ⟨hΔ₂_sub hx₂, hxN⟩
        rcases hx3 with hEq | hEq | hEq
        · have : n₁ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₁_F₁, hEq ▸ hx₂⟩
          rw [hinter] at this
          exact (hn₀_ne_n₁ this.symm).elim
        · exact Or.inr hEq
        · have : n₃ ∈ Δ₁ ∩ Δ₂ := ⟨hF₁_Δ₁ hn₃_F₁, hEq ▸ hx₂⟩
          rw [hinter] at this
          exact (hn₀_ne_n₃ this.symm).elim
    · rintro (rfl | rfl)
      · exact ⟨hn₀_Δ₂, Or.inl rfl⟩
      · exact ⟨hn₂_Δ₂, Or.inr (Γ.tilde_subset_N hc₀ hn₂_tc)⟩
  have hΔ₁_bdN' : Δ₁ ∩ insert n₀ Γ.N ⊆ discBd Δ₁ := by
    rw [hΔ₁_N']
    rintro x (rfl | rfl | rfl)
    · exact hF₁_bdΔ₁ hn₀_F₁
    · exact hF₁_bdΔ₁ hn₁_F₁
    · exact hF₁_bdΔ₁ hn₃_F₁
  have hΔ₂_bdN' : Δ₂ ∩ insert n₀ Γ.N ⊆ discBd Δ₂ := by
    rw [hΔ₂_N']
    rintro x (rfl | rfl)
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₀_Δ₂, hn₀_bdD'⟩
    · exact disc_inter_discBd_subset_discBd hD'_disc hΔ₂_disc hΔ₂_sub' ⟨hn₂_Δ₂, hn₂_bdD'⟩
  exact ⟨n₀, hn₀_c₀, Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hinter,
    hΔ₁_N', hΔ₂_N', hΔ₁_bdN', hΔ₂_bdN'⟩

open Classical in
private noncomputable abbrev split_internal_cell_with_new_node_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C)
    (hint₀ : ¬(c₀ ∩ bd π.S).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    {n₃ : π.S}
    (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    (hcard3 : (tilde c₀).ncard = 3)
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    {A₃ : Hypergraph α β}
    {v : α}
    (hA₁_le : A₁ ≤ π.cellGraph c₀)
    (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA₃_le : A₃ ≤ π.cellGraph c₀)
    (hv : v ∈ (π.cellGraph c₀).vertexSet)
    (hn₁_A₁ : π.nodeVertex n₁ ∈ A₁.vertexSet)
    (hn₂_A₂ : π.nodeVertex n₂ ∈ A₂.vertexSet)
    (hn₃_A₃ : π.nodeVertex n₃ ∈ A₃.vertexSet)
    (hA_union : A₁ ∪ A₂ ∪ A₃ = π.cellGraph c₀)
    (hdom : π.domγ = π.Γ.N)
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hn₃_tc : n₃ ∈ tilde c₀)
    (htc₀_dom : tilde c₀ ⊆ π.domγ)
    (hA₁₃_le : A₁ ∪ A₃ ≤ π.cellGraph c₀)
    (hA₂₃_le : A₂ ∪ A₃ ≤ π.cellGraph c₀)
    (hsep_1_23 : (π.cellGraph c₀).IsSeparation A₁ (A₂ ∪ A₃))
    (hsep_13_2 : (π.cellGraph c₀).IsSeparation (A₁ ∪ A₃) A₂)
    (hv_not_tc₀ : ∀ n ∈ tilde c₀, v ≠ π.nodeVertex n)
    (hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet)
    (hv_not_nodeVertex : ∀ n ∈ π.Γ.N, v ≠ π.nodeVertex n)
    (hv_not_borderSet : ∀ n ∈ π.Γ.N ∩ bd π.S, v ∉ π.borderSet n)
    (n₀ : π.S)
    (hn₀_c₀ : n₀ ∈ c₀)
    (Δ₁ : Set π.S)
    (Δ₂ : Set π.S)
    (hΔ₁_sub : Δ₁ ⊆ closure c₀)
    (hΔ₂_sub : Δ₂ ⊆ closure c₀)
    (hΔ_inter : Δ₁ ∩ Δ₂ = {n₀})
    (hΔ₁_N' : Δ₁ ∩ insert n₀ π.Γ.N = {n₀, n₁, n₃})
    (hΔ₂_N' : Δ₂ ∩ insert n₀ π.Γ.N = {n₀, n₂})
    (hΔ₁_bdN' : Δ₁ ∩ insert n₀ π.Γ.N ⊆ discBd Δ₁)
    (hΔ₂_bdN' : Δ₂ ∩ insert n₀ π.Γ.N ⊆ discBd Δ₂)
    (hn₀_not_N : n₀ ∉ π.Γ.N)
    (hn₀_not_bd : n₀ ∉ bd π.S)
    (hn₀_not_tc₀ : n₀ ∉ tilde c₀)
    (hn₀_ne_n₁ : n₀ ≠ n₁)
    (hn₀_ne_n₂ : n₀ ≠ n₂)
    (hn₀_ne_n₃ : n₀ ≠ n₃)
    (N' : Set π.S)
    (hN' : N' = insert n₀ π.Γ.N)
    (hN_sub : π.Γ.N ⊆ N')
    (hN'_fin : N'.Finite)
    (hN'_diff : N' \ π.Γ.N ⊆ Δ₁ ∩ Δ₂)
    (hΔ_inter_N' : Δ₁ ∩ Δ₂ ⊆ N')
    (hΔ₁_card : (Δ₁ ∩ N').ncard = 3)
    (hΔ₂_card : (Δ₂ ∩ N').ncard = 2)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (Γ₁ : Painting π.S)
    (hΓN : Γ₁.N = N')
    (hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (htc₁ : tilde c₁ = {n₀, n₁, n₃})
    (htc₂ : tilde c₂ = {n₀, n₂})
    (hc₁_sub_c₀ : c₁ ⊆ c₀)
    (hc₂_sub_c₀ : c₂ ⊆ c₀)
    (hc₁_ne : c₁.Nonempty)
    (hc₂_ne : c₂.Nonempty)
    (hc₁_disj_c₂ : Disjoint c₁ c₂)
    (hc₁_ne_c₂ : c₁ ≠ c₂)
    (hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁)
    (hc₂_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₂)
    (hint₁ : ¬(c₁ ∩ bd π.S).Nonempty)
    (hint₂ : ¬(c₂ ∩ bd π.S).Nonempty)
    (hc₁_C₁ : c₁ ∈ Γ₁.C)
    (hc₂_C₁ : c₂ ∈ Γ₁.C)
    (cellG₁ : Set π.S → Hypergraph α β)
    (nodeV₁ : π.S → α)
    (hcellG₁_c₁ : cellG₁ c₁ = A₁ ∪ A₃)
    (hcellG₁_c₂ : cellG₁ c₂ = A₂)
    (hcellG₁_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG₁ d = π.cellGraph d)
    (hnodeV₁_n₀ : nodeV₁ n₀ = v)
    (hnodeV₁_other : ∀ n ∈ π.Γ.N, nodeV₁ n = π.nodeVertex n)
    (hbd_N' : N' ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hcellG₁_le : ∀ c ∈ Γ₁.C, cellG₁ c ≤ G)
    (hv_mem_A₁ : v ∈ A₁.vertexSet)
    (hv_mem_A₂ : v ∈ A₂.vertexSet)
    (hp5_aux₁ : ∀ c ∈ Γ₁.C, ¬(c ∩ bd π.S).Nonempty → ∀ w ∈ (cellG₁ c).vertexSet, (∃ d ∈ Γ₁.C, d ≠
      c ∧ w ∈ (cellG₁ d).vertexSet) → w ∈ nodeV₁ '' (tilde c ∩ N'))
    (hΘ_bd : ∀ Θ ∈ cuffs π.S, Θ ⊆ bd π.S)
    (hN'_Θ : ∀ Θ ∈ cuffs π.S, N' ∩ Θ = π.Γ.N ∩ Θ) : Portrayal G := by
  subst N'
  let N' : Set π.S := insert n₀ π.Γ.N
  exact {
    S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ₁
    cellGraph := cellG₁
    borderSet := π.borderSet
    domγ := N'
    nodeVertex := nodeV₁
    cellGraph_le := hcellG₁_le
    borderSet_subset := fun n hn => π.borderSet_subset n (hbd_N' ▸ hΓN ▸ hn)
    domγ_subset := hΓN.symm ▸ Subset.rfl
    nodeVertex_mem := fun n hn => by
      rcases hn with rfl | hnN
      · rw [hnodeV₁_n₀]; exact (π.cellGraph_le c₀ hc₀).1 hv
      · rw [hnodeV₁_other n hnN]; exact π.nodeVertex_mem n (hdom ▸ hnN)
    nodeVertex_injOn := fun x hx y hy hEq => by
      rcases hx with rfl | hxN <;> rcases hy with rfl | hyN
      · rfl
      · rw [hnodeV₁_n₀, hnodeV₁_other y hyN] at hEq
        exact (hv_not_nodeVertex y hyN hEq).elim
      · rw [hnodeV₁_other x hxN, hnodeV₁_n₀] at hEq
        exact (hv_not_nodeVertex x hxN hEq.symm).elim
      · rw [hnodeV₁_other x hxN, hnodeV₁_other y hyN] at hEq
        exact π.nodeVertex_injOn (hdom ▸ hxN) (hdom ▸ hyN) hEq
    p1_vertex := fun w hw => by
      obtain ⟨c, hc, hwc⟩ := π.p1_vertex w hw
      by_cases hcc₀ : c = c₀
      · subst hcc₀
        have hwc_union : w ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hA_union.symm ▸ hwc
        rcases hwc_union with (hw₁ | hw₂) | hw₃
        · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ Or.inl hw₁⟩
        · exact ⟨c₂, hc₂_C₁, hcellG₁_c₂.symm ▸ hw₂⟩
        · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ Or.inr hw₃⟩
      · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
          (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hwc⟩
    p1_edge := fun e he => by
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      by_cases hcc₀ : c = c₀
      · subst hcc₀
        have hec_union : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := hA_union.symm ▸ hec
        rcases hec_union with (he₁ | he₂) | he₃
        · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ Or.inl he₁⟩
        · exact ⟨c₂, hc₂_C₁, hcellG₁_c₂.symm ▸ he₂⟩
        · exact ⟨c₁, hc₁_C₁, hcellG₁_c₁.symm ▸ Or.inr he₃⟩
      · exact ⟨c, hC₁.symm ▸ Or.inr (Or.inr ⟨hc, hcc₀⟩),
          (hcellG₁_other c ⟨hc, hcc₀⟩).symm ▸ hec⟩
    p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
      rw [hC₁] at hd₁ hd₂
      rcases hd₁ with rfl | rfl | hd₁I <;> rcases hd₂ with rfl | rfl | hd₂I
      · exact (hne rfl).elim
      · rw [hcellG₁_c₁, hcellG₁_c₂]
        exact hsep_13_2.disjoint_edgeSet
      · rw [hcellG₁_c₁, hcellG₁_other d₂ hd₂I]
        exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₁₃_le.2
      · rw [hcellG₁_c₂, hcellG₁_c₁]
        exact hsep_13_2.disjoint_edgeSet.symm
      · exact (hne rfl).elim
      · rw [hcellG₁_c₂, hcellG₁_other d₂ hd₂I]
        exact (π.p1_disjoint c₀ hc₀ d₂ hd₂I.1 (Ne.symm hd₂I.2)).mono_left hA₂_le.2
      · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₁]
        exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₁₃_le.2
      · rw [hcellG₁_other d₁ hd₁I, hcellG₁_c₂]
        exact (π.p1_disjoint d₁ hd₁I.1 c₀ hc₀ hd₁I.2).mono_right hA₂_le.2
      · rw [hcellG₁_other d₁ hd₁I, hcellG₁_other d₂ hd₂I]
        exact π.p1_disjoint d₁ hd₁I.1 d₂ hd₂I.1 hne
    p2 := fun c hc n hn => by
      rw [hC₁] at hc
      rcases hc with rfl | rfl | hcI
      · rw [hcellG₁_c₁]
        have hntc₁ : n ∈ ({n₀, n₁, n₃} : Set π.S) := htc₁ ▸ hn.1
        rcases hntc₁ with hEq | hEq | hEq
        · rw [hEq, hnodeV₁_n₀]; exact Or.inl hv_mem_A₁
        · rw [hEq, hnodeV₁_other n₁ (π.Γ.tilde_subset_N hc₀ hn₁_tc)]; exact Or.inl hn₁_A₁
        · rw [hEq, hnodeV₁_other n₃ (π.Γ.tilde_subset_N hc₀ hn₃_tc)]; exact Or.inr hn₃_A₃
      · rw [hcellG₁_c₂]
        have hntc₂ : n ∈ ({n₀, n₂} : Set π.S) := htc₂ ▸ hn.1
        rcases hntc₂ with hEq | hEq
        · rw [hEq, hnodeV₁_n₀]; exact hv_mem_A₂
        · rw [hEq, hnodeV₁_other n₂ (π.Γ.tilde_subset_N hc₀ hn₂_tc)]; exact hn₂_A₂
      · rw [hcellG₁_other c hcI]
        have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hcI.1 hn.1
        rw [hnodeV₁_other n hnN]
        exact π.p2 c hcI.1 n ⟨hn.1, hdom ▸ hnN⟩
    p3_notMem := fun n hn => by
      have hn' : n ∈ π.Γ.N ∩ bd π.S := hbd_N' ▸ hn
      rw [hnodeV₁_other n hn'.1]
      exact π.p3_notMem n ⟨hdom ▸ hn'.1, hn'.2⟩
    p3_subset := fun c hc hbd n hn => by
      rw [hC₁] at hc
      rcases hc with rfl | rfl | hcI
      · exact (hint₁ hbd).elim
      · exact (hint₂ hbd).elim
      · rw [hcellG₁_other c hcI]
        exact π.p3_subset c hcI.1 hbd n hn
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ hm₁ m₂ hm₂ =>
      π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne m₁ (hN'_Θ Θ₁ hΘ₁ ▸ hΓN ▸ hm₁) m₂ (hN'_Θ Θ₂ hΘ₂ ▸ hΓN ▸ hm₂)
    p4_notMem := fun Θ hΘ m₁ hm₁ m₂ hm₂ hnot => by
      have hm₁' : m₁ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hΓN ▸ hm₁
      rcases hm₂ with hEq | hm₂N
      · rw [hEq, hnodeV₁_n₀]
        exact hv_not_borderSet m₁ ⟨hm₁'.1, hΘ_bd Θ hΘ hm₁'.2⟩
      · rw [hnodeV₁_other m₂ hm₂N]
        exact π.p4_notMem Θ hΘ m₁ hm₁' m₂ (hdom ▸ hm₂N) hnot
    p5 := hp5_aux₁
    p6 := fun c hc hbd w hwc ⟨d, hd, hne_dc, hwd⟩ => by
      rw [hC₁] at hc hd
      rcases hc with rfl | rfl | hcI
      · exact (hint₁ hbd).elim
      · exact (hint₂ hbd).elim
      · rw [hcellG₁_other c hcI] at hwc
        have hw_bp : ∃ n ∈ tilde c, w ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ w = π.nodeVertex n) := by
          rcases hd with rfl | rfl | hdI
          · rw [hcellG₁_c₁] at hwd
            exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁₃_le.1 hwd⟩
          · rw [hcellG₁_c₂] at hwd
            exact π.p6 c hcI.1 hbd w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hwd⟩
          · rw [hcellG₁_other d hdI] at hwd
            exact π.p6 c hcI.1 hbd w hwc ⟨d, hdI.1, hne_dc, hwd⟩
        rcases hw_bp with ⟨n, hn_tc, hwn | ⟨hn_dom, hwn⟩⟩
        · exact ⟨n, hn_tc, Or.inl hwn⟩
        · have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
          exact ⟨n, hn_tc, Or.inr ⟨Or.inr hnN, hwn.trans (hnodeV₁_other n hnN).symm⟩⟩
    p7 := fun Θ hΘ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃ => by
      have hm₁' : m₁ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hΓN ▸ hm₁
      have hm₂' : m₂ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hΓN ▸ hm₂
      have hm₃' : m₃ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hΓN ▸ hm₃
      have hm₄' : m₄ ∈ π.Γ.N ∩ Θ := hN'_Θ Θ hΘ ▸ hΓN ▸ hm₄
      have hbp_iff : ∀ m ∈ π.Γ.N ∩ Θ,
          (w ∈ π.borderSet m ∨ (m ∈ N' ∧ w = nodeV₁ m)) ↔
          (w ∈ π.borderSet m ∨ (m ∈ π.domγ ∧ w = π.nodeVertex m)) := by
        rintro m ⟨hmN, _⟩
        have hmN' : m ∈ N' := Or.inr hmN
        have hmdom : m ∈ π.domγ := hdom ▸ hmN
        simp [hmN', hmdom, hnodeV₁_other m hmN]
      have hw₁' := (hbp_iff m₁ hm₁').mp hw₁
      have hw₃' := (hbp_iff m₃ hm₃').mp hw₃
      rcases π.p7 Θ hΘ m₁ hm₁' m₂ hm₂' m₃ hm₃' m₄ hm₄' hord w hw₁' hw₃' with hw₂' | hw₄'
      · exact Or.inl ((hbp_iff m₂ hm₂').mpr hw₂')
      · exact Or.inr ((hbp_iff m₄ hm₄').mpr hw₄') }

private theorem new_node_split_shared_vertices_correspond_to_nodes
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C)
    (hint₀ : ¬(c₀ ∩ bd π.S).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    {n₃ : π.S}
    (htc₀ : tilde c₀ = {n₁, n₂, n₃})
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    {A₃ : Hypergraph α β}
    {v : α}
    (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hv : v ∈ (π.cellGraph c₀).vertexSet)
    (hn₁_A₁ : π.nodeVertex n₁ ∈ A₁.vertexSet)
    (hn₂_A₂ : π.nodeVertex n₂ ∈ A₂.vertexSet)
    (hn₃_A₃ : π.nodeVertex n₃ ∈ A₃.vertexSet)
    (hV12 : (A₁ ∩ A₂).vertexSet = {v})
    (hV13 : (A₁ ∩ A₃).vertexSet = {v})
    (hV23 : (A₂ ∩ A₃).vertexSet = {v})
    (hdom : π.domγ = π.Γ.N)
    (hA₁₃_le : A₁ ∪ A₃ ≤ π.cellGraph c₀)
    (hV_1_23 : (A₁ ∩ (A₂ ∪ A₃)).vertexSet = {v})
    (hV_13_2 : ((A₁ ∪ A₃) ∩ A₂).vertexSet = {v})
    (hv_ne_n₁ : v ≠ π.nodeVertex n₁)
    (hv_ne_n₂ : v ≠ π.nodeVertex n₂)
    (hv_ne_n₃ : v ≠ π.nodeVertex n₃)
    (hv_not_tc₀ : ∀ n ∈ tilde c₀, v ≠ π.nodeVertex n)
    (hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet)
    (hv_not_nodeVertex : ∀ n ∈ π.Γ.N, v ≠ π.nodeVertex n)
    (hv_not_borderSet : ∀ n ∈ π.Γ.N ∩ bd π.S, v ∉ π.borderSet n)
    (n₀ : π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (Γ₁ : Painting π.S)
    (hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (htc₁ : tilde c₁ = {n₀, n₁, n₃})
    (htc₂ : tilde c₂ = {n₀, n₂})
    (cellG₁ : Set π.S → Hypergraph α β)
    (nodeV₁ : π.S → α)
    (hcellG₁_c₁ : cellG₁ c₁ = A₁ ∪ A₃)
    (hcellG₁_c₂ : cellG₁ c₂ = A₂)
    (hcellG₁_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG₁ d = π.cellGraph d)
    (hnodeV₁_n₀ : nodeV₁ n₀ = v)
    (hnodeV₁_other : ∀ n ∈ π.Γ.N, nodeV₁ n = π.nodeVertex n)
    (hv_mem_A₁ : v ∈ A₁.vertexSet)
    (hv_mem_A₂ : v ∈ A₂.vertexSet)
    (hv_mem_A₃ : v ∈ A₃.vertexSet) :
    ∀ c ∈ Γ₁.C, ¬(c ∩ bd π.S).Nonempty → ∀ w ∈ (cellG₁ c).vertexSet, (∃ d ∈ Γ₁.C, d ≠ c ∧ w ∈
      (cellG₁ d).vertexSet) → w ∈ nodeV₁ '' (tilde c ∩ (insert n₀ π.Γ.N)) := by
  let N' := insert n₀ π.Γ.N
  intro c hc hint w hwc ⟨d, hd, hne_dc, hwd⟩
  rw [hC₁] at hc hd
  rcases hc with rfl | rfl | hcI
  · rw [hcellG₁_c₁] at hwc
    rw [htc₁]
    rcases hd with rfl | rfl | hdI
    · exact (hne_dc rfl).elim
    · rw [hcellG₁_c₂] at hwd
      have hw_v : w = v := by
        have : w ∈ ((A₁ ∪ A₃) ∩ A₂).vertexSet := ⟨hwc, hwd⟩
        rwa [hV_13_2, mem_singleton_iff] at this
      subst hw_v
      exact ⟨n₀, ⟨Or.inl rfl, Or.inl rfl⟩, hnodeV₁_n₀⟩
    · rw [hcellG₁_other d hdI] at hwd
      obtain ⟨n, ⟨hn_tc₀, hn_dom⟩, hnw⟩ :=
        π.p5 c₀ hc₀ hint₀ w (hA₁₃_le.1 hwc) ⟨d, hdI.1, hdI.2, hwd⟩
      have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
      rw [htc₀] at hn_tc₀
      rcases hn_tc₀ with hEq | hEq | hEq
      · exact ⟨n, ⟨Or.inr (Or.inl hEq), Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
      · exfalso
        have : π.nodeVertex n₂ ∈ ((A₁ ∪ A₃) ∩ A₂).vertexSet := ⟨hEq ▸ hnw ▸ hwc, hn₂_A₂⟩
        rw [hV_13_2, mem_singleton_iff] at this
        exact hv_ne_n₂ this.symm
      · exact ⟨n, ⟨Or.inr (Or.inr hEq), Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
  · rw [hcellG₁_c₂] at hwc
    rw [htc₂]
    rcases hd with rfl | rfl | hdI
    · rw [hcellG₁_c₁] at hwd
      have hw_v : w = v := by
        have : w ∈ ((A₁ ∪ A₃) ∩ A₂).vertexSet := ⟨hwd, hwc⟩
        rwa [hV_13_2, mem_singleton_iff] at this
      subst hw_v
      exact ⟨n₀, ⟨Or.inl rfl, Or.inl rfl⟩, hnodeV₁_n₀⟩
    · exact (hne_dc rfl).elim
    · rw [hcellG₁_other d hdI] at hwd
      obtain ⟨n, ⟨hn_tc₀, hn_dom⟩, hnw⟩ :=
        π.p5 c₀ hc₀ hint₀ w (hA₂_le.1 hwc) ⟨d, hdI.1, hdI.2, hwd⟩
      have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
      rw [htc₀] at hn_tc₀
      rcases hn_tc₀ with hEq | hEq | hEq
      · exfalso
        have : π.nodeVertex n₁ ∈ (A₁ ∩ A₂).vertexSet := ⟨hn₁_A₁, hEq ▸ hnw ▸ hwc⟩
        rw [hV12, mem_singleton_iff] at this
        exact hv_ne_n₁ this.symm
      · exact ⟨n, ⟨Or.inr hEq, Or.inr hnN⟩, (hnodeV₁_other n hnN).trans hnw⟩
      · exfalso
        have : π.nodeVertex n₃ ∈ (A₂ ∩ A₃).vertexSet := ⟨hEq ▸ hnw ▸ hwc, hn₃_A₃⟩
        rw [hV23, mem_singleton_iff] at this
        exact hv_ne_n₃ this.symm
  · rw [hcellG₁_other c hcI] at hwc
    have hsub : π.nodeVertex '' (tilde c ∩ π.domγ) ⊆ nodeV₁ '' (tilde c ∩ N') := by
      rintro _ ⟨n, ⟨hn_tc, hn_dom⟩, rfl⟩
      have hnN : n ∈ π.Γ.N := hdom ▸ hn_dom
      exact ⟨n, ⟨hn_tc, Or.inr hnN⟩, hnodeV₁_other n hnN⟩
    apply hsub
    rcases hd with rfl | rfl | hdI
    · rw [hcellG₁_c₁] at hwd
      exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hA₁₃_le.1 hwd⟩
    · rw [hcellG₁_c₂] at hwd
      exact π.p5 c hcI.1 hint w hwc ⟨c₀, hc₀, Ne.symm hcI.2, hA₂_le.1 hwd⟩
    · rw [hcellG₁_other d hdI] at hwd
      exact π.p5 c hcI.1 hint w hwc ⟨d, hdI.1, hne_dc, hwd⟩

private theorem first_piece_separates_from_the_other_pieces
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    {A₃ : Hypergraph α β}
    (hA₁_le : A₁ ≤ π.cellGraph c₀)
    (hA_union : A₁ ∪ A₂ ∪ A₃ = π.cellGraph c₀)
    (hE12 : (A₁ ∩ A₂).edgeSet = ∅)
    (hE13 : (A₁ ∩ A₃).edgeSet = ∅)
    (hA₂₃_le : A₂ ∪ A₃ ≤ π.cellGraph c₀) :
    (π.cellGraph c₀).IsSeparation A₁ (A₂ ∪ A₃) := by
  refine ⟨hA₁_le, hA₂₃_le, ?_, ?_⟩
  · rw [← hA_union]
    ext x
    · change x ∈ A₁.vertexSet ∪ (A₂.vertexSet ∪ A₃.vertexSet) ↔
        x ∈ (A₁.vertexSet ∪ A₂.vertexSet) ∪ A₃.vertexSet
      rw [Set.union_assoc]
    · change x ∈ A₁.edgeSet ∪ (A₂.edgeSet ∪ A₃.edgeSet) ↔
        x ∈ (A₁.edgeSet ∪ A₂.edgeSet) ∪ A₃.edgeSet
      rw [Set.union_assoc]
    · change A₁.Inc _ _ ∨ (A₂.Inc _ _ ∨ A₃.Inc _ _) ↔
        (A₁.Inc _ _ ∨ A₂.Inc _ _) ∨ A₃.Inc _ _
      tauto
  · change A₁.edgeSet ∩ (A₂.edgeSet ∪ A₃.edgeSet) = ∅
    rw [inter_union_distrib_left, show A₁.edgeSet ∩ A₂.edgeSet = ∅ from hE12,
      show A₁.edgeSet ∩ A₃.edgeSet = ∅ from hE13, union_empty]

private theorem middle_piece_separates_from_the_other_pieces
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    {A₁ : Hypergraph α β}
    {A₂ : Hypergraph α β}
    {A₃ : Hypergraph α β}
    (hA₂_le : A₂ ≤ π.cellGraph c₀)
    (hA_union : A₁ ∪ A₂ ∪ A₃ = π.cellGraph c₀)
    (hE12 : (A₁ ∩ A₂).edgeSet = ∅)
    (hE23 : (A₂ ∩ A₃).edgeSet = ∅)
    (hA₁₃_le : A₁ ∪ A₃ ≤ π.cellGraph c₀) :
    (π.cellGraph c₀).IsSeparation (A₁ ∪ A₃) A₂ := by
  refine ⟨hA₁₃_le, hA₂_le, ?_, ?_⟩
  · rw [← hA_union]
    ext x
    · change x ∈ (A₁.vertexSet ∪ A₃.vertexSet) ∪ A₂.vertexSet ↔
        x ∈ (A₁.vertexSet ∪ A₂.vertexSet) ∪ A₃.vertexSet
      rw [Set.union_right_comm]
    · change x ∈ (A₁.edgeSet ∪ A₃.edgeSet) ∪ A₂.edgeSet ↔
        x ∈ (A₁.edgeSet ∪ A₂.edgeSet) ∪ A₃.edgeSet
      rw [Set.union_right_comm]
    · change (A₁.Inc _ _ ∨ A₃.Inc _ _) ∨ A₂.Inc _ _ ↔
        (A₁.Inc _ _ ∨ A₂.Inc _ _) ∨ A₃.Inc _ _
      tauto
  · change (A₁.edgeSet ∪ A₃.edgeSet) ∩ A₂.edgeSet = ∅
    rw [union_inter_distrib_right, show A₁.edgeSet ∩ A₂.edgeSet = ∅ from hE12,
      inter_comm A₃.edgeSet, show A₂.edgeSet ∩ A₃.edgeSet = ∅ from hE23, union_empty]

private theorem internal_split_vertex_is_not_a_node_vertex
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c₀ : Set π.S}
    {v : α}
    (hdom : π.domγ = π.Γ.N)
    (hv_not_tc₀ : ∀ n ∈ tilde c₀, v ≠ π.nodeVertex n)
    (hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet) :
    ∀ n ∈ π.Γ.N, v ≠ π.nodeVertex n := by
  intro n hn hEq
  by_cases hn_tc₀ : n ∈ tilde c₀
  · exact hv_not_tc₀ n hn_tc₀ hEq
  · have h87 :=
      (theorem_8_7_proof
        h𝒯 π htrue hred hwarp hθ hn).1
    have hne_star : {c ∈ π.Γ.CStar | n ∈ tilde c}.Nonempty :=
      nonempty_of_ncard_ne_zero (by omega)
    rcases hne_star with ⟨d, ⟨hd_C, _⟩, hn_td⟩
    have hd_ne : d ≠ c₀ := fun h => hn_tc₀ (h ▸ hn_td)
    exact hv_not_other d hd_C hd_ne (hEq ▸ π.p2 d hd_C n ⟨hn_td, hdom ▸ hn⟩)

private theorem internal_split_vertex_is_not_a_border_vertex
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (hint₀ : ¬(c₀ ∩ bd π.S).Nonempty)
    {v : α}
    (hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet) :
    ∀ n ∈ π.Γ.N ∩ bd π.S, v ∉ π.borderSet n := by
  rintro n ⟨hnN, hnbd⟩ hvb
  let Θ := connectedComponentIn (bd π.S) n
  have hΘ : Θ ∈ cuffs π.S := ⟨n, hnbd, rfl⟩
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  set k := (π.Γ.N ∩ Θ).ncard
  obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hnN, mem_connectedComponentIn hnbd⟩
  rw [← E.range_node] at hn_Θ
  rcases hn_Θ with ⟨i, hi_eq⟩
  let d := E.cell i
  have hd_mem : d ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := E.range_cell ▸ ⟨i, rfl⟩
  have hΘ_sub_bd : Θ ⊆ bd π.S := connectedComponentIn_subset (bd π.S) n
  have hd_bd : (d ∩ bd π.S).Nonempty := hd_mem.2.mono (inter_subset_inter_right _ hΘ_sub_bd)
  have hn_td : n ∈ tilde d := by
    rw [← hi_eq, E.cell_tilde i]
    exact Or.inl rfl
  have hd_ne : d ≠ c₀ := fun h => hint₀ (h ▸ hd_bd)
  exact hv_not_other d hd_mem.1 hd_ne (π.p3_subset d hd_mem.1 hd_bd n hn_td hvb)

private theorem distinct_of_three_node_cardinality {S : Type w} {C : Set S}
    {n₁ n₂ n₃ : S} (htc₀ : C = {n₁, n₂, n₃}) (hcard3 : C.ncard = 3) :
    n₁ ≠ n₂ ∧ n₁ ≠ n₃ ∧ n₂ ≠ n₃ := by
  have hpair_le : ∀ a b : S, ({a, b} : Set S).ncard ≤ 2 := fun a b => by
    have := ncard_insert_le a {b}
    rw [ncard_singleton] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    have : C.ncard ≤ 2 := by
      rw [htc₀, insert_idem]
      exact hpair_le n₁ n₃
    omega
  · rintro rfl
    have : C.ncard ≤ 2 := by
      rw [htc₀]
      have hEq : ({n₁, n₂, n₁} : Set S) = {n₁, n₂} := by ext; simp [or_comm]
      rw [hEq]
      exact hpair_le n₁ n₂
    omega
  · rintro rfl
    have : C.ncard ≤ 2 := by
      rw [htc₀]
      have hEq : ({n₁, n₂, n₂} : Set S) = {n₁, n₂} := by ext; simp
      rw [hEq]
      exact hpair_le n₁ n₂
    omega

private theorem split_vertex_is_not_third_node
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p) (hθ : 4 * p + 5 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    (htc₀_dom : tilde c₀ ⊆ π.domγ)
    {n₁ n₂ n₃ : π.S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hn₃ : n₃ ∈ tilde c₀)
    (h12 : n₁ ≠ n₂) (h31 : n₃ ≠ n₁) (h32 : n₃ ≠ n₂)
    {A B : Hypergraph α β} {v : α} (hsep : (π.cellGraph c₀).IsSeparation A B)
    (hinter : (A ∩ B).vertexSet = {v})
    (hfirst : π.nodeVertex n₁ ∈ A.vertexSet) (hlast : π.nodeVertex n₂ ∈ B.vertexSet) :
    v ≠ π.nodeVertex n₃ := by
  intro heq
  obtain ⟨L, hL⟩ := theorem_9_1_proof h𝒯 π htrue hred hwarp hθ hc₀ hint₀ hn₁ hn₂ h12
  have hf : L.first ∈ A.vertexSet := (mem_singleton_iff.mp L.first_mem).symm ▸ hfirst
  have hl : L.last ∈ B.vertexSet := (mem_singleton_iff.mp L.last_mem).symm ▸ hlast
  obtain ⟨z, hz_sup, hz_inter⟩ := walk_meets_separation hsep L.walk hf hl
  rw [hinter, mem_singleton_iff] at hz_inter
  subst hz_inter
  rcases hL z hz_sup ⟨n₃, hn₃, heq.symm⟩ with h1 | h2
  · exact h31 (π.nodeVertex_injOn (htc₀_dom hn₃) (htc₀_dom hn₁) (heq.symm.trans h1))
  · exact h32 (π.nodeVertex_injOn (htc₀_dom hn₃) (htc₀_dom hn₂) (heq.symm.trans h2))

private theorem cell_warp_eq_of_preserved_nodes
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G) (c : Set π.S)
    (A : Hypergraph α β) (hA : A = π.cellGraph c)
    (borderPlus : π.S → Set α) (nodeVertex : π.S → α) (warp : ℕ)
    (hwarp : warp = sInf {q | ∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
      (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
        ((borderPlus n₁).ncard = q + 1 → (borderPlus n₂).ncard = q + 1 →
          Portrayal.LinkagePairs A.skeleton (borderPlus n₁) (borderPlus n₂) (q + 1)
            (nodeVertex n₁) (nodeVertex n₂))})
    (hborder : ∀ n ∈ tilde c, borderPlus n = π.borderPlus n)
    (hnode : ∀ n ∈ tilde c, nodeVertex n = π.nodeVertex n) :
    warp = π.cellWarp c := by
  rw [hwarp, Portrayal.cellWarp, hA]
  congr 1
  ext q
  simp only [mem_ofPred_eq, Portrayal.CellWarpLE]
  constructor <;> intro h n₁ hn₁ n₂ hn₂ hne
  · simpa only [hborder n₁ hn₁, hborder n₂ hn₂, hnode n₁ hn₁, hnode n₂ hn₂]
      using h n₁ hn₁ n₂ hn₂ hne
  · simp only [hborder n₁ hn₁, hborder n₂ hn₂, hnode n₁ hn₁, hnode n₂ hn₂]
    exact h n₁ hn₁ n₂ hn₂ hne

private theorem cuff_warp_eq_after_internal_cell_split
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G) (Γ₁ : Painting π.S)
    {c₀ c₁ c₂ : Set π.S} (hC : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty) (hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty)
    (hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty) (Θ : Set π.S) (hΘ : Θ ⊆ bd π.S)
    (cellWarp : Set π.S → ℕ) (warp : ℕ)
    (hwarp : warp = sSup {p | ∃ c ∈ Γ₁.C, (c ∩ Θ).Nonempty ∧ p = cellWarp c})
    (hcellWarp : ∀ c ∈ π.Γ.C \ {c₀}, cellWarp c = π.cellWarp c) :
    warp = π.warpAt Θ := by
  rw [hwarp, Portrayal.warpAt]
  congr 1
  ext q
  constructor
  · rintro ⟨c, hc', hcΘ, rfl⟩
    have hbd_c := hcΘ.mono (inter_subset_inter_right _ hΘ)
    rw [hC] at hc'
    rcases hc' with rfl | rfl | hcI
    · exact (hint₁ hbd_c).elim
    · exact (hint₂ hbd_c).elim
    · exact ⟨c, hcI.1, hcΘ, hcellWarp c hcI⟩
  · rintro ⟨c, hc, hcΘ, rfl⟩
    have hne : c ≠ c₀ := fun h => hint₀ (h ▸ hcΘ.mono (inter_subset_inter_right _ hΘ))
    exact ⟨c, hC.symm ▸ Or.inr (Or.inr ⟨hc, hne⟩), hcΘ, (hcellWarp c ⟨hc, hne⟩).symm⟩

private theorem replacement_internal_cell_geometry
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {c₀ Δ N : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    (hΔ : IsClosedDisc Δ) (hΔ_sub : Δ ⊆ closure c₀)
    (hN_sub : π.Γ.N ⊆ N) (hN_fin : N.Finite) :
    Δ \ N ⊆ c₀ ∧ (Δ \ N).Nonempty ∧
      (∀ d ∈ π.Γ.C \ {c₀}, d ≠ Δ \ N) ∧ ¬ ((Δ \ N) ∩ bd π.S).Nonempty := by
  have hsub : Δ \ N ⊆ c₀ := by
    rw [← π.Γ.closure_cell_diff_N hc₀]
    exact fun x ⟨hxΔ, hxN⟩ => ⟨hΔ_sub hxΔ, fun hx => hxN (hN_sub hx)⟩
  have hne := (isPathConnected_of_isClosedDisc_finite_diff hΔ sdiff_subset
    (hN_fin.subset fun x hx => by by_contra hxN; exact hx.2 ⟨hx.1, hxN⟩)).nonempty
  refine ⟨hsub, hne, ?_, fun h => hint₀ (h.mono (inter_subset_inter_left _ hsub))⟩
  rintro d ⟨hd, hne₀⟩ rfl
  rcases hne with ⟨x, hx⟩
  exact Set.disjoint_left.mp (π.Γ.cell_disjoint hd hc₀ hne₀) hx (hsub hx)

private theorem internal_split_preserves_truth_at_zero
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π π₁ : Portrayal G)
    {c₀ c₁ c₂ : Set π.S} (Γ₁ : Painting π.S)
    (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    (hcard3 : (tilde c₀).ncard = 3)
    (hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})))
    (hc₁_not_I₀ : ∀ d ∈ π.Γ.C \ {c₀}, d ≠ c₁)
    (hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty)
    (htc₁_card : (tilde c₁).ncard = 3) (htc₂_card : (tilde c₂).ncard = 2)
    (htruth : π₁.truth 0 = {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard) :
    π₁.truth 0 = π.truth 0 := by
  let S₀ : Set (Set π.S) := {c ∈ π.Γ.C \ {c₀} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}
  have hS₀_fin : S₀.Finite := π.Γ.finite_cells.subset fun _ hd => hd.1.1
  have h1 : {c ∈ Γ₁.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₁ S₀ := by
    rw [hC₁]
    ext d
    simp only [S₀, mem_sep_iff, mem_insert_iff]
    constructor
    · rintro ⟨rfl | rfl | hdI, hint_d, hcard_d⟩
      · exact Or.inl rfl
      · omega
      · exact Or.inr ⟨hdI, hint_d, hcard_d⟩
    · rintro (rfl | ⟨hdI, hint_d, hcard_d⟩)
      · exact ⟨Or.inl rfl, hint₁, htc₁_card⟩
      · exact ⟨Or.inr (Or.inr hdI), hint_d, hcard_d⟩
  have h2 : {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3} = insert c₀ S₀ := by
    ext d
    simp only [S₀, mem_sep_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hd, hint_d, hcard_d⟩
      by_cases h : d = c₀
      · exact Or.inl h
      · exact Or.inr ⟨⟨hd, h⟩, hint_d, hcard_d⟩
    · rintro (rfl | ⟨⟨hd, _⟩, hint_d, hcard_d⟩)
      · exact ⟨hc₀, hint₀, hcard3⟩
      · exact ⟨hd, hint_d, hcard_d⟩
  have hc₁_not_S₀ : c₁ ∉ S₀ := fun h => hc₁_not_I₀ c₁ h.1 rfl
  have hc₀_not_S₀ : c₀ ∉ S₀ := fun h => h.1.2 rfl
  rw [htruth, show π.truth 0 =
    {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3}.ncard from rfl]
  rw [h1, h2, ncard_insert_of_notMem hc₁_not_S₀ hS₀_fin, ncard_insert_of_notMem hc₀_not_S₀
    hS₀_fin]

private theorem second_split_contradicts_truth
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π π₁ : Portrayal G) (htrue : π.IsTrue 𝒯) (hπ₁_central : π₁.IsCentral 𝒯)
    (hdom₁ : π₁.domγ = π₁.Γ.N)
    (e : π₁.S ≃ₜ π.S)
    (hπ₁_warpAt : ∀ Θ ∈ cuffs π₁.S, π₁.warpAt Θ = π.warpAt (e '' Θ))
    (hπ₁_truth0 : π₁.truth 0 = π.truth 0)
    {c₁ : Set π₁.S} (hc₁_C₁ : c₁ ∈ π₁.Γ.C)
    (hint₁ : ¬ (c₁ ∩ bd π₁.S).Nonempty) (htc₁_card : (tilde c₁).ncard = 3)
    {n₀ n₁ n₃ : π₁.S} (htc₁ : tilde c₁ = {n₀, n₁, n₃})
    (hn₀_ne_n₁ : n₀ ≠ n₁) (hn₀_ne_n₃ : n₀ ≠ n₃) (h13 : n₁ ≠ n₃)
    {A₁ A₃ B : Hypergraph α β} (hA₁_le : A₁ ≤ B) (hA₃_le : A₃ ≤ B)
    (hcellG₁_c₁ : π₁.cellGraph c₁ = A₁ ∪ A₃) (hE13 : (A₁ ∩ A₃).edgeSet = ∅)
    {v a₁ a₃ : α} (hV13 : (A₁ ∩ A₃).vertexSet = {v})
    (hv_mem_A₁ : v ∈ A₁.vertexSet) (hv_mem_A₃ : v ∈ A₃.vertexSet)
    (hn₁_A₁ : a₁ ∈ A₁.vertexSet) (hn₃_A₃ : a₃ ∈ A₃.vertexSet)
    (hv_ne_n₁ : v ≠ a₁) (hv_ne_n₃ : v ≠ a₃)
    (hnodeV₁_n₀ : π₁.nodeVertex n₀ = v)
    (hnodeV₁_n₁ : π₁.nodeVertex n₁ = a₁)
    (hnodeV₁_n₃ : π₁.nodeVertex n₃ = a₃) :
    False := by
  have hn₁_tc₁ : n₁ ∈ tilde c₁ := htc₁ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc₁ : n₃ ∈ tilde c₁ := htc₁ ▸ Or.inr (Or.inr rfl)
  have hA₁_le₁ : A₁ ≤ π₁.cellGraph c₁ := by
    rw [hcellG₁_c₁]
    refine ⟨subset_union_left, subset_union_left, fun e he => ?_⟩
    ext x
    exact ⟨fun hx => hx.elim id (fun hx₃ => (hA₁_le.3 e he ▸ (hA₃_le.3 e
      (A₃.edge_mem_of_inc hx₃)).symm ▸ hx₃)),
      fun hx => Or.inl hx⟩
  have hA₃_le₁ : A₃ ≤ π₁.cellGraph c₁ := by
    rw [hcellG₁_c₁]
    refine ⟨subset_union_right, subset_union_right, fun e he => ?_⟩
    ext x
    exact ⟨fun hx => hx.elim (fun hx₁ => (hA₃_le.3 e he ▸ (hA₁_le.3 e
      (A₁.edge_mem_of_inc hx₁)).symm ▸ hx₁)) id,
      fun hx => Or.inr hx⟩
  have hA₁₃_union_V : A₁.vertexSet ∪ A₃.vertexSet = (π₁.cellGraph c₁).vertexSet := by
    rw [hcellG₁_c₁]; rfl
  have hA₁₃_union_E : A₁.edgeSet ∪ A₃.edgeSet = (π₁.cellGraph c₁).edgeSet := by
    rw [hcellG₁_c₁]; rfl
  have hA₁₃_disj_E : Disjoint A₁.edgeSet A₃.edgeSet :=
    Set.disjoint_iff_inter_eq_empty.mpr hE13
  have hA₁_tc₁ : ∀ n ∈ tilde c₁ \ {n₃}, π₁.nodeVertex n ∈ A₁.vertexSet := by
    rw [htc₁]
    rintro n ⟨hEq | hEq | hEq, hnot⟩
    · rw [hEq, hnodeV₁_n₀]; exact hv_mem_A₁
    · rw [hEq, hnodeV₁_n₁]; exact hn₁_A₁
    · exact (hnot hEq).elim
  have hA₃_tc₁ : ∀ n ∈ tilde c₁ \ {n₁}, π₁.nodeVertex n ∈ A₃.vertexSet := by
    rw [htc₁]
    rintro n ⟨hEq | hEq | hEq, hnot⟩
    · rw [hEq, hnodeV₁_n₀]; exact hv_mem_A₃
    · exact (hnot hEq).elim
    · rw [hEq, hnodeV₁_n₃]; exact hn₃_A₃
  have hA₁_not_n₃ : π₁.nodeVertex n₃ ∉ A₁.vertexSet := by
    rw [hnodeV₁_n₃]
    intro hmem
    have : a₃ ∈ (A₁ ∩ A₃).vertexSet := ⟨hmem, hn₃_A₃⟩
    rw [hV13, mem_singleton_iff] at this
    exact hv_ne_n₃ this.symm
  have hA₃_not_n₁ : π₁.nodeVertex n₁ ∉ A₃.vertexSet := by
    rw [hnodeV₁_n₁]
    intro hmem
    have : a₁ ∈ (A₁ ∩ A₃).vertexSet := ⟨hn₁_A₁, hmem⟩
    rw [hV13, mem_singleton_iff] at this
    exact hv_ne_n₁ this.symm
  have hA₁₃_inter_V : A₁.vertexSet ∩ A₃.vertexSet ⊆ π₁.nodeVertex '' (tilde c₁ \ {n₁, n₃}) := by
    intro w hw
    have hw_v : w = v := by
      have : w ∈ (A₁ ∩ A₃).vertexSet := hw
      rwa [hV13, mem_singleton_iff] at this
    subst hw_v
    refine ⟨n₀, ⟨htc₁ ▸ Or.inl rfl, ?_⟩, hnodeV₁_n₀⟩
    rintro (hEq | hEq)
    · exact hn₀_ne_n₁ hEq
    · exact hn₀_ne_n₃ hEq
  obtain ⟨π', hπ'_central, _, _, hπ'_3⟩ :=
    exists_truer_of_splitInternalCell h𝒯 (by omega) π₁ hπ₁_central hdom₁ hc₁_C₁ hint₁
      (by omega) hn₁_tc₁ hn₃_tc₁ h13 hA₁_le₁ hA₃_le₁ hA₁₃_union_V hA₁₃_union_E hA₁₃_disj_E
      hA₁_tc₁ hA₃_tc₁ hA₁_not_n₃ hA₃_not_n₁ hA₁₃_inter_V
  have hπ'_truer : π'.IsTruer π := by
    refine ⟨0, fun i hi => (Nat.not_lt_zero i.1 hi).elim, ?_⟩
    exact (hπ'_3 htc₁_card).1.trans_eq hπ₁_truth0
  obtain ⟨ψ, hψ⟩ := (hπ'_3 htc₁_card).2 (fun Θ => π.warpAt (e '' Θ)) hπ₁_warpAt
  have hπ'_res : π'.Resembles π := by
    refine ⟨ψ.trans e, fun Θ hΘ => ?_⟩
    rw [hψ Θ hΘ]
    change π.warpAt (e '' (ψ '' Θ)) = π.warpAt ((e ∘ ψ) '' Θ)
    rw [image_comp]
  exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res

/-- **Graph Minors XVII, (9.2)** (page 184):
"Let $c_0$ be an internal cell with $|\tilde{c}_0| = 3$, and $\tilde{c}_0 = \{n_1, n_2, n_3\}$. Then
there
do not exist subhypergraphs $A_1, A_2, A_3 \subseteq \alpha(c_0)$ and $v \in V(\alpha(c_0))$ such
that
$\gamma(n_i) \in V(A_i)$ $(i = 1, 2, 3)$, $A_1 \cup A_2 \cup A_3 = \alpha(c_0)$, and for $1 \le i <
j \le 3$,
$E(A_i \cap A_j) = \emptyset$ and $V(A_i \cap A_j) = \{v\}$." -/
theorem theorem_9_2_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ n₃ : π.S} (htc₀ : tilde c₀ = {n₁, n₂, n₃}) (hcard3 : (tilde c₀).ncard = 3)
    {A₁ A₂ A₃ : Hypergraph α β} {v : α}
    (hA₁_le : A₁ ≤ π.cellGraph c₀) (hA₂_le : A₂ ≤ π.cellGraph c₀) (hA₃_le : A₃ ≤ π.cellGraph c₀)
    (hv : v ∈ (π.cellGraph c₀).vertexSet)
    (hn₁_A₁ : π.nodeVertex n₁ ∈ A₁.vertexSet)
    (hn₂_A₂ : π.nodeVertex n₂ ∈ A₂.vertexSet)
    (hn₃_A₃ : π.nodeVertex n₃ ∈ A₃.vertexSet)
    (hA_union : A₁ ∪ A₂ ∪ A₃ = π.cellGraph c₀)
    (hE12 : (A₁ ∩ A₂).edgeSet = ∅) (hE13 : (A₁ ∩ A₃).edgeSet = ∅) (hE23 : (A₂ ∩ A₃).edgeSet = ∅)
    (hV12 : (A₁ ∩ A₂).vertexSet = {v}) (hV13 : (A₁ ∩ A₃).vertexSet = {v})
    (hV23 : (A₂ ∩ A₃).vertexSet = {v}) :
    False := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  have hn₁_tc : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inl rfl)
  have hn₃_tc : n₃ ∈ tilde c₀ := htc₀ ▸ Or.inr (Or.inr rfl)
  have htc₀_dom : tilde c₀ ⊆ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀
  obtain ⟨h12, h13, h23⟩ := distinct_of_three_node_cardinality htc₀ hcard3
  have hA₁₃_le := union_le hA₁_le hA₃_le
  have hA₂₃_le := union_le hA₂_le hA₃_le
  have hsep_1_23 : (π.cellGraph c₀).IsSeparation A₁ (A₂ ∪ A₃) := by
    exact first_piece_separates_from_the_other_pieces (α := α) (β := β) (G := G) π (c₀ := c₀) (A₁
      := A₁) (A₂ := A₂) (A₃ := A₃) hA₁_le hA_union hE12 hE13 hA₂₃_le
  have hsep_13_2 : (π.cellGraph c₀).IsSeparation (A₁ ∪ A₃) A₂ := by
    exact middle_piece_separates_from_the_other_pieces (α := α) (β := β) (G := G) π (c₀ := c₀) (A₁
      := A₁) (A₂ := A₂) (A₃ := A₃) hA₂_le hA_union hE12 hE23 hA₁₃_le
  have hV_1_23 : (A₁ ∩ (A₂ ∪ A₃)).vertexSet = {v} := by
    change A₁.vertexSet ∩ (A₂.vertexSet ∪ A₃.vertexSet) = {v}
    rw [inter_union_distrib_left, show A₁.vertexSet ∩ A₂.vertexSet = {v} from hV12,
      show A₁.vertexSet ∩ A₃.vertexSet = {v} from hV13, Set.union_self]
  have hV_13_2 : ((A₁ ∪ A₃) ∩ A₂).vertexSet = {v} := by
    change (A₁.vertexSet ∪ A₃.vertexSet) ∩ A₂.vertexSet = {v}
    rw [union_inter_distrib_right, show A₁.vertexSet ∩ A₂.vertexSet = {v} from hV12,
      inter_comm A₃.vertexSet, show A₂.vertexSet ∩ A₃.vertexSet = {v} from hV23, Set.union_self]
  have hv_ne_n₁ := split_vertex_is_not_third_node h𝒯 π htrue hred hwarp hθ hc₀ hint₀
    htc₀_dom hn₃_tc hn₂_tc hn₁_tc h23.symm h13 h12 hsep_13_2 hV_13_2 (Or.inr hn₃_A₃) hn₂_A₂
  have hv_ne_n₂ := split_vertex_is_not_third_node h𝒯 π htrue hred hwarp hθ hc₀ hint₀
    htc₀_dom hn₁_tc hn₃_tc hn₂_tc h13 h12.symm h23 hsep_1_23 hV_1_23 hn₁_A₁ (Or.inr hn₃_A₃)
  have hv_ne_n₃ := split_vertex_is_not_third_node h𝒯 π htrue hred hwarp hθ hc₀ hint₀
    htc₀_dom hn₁_tc hn₂_tc hn₃_tc h12 h13.symm h23.symm hsep_1_23 hV_1_23 hn₁_A₁ (Or.inl hn₂_A₂)
  have hv_not_tc₀ : ∀ n ∈ tilde c₀, v ≠ π.nodeVertex n := by
    rw [htc₀]
    rintro n (rfl | rfl | rfl)
    · exact hv_ne_n₁
    · exact hv_ne_n₂
    · exact hv_ne_n₃
  have hv_not_other : ∀ d ∈ π.Γ.C, d ≠ c₀ → v ∉ (π.cellGraph d).vertexSet := by
    intro d hd hne hvd
    obtain ⟨n, ⟨hn_tc, _⟩, hEq⟩ := π.p5 c₀ hc₀ hint₀ v hv ⟨d, hd, hne, hvd⟩
    exact hv_not_tc₀ n hn_tc hEq.symm
  have hv_not_nodeVertex : ∀ n ∈ π.Γ.N, v ≠ π.nodeVertex n := by
    exact internal_split_vertex_is_not_a_node_vertex (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ)
      (p := p) h𝒯 π htrue hred hwarp hθ (c₀ := c₀) (v := v) hdom hv_not_tc₀ hv_not_other
  have hv_not_borderSet : ∀ n ∈ π.Γ.N ∩ bd π.S, v ∉ π.borderSet n := by
    exact internal_split_vertex_is_not_a_border_vertex (α := α) (β := β) (G := G) π (c₀ := c₀)
      hint₀ (v := v) hv_not_other
  obtain ⟨n₀, hn₀_c₀, Δ₁, Δ₂, hΔ₁_disc, hΔ₂_disc, hΔ₁_sub, hΔ₂_sub, hΔ_inter,
    hΔ₁_N', hΔ₂_N', hΔ₁_bdN', hΔ₂_bdN'⟩ :=
    exists_discs_for_9_2 π.Γ hc₀ htc₀ h12 h13 h23
  have hn₀_not_N : n₀ ∉ π.Γ.N := (π.Γ.cell_subset_diff hc₀ hn₀_c₀).2
  have hn₀_not_bd : n₀ ∉ bd π.S := fun hbd => hint₀ ⟨n₀, hn₀_c₀, hbd⟩
  have hn₀_not_tc₀ : n₀ ∉ tilde c₀ := fun h => hn₀_not_N (π.Γ.tilde_subset_N hc₀ h)
  have hn₀_ne_n₁ : n₀ ≠ n₁ := fun h => hn₀_not_tc₀ (h ▸ hn₁_tc)
  have hn₀_ne_n₂ : n₀ ≠ n₂ := fun h => hn₀_not_tc₀ (h ▸ hn₂_tc)
  have hn₀_ne_n₃ : n₀ ≠ n₃ := fun h => hn₀_not_tc₀ (h ▸ hn₃_tc)
  let N' : Set π.S := insert n₀ π.Γ.N
  have hN_sub : π.Γ.N ⊆ N' := subset_insert n₀ π.Γ.N
  have hN'_fin : N'.Finite := π.Γ.finite_N.insert n₀
  have hN'_diff : N' \ π.Γ.N ⊆ Δ₁ ∩ Δ₂ := by
    rw [hΔ_inter]
    rintro x ⟨rfl | hxN, hx_not_N⟩
    · rfl
    · exact (hx_not_N hxN).elim
  have hΔ_inter_N' : Δ₁ ∩ Δ₂ ⊆ N' := by
    rw [hΔ_inter]
    rintro x rfl
    exact Or.inl rfl
  have hΔ₁_card : (Δ₁ ∩ N').ncard = 3 := by
    rw [hΔ₁_N', ncard_insert_of_notMem, ncard_pair h13]
    rintro (rfl | rfl)
    · exact hn₀_ne_n₁ rfl
    · exact hn₀_ne_n₃ rfl
  have hΔ₂_card : (Δ₂ ∩ N').ncard = 2 := by
    rw [hΔ₂_N', ncard_pair hn₀_ne_n₂]
  let c₁ : Set π.S := Δ₁ \ N'
  let c₂ : Set π.S := Δ₂ \ N'
  let Γ₁ : Painting π.S :=
    splitInternalCell π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N' hΔ₁_bdN' hΔ₂_bdN' hΔ₁_card.le (by omega)
  have hC₁ : Γ₁.C = insert c₁ (insert c₂ (π.Γ.C \ {c₀})) :=
    splitInternalCell_C π.Γ hc₀ hint₀ hΔ₁_disc hΔ₂_disc hΔ₁_sub hΔ₂_sub
      hN_sub hN'_fin hN'_diff hΔ_inter_N' hΔ₁_bdN' hΔ₂_bdN' hΔ₁_card.le (by omega)
  have htc₁ : tilde c₁ = {n₀, n₁, n₃} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin, hΔ₁_N']
  have htc₂ : tilde c₂ = {n₀, n₂} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin, hΔ₂_N']
  obtain ⟨hc₁_sub_c₀, hc₁_ne, hc₁_not_I₀, hint₁⟩ :=
    replacement_internal_cell_geometry π hc₀ hint₀ hΔ₁_disc hΔ₁_sub hN_sub hN'_fin
  obtain ⟨hc₂_sub_c₀, hc₂_ne, hc₂_not_I₀, hint₂⟩ :=
    replacement_internal_cell_geometry π hc₀ hint₀ hΔ₂_disc hΔ₂_sub hN_sub hN'_fin
  have hc₁_disj_c₂ : Disjoint c₁ c₂ :=
    Set.disjoint_left.mpr fun x ⟨hx₁, hxN⟩ ⟨hx₂, _⟩ => hxN (hΔ_inter_N' ⟨hx₁, hx₂⟩)
  have hc₁_ne_c₂ : c₁ ≠ c₂ := by
    rcases hc₁_ne with ⟨x, hx⟩
    exact fun h => Set.disjoint_left.mp hc₁_disj_c₂ hx (h ▸ hx)
  have hc₁_C₁ : c₁ ∈ Γ₁.C := hC₁.symm ▸ Or.inl rfl
  have hc₂_C₁ : c₂ ∈ Γ₁.C := hC₁.symm ▸ Or.inr (Or.inl rfl)
  let cellG₁ : Set π.S → Hypergraph α β := fun c =>
    if c = c₁ then A₁ ∪ A₃ else if c = c₂ then A₂ else π.cellGraph c
  let nodeV₁ : π.S → α := fun n => if n = n₀ then v else π.nodeVertex n
  have hcellG₁_c₁ : cellG₁ c₁ = A₁ ∪ A₃ := by simp [cellG₁]
  have hcellG₁_c₂ : cellG₁ c₂ = A₂ := by simp [cellG₁, hc₁_ne_c₂.symm]
  have hcellG₁_other : ∀ d ∈ π.Γ.C \ {c₀}, cellG₁ d = π.cellGraph d := fun d hd => by
    have h₁ : d ≠ c₁ := hc₁_not_I₀ d hd
    have h₂ : d ≠ c₂ := hc₂_not_I₀ d hd
    simp only [cellG₁, ite_eq_right h₁, ite_eq_right h₂]
  have hnodeV₁_n₀ : nodeV₁ n₀ = v := by simp [nodeV₁]
  have hnodeV₁_other : ∀ n ∈ π.Γ.N, nodeV₁ n = π.nodeVertex n := fun n hn => by
    have hne : n ≠ n₀ := fun h => hn₀_not_N (h ▸ hn)
    simp [nodeV₁, hne]
  have hbd_N' : N' ∩ bd π.S = π.Γ.N ∩ bd π.S := insert_inter_of_notMem hn₀_not_bd
  have hcellG₁_le : ∀ c ∈ Γ₁.C, cellG₁ c ≤ G := by
    intro c hc
    rw [hC₁] at hc
    rcases hc with rfl | rfl | hd
    · rw [hcellG₁_c₁]; exact hA₁₃_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_c₂]; exact hA₂_le.trans (π.cellGraph_le c₀ hc₀)
    · rw [hcellG₁_other c hd]; exact π.cellGraph_le c hd.1
  have hv12 : v ∈ (A₁ ∩ A₂).vertexSet := hV12.symm ▸ rfl
  have hv13 : v ∈ (A₁ ∩ A₃).vertexSet := hV13.symm ▸ rfl
  have hv_mem_A₁ := hv12.1
  have hv_mem_A₂ := hv12.2
  have hv_mem_A₃ := hv13.2
  have hp5_aux₁ : ∀ c ∈ Γ₁.C, ¬ (c ∩ bd π.S).Nonempty → ∀ w ∈ (cellG₁ c).vertexSet,
      (∃ d ∈ Γ₁.C, d ≠ c ∧ w ∈ (cellG₁ d).vertexSet) → w ∈ nodeV₁ '' (tilde c ∩ N') := by
    exact new_node_split_shared_vertices_correspond_to_nodes (α := α) (β := β) (G := G) π (c₀ :=
      c₀) hc₀ hint₀ (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) htc₀ (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (v :=
      v) hA₂_le hv hn₁_A₁ hn₂_A₂ hn₃_A₃ hV12 hV13 hV23 hdom hA₁₃_le hV_1_23 hV_13_2 hv_ne_n₁
      hv_ne_n₂ hv_ne_n₃ hv_not_tc₀ hv_not_other hv_not_nodeVertex hv_not_borderSet n₀ c₁ c₂ Γ₁ hC₁
      htc₁ htc₂ cellG₁ nodeV₁ hcellG₁_c₁ hcellG₁_c₂ hcellG₁_other hnodeV₁_n₀ hnodeV₁_other
      hv_mem_A₁ hv_mem_A₂ hv_mem_A₃
  have hΘ_bd : ∀ Θ ∈ cuffs π.S, Θ ⊆ bd π.S := by
    rintro Θ ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hN'_Θ : ∀ Θ ∈ cuffs π.S, N' ∩ Θ = π.Γ.N ∩ Θ := fun Θ hΘ =>
    insert_inter_of_notMem (fun hn => hn₀_not_bd (hΘ_bd Θ hΘ hn))
  let π₁ : Portrayal G :=
    split_internal_cell_with_new_node_portrayal (α := α) (β := β) (G := G) π (c₀
      := c₀) hc₀ hint₀ (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) htc₀ hcard3 (A₁ := A₁) (A₂ := A₂) (A₃ :=
      A₃) (v := v) hA₁_le hA₂_le hA₃_le hv hn₁_A₁ hn₂_A₂ hn₃_A₃ hA_union hdom hn₁_tc hn₂_tc hn₃_tc
      htc₀_dom hA₁₃_le hA₂₃_le hsep_1_23 hsep_13_2 hv_not_tc₀ hv_not_other hv_not_nodeVertex
      hv_not_borderSet n₀ hn₀_c₀ Δ₁ Δ₂ hΔ₁_sub hΔ₂_sub hΔ_inter hΔ₁_N' hΔ₂_N'
      hΔ₁_bdN' hΔ₂_bdN' hn₀_not_N hn₀_not_bd hn₀_not_tc₀ hn₀_ne_n₁ hn₀_ne_n₂ hn₀_ne_n₃ N' rfl hN_sub
      hN'_fin hN'_diff hΔ_inter_N' hΔ₁_card hΔ₂_card c₁ c₂ Γ₁ rfl hC₁ htc₁ htc₂ hc₁_sub_c₀
        hc₂_sub_c₀
      hc₁_ne hc₂_ne hc₁_disj_c₂ hc₁_ne_c₂ hc₁_not_I₀ hc₂_not_I₀ hint₁ hint₂ hc₁_C₁ hc₂_C₁ cellG₁
      nodeV₁ hcellG₁_c₁ hcellG₁_c₂ hcellG₁_other hnodeV₁_n₀ hnodeV₁_other hbd_N' hcellG₁_le
      hv_mem_A₁ hv_mem_A₂ hp5_aux₁ hΘ_bd hN'_Θ
  have hπ₁_central : π₁.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG₁ c)
    have hcases : c ∈ insert c₁ (insert c₂ (π.Γ.C \ {c₀})) := hC₁ ▸ hc
    rcases hcases with rfl | rfl | hcI
    · have hatt_le := internal_cell_attachments_le_three π₁ hc₁_C₁ hint₁
      have hatt_lt : (attachments G (cellG₁ c₁)).ncard < θ := hatt_le.trans_lt (by omega)
      exact IsSmallWrt.mono h𝒯 (htrue.1 c₀ hc₀) (hcellG₁_c₁ ▸ hA₁₃_le) hatt_lt
    · have hatt_le := internal_cell_attachments_le_three π₁ hc₂_C₁ hint₂
      have hatt_lt : (attachments G (cellG₁ c₂)).ncard < θ := hatt_le.trans_lt (by omega)
      exact IsSmallWrt.mono h𝒯 (htrue.1 c₀ hc₀) (hcellG₁_c₂ ▸ hA₂_le) hatt_lt
    · rw [hcellG₁_other c hcI]
      exact htrue.1 c hcI.1
  have hπ₁_warpAt : ∀ Θ ∈ cuffs π.S, π₁.warpAt Θ = π.warpAt Θ := by
    intro Θ hΘ
    refine cuff_warp_eq_after_internal_cell_split π Γ₁ hC₁ hint₀ hint₁ hint₂ Θ (hΘ_bd Θ hΘ)
      π₁.cellWarp (π₁.warpAt Θ) rfl ?_
    intro c hcI
    refine cell_warp_eq_of_preserved_nodes π c (cellG₁ c) (hcellG₁_other c hcI)
      π₁.borderPlus nodeV₁ (π₁.cellWarp c) rfl ?_ ?_
    · intro n hn_tc
      have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hcI.1 hn_tc
      have hnN' : n ∈ N' := Or.inr hnN
      have hndom : n ∈ π.domγ := hdom ▸ hnN
      ext w
      change (w ∈ π.borderSet n ∨ (n ∈ N' ∧ w = nodeV₁ n)) ↔
        (w ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ w = π.nodeVertex n))
      simp only [hnN', hndom, hnodeV₁_other n hnN]
    · exact fun n hn => hnodeV₁_other n (π.Γ.tilde_subset_N hcI.1 hn)
  have htc₁_card : (tilde c₁).ncard = 3 := by
    rw [show tilde c₁ = Δ₁ ∩ N' from tilde_diff_eq_of_isClosedDisc_finite hΔ₁_disc hN'_fin,
      hΔ₁_card]
  have htc₂_card : (tilde c₂).ncard = 2 := by
    rw [show tilde c₂ = Δ₂ ∩ N' from tilde_diff_eq_of_isClosedDisc_finite hΔ₂_disc hN'_fin,
      hΔ₂_card]
  have hπ₁_truth0 : π₁.truth 0 = π.truth 0 :=
    internal_split_preserves_truth_at_zero π π₁ Γ₁ hc₀ hint₀ hcard3 hC₁ hc₁_not_I₀ hint₁
      htc₁_card htc₂_card rfl
  exact second_split_contradicts_truth h𝒯 (by omega) π π₁ htrue hπ₁_central rfl
    (Homeomorph.refl π.S) (fun Θ hΘ => by
      change π₁.warpAt Θ = π.warpAt (id '' Θ)
      simpa only [image_id] using hπ₁_warpAt Θ hΘ)
    hπ₁_truth0 hc₁_C₁ hint₁ htc₁_card htc₁ hn₀_ne_n₁ hn₀_ne_n₃ h13
    hA₁_le hA₃_le hcellG₁_c₁ hE13 hV13 hv_mem_A₁ hv_mem_A₃ hn₁_A₁ hn₃_A₃ hv_ne_n₁ hv_ne_n₃
    hnodeV₁_n₀ (hnodeV₁_other n₁ (π.Γ.tilde_subset_N hc₀ hn₁_tc))
    (hnodeV₁_other n₃ (π.Γ.tilde_subset_N hc₀ hn₃_tc))

end GraphMinor.GM17
