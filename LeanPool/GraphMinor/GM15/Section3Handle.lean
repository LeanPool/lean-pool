/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.ControllingTangle

import LeanPool.GraphMinor.GM12.Section79

public import LeanPool.GraphMinor.GM15.Section3Disc
public import LeanPool.GraphMinor.GM15.Section3SpanGlue
public import LeanPool.GraphMinor.Surface.Cap
public import LeanPool.GraphMinor.Surface.EdgeLens
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.ForestRegions

import LeanPool.GraphMinor.GM12.Section5Final

/-!
# Proof of Graph Minors XV, (3.5): Adding a Handle

This file proves `(3.5)` (`theorem_3_5` : `GM15Theorem35Statement`) of N. Robertson and P. D.
Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148 (pages 123–124):
- Section 1 constructs striped closed discs inside `ClosedCylinder` obtained by removing a narrow
  open sector around one missed radial segment `Icc 1 2 ×ˢ {w i₀}`.
- Section 2 constructs the unpinched and pinched handle splits on the glued closed surface
  `S' = GluedSpace hb_inj` obtained by gluing `ClosedCylinder` onto `univ \ (Λ₁ ∪ Λ₂)`.
- Section 3 combines `exists_glued_span_of_lines`, Graph Minors XII (5.1)
  (`GM12Theorem51Statement`),
  and Graph Minors XV (3.2) (`theorem_3_2`) with Claim (1) (`theorem_3_5_claim_1`) to prove
  `theorem_3_5`.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

/-! ## 1. Striped Closed Discs in `ClosedCylinder` -/

/-- Clamp a real number into `Icc 1 2`. -/
def cylClamp (r : ℝ) : ℝ := max 1 (min 2 r)

theorem continuous_cylClamp : Continuous cylClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem cylClamp_mem (r : ℝ) : cylClamp r ∈ Icc (1 : ℝ) 2 :=
  ⟨le_max_left 1 (min 2 r), max_le (by norm_num) (min_le_left 2 r)⟩

theorem cylClamp_of_mem {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) : cylClamp r = r := by
  dsimp [cylClamp]
  rw [min_eq_right hr.2, max_eq_right hr.1]

/-- Map from `ℂ` into `ClosedCylinder` sending `x + iy` to `(cylClamp x, Circle.exp y)`. -/
noncomputable def cylRectMap (z : ℂ) : ClosedCylinder :=
  ⟨(cylClamp z.re, Circle.exp z.im), cylClamp_mem z.re, mem_univ _⟩

theorem continuous_cylRectMap : Continuous cylRectMap := by
  unfold cylRectMap
  refine Continuous.subtype_mk ?_ _
  exact (continuous_cylClamp.comp Complex.continuous_re).prodMk
    (Circle.exp.continuous.comp Complex.continuous_im)

/-- `Circle.exp` is injective on any open interval of length `2π`. -/
theorem circle_exp_injOn_Ioo (θ₀ : ℝ) :
    InjOn Circle.exp (Ioo θ₀ (θ₀ + 2 * Real.pi)) := by
  intro x hx y hy hxy
  let c : ℝ := θ₀ + Real.pi
  have hx' : x - c ∈ Ioo (-Real.pi) Real.pi := by
    dsimp [c]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hy' : y - c ∈ Ioo (-Real.pi) Real.pi := by
    dsimp [c]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hshift : Circle.exp (x - c) = Circle.exp (y - c) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Circle.exp_add, Circle.exp_add, hxy]
  have hcis : cis' (x - c) = cis' (y - c) := congrArg Subtype.val hshift
  have hsub := cis'_injOn hx' hy' hcis
  linarith

/-- `Circle.exp` maps `[θ₀, θ₀ + 2π]` onto `Circle`. -/
theorem circle_exp_surjOn_Icc (θ₀ : ℝ) :
    Circle.exp '' Icc θ₀ (θ₀ + 2 * Real.pi) = univ := by
  rw [eq_univ_iff_forall]
  intro w
  obtain ⟨t, rfl⟩ := ee_surjective w
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let u₀ : ℝ := θ₀ / (2 * Real.pi)
  let u : ℝ := u₀ + Int.fract (t - u₀)
  have hu_eq : ee u = ee t := by
    apply ee_eq_iff.mpr
    refine ⟨-⌊t - u₀⌋, ?_⟩
    dsimp [u]
    have h := Int.self_sub_floor (t - u₀)
    push_cast
    linarith
  refine ⟨2 * Real.pi * u, ⟨?_, ?_⟩, ?_⟩
  · have h1 : 0 ≤ Int.fract (t - u₀) := Int.fract_nonneg (t - u₀)
    have h2 : 2 * Real.pi * u₀ = θ₀ := mul_div_cancel₀ θ₀ hpi.ne'
    nlinarith
  · have h1 : Int.fract (t - u₀) ≤ 1 := (Int.fract_lt_one (t - u₀)).le
    have h2 : 2 * Real.pi * u₀ = θ₀ := mul_div_cancel₀ θ₀ hpi.ne'
    nlinarith
  · exact hu_eq

theorem injOn_cylRectMap (θ₀ ε : ℝ) (hε : 0 < ε) :
    InjOn cylRectMap (Icc 1 2 ×ℂ Icc (θ₀ + ε) (θ₀ + 2 * Real.pi - ε)) := by
  intro z₁ hz₁ z₂ hz₂ h
  obtain ⟨hz₁_re, hz₁_im⟩ := Complex.mem_reProdIm.mp hz₁
  obtain ⟨hz₂_re, hz₂_im⟩ := Complex.mem_reProdIm.mp hz₂
  have h1 := Prod.ext_iff.mp (congrArg Subtype.val h)
  have hre : z₁.re = z₂.re := by
    have hclamp : cylClamp z₁.re = cylClamp z₂.re := h1.1
    rwa [cylClamp_of_mem hz₁_re, cylClamp_of_mem hz₂_re] at hclamp
  have him : z₁.im = z₂.im := by
    refine circle_exp_injOn_Ioo θ₀ ⟨by linarith [hz₁_im.1], by linarith [hz₁_im.2]⟩
      ⟨by linarith [hz₂_im.1], by linarith [hz₂_im.2]⟩ h1.2
  exact Complex.ext hre him

theorem isClosedDisc_image_cylRectMap (θ₀ ε : ℝ) (hε0 : 0 < ε) (hεpi : ε < Real.pi) :
    IsClosedDisc (cylRectMap '' (Icc 1 2 ×ℂ Icc (θ₀ + ε) (θ₀ + 2 * Real.pi - ε))) ∧
      discBd (cylRectMap '' (Icc 1 2 ×ℂ Icc (θ₀ + ε) (θ₀ + 2 * Real.pi - ε))) =
        cylRectMap '' frontier (Icc 1 2 ×ℂ Icc (θ₀ + ε) (θ₀ + 2 * Real.pi - ε)) := by
  have h12 : (1 : ℝ) < 2 := by norm_num
  have hcd : θ₀ + ε < θ₀ + 2 * Real.pi - ε := by linarith
  obtain ⟨hD_rect, hbd_rect⟩ := isClosedDisc_rect h12 hcd
  obtain ⟨hD_img, hbd_img⟩ := hD_rect.image_injOn
    continuous_cylRectMap.continuousOn (injOn_cylRectMap θ₀ ε hε0)
  exact ⟨hD_img, hbd_img.trans (congrArg (cylRectMap '' ·) hbd_rect)⟩

theorem reProdIm_mem_frontier_of_re_eq {a b c d : ℝ} {z : ℂ}
    (hz : z ∈ Icc a b ×ℂ Icc c d) (hre : z.re = a ∨ z.re = b) :
    z ∈ frontier (Icc a b ×ℂ Icc c d) := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq]
  refine ⟨hz, fun hint => ?_⟩
  obtain ⟨r, hr_pos, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  rcases hre with hre_a | hre_b
  · let z' : ℂ := z - (r / 2 : ℝ)
    have hz'_ball : z' ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : z' - z = -(r / 2 : ℝ) := by dsimp [z']; ring
      rw [hsub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hz'_re : a ≤ z'.re := (Complex.mem_reProdIm.mp (hball hz'_ball)).1.1
    have hcalc : z'.re = a - r / 2 := by
      simp [z', hre_a]
    linarith
  · let z' : ℂ := z + (r / 2 : ℝ)
    have hz'_ball : z' ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : z' - z = (r / 2 : ℝ) := by dsimp [z']; ring
      rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hz'_re : z'.re ≤ b := (Complex.mem_reProdIm.mp (hball hz'_ball)).1.2
    have hcalc : z'.re = b + r / 2 := by
      simp [z', hre_b]
    linarith

theorem re_eq_of_mem_frontier_reProdIm {a b c d : ℝ} {z : ℂ}
    (hz : z ∈ frontier (Icc a b ×ℂ Icc c d)) (him : z.im ∈ Ioo c d) :
    z.re = a ∨ z.re = b := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq] at hz
  obtain ⟨hz_mem, hz_not_int⟩ := hz
  obtain ⟨hz_re, _⟩ := Complex.mem_reProdIm.mp hz_mem
  have hopen : IsOpen (Ioo a b ×ℂ Ioo c d) :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hsub : Ioo a b ×ℂ Ioo c d ⊆ interior (Icc a b ×ℂ Icc c d) :=
    interior_maximal
      (fun w hw => Complex.mem_reProdIm.mpr
        ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
         Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩)
      hopen
  have hnot_re : z.re ∉ Ioo a b := fun hre_in =>
    hz_not_int (hsub (Complex.mem_reProdIm.mpr ⟨hre_in, him⟩))
  rcases eq_or_lt_of_le hz_re.1 with h1 | h1
  · exact Or.inl h1.symm
  · rcases eq_or_lt_of_le hz_re.2 with h2 | h2
    · exact Or.inr h2
    · exact (hnot_re ⟨h1, h2⟩).elim

/-- Given `θ₀ : ℝ` and a closed set `K_all ⊆ ClosedCylinder` disjoint from the radial segment
`{p : ClosedCylinder | p.1.2 = Circle.exp θ₀}`, there is a closed disc `D_cyl ⊆ ClosedCylinder`
containing `K_all` such that `D_cyl ∩ bd ↥ClosedCylinder ⊆ discBd D_cyl` and every radial segment
`{p : ClosedCylinder | p.1.2 = w_j} ⊆ K_all` meets `discBd D_cyl` only at its two endpoints. -/
theorem exists_striped_disc_in_closedCylinder (θ₀ : ℝ) {K_all : Set ClosedCylinder}
    (hK_cl : IsClosed K_all)
    (hK_disj : Disjoint K_all {p : ClosedCylinder | p.1.2 = Circle.exp θ₀}) :
    ∃ D_cyl : Set ClosedCylinder,
      IsClosedDisc D_cyl ∧
      K_all ⊆ D_cyl ∧
      Disjoint D_cyl {p : ClosedCylinder | p.1.2 = Circle.exp θ₀} ∧
      D_cyl ∩ bd ↥ClosedCylinder ⊆ discBd D_cyl ∧
      ∀ w_j : Circle, {p : ClosedCylinder | p.1.2 = w_j} ⊆ K_all →
        {p : ClosedCylinder | p.1.2 = w_j} ⊆ D_cyl ∧
        {p : ClosedCylinder | p.1.2 = w_j} ∩ discBd D_cyl =
          {cylEnd 1 (by norm_num) w_j, cylEnd 2 (by norm_num) w_j} := by
  let Q : Set ℂ := Icc 1 2 ×ℂ Icc θ₀ (θ₀ + 2 * Real.pi)
  have hQ_comp : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  let K' : Set ℂ := Q ∩ cylRectMap ⁻¹' K_all
  have hK'_comp : IsCompact K' :=
    hQ_comp.of_isClosed_subset (hQ_comp.isClosed.inter (hK_cl.preimage continuous_cylRectMap))
      inter_subset_left
  let d : ℂ → ℝ := fun z => min (z.im - θ₀) (θ₀ + 2 * Real.pi - z.im)
  have hd_cont : Continuous d :=
    (Complex.continuous_im.sub continuous_const).min (continuous_const.sub Complex.continuous_im)
  have hd_pos : ∀ z ∈ K', 0 < d z := by
    intro z ⟨hzQ, hzK⟩
    obtain ⟨_, hz_im⟩ := Complex.mem_reProdIm.mp hzQ
    have hnot_exp : Circle.exp z.im ≠ Circle.exp θ₀ := fun heq =>
      Set.disjoint_left.mp hK_disj hzK heq
    have hne1 : z.im ≠ θ₀ := fun h => hnot_exp (congrArg Circle.exp h)
    have hne2 : z.im ≠ θ₀ + 2 * Real.pi := fun h => by
      apply hnot_exp
      rw [h, Circle.exp_add, Circle.exp_two_pi, mul_one]
    have hlt1 : θ₀ < z.im := lt_of_le_of_ne hz_im.1 hne1.symm
    have hlt2 : z.im < θ₀ + 2 * Real.pi := lt_of_le_of_ne hz_im.2 hne2
    exact lt_min (by linarith) (by linarith)
  have hex_ε : ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧ ∀ z ∈ K', ε < d z := by
    by_cases hne : K'.Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := hK'_comp.exists_isMinOn hne hd_cont.continuousOn
      have hd₀ : 0 < d z₀ := hd_pos z₀ hz₀
      refine ⟨min (d z₀ / 2) (Real.pi / 4), lt_min (by linarith) (by positivity),
        lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]), fun z hz => ?_⟩
      have hle : d z₀ ≤ d z := hmin hz
      have hlt : min (d z₀ / 2) (Real.pi / 4) ≤ d z₀ / 2 := min_le_left _ _
      linarith
    · rw [not_nonempty_iff_eq_empty] at hne
      refine ⟨Real.pi / 4, by positivity, by linarith [Real.pi_pos], ?_⟩
      intro z hz
      rw [hne] at hz
      exact hz.elim
  obtain ⟨ε, hε0, hε_pi2, hε_lt⟩ := hex_ε
  have hε_pi : ε < Real.pi := by linarith [Real.pi_pos]
  let R_ε : Set ℂ := Icc 1 2 ×ℂ Icc (θ₀ + ε) (θ₀ + 2 * Real.pi - ε)
  let U_ε : Set ℂ := Icc 1 2 ×ℂ Ioo (θ₀ + ε) (θ₀ + 2 * Real.pi - ε)
  let D_cyl : Set ClosedCylinder := cylRectMap '' R_ε
  obtain ⟨hD_disc, hD_bd⟩ := isClosedDisc_image_cylRectMap θ₀ ε hε0 hε_pi
  have hK_sub_U : K_all ⊆ cylRectMap '' U_ε := by
    intro p hp
    have hsurj := circle_exp_surjOn_Icc θ₀
    obtain ⟨t, ht, h_exp⟩ : p.1.2 ∈ Circle.exp '' Icc θ₀ (θ₀ + 2 * Real.pi) :=
      hsurj ▸ mem_univ p.1.2
    let z : ℂ := ⟨p.1.1, t⟩
    have hzQ : z ∈ Q := Complex.mem_reProdIm.mpr ⟨p.2.1, ht⟩
    have hmap : cylRectMap z = p := by
      apply Subtype.ext
      apply Prod.ext
      · dsimp [cylRectMap, z]
        exact cylClamp_of_mem p.2.1
      · exact h_exp
    have hzK' : z ∈ K' := ⟨hzQ, by change cylRectMap z ∈ K_all; rwa [hmap]⟩
    have hd_z : ε < d z := hε_lt z hzK'
    have ht_Ioo : t ∈ Ioo (θ₀ + ε) (θ₀ + 2 * Real.pi - ε) := by
      obtain ⟨h1, h2⟩ := lt_min_iff.mp hd_z
      exact ⟨by dsimp [z] at h1; linarith, by dsimp [z] at h2; linarith⟩
    exact ⟨z, Complex.mem_reProdIm.mpr ⟨p.2.1, ht_Ioo⟩, hmap⟩
  have hU_sub_R : U_ε ⊆ R_ε := fun z hz =>
    Complex.mem_reProdIm.mpr
      ⟨(Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
  have hK_sub_D : K_all ⊆ D_cyl := hK_sub_U.trans (image_mono hU_sub_R)
  have hbd_sub : D_cyl ∩ bd ↥ClosedCylinder ⊆ discBd D_cyl := by
    rw [hD_bd, bd_cylinder]
    rintro _ ⟨⟨z, hzR, rfl⟩, hbd⟩
    obtain ⟨hz_re, _⟩ := Complex.mem_reProdIm.mp hzR
    have hre_12 : z.re = 1 ∨ z.re = 2 := by
      rcases hbd with ⟨w, hw⟩ | ⟨w, hw⟩
      · left
        have h1 : (cylEnd 1 (by norm_num) w).1.1 = (cylRectMap z).1.1 :=
          congrArg (fun q : ClosedCylinder => q.1.1) hw
        dsimp [cylEnd, cylRectMap] at h1
        rw [cylClamp_of_mem hz_re] at h1
        exact h1.symm
      · right
        have h2 : (cylEnd 2 (by norm_num) w).1.1 = (cylRectMap z).1.1 :=
          congrArg (fun q : ClosedCylinder => q.1.1) hw
        dsimp [cylEnd, cylRectMap] at h2
        rw [cylClamp_of_mem hz_re] at h2
        exact h2.symm
    exact ⟨z, reProdIm_mem_frontier_of_re_eq hzR hre_12, rfl⟩
  have hD_disj : Disjoint D_cyl {p : ClosedCylinder | p.1.2 = Circle.exp θ₀} := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z, hzR, rfl⟩ heq
    obtain ⟨_, hz_im⟩ := Complex.mem_reProdIm.mp hzR
    have h_exp : Circle.exp z.im = Circle.exp θ₀ := heq
    by_cases h_le : z.im ≤ θ₀ + Real.pi
    · have h1 : z.im ∈ Ioo (θ₀ - Real.pi / 2) (θ₀ - Real.pi / 2 + 2 * Real.pi) :=
        ⟨by linarith [hz_im.1, hε0, Real.pi_pos], by linarith [h_le, Real.pi_pos]⟩
      have h2 : θ₀ ∈ Ioo (θ₀ - Real.pi / 2) (θ₀ - Real.pi / 2 + 2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have heq_im := circle_exp_injOn_Ioo (θ₀ - Real.pi / 2) h1 h2 h_exp
      linarith [hz_im.1, hε0]
    · have h1 : z.im ∈ Ioo (θ₀ + Real.pi / 2) (θ₀ + Real.pi / 2 + 2 * Real.pi) :=
        ⟨by linarith [h_le, Real.pi_pos], by linarith [hz_im.2, hε0, Real.pi_pos]⟩
      have h2 : θ₀ + 2 * Real.pi ∈ Ioo (θ₀ + Real.pi / 2) (θ₀ + Real.pi / 2 + 2 * Real.pi) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have h_exp2 : Circle.exp z.im = Circle.exp (θ₀ + 2 * Real.pi) := by
        rw [Circle.exp_add, Circle.exp_two_pi, mul_one, h_exp]
      have heq_im := circle_exp_injOn_Ioo (θ₀ + Real.pi / 2) h1 h2 h_exp2
      linarith [hz_im.2, hε0]
  refine ⟨D_cyl, hD_disc, hK_sub_D, hD_disj, hbd_sub, fun w_j hw_j => ?_⟩
  have hw_sub_D : {p : ClosedCylinder | p.1.2 = w_j} ⊆ D_cyl := hw_j.trans hK_sub_D
  refine ⟨hw_sub_D, Subset.antisymm ?_ ?_⟩
  · rintro p ⟨hp_w, hp_bd⟩
    obtain ⟨z₁, hz₁U, h₁⟩ := hK_sub_U (hw_j hp_w)
    rw [hD_bd] at hp_bd
    obtain ⟨z₂, hz₂_fr, h₂⟩ := hp_bd
    have hz₂R : z₂ ∈ R_ε :=
      ((isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_eq ▸ hz₂_fr).1
    have hz_eq : z₁ = z₂ :=
      injOn_cylRectMap θ₀ ε hε0 (hU_sub_R hz₁U) hz₂R (h₁.trans h₂.symm)
    subst hz_eq
    obtain ⟨hz₁_re, hz₁_im⟩ := Complex.mem_reProdIm.mp hz₁U
    have hre : z₁.re = 1 ∨ z₁.re = 2 := re_eq_of_mem_frontier_reProdIm hz₂_fr hz₁_im
    have hp_re : p.1.1 = z₁.re := by
      have h := congrArg (fun q : ClosedCylinder => q.1.1) h₁.symm
      dsimp [cylRectMap] at h
      rwa [cylClamp_of_mem hz₁_re] at h
    rcases hre with hre1 | hre2
    · left
      exact Subtype.ext (Prod.ext (hp_re.trans hre1) hp_w)
    · right
      exact Subtype.ext (Prod.ext (hp_re.trans hre2) hp_w)
  · rintro p (rfl | rfl)
    · refine ⟨rfl, hbd_sub ⟨hw_sub_D rfl, ?_⟩⟩
      rw [bd_cylinder]
      exact Or.inl ⟨w_j, rfl⟩
    · refine ⟨rfl, hbd_sub ⟨hw_sub_D rfl, ?_⟩⟩
      rw [bd_cylinder]
      exact Or.inr ⟨w_j, rfl⟩

/-! ## 2. Unpinched and Pinched Handle Splits -/

theorem isOpenDisc_of_isClosedDisc_closure {S : Type w} [TopologicalSpace S]
    (hS : IsClosedSurface S)
    {D : Set S} (hD_open : IsOpen D) (hCD : IsClosedDisc (closure D))
    (hout : ∀ x ∈ closure D \ D, x ∈ closure (closure D)ᶜ) :
    IsOpenDisc D := by
  have hDiff : closure D \ subBd (closure D) = D := by
    ext x
    constructor
    · rintro ⟨hx_cl, hx_not_bd⟩
      by_contra hxD
      exact hx_not_bd ⟨subset_closure hx_cl, compl_eq_univ_sdiff (closure D) ▸ hout x ⟨hx_cl, hxD⟩⟩
    · intro hxD
      refine ⟨subset_closure hxD, fun ⟨_, hx_out⟩ => ?_⟩
      obtain ⟨w, hwD, hwc⟩ := mem_closure_iff.mp hx_out D hD_open hxD
      exact hwc.2 (subset_closure hwD)
  exact hDiff ▸ (GM14.IsClosedDisc.isOpenDisc_diff_subBd hS hCD).1

/-- Forward map of `pinchCylHomeo`. -/
def pinchCylMap (δ₁ δ₂ : Circle → ℝ)
    (hδ₁_bd : ∀ z, 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₂_bd : ∀ z, 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (p : ClosedCylinder) :
    ↥{q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2} :=
  have hr := p.2.1
  have h1 := hδ₁_bd p.1.2
  have h2 := hδ₂_bd p.1.2
  ⟨⟨((1 + δ₁ p.1.2) + (p.1.1 - 1) * (1 - δ₁ p.1.2 - δ₂ p.1.2), p.1.2),
    ⟨⟨by nlinarith [hr.1, hr.2, h1.1, h1.2, h2.1, h2.2],
      by nlinarith [hr.1, hr.2, h1.1, h1.2, h2.1, h2.2]⟩, mem_univ _⟩⟩,
   ⟨by dsimp; nlinarith [hr.1, hr.2, h1.1, h1.2, h2.1, h2.2],
    by dsimp; nlinarith [hr.1, hr.2, h1.1, h1.2, h2.1, h2.2]⟩⟩

/-- Homeomorphism between `ClosedCylinder` and the pinched cylinder
`{p : ClosedCylinder | 1 + δ₁ p.1.2 ≤ p.1.1 ∧ p.1.1 ≤ 2 - δ₂ p.1.2}`. -/
noncomputable def pinchCylHomeo {δ₁ δ₂ : Circle → ℝ}
    (hδ₁_cont : Continuous δ₁) (hδ₂_cont : Continuous δ₂)
    (hδ₁_bd : ∀ z, 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₂_bd : ∀ z, 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4) :
    ClosedCylinder ≃ₜ ↥{p : ClosedCylinder | 1 + δ₁ p.1.2 ≤ p.1.1 ∧ p.1.1 ≤ 2 - δ₂ p.1.2} := by
  have : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  let f := pinchCylMap δ₁ δ₂ hδ₁_bd hδ₂_bd
  have hf_cont : Continuous f := by
    unfold f pinchCylMap
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop
  have hf_bij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro p q hpq
      have h1 := Prod.ext_iff.mp (congrArg Subtype.val (congrArg Subtype.val hpq))
      have hz : p.1.2 = q.1.2 := h1.2
      have hpos : 0 < 1 - δ₁ p.1.2 - δ₂ p.1.2 := by
        linarith [(hδ₁_bd p.1.2).2, (hδ₂_bd p.1.2).2]
      have hr_eq : (1 + δ₁ p.1.2) + (p.1.1 - 1) * (1 - δ₁ p.1.2 - δ₂ p.1.2) =
          (1 + δ₁ p.1.2) + (q.1.1 - 1) * (1 - δ₁ p.1.2 - δ₂ p.1.2) := by
        have h1_fst := h1.1
        dsimp [f, pinchCylMap] at h1_fst
        rw [← hz] at h1_fst
        exact h1_fst
      have hr : p.1.1 = q.1.1 := by nlinarith
      exact Subtype.ext (Prod.ext hr hz)
    · rintro ⟨q, hq1, hq2⟩
      obtain ⟨h10, h14⟩ := hδ₁_bd q.1.2
      obtain ⟨h20, h24⟩ := hδ₂_bd q.1.2
      have hpos : 0 < 1 - δ₁ q.1.2 - δ₂ q.1.2 := by linarith
      let r : ℝ := 1 + (q.1.1 - (1 + δ₁ q.1.2)) / (1 - δ₁ q.1.2 - δ₂ q.1.2)
      have hr_mem : r ∈ Icc (1 : ℝ) 2 := by
        dsimp [r]
        constructor
        · have : 0 ≤ (q.1.1 - (1 + δ₁ q.1.2)) / (1 - δ₁ q.1.2 - δ₂ q.1.2) :=
            div_nonneg (by linarith) hpos.le
          linarith
        · have : (q.1.1 - (1 + δ₁ q.1.2)) / (1 - δ₁ q.1.2 - δ₂ q.1.2) ≤ 1 :=
            (div_le_one hpos).mpr (by linarith)
          linarith
      refine ⟨⟨(r, q.1.2), hr_mem, mem_univ _⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · dsimp [f, pinchCylMap, r]
        rw [add_sub_cancel_left, div_mul_cancel₀ _ hpos.ne']
        ring
      · rfl
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont

@[simp]
theorem pinchCylHomeo_apply {δ₁ δ₂ : Circle → ℝ}
    (hδ₁_cont : Continuous δ₁) (hδ₂_cont : Continuous δ₂)
    (hδ₁_bd : ∀ z, 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₂_bd : ∀ z, 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4) (p : ClosedCylinder) :
    pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd p =
      pinchCylMap δ₁ δ₂ hδ₁_bd hδ₂_bd p := rfl

theorem pinchCylHomeo_cylEnd_one {δ₁ δ₂ : Circle → ℝ}
    (hδ₁_cont : Continuous δ₁) (hδ₂_cont : Continuous δ₂)
    (hδ₁_bd : ∀ z, 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₂_bd : ∀ z, 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4) (z : Circle) :
    ((pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd (cylEnd 1 (by norm_num) z)).1 :
      ClosedCylinder).1 =
      (1 + δ₁ z, z) := by
  rw [pinchCylHomeo_apply]
  ext <;> simp [pinchCylMap, cylEnd]

theorem pinchCylHomeo_cylEnd_two {δ₁ δ₂ : Circle → ℝ}
    (hδ₁_cont : Continuous δ₁) (hδ₂_cont : Continuous δ₂)
    (hδ₁_bd : ∀ z, 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₂_bd : ∀ z, 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4) (z : Circle) :
    ((pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd (cylEnd 2 (by norm_num) z)).1 :
      ClosedCylinder).1 =
      (2 - δ₂ z, z) := by
  rw [pinchCylHomeo_apply]
  ext
  · dsimp [pinchCylMap, cylEnd]
    ring
  · rfl

/-- If the closure of a region `r ∈ H.R` meets `subBd Λ` (where `Λ ∈ H.R` has `IsOArc (subBd Λ)`),
then `closure r` meets `H.V ∩ subBd Λ`. -/
theorem closure_region_inter_V_subBd_nonempty_of_inter_subBd_nonempty
    {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {r Λ : Set S}
    (hr : r ∈ H.R) (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ))
    (hne : (closure r ∩ subBd Λ).Nonempty) :
    (closure r ∩ (H.V ∩ subBd Λ)).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hC, hU, hV⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ hOArc
  obtain ⟨z, hzr, hz_bd⟩ := hne
  by_cases hzV : z ∈ H.V
  · exact ⟨z, hzr, hzV, hz_bd⟩
  · have hz_not_V : z ∉ (H.interSet (subBd Λ)).V := fun h => hzV (hV ▸ h).1
    obtain ⟨e, he, hze⟩ := (H.interSet (subBd Λ)).exists_edge_of_mem (hU.symm ▸ hz_bd) hz_not_V
    have he_pair : e ∈ H.E ∧ e ⊆ subBd Λ := by
      have h := he
      rwa [interSet_E H (subBd Λ)] at h
    have he_cl_r : e ⊆ closure r :=
      GM11.edge_subset_closure_of_incident hS he_pair.1 hr ⟨z, hze, hzr⟩
    have hcl_e_sub : closure e ⊆ closure r := isClosed_closure.closure_subset_iff.mpr he_cl_r
    obtain ⟨u, W, _, _, hCV, hCE⟩ := hC
    have he_W : e ∈ W.edges := by
      have h := he
      rwa [hCE] at h
    have hex_end : ∀ {a b : S} (W' : GraphWalk (H.interSet (subBd Λ)).toGraph a b),
        e ∈ W'.edges → ∃ w ∈ W'.support, w ∈ closure e := by
      intro a b W' hmem
      induction W' with
      | nil _ => simp [GraphWalk.edges] at hmem
      | @cons a y b e' hl rest ih =>
        rcases List.mem_cons.mp hmem with rfl | hmem
        · refine ⟨a, (GraphWalk.cons hl rest).start_mem_support, ?_⟩
          have ha_mem : a ∈ closure e ∩ (H.interSet (subBd Λ)).V := by
            rw [hl.2.2.2]
            exact mem_insert a {y}
          exact ha_mem.1
        · obtain ⟨w, hw1, hw2⟩ := ih hmem
          exact ⟨w, List.mem_cons_of_mem _ hw1, hw2⟩
    obtain ⟨w, hw_supp, hw_cl_e⟩ := hex_end W he_W
    have hw_V : w ∈ H.V ∩ subBd Λ := by
      rw [← hV, hCV]
      exact hw_supp
    exact ⟨w, hcl_e_sub hw_cl_e, hw_V⟩

/-- Pigeonhole principle for `3 ≤ φ` pairwise disjoint sets `L i` whose intersections with `K`
lie in a finite set `Z` of cardinality `≤ 2`. -/
theorem exists_disjoint_of_three_le {X : Type*} {φ : ℕ} (hφ : 3 ≤ φ)
    {K Z : Set X} (hZ_fin : Z.Finite) (hZ_card : Z.ncard ≤ 2)
    {L : Fin φ → Set X}
    (hL_disj : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hKL_sub : ∀ i, K ∩ L i ⊆ Z) :
    ∃ i₀ : Fin φ, Disjoint K (L i₀) := by
  by_contra h
  have hne : ∀ i : Fin φ, (K ∩ L i).Nonempty := fun i =>
    Set.not_disjoint_iff_nonempty_inter.mp fun hd => h ⟨i, hd⟩
  let i0 : Fin φ := ⟨0, by omega⟩
  let i1 : Fin φ := ⟨1, by omega⟩
  let i2 : Fin φ := ⟨2, by omega⟩
  obtain ⟨x0, hx0⟩ := hne i0
  obtain ⟨x1, hx1⟩ := hne i1
  obtain ⟨x2, hx2⟩ := hne i2
  have h01 : x0 ≠ x1 := fun heq =>
    Set.disjoint_left.mp (hL_disj (fun h_eq => by
      have : (0 : ℕ) = 1 := congrArg Fin.val h_eq
      omega)) hx0.2 (heq ▸ hx1.2)
  have h02 : x0 ≠ x2 := fun heq =>
    Set.disjoint_left.mp (hL_disj (fun h_eq => by
      have : (0 : ℕ) = 2 := congrArg Fin.val h_eq
      omega)) hx0.2 (heq ▸ hx2.2)
  have h12 : x1 ≠ x2 := fun heq =>
    Set.disjoint_left.mp (hL_disj (fun h_eq => by
      have : (1 : ℕ) = 2 := congrArg Fin.val h_eq
      omega)) hx1.2 (heq ▸ hx2.2)
  have hsub : ({x0, x1, x2} : Set X) ⊆ Z := by
    rintro x (rfl | rfl | rfl)
    · exact hKL_sub i0 hx0
    · exact hKL_sub i1 hx1
    · exact hKL_sub i2 hx2
  have hcard3 : ({x0, x1, x2} : Set X).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h01, h02]),
      Set.ncard_pair h12]
  have hle := Set.ncard_le_ncard hsub hZ_fin
  omega

/-- Gluing map from `bd ↥ClosedCylinder` to `univ \ (Λ₁ ∪ Λ₂)` sending the `r = 1` boundary circle
to `subBd Λ₁` via `g₁` and the `r = 2` boundary circle to `subBd Λ₂` via `g₂`. -/
noncomputable def handleGlueMap {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (p : ↥(bd ↥ClosedCylinder)) : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) :=
  ⟨if p.1.1.1 ≤ 3 / 2 then (g₁ p.1.1.2).1 else (g₂ p.1.1.2).1, by
    split_ifs with hp
    · have hmem : (g₁ p.1.1.2).1 ∈ closure Λ₁ \ Λ₁ := by
        rw [← hΛ₁_open.frontier_eq, ← subBd_eq_frontier]
        exact (g₁ p.1.1.2).2
      refine ⟨mem_univ _, fun h => ?_⟩
      rcases h with h1 | h2
      · exact hmem.2 h1
      · exact Set.disjoint_left.mp hd hmem.1 (subset_closure h2)
    · have hmem : (g₂ p.1.1.2).1 ∈ closure Λ₂ \ Λ₂ := by
        rw [← hΛ₂_open.frontier_eq, ← subBd_eq_frontier]
        exact (g₂ p.1.1.2).2
      refine ⟨mem_univ _, fun h => ?_⟩
      rcases h with h1 | h2
      · exact Set.disjoint_left.mp hd (subset_closure h1) hmem.1
      · exact hmem.2 h2⟩

theorem handleGlueMap_fst_eq_one_or_two (p : ↥(bd ↥ClosedCylinder)) :
    p.1.1.1 = 1 ∨ p.1.1.1 = 2 := by
  obtain ⟨q, hq⟩ := p
  rw [bd_cylinder] at hq
  rcases hq with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    exact (congrArg (fun x : ClosedCylinder => x.1.1) hz).symm
  · right
    exact (congrArg (fun x : ClosedCylinder => x.1.1) hz).symm

@[simp]
theorem handleGlueMap_cylEnd_one {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂)) (z : Circle) :
    (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
      ⟨cylEnd 1 (by norm_num) z, by rw [bd_cylinder]; exact .inl ⟨z, rfl⟩⟩).1 = (g₁ z).1 := by
  dsimp [handleGlueMap, cylEnd]
  have hle : (1 : ℝ) ≤ 3 / 2 := by norm_num
  simp only [hle, ↓reduceIte]

@[simp]
theorem handleGlueMap_cylEnd_two {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂)) (z : Circle) :
    (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
      ⟨cylEnd 2 (by norm_num) z, by rw [bd_cylinder]; exact .inr ⟨z, rfl⟩⟩).1 = (g₂ z).1 := by
  dsimp [handleGlueMap, cylEnd]
  have hnot : ¬ ((2 : ℝ) ≤ 3 / 2) := by norm_num
  simp only [hnot, ↓reduceIte]

theorem continuous_handleGlueMap {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂)) :
    Continuous (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂) := by
  refine Continuous.subtype_mk ?_ _
  rw [← continuousOn_univ]
  let A₁ : Set ↥(bd ↥ClosedCylinder) := {p | p.1.1.1 ≤ 3 / 2}
  let A₂ : Set ↥(bd ↥ClosedCylinder) := {p | 3 / 2 ≤ p.1.1.1}
  have hA₁_cl : IsClosed A₁ :=
    isClosed_le (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
      continuous_const
  have hA₂_cl : IsClosed A₂ :=
    isClosed_le continuous_const (continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val))
  have hunion : A₁ ∪ A₂ = univ := by
    ext p
    exact ⟨fun _ => mem_univ _, fun _ => le_total p.1.1.1 (3 / 2)⟩
  rw [← hunion]
  refine ContinuousOn.union_of_isClosed ?_ ?_ hA₁_cl hA₂_cl
  · refine (continuous_subtype_val.comp (g₁.continuous.comp
      (continuous_snd.comp (continuous_subtype_val.comp
        continuous_subtype_val)))).continuousOn.congr ?_
    intro p hp
    have hp' : p.1.1.1 ≤ 3 / 2 := hp
    simp only [hp', ↓reduceIte]
    rfl
  · refine (continuous_subtype_val.comp (g₂.continuous.comp
      (continuous_snd.comp (continuous_subtype_val.comp
        continuous_subtype_val)))).continuousOn.congr ?_
    intro p hp
    have hp_not : ¬ p.1.1.1 ≤ 3 / 2 := by
      rcases handleGlueMap_fst_eq_one_or_two p with h1 | h2 <;> linarith [ show (3 / 2 : ℝ)
        ≤ p.1.1.1 from hp ]
    simp only [hp_not, ↓reduceIte]
    rfl

theorem injective_handleGlueMap {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂)) :
    Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂) := by
  have hsub₁ : subBd Λ₁ ⊆ closure Λ₁ := by
    rw [subBd_eq_frontier, hΛ₁_open.frontier_eq]
    exact sdiff_subset
  have hsub₂ : subBd Λ₂ ⊆ closure Λ₂ := by
    rw [subBd_eq_frontier, hΛ₂_open.frontier_eq]
    exact sdiff_subset
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  dsimp [handleGlueMap] at hval
  by_cases hp1 : p.1.1.1 ≤ 3 / 2 <;> by_cases hq1 : q.1.1.1 ≤ 3 / 2
  · simp only [hp1, hq1, ↓reduceIte] at hval
    have hz : p.1.1.2 = q.1.1.2 := g₁.injective (Subtype.ext hval)
    have hr_p : p.1.1.1 = 1 := by
      rcases handleGlueMap_fst_eq_one_or_two p with h | h <;> linarith
    have hr_q : q.1.1.1 = 1 := by
      rcases handleGlueMap_fst_eq_one_or_two q with h | h <;> linarith
    exact Subtype.ext (Subtype.ext (Prod.ext (hr_p.trans hr_q.symm) hz))
  · simp only [hp1, hq1, ↓reduceIte] at hval
    exfalso
    exact Set.disjoint_left.mp hd (hsub₁ (g₁ p.1.1.2).2) (hval.symm ▸ hsub₂ (g₂ q.1.1.2).2)
  · simp only [hp1, hq1, ↓reduceIte] at hval
    exfalso
    exact Set.disjoint_left.mp hd (hval ▸ hsub₁ (g₁ q.1.1.2).2) (hsub₂ (g₂ p.1.1.2).2)
  · simp only [hp1, hq1, ↓reduceIte] at hval
    have hz : p.1.1.2 = q.1.1.2 := g₂.injective (Subtype.ext hval)
    have hr_p : p.1.1.1 = 2 := by
      rcases handleGlueMap_fst_eq_one_or_two p with h | h <;> linarith
    have hr_q : q.1.1.1 = 2 := by
      rcases handleGlueMap_fst_eq_one_or_two q with h | h <;> linarith
    exact Subtype.ext (Subtype.ext (Prod.ext (hr_p.trans hr_q.symm) hz))

theorem range_handleGlueMap {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂)) :
    range (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂) =
      bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) := by
  obtain ⟨_, _, hbd_eq⟩ :=
    compl_two_open_isSurface hS hΛ₁_open hΛ₂_open hOArc₁ hOArc₂ hout₁ hout₂ hd
  rw [hbd_eq]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂ p).1 ∈ subBd Λ₁ ∪ subBd Λ₂
    dsimp [handleGlueMap]
    split_ifs
    · exact .inl (g₁ p.1.1.2).2
    · exact .inr (g₂ p.1.1.2).2
  · intro hx
    rcases hx with hx1 | hx2
    · let z := g₁.symm ⟨x.1, hx1⟩
      refine ⟨⟨cylEnd 1 (by norm_num) z, by rw [bd_cylinder]; exact .inl ⟨z, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [handleGlueMap_cylEnd_one]
      exact congrArg Subtype.val (g₁.apply_symm_apply ⟨x.1, hx1⟩)
    · let z := g₂.symm ⟨x.1, hx2⟩
      refine ⟨⟨cylEnd 2 (by norm_num) z, by rw [bd_cylinder]; exact .inr ⟨z, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [handleGlueMap_cylEnd_two]
      exact congrArg Subtype.val (g₂.apply_symm_apply ⟨x.1, hx2⟩)

/-- Radial line `{p : ClosedCylinder | p.1.2 = z}` in `ClosedCylinder` from `cylEnd 1 m1 z` to
`cylEnd 2 m2 z`. -/
theorem isLineWithEnds_cylRadial (z : Circle) :
    IsLineWithEnds {p : ClosedCylinder | p.1.2 = z}
      (cylEnd 1 (by norm_num) z) (cylEnd 2 (by norm_num) z) := by
  let f : unitInterval → ↥{p : ClosedCylinder | p.1.2 = z} := fun t =>
    ⟨⟨(1 + (t : ℝ), z), ⟨⟨by linarith [t.2.1], by linarith [t.2.2]⟩, mem_univ _⟩⟩, rfl⟩
  have hf_cont : Continuous f := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop
  have hf_bij : Function.Bijective f := by
    refine ⟨fun t₁ t₂ h => ?_, fun ⟨p, hp⟩ => ?_⟩
    · have h1 := Prod.ext_iff.mp (congrArg Subtype.val (congrArg Subtype.val h))
      exact Subtype.ext (by dsimp [f] at h1; linarith [h1.1])
    · refine ⟨⟨p.1.1 - 1, ⟨by linarith [p.2.1.1], by linarith [p.2.1.2]⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · dsimp [f]; ring
      · exact hp.symm
  let e : unitInterval ≃ₜ ↥{p : ClosedCylinder | p.1.2 = z} :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont
  refine ⟨e, ?_, ?_⟩
  · change (f 0).1 = cylEnd 1 (by norm_num) z
    ext <;> simp [f, cylEnd]
  · change (f 1).1 = cylEnd 2 (by norm_num) z
    ext
    · dsimp [f, cylEnd]; norm_num
    · rfl

/-- The unpinched handle split on `GluedSpace hb_inj`, where `S₁ = range (GluedSpace.inl hb_inj)`
and `S₂ = range (GluedSpace.inr hb_inj)`. -/
theorem isCappedSplit_handle_unpinched {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hΛ₁ : IsOpenDisc Λ₁) (hΛ₂ : IsOpenDisc Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂)) :
    let S' := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let S₂ : Set S' := range (GluedSpace.inr hb_inj)
    ∃ (C_unp : Fin 2 → Set S') (ι_unp : ↥S₁ → S),
      IsClosedSurface S' ∧ ConnectedSpace S' ∧ IsObtainedByAddingHandle S S' ∧
      GM12.IsCappedSplit C_unp S₁ S₂ ι_unp ![Λ₁, Λ₂] ∧
      C_unp 0 = GluedSpace.inr hb_inj '' range (cylEnd 1 (by norm_num)) ∧
      C_unp 1 = GluedSpace.inr hb_inj '' range (cylEnd 2 (by norm_num)) ∧
      S₁ ∩ S₂ = GluedSpace.inl hb_inj '' (Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂)) ∧
      (∀ y : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S), ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = y.1) := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open)
  have : CompactSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isCompact_iff_compactSpace.mp hX_closed.isCompact
  have : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  let b := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_cont := continuous_handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_range := range_handleGlueMap hS hΛ₁_open hΛ₂_open hOArc₁ hOArc₂ hout₁ hout₂ hd g₁ g₂
  have : T2Space (GluedSpace hb_inj) :=
    GluedSpace.t2Space (isClosed_bd ↥ClosedCylinder) hb_cont hb_inj
  obtain ⟨hS', hConn', hHandle, hS₁_surf, hS₂_surf, hU_eq, h1_bd, h2_bd⟩ :=
    isClosedSurface_of_handle_glue hS hΛ₁ hΛ₂ hd hOArc₁ hOArc₂ hout₁ hout₂ hb_cont hb_inj hb_range
  obtain ⟨_, _, hX_bd⟩ :=
    compl_two_open_isSurface hS hΛ₁_open hΛ₂_open hOArc₁ hOArc₂ hout₁ hout₂ hd
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  let C_unp : Fin 2 → Set S' :=
    ![GluedSpace.inr hb_inj '' range (cylEnd 1 m1),
      GluedSpace.inr hb_inj '' range (cylEnd 2 m2)]
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let ι_unp : ↥S₁ → S := Subtype.val ∘ e₁.symm
  have hι_emb : IsEmbedding ι_unp :=
    hX_closed.isClosedEmbedding_subtypeVal.isEmbedding.comp e₁.symm.isEmbedding
  have hι_inl : ∀ y : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S),
      ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = y.1 := by
    intro y
    change (e₁.symm (e₁ y)).1 = y.1
    rw [e₁.symm_apply_apply]
  have hι_range : range ι_unp = univ \ (Λ₁ ∪ Λ₂) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (e₁.symm z).2
    · intro hx
      exact ⟨⟨GluedSpace.inl hb_inj ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, hι_inl ⟨x, hx⟩⟩
  have hC0_inl : C_unp 0 = GluedSpace.inl hb_inj '' (Subtype.val ⁻¹' subBd Λ₁) := by
    change GluedSpace.inr hb_inj '' range (cylEnd 1 m1) = _
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      have hmem : cylEnd 1 m1 z ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        exact .inl ⟨z, rfl⟩
      refine ⟨b ⟨cylEnd 1 m1 z, hmem⟩, ?_, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hmem, rfl⟩⟩
      change (b ⟨cylEnd 1 m1 z, hmem⟩).1 ∈ subBd Λ₁
      rw [handleGlueMap_cylEnd_one]
      exact (g₁ z).2
    · rintro ⟨y, hy, rfl⟩
      let z := g₁.symm ⟨y.1, hy⟩
      have hmem : cylEnd 1 m1 z ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        exact .inl ⟨z, rfl⟩
      have hby : y = b ⟨cylEnd 1 m1 z, hmem⟩ := by
        apply Subtype.ext
        rw [handleGlueMap_cylEnd_one]
        exact (congrArg Subtype.val (g₁.apply_symm_apply ⟨y.1, hy⟩)).symm
      exact ⟨cylEnd 1 m1 z, ⟨z, rfl⟩, ((GluedSpace.inl_eq_inr hb_inj).mpr ⟨hmem, hby⟩).symm⟩
  have hC1_inl : C_unp 1 = GluedSpace.inl hb_inj '' (Subtype.val ⁻¹' subBd Λ₂) := by
    change GluedSpace.inr hb_inj '' range (cylEnd 2 m2) = _
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      have hmem : cylEnd 2 m2 z ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        exact .inr ⟨z, rfl⟩
      refine ⟨b ⟨cylEnd 2 m2 z, hmem⟩, ?_, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hmem, rfl⟩⟩
      change (b ⟨cylEnd 2 m2 z, hmem⟩).1 ∈ subBd Λ₂
      rw [handleGlueMap_cylEnd_two]
      exact (g₂ z).2
    · rintro ⟨y, hy, rfl⟩
      let z := g₂.symm ⟨y.1, hy⟩
      have hmem : cylEnd 2 m2 z ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        exact .inr ⟨z, rfl⟩
      have hby : y = b ⟨cylEnd 2 m2 z, hmem⟩ := by
        apply Subtype.ext
        rw [handleGlueMap_cylEnd_two]
        exact (congrArg Subtype.val (g₂.apply_symm_apply ⟨y.1, hy⟩)).symm
      exact ⟨cylEnd 2 m2 z, ⟨z, rfl⟩, ((GluedSpace.inl_eq_inr hb_inj).mpr ⟨hmem, hby⟩).symm⟩
  have hiUnion2 : ∀ {α : Type w} (f : Fin 2 → Set α), (⋃ i : Fin 2, f i) = f 0 ∪ f 1 := by
    intro α f
    ext x
    simp [Fin.exists_fin_two]
  have hCu_eq : (⋃ i : Fin 2, C_unp i) = S₁ ∩ S₂ := by
    rw [hiUnion2 C_unp, GluedSpace.range_inl_inter_range_inr_eq_inr hb_inj,
      congrArg (GluedSpace.inr hb_inj '' ·) bd_cylinder, image_union]
    rfl
  have hS12_inl : S₁ ∩ S₂ = GluedSpace.inl hb_inj '' (Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂)) := by
    rw [GluedSpace.range_inl_inter_range_inr hb_inj, hb_range, hX_bd]
  refine ⟨C_unp, ι_unp, hS', hConn', hHandle, ?_, rfl, rfl, hS12_inl, hι_inl⟩
  refine
    { surface := ⟨hS', hConn'⟩
      isOArc := ?_
      disjoint := ?_
      manifold₁ := hS₁_surf
      manifold₂ := hS₂_surf
      union := hU_eq
      inter := hCu_eq.symm
      bd₁ := h1_bd.symm.trans hCu_eq.symm
      bd₂ := h2_bd.symm.trans hCu_eq.symm
      surface_hat := hS
      isEmbedding := hι_emb
      isOpenDisc := fun i => by fin_cases i <;> [exact hΛ₁; exact hΛ₂]
      bounds := ?_
      disjoint_D := fun i j hij => by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hd.mono subset_closure subset_closure
        · exact hd.symm.mono subset_closure subset_closure
        · exact (hij rfl).elim
      compl := ?_ }
  · intro i
    fin_cases i
    · exact isOArc_image hinr_emb.isEmbedding ⟨(isEmbedding_cylEnd 1 m1).toHomeomorph⟩
    · exact isOArc_image hinr_emb.isEmbedding ⟨(isEmbedding_cylEnd 2 m2).toHomeomorph⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨z₁, rfl⟩, rfl⟩ ⟨_, ⟨z₂, rfl⟩, he⟩
      have h1 := GluedSpace.inr_injective hb_inj he
      have h2 : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) h1
      norm_num at h2
    · rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨z₁, rfl⟩, rfl⟩ ⟨_, ⟨z₂, rfl⟩, he⟩
      have h1 := GluedSpace.inr_injective hb_inj he
      have h2 : (1 : ℝ) = 2 := congrArg (fun p : ClosedCylinder => p.1.1) h1
      norm_num at h2
    · exact (hij rfl).elim
  · intro i
    fin_cases i
    · change subBd Λ₁ = ι_unp '' (Subtype.val ⁻¹' (C_unp 0))
      rw [hC0_inl]
      ext x
      constructor
      · intro hx
        have hx_mem : x ∈ univ \ (Λ₁ ∪ Λ₂) := by
          have hmem : x ∈ closure Λ₁ \ Λ₁ := by
            rw [← hΛ₁_open.frontier_eq, ← subBd_eq_frontier]
            exact hx
          refine ⟨mem_univ _, fun h => ?_⟩
          rcases h with h1 | h2
          · exact hmem.2 h1
          · exact Set.disjoint_left.mp hd hmem.1 (subset_closure h2)
        refine ⟨⟨GluedSpace.inl hb_inj ⟨x, hx_mem⟩, ⟨⟨x, hx_mem⟩, rfl⟩⟩, ?_, hι_inl ⟨x, hx_mem⟩⟩
        exact ⟨⟨x, hx_mem⟩, hx, rfl⟩
      · rintro ⟨⟨_, ⟨y, rfl⟩⟩, ⟨y', hy', he⟩, rfl⟩
        have hyy' : y = y' := GluedSpace.inl_injective hb_inj he.symm
        subst hyy'
        rw [hι_inl y]
        exact hy'
    · change subBd Λ₂ = ι_unp '' (Subtype.val ⁻¹' (C_unp 1))
      rw [hC1_inl]
      ext x
      constructor
      · intro hx
        have hx_mem : x ∈ univ \ (Λ₁ ∪ Λ₂) := by
          have hmem : x ∈ closure Λ₂ \ Λ₂ := by
            rw [← hΛ₂_open.frontier_eq, ← subBd_eq_frontier]
            exact hx
          refine ⟨mem_univ _, fun h => ?_⟩
          rcases h with h1 | h2
          · exact Set.disjoint_left.mp hd (subset_closure h1) hmem.1
          · exact hmem.2 h2
        refine ⟨⟨GluedSpace.inl hb_inj ⟨x, hx_mem⟩, ⟨⟨x, hx_mem⟩, rfl⟩⟩, ?_, hι_inl ⟨x, hx_mem⟩⟩
        exact ⟨⟨x, hx_mem⟩, hx, rfl⟩
      · rintro ⟨⟨_, ⟨y, rfl⟩⟩, ⟨y', hy', he⟩, rfl⟩
        have hyy' : y = y' := GluedSpace.inl_injective hb_inj he.symm
        subst hyy'
        rw [hι_inl y]
        exact hy'
  · rw [hiUnion2 ![Λ₁, Λ₂], hι_range]
    ext x
    simp only [mem_compl_iff, mem_sdiff, mem_univ, mem_union, true_and, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto

/-- Map from `GluedSpace hb_inj` to `S` that equals the inclusion on `S₁` and maps the two halves
of `ClosedCylinder` via `cMap₁` and `cMap₂`. -/
noncomputable def handlePinchRetract {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (cMap₁ cMap₂ : ℝ × Circle → S)
    (hcMap₁_zero : ∀ z : Circle, cMap₁ (0, z) = (g₁ z).1)
    (hcMap₂_zero : ∀ z : Circle, cMap₂ (0, z) = (g₂ z).1) :
    GluedSpace hb_inj → S :=
  Quotient.lift
    (fun a => match a with
      | .inl x => x.1
      | .inr q =>
        if q.down.1.1 ≤ 3 / 2 then cMap₁ (q.down.1.1 - 1, q.down.1.2)
        else cMap₂ (2 - q.down.1.1, q.down.1.2))
    (by
      have hagree : ∀ z : ↥(bd ↥ClosedCylinder),
          (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂ z).1 =
            if z.1.1.1 ≤ 3 / 2 then cMap₁ (z.1.1.1 - 1, z.1.1.2)
            else cMap₂ (2 - z.1.1.1, z.1.1.2) := by
        intro z
        rcases handleGlueMap_fst_eq_one_or_two z with h1 | h2
        · have hle : (1 : ℝ) ≤ 3 / 2 := by norm_num
          change (if z.1.1.1 ≤ 3 / 2 then (g₁ z.1.1.2).1 else (g₂ z.1.1.2).1) = _
          simp only [h1, hle, ↓reduceIte, sub_self, hcMap₁_zero]
        · have hnot : ¬ ((2 : ℝ) ≤ 3 / 2) := by norm_num
          change (if z.1.1.1 ≤ 3 / 2 then (g₁ z.1.1.2).1 else (g₂ z.1.1.2).1) = _
          simp only [h2, hnot, ↓reduceIte, sub_self, hcMap₂_zero]
      rintro a a' (rfl | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩)
      · rfl
      · exact hagree z
      · exact (hagree z).symm)

@[simp]
theorem handlePinchRetract_inl {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (cMap₁ cMap₂ : ℝ × Circle → S)
    (hcMap₁_zero : ∀ z : Circle, cMap₁ (0, z) = (g₁ z).1)
    (hcMap₂_zero : ∀ z : Circle, cMap₂ (0, z) = (g₂ z).1)
    (x : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S)) :
    handlePinchRetract hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂
      hcMap₁_zero hcMap₂_zero (GluedSpace.inl hb_inj x) = x.1 := rfl

theorem handlePinchRetract_inr_one {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (cMap₁ cMap₂ : ℝ × Circle → S)
    (hcMap₁_zero : ∀ z : Circle, cMap₁ (0, z) = (g₁ z).1)
    (hcMap₂_zero : ∀ z : Circle, cMap₂ (0, z) = (g₂ z).1)
    (q : ClosedCylinder) (hq : q.1.1 ≤ 3 / 2) :
    handlePinchRetract hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂
      hcMap₁_zero hcMap₂_zero (GluedSpace.inr hb_inj q) = cMap₁ (q.1.1 - 1, q.1.2) := by
  change (if q.1.1 ≤ 3 / 2 then cMap₁ (q.1.1 - 1, q.1.2) else cMap₂ (2 - q.1.1, q.1.2)) = _
  simp only [hq, ↓reduceIte]

theorem handlePinchRetract_inr_two {S : Type w} [TopologicalSpace S] {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (cMap₁ cMap₂ : ℝ × Circle → S)
    (hcMap₁_zero : ∀ z : Circle, cMap₁ (0, z) = (g₁ z).1)
    (hcMap₂_zero : ∀ z : Circle, cMap₂ (0, z) = (g₂ z).1)
    (q : ClosedCylinder) (hq : ¬ q.1.1 ≤ 3 / 2) :
    handlePinchRetract hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂
      hcMap₁_zero hcMap₂_zero (GluedSpace.inr hb_inj q) = cMap₂ (2 - q.1.1, q.1.2) := by
  change (if q.1.1 ≤ 3 / 2 then cMap₁ (q.1.1 - 1, q.1.2) else cMap₂ (2 - q.1.1, q.1.2)) = _
  simp only [hq, ↓reduceIte]

private theorem lower_cylinder_collar_closed
    (δ₁ : Circle → ℝ)
    (hδ₁_cont : Continuous δ₁) :
    IsClosed ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}) := by
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  refine isClosed_le (continuous_fst.comp continuous_subtype_val) ?_
  fun_prop

private theorem upper_cylinder_collar_closed
    (δ₂ : Circle → ℝ)
    (hδ₂_cont : Continuous δ₂) :
    IsClosed ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}) := by
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  refine isClosed_le ?_ (continuous_fst.comp continuous_subtype_val)
  fun_prop

private theorem middle_cylinder_strip_closed
    (δ₁ : Circle → ℝ)
    (hδ₁_cont : Continuous δ₁)
    (δ₂ : Circle → ℝ)
    (hδ₂_cont : Continuous δ₂) :
    IsClosed ({q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}) := by
  let A_mid := {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}
  have hlo : IsClosed {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1} := by
    refine isClosed_le ?_ (continuous_fst.comp continuous_subtype_val)
    fun_prop
  have hhi : IsClosed {q : ClosedCylinder | q.1.1 ≤ 2 - δ₂ q.1.2} := by
    refine isClosed_le (continuous_fst.comp continuous_subtype_val) ?_
    fun_prop
  exact hlo.inter hhi

private theorem handle_map_continuous_on_original_surface
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (e₁ : ↑(univ \ (Λ₁ ∪ Λ₂)) ≃ₜ ↑(range (GluedSpace.inl hb_inj)))
    (he₁ : ∀ y, (e₁ y).1 = GluedSpace.inl hb_inj y)
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inl : ∀ (y : ↑(univ \ (Λ₁ ∪ Λ₂))), f_XII (GluedSpace.inl hb_inj y) = ↑y) :
    ContinuousOn f_XII (range (GluedSpace.inl hb_inj)) := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  rw [continuousOn_iff_continuous_domRestrict]
  have hcongr : S₁.domRestrict f_XII = fun x : ↥S₁ => (e₁.symm x).1 := by
    ext x
    have hx : x.1 = GluedSpace.inl hb_inj (e₁.symm x) := by
      rw [← he₁, e₁.apply_symm_apply]
    change f_XII x.1 = (e₁.symm x).1
    rw [hx, hf_inl]
  rw [hcongr]
  exact continuous_subtype_val.comp e₁.symm.continuous

private theorem handle_map_continuous_on_lower_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (cMap₁ : ℝ × Circle → S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hcMap₁_cont : Continuous cMap₁)
    (e₂ : ↑ClosedCylinder ≃ₜ ↑(range (GluedSpace.inr hb_inj)))
    (he₂ : ∀ q, (e₂ q).1 = GluedSpace.inr hb_inj q)
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_one : ∀ (q : ↑ClosedCylinder), q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ (q.1.1 - 1, q.1.2)) :
    ContinuousOn f_XII (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}))
      := by
  let S' := GluedSpace hb_inj
  let S₂ := range (GluedSpace.inr hb_inj)
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  have hsub : C_col₁ ⊆ S₂ := image_subset_range _ _
  rw [continuousOn_iff_continuous_domRestrict]
  have hcongr : C_col₁.domRestrict f_XII =
      fun x : ↥C_col₁ =>
        cMap₁ ((e₂.symm ⟨x.1, hsub x.2⟩).1.1 - 1, (e₂.symm ⟨x.1, hsub x.2⟩).1.2) := by
    ext ⟨_, ⟨q, hq, rfl⟩⟩
    have hq_le : q.1.1 ≤ 3 / 2 := by linarith [(hδ₁_bd q.1.2).2, show q.1.1 ≤ 1 + δ₁ q.1.2 from hq]
    have hmem2 : GluedSpace.inr hb_inj q ∈ S₂ := ⟨q, rfl⟩
    have he₂_q : e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩ = q := by
      have hEq : (⟨GluedSpace.inr hb_inj q, hmem2⟩ : S₂) = e₂ q :=
        Subtype.ext (he₂ q).symm
      rw [hEq, e₂.symm_apply_apply]
    change f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ ((e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩).1.1 - 1,
        (e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩).1.2)
    rw [he₂_q, hf_inr_one q hq_le]
  rw [hcongr]
  refine hcMap₁_cont.comp ?_
  fun_prop

private theorem handle_map_continuous_on_upper_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₂ : Circle → ℝ)
    (cMap₂ : ℝ × Circle → S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hcMap₂_cont : Continuous cMap₂)
    (e₂ : ↑ClosedCylinder ≃ₜ ↑(range (GluedSpace.inr hb_inj)))
    (he₂ : ∀ q, (e₂ q).1 = GluedSpace.inr hb_inj q)
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_two : ∀ (q : ↑ClosedCylinder), ¬q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - q.1.1, q.1.2)) :
    ContinuousOn f_XII (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}))
      := by
  let S' := GluedSpace hb_inj
  let S₂ := range (GluedSpace.inr hb_inj)
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  have hsub : C_col₂ ⊆ S₂ := image_subset_range _ _
  rw [continuousOn_iff_continuous_domRestrict]
  have hcongr : C_col₂.domRestrict f_XII =
      fun x : ↥C_col₂ =>
        cMap₂ (2 - (e₂.symm ⟨x.1, hsub x.2⟩).1.1, (e₂.symm ⟨x.1, hsub x.2⟩).1.2) := by
    ext ⟨_, ⟨q, hq, rfl⟩⟩
    have hq_not : ¬ q.1.1 ≤ 3 / 2 := by
      linarith [(hδ₂_bd q.1.2).2, show 2 - δ₂ q.1.2 ≤ q.1.1 from hq]
    have hmem2 : GluedSpace.inr hb_inj q ∈ S₂ := ⟨q, rfl⟩
    have he₂_q : e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩ = q := by
      have hEq : (⟨GluedSpace.inr hb_inj q, hmem2⟩ : S₂) = e₂ q :=
        Subtype.ext (he₂ q).symm
      rw [hEq, e₂.symm_apply_apply]
    change f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - (e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩).1.1,
        (e₂.symm ⟨GluedSpace.inr hb_inj q, hmem2⟩).1.2)
    rw [he₂_q, hf_inr_two q hq_not]
  rw [hcongr]
  refine hcMap₂_cont.comp ?_
  fun_prop

private theorem handle_map_image_of_original_surface
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inl : ∀ y, f_XII (GluedSpace.inl hb_inj y) = y.1) :
    f_XII '' (range (GluedSpace.inl hb_inj)) = univ \ (Λ₁ ∪ Λ₂) := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [hf_inl]
    exact x.2
  · intro hy
    exact ⟨GluedSpace.inl hb_inj ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hf_inl _⟩

private theorem handle_map_image_of_lower_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (D₁ : Set S)
    (cMap₁ : ℝ × Circle → S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hcMap₁_collar : cMap₁ '' {p | 0 ≤ p.1 ∧ p.1 ≤ δ₁ p.2} = closure Λ₁ \ D₁)
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_one : ∀ (q : ↑ClosedCylinder), q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ (q.1.1 - 1, q.1.2)) :
    f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2})) = closure
      Λ₁ \ D₁ := by
  let S' := GluedSpace hb_inj
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  rw [← hcMap₁_collar]
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq_le : q.1.1 ≤ 3 / 2 := by linarith [(hδ₁_bd q.1.2).2, show q.1.1 ≤ 1 + δ₁ q.1.2 from hq]
    rw [hf_inr_one q hq_le]
    have hq₁ : q.1.1 ≤ 1 + δ₁ q.1.2 := hq
    exact ⟨(q.1.1 - 1, q.1.2), ⟨by linarith [q.2.1.1], by linarith⟩, rfl⟩
  · rintro ⟨p, ⟨hp0, hpδ⟩, rfl⟩
    have hr : 1 + p.1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith [(hδ₁_bd p.2).2]⟩
    let q : ClosedCylinder := ⟨(1 + p.1, p.2), hr, mem_univ _⟩
    have hq_col : q ∈ A_col₁ := by dsimp [A_col₁, q]; linarith
    have hq_le : q.1.1 ≤ 3 / 2 := by dsimp [q]; linarith [(hδ₁_bd p.2).2]
    refine ⟨GluedSpace.inr hb_inj q, ⟨q, hq_col, rfl⟩, ?_⟩
    rw [hf_inr_one q hq_le]
    dsimp [q]
    rw [add_sub_cancel_left]

private theorem handle_map_image_of_upper_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₂ : Circle → ℝ)
    (D₂ : Set S)
    (cMap₂ : ℝ × Circle → S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hcMap₂_collar : cMap₂ '' {p | 0 ≤ p.1 ∧ p.1 ≤ δ₂ p.2} = closure Λ₂ \ D₂)
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_two : ∀ (q : ↑ClosedCylinder), ¬q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - q.1.1, q.1.2)) :
    f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1})) = closure
      Λ₂ \ D₂ := by
  let S' := GluedSpace hb_inj
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  rw [← hcMap₂_collar]
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq_not : ¬ q.1.1 ≤ 3 / 2 := by
      linarith [(hδ₂_bd q.1.2).2, show 2 - δ₂ q.1.2 ≤ q.1.1 from hq]
    rw [hf_inr_two q hq_not]
    exact ⟨(2 - q.1.1, q.1.2), ⟨by linarith [q.2.1.2], by linarith [show 2 - δ₂ q.1.2
      ≤ q.1.1 from hq]⟩, rfl⟩
  · rintro ⟨p, ⟨hp0, hpδ⟩, rfl⟩
    have hr : 2 - p.1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith [(hδ₂_bd p.2).2], by linarith⟩
    let q : ClosedCylinder := ⟨(2 - p.1, p.2), hr, mem_univ _⟩
    have hq_col : q ∈ A_col₂ := by dsimp [A_col₂, q]; linarith
    have hq_not : ¬ q.1.1 ≤ 3 / 2 := by dsimp [q]; linarith [(hδ₂_bd p.2).2]
    refine ⟨GluedSpace.inr hb_inj q, ⟨q, hq_col, rfl⟩, ?_⟩
    rw [hf_inr_two q hq_not]
    dsimp [q]
    rw [sub_sub_cancel]

private theorem lower_collar_interior_maps_inside_disc
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (D₁ : Set S)
    (cMap₁ : ℝ × Circle → S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hcMap₁_inj : InjOn cMap₁ {p | 0 ≤ p.1 ∧ p.1 ≤ δ₁ p.2})
    (hcMap₁_zero : ∀ (z : Circle), cMap₁ (0, z) = ↑(g₁ z))
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_one : ∀ (q : ↑ClosedCylinder), q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ (q.1.1 - 1, q.1.2))
    (hf_img_col₁ : f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁
      q.1.2})) = closure Λ₁ \ D₁) :
    ∀ q ∈ ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}), 1 < q.1.1 → f_XII (GluedSpace.inr
      hb_inj q) ∈ Λ₁ := by
  let S' := GluedSpace hb_inj
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  intro q hq hq1
  have hq_le : q.1.1 ≤ 3 / 2 := by linarith [(hδ₁_bd q.1.2).2, show q.1.1 ≤ 1 + δ₁ q.1.2 from hq]
  have hmem_col : f_XII (GluedSpace.inr hb_inj q) ∈ closure Λ₁ \ D₁ := by
    rw [← hf_img_col₁]
    exact ⟨GluedSpace.inr hb_inj q, ⟨q, hq, rfl⟩, rfl⟩
  by_contra hnot_Λ₁
  have hbd : f_XII (GluedSpace.inr hb_inj q) ∈ subBd Λ₁ := by
    rw [subBd_eq_frontier, hΛ₁_open.frontier_eq]
    exact ⟨hmem_col.1, hnot_Λ₁⟩
  let z := g₁.symm ⟨f_XII (GluedSpace.inr hb_inj q), hbd⟩
  have hcz : cMap₁ (0, z) = cMap₁ (q.1.1 - 1, q.1.2) := by
    rw [hcMap₁_zero z, ← hf_inr_one q hq_le]
    exact congrArg Subtype.val (g₁.apply_symm_apply ⟨f_XII (GluedSpace.inr hb_inj q), hbd⟩)
  have hinj := hcMap₁_inj ⟨le_rfl, (hδ₁_bd z).1⟩
    ⟨by linarith [q.2.1.1], by linarith [show q.1.1 ≤ 1 + δ₁ q.1.2 from hq]⟩ hcz
  have : (0 : ℝ) = q.1.1 - 1 := congrArg Prod.fst hinj
  linarith

private theorem upper_collar_interior_maps_inside_disc
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₂ : Circle → ℝ)
    (D₂ : Set S)
    (cMap₂ : ℝ × Circle → S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hcMap₂_inj : InjOn cMap₂ {p | 0 ≤ p.1 ∧ p.1 ≤ δ₂ p.2})
    (hcMap₂_zero : ∀ (z : Circle), cMap₂ (0, z) = ↑(g₂ z))
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_two : ∀ (q : ↑ClosedCylinder), ¬q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - q.1.1, q.1.2))
    (hf_img_col₂ : f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤
      q.1.1})) = closure Λ₂ \ D₂) :
    ∀ q ∈ ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}), q.1.1 < 2 → f_XII (GluedSpace.inr
      hb_inj q) ∈ Λ₂ := by
  let S' := GluedSpace hb_inj
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  intro q hq hq2
  have hq_not : ¬ q.1.1 ≤ 3 / 2 := by linarith [(hδ₂_bd q.1.2).2, show 2 - δ₂ q.1.2 ≤ q.1.1 from hq]
  have hmem_col : f_XII (GluedSpace.inr hb_inj q) ∈ closure Λ₂ \ D₂ := by
    rw [← hf_img_col₂]
    exact ⟨GluedSpace.inr hb_inj q, ⟨q, hq, rfl⟩, rfl⟩
  by_contra hnot_Λ₂
  have hbd : f_XII (GluedSpace.inr hb_inj q) ∈ subBd Λ₂ := by
    rw [subBd_eq_frontier, hΛ₂_open.frontier_eq]
    exact ⟨hmem_col.1, hnot_Λ₂⟩
  let z := g₂.symm ⟨f_XII (GluedSpace.inr hb_inj q), hbd⟩
  have hcz : cMap₂ (0, z) = cMap₂ (2 - q.1.1, q.1.2) := by
    rw [hcMap₂_zero z, ← hf_inr_two q hq_not]
    exact congrArg Subtype.val (g₂.apply_symm_apply ⟨f_XII (GluedSpace.inr hb_inj q), hbd⟩)
  have hinj := hcMap₂_inj ⟨le_rfl, (hδ₂_bd z).1⟩
    ⟨by linarith [q.2.1.2], by linarith [show 2 - δ₂ q.1.2 ≤ q.1.1 from hq]⟩ hcz
  have : (0 : ℝ) = 2 - q.1.1 := congrArg Prod.fst hinj
  linarith

private theorem handle_map_complement_has_original_preimage
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ δ₂ : Circle → ℝ)
    (f_XII : (GluedSpace hb_inj) → S)
    (hcol₁_interior : ∀ q ∈ ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}), 1 < q.1.1 → f_XII
      (GluedSpace.inr hb_inj q) ∈ Λ₁)
    (hcol₂_interior : ∀ q ∈ ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}), q.1.1 < 2 → f_XII
      (GluedSpace.inr hb_inj q) ∈ Λ₂) :
    ∀ x ∈ ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder |
      q.1.1 ≤ 1 + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤
      q.1.1}))), f_XII x ∈ univ \ (Λ₁ ∪ Λ₂) → x ∈ (range (GluedSpace.inl hb_inj)) := by
  let b := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII := S₁ ∪ C_col₁ ∪ C_col₂
  rintro x ((hx | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) hfx
  · exact hx
  · rcases eq_or_lt_of_le q.2.1.1 with hr1 | hr1
    · have hq_bd : q ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        left
        refine ⟨q.1.2, ?_⟩
        ext
        · exact hr1
        · rfl
      exact ⟨b ⟨q, hq_bd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hq_bd, rfl⟩⟩
    · exact (hfx.2 (.inl (hcol₁_interior q hq hr1))).elim
  · rcases eq_or_lt_of_le q.2.1.2 with hr2 | hr2
    · have hq_bd : q ∈ bd ↥ClosedCylinder := by
        rw [bd_cylinder]
        right
        refine ⟨q.1.2, ?_⟩
        ext
        · exact hr2.symm
        · rfl
      exact ⟨b ⟨q, hq_bd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hq_bd, rfl⟩⟩
    · exact (hfx.2 (.inr (hcol₂_interior q hq hr2))).elim

private theorem handle_map_injective_on_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (D₁ : Set S)
    (cMap₁ : ℝ × Circle → S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hcMap₁_inj : InjOn cMap₁ {p | 0 ≤ p.1 ∧ p.1 ≤ δ₁ p.2})
    (δ₂ : Circle → ℝ)
    (D₂ : Set S)
    (cMap₂ : ℝ × Circle → S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hcMap₂_inj : InjOn cMap₂ {p | 0 ≤ p.1 ∧ p.1 ≤ δ₂ p.2})
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inl : ∀ y, f_XII (GluedSpace.inl hb_inj y) = y.1)
    (hf_inr_one : ∀ (q : ↑ClosedCylinder), q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ (q.1.1 - 1, q.1.2))
    (hf_inr_two : ∀ (q : ↑ClosedCylinder), ¬q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - q.1.1, q.1.2))
    (hf_img_col₁ : f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁
      q.1.2})) = closure Λ₁ \ D₁)
    (hf_img_col₂ : f_XII '' (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤
      q.1.1})) = closure Λ₂ \ D₂)
    (hf_mem_S₁_of_compl : ∀ x ∈ ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q :
      ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder
      | 2 - δ₂ q.1.2 ≤ q.1.1}))), f_XII x ∈ univ \ (Λ₁ ∪ Λ₂) → x ∈ (range (GluedSpace.inl
      hb_inj))) :
    let E := ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj ''
      ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj ''
        ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1})))
    Injective (fun x : ↥E => f_XII x.1) := by
  dsimp only
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII := S₁ ∪ C_col₁ ∪ C_col₂
  let ι_XII : ↥P₁_XII → S := fun x => f_XII x.1
  intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ hfx
  apply Subtype.ext
  change f_XII x₁ = f_XII x₂ at hfx
  have hcol₁_inj : Set.InjOn f_XII C_col₁ := by
    rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩ heq
    have hq₁_le : q₁.1.1 ≤ 3 / 2 := by
      linarith [(hδ₁_bd q₁.1.2).2, show q₁.1.1 ≤ 1 + δ₁ q₁.1.2 from hq₁]
    have hq₂_le : q₂.1.1 ≤ 3 / 2 := by
      linarith [(hδ₁_bd q₂.1.2).2, show q₂.1.1 ≤ 1 + δ₁ q₂.1.2 from hq₂]
    rw [hf_inr_one q₁ hq₁_le, hf_inr_one q₂ hq₂_le] at heq
    have hq₁_bound : q₁.1.1 ≤ 1 + δ₁ q₁.1.2 := hq₁
    have hq₂_bound : q₂.1.1 ≤ 1 + δ₁ q₂.1.2 := hq₂
    have hp := hcMap₁_inj ⟨by linarith [q₁.2.1.1], by linarith⟩
      ⟨by linarith [q₂.2.1.1], by linarith⟩ heq
    have h1 := Prod.ext_iff.mp hp
    have hq_eq : q₁ = q₂ := Subtype.ext (Prod.ext (by dsimp at h1; linarith [h1.1]) h1.2)
    rw [hq_eq]
  have hcol₂_inj : Set.InjOn f_XII C_col₂ := by
    rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩ heq
    have hq₁_not : ¬ q₁.1.1 ≤ 3 / 2 := by
      linarith [(hδ₂_bd q₁.1.2).2, show 2 - δ₂ q₁.1.2 ≤ q₁.1.1 from hq₁]
    have hq₂_not : ¬ q₂.1.1 ≤ 3 / 2 := by
      linarith [(hδ₂_bd q₂.1.2).2, show 2 - δ₂ q₂.1.2 ≤ q₂.1.1 from hq₂]
    rw [hf_inr_two q₁ hq₁_not, hf_inr_two q₂ hq₂_not] at heq
    have hp := hcMap₂_inj ⟨by linarith [q₁.2.1.2], by linarith [show 2 - δ₂ q₁.1.2
      ≤ q₁.1.1 from hq₁]⟩
      ⟨by linarith [q₂.2.1.2], by linarith [show 2 - δ₂ q₂.1.2 ≤ q₂.1.1 from hq₂]⟩ heq
    have h1 := Prod.ext_iff.mp hp
    have hq_eq : q₁ = q₂ := Subtype.ext (Prod.ext (by dsimp at h1; linarith [h1.1]) h1.2)
    rw [hq_eq]
  by_cases hfx_compl : f_XII x₁ ∈ univ \ (Λ₁ ∪ Λ₂)
  · obtain ⟨y₁, rfl⟩ := hf_mem_S₁_of_compl x₁ hx₁ hfx_compl
    obtain ⟨y₂, rfl⟩ := hf_mem_S₁_of_compl x₂ hx₂ (hfx ▸ hfx_compl)
    rw [hf_inl, hf_inl] at hfx
    exact congrArg (GluedSpace.inl hb_inj) (Subtype.ext hfx)
  · have h_in_12 : f_XII x₁ ∈ Λ₁ ∪ Λ₂ := by
      by_contra hnot
      exact hfx_compl ⟨mem_univ _, hnot⟩
    rcases h_in_12 with h_in_1 | h_in_2
    · have hx₁_col₁ : x₁ ∈ C_col₁ := by
        rcases hx₁ with (⟨y, rfl⟩ | hx₁_col₁) | hx₁_col₂
        · rw [hf_inl] at h_in_1
          exact (y.2.2 (.inl h_in_1)).elim
        · exact hx₁_col₁
        · have h_cl2 : f_XII x₁ ∈ closure Λ₂ \ D₂ :=
            hf_img_col₂ ▸ mem_image_of_mem f_XII hx₁_col₂
          exact (Set.disjoint_left.mp hd (subset_closure h_in_1) h_cl2.1).elim
      have hx₂_col₁ : x₂ ∈ C_col₁ := by
        have h_in_1' : f_XII x₂ ∈ Λ₁ := hfx ▸ h_in_1
        rcases hx₂ with (⟨y, rfl⟩ | hx₂_col₁) | hx₂_col₂
        · rw [hf_inl] at h_in_1'
          exact (y.2.2 (.inl h_in_1')).elim
        · exact hx₂_col₁
        · have h_cl2 : f_XII x₂ ∈ closure Λ₂ \ D₂ :=
            hf_img_col₂ ▸ mem_image_of_mem f_XII hx₂_col₂
          exact (Set.disjoint_left.mp hd (subset_closure h_in_1') h_cl2.1).elim
      exact hcol₁_inj hx₁_col₁ hx₂_col₁ hfx
    · have hx₁_col₂ : x₁ ∈ C_col₂ := by
        rcases hx₁ with (⟨y, rfl⟩ | hx₁_col₁) | hx₁_col₂
        · rw [hf_inl] at h_in_2
          exact (y.2.2 (.inr h_in_2)).elim
        · have h_cl1 : f_XII x₁ ∈ closure Λ₁ \ D₁ :=
            hf_img_col₁ ▸ mem_image_of_mem f_XII hx₁_col₁
          exact (Set.disjoint_left.mp hd h_cl1.1 (subset_closure h_in_2)).elim
        · exact hx₁_col₂
      have hx₂_col₂ : x₂ ∈ C_col₂ := by
        have h_in_2' : f_XII x₂ ∈ Λ₂ := hfx ▸ h_in_2
        rcases hx₂ with (⟨y, rfl⟩ | hx₂_col₁) | hx₂_col₂
        · rw [hf_inl] at h_in_2'
          exact (y.2.2 (.inr h_in_2')).elim
        · have h_cl1 : f_XII x₂ ∈ closure Λ₁ \ D₁ :=
            hf_img_col₁ ▸ mem_image_of_mem f_XII hx₂_col₁
          exact (Set.disjoint_left.mp hd h_cl1.1 (subset_closure h_in_2')).elim
        · exact hx₂_col₂
      exact hcol₂_inj hx₁_col₂ hx₂_col₂ hfx

private theorem pinched_cylinder_maps_onto_middle_strip
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (δ₂ : Circle → ℝ)
    (e_pinch : ↑ClosedCylinder ≃ₜ ↑{p : ClosedCylinder | 1 + δ₁ p.1.2 ≤ p.1.1 ∧ p.1.1
      ≤ 2 - δ₂ p.1.2}) :
    range (fun p : ClosedCylinder => GluedSpace.inr hb_inj ↑(e_pinch p)) =
      (GluedSpace.inr hb_inj '' ({q :
      ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2})) := by
  let S' := GluedSpace hb_inj
  let A_mid := {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}
  let P₂_XII := GluedSpace.inr hb_inj '' A_mid
  let j_P₂ := fun p : ClosedCylinder => GluedSpace.inr hb_inj ↑(e_pinch p)
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(e_pinch p).1, (e_pinch p).2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨e_pinch.symm ⟨q, hq⟩, by dsimp [j_P₂]; rw [e_pinch.apply_symm_apply]⟩

private theorem handle_pieces_cover_glued_surface
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (hU_eq : range (GluedSpace.inl hb_inj) ∪ range (GluedSpace.inr hb_inj) = univ)
    (δ₁ : Circle → ℝ)
    (δ₂ : Circle → ℝ) :
    ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1
      + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1})))
      ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂
      q.1.2})) = univ := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let A_mid := {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII := S₁ ∪ C_col₁ ∪ C_col₂
  let P₂_XII := GluedSpace.inr hb_inj '' A_mid
  ext x
  refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
  obtain hx1 | ⟨q, rfl⟩ : x ∈ S₁ ∪ S₂ := hU_eq.symm ▸ mem_univ x
  · exact .inl (.inl (.inl hx1))
  · by_cases h1 : q.1.1 ≤ 1 + δ₁ q.1.2
    · exact .inl (.inl (.inr ⟨q, h1, rfl⟩))
    · by_cases h2 : 2 - δ₂ q.1.2 ≤ q.1.1
      · exact .inl (.inr ⟨q, h2, rfl⟩)
      · exact .inr ⟨q, ⟨le_of_not_ge h1, le_of_not_ge h2⟩, rfl⟩

private theorem handle_pieces_meet_at_pinched_cuffs
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (δ₂ : Circle → ℝ)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hiUnion2 : ∀ {α : Type w} (f : Fin 2 → Set α), ⋃ i, f i = f 0 ∪ f 1)
    (hC0_sub_P₁ : (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}),
      GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 0 ⊆ ((range
      (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁
      q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}))))
    (hC1_sub_P₁ : (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}),
      GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 1 ⊆ ((range
      (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1 + δ₁
      q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1})))) :
    ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1
      + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1})))
      ∩ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂
      q.1.2})) = ⋃ i, (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁
      q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) i := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let A_mid := {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII := S₁ ∪ C_col₁ ∪ C_col₂
  let P₂_XII := GluedSpace.inr hb_inj '' A_mid
  let C_XII := ![GluedSpace.inr hb_inj '' A_cuff₁, GluedSpace.inr hb_inj '' A_cuff₂]
  rw [hiUnion2 C_XII]
  ext x
  constructor
  · rintro ⟨hx1, ⟨q, hq_mid, rfl⟩⟩
    rcases hx1 with (⟨y, hy_eq⟩ | ⟨q₁, hq₁, he₁⟩) | ⟨q₂, hq₂, he₂⟩
    · obtain ⟨hq_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
      rcases handleGlueMap_fst_eq_one_or_two ⟨q, hq_bd⟩ with hr1 | hr2
      · left
        refine ⟨q, ?_, rfl⟩
        change q.1.1 = 1 + δ₁ q.1.2
        linarith [hr1, hq_mid.1, (hδ₁_bd q.1.2).1]
      · right
        refine ⟨q, ?_, rfl⟩
        change q.1.1 = 2 - δ₂ q.1.2
        linarith [hr2, hq_mid.2, (hδ₂_bd q.1.2).1]
    · obtain rfl := GluedSpace.inr_injective hb_inj he₁
      left
      exact ⟨q₁, le_antisymm hq₁ hq_mid.1, rfl⟩
    · obtain rfl := GluedSpace.inr_injective hb_inj he₂
      right
      exact ⟨q₂, le_antisymm hq_mid.2 hq₂, rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · refine ⟨hC0_sub_P₁ ⟨q, hq, rfl⟩, ⟨q, ⟨le_of_eq hq.symm, ?_⟩, rfl⟩⟩
      linarith [show q.1.1 = 1 + δ₁ q.1.2 from hq, (hδ₁_bd q.1.2).2, (hδ₂_bd q.1.2).2]
    · refine ⟨hC1_sub_P₁ ⟨q, hq, rfl⟩, ⟨q, ⟨?_, le_of_eq hq⟩, rfl⟩⟩
      linarith [show q.1.1 = 2 - δ₂ q.1.2 from hq, (hδ₁_bd q.1.2).2, (hδ₂_bd q.1.2).2]

private theorem handle_map_image_of_lower_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (D₁ : Set S)
    (cMap₁ : ℝ × Circle → S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hcMap₁_bd : cMap₁ '' {p | p.1 = δ₁ p.2} = subBd D₁)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 0 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2})
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_one : ∀ (q : ↑ClosedCylinder), q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₁ (q.1.1 - 1, q.1.2)) :
    f_XII '' C_XII 0 = subBd D₁ := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  change f_XII '' (GluedSpace.inr hb_inj '' A_cuff₁) = subBd D₁
  rw [← hcMap₁_bd]
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq_le : q.1.1 ≤ 3 / 2 := by linarith [(hδ₁_bd q.1.2).2, show q.1.1 = 1 + δ₁ q.1.2 from hq]
    rw [hf_inr_one q hq_le]
    exact ⟨(q.1.1 - 1, q.1.2), by dsimp; linarith [show q.1.1 = 1 + δ₁ q.1.2 from hq], rfl⟩
  · rintro ⟨p, hp_eq, rfl⟩
    have hp_eq' : p.1 = δ₁ p.2 := hp_eq
    have hr : 1 + p.1 ∈ Icc (1 : ℝ) 2 :=
      ⟨by linarith [hp_eq', (hδ₁_bd p.2).1], by linarith [hp_eq', (hδ₁_bd p.2).2]⟩
    let q : ClosedCylinder := ⟨(1 + p.1, p.2), hr, mem_univ _⟩
    have hq_cuff : q ∈ A_cuff₁ := by dsimp [A_cuff₁, q]; linarith
    have hq_le : q.1.1 ≤ 3 / 2 := by dsimp [q]; linarith [hp_eq', (hδ₁_bd p.2).2]
    refine ⟨GluedSpace.inr hb_inj q, ⟨q, hq_cuff, rfl⟩, ?_⟩
    rw [hf_inr_one q hq_le]
    dsimp [q]
    rw [add_sub_cancel_left]

private theorem handle_map_image_of_upper_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₂ : Circle → ℝ)
    (D₂ : Set S)
    (cMap₂ : ℝ × Circle → S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hcMap₂_bd : cMap₂ '' {p | p.1 = δ₂ p.2} = subBd D₂)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 1 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_inr_two : ∀ (q : ↑ClosedCylinder), ¬q.1.1 ≤ 3 / 2 → f_XII (GluedSpace.inr hb_inj q) =
      cMap₂ (2 - q.1.1, q.1.2)) :
    f_XII '' C_XII 1 = subBd D₂ := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  change f_XII '' (GluedSpace.inr hb_inj '' A_cuff₂) = subBd D₂
  rw [← hcMap₂_bd]
  ext y
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq_not : ¬ q.1.1 ≤ 3 / 2 := by
      linarith [(hδ₂_bd q.1.2).2, show q.1.1 = 2 - δ₂ q.1.2 from hq]
    rw [hf_inr_two q hq_not]
    exact ⟨(2 - q.1.1, q.1.2), by dsimp; linarith [show q.1.1 = 2 - δ₂ q.1.2 from hq], rfl⟩
  · rintro ⟨p, hp_eq, rfl⟩
    have hp_eq' : p.1 = δ₂ p.2 := hp_eq
    have hr : 2 - p.1 ∈ Icc (1 : ℝ) 2 :=
      ⟨by linarith [hp_eq', (hδ₂_bd p.2).2], by linarith [hp_eq', (hδ₂_bd p.2).1]⟩
    let q : ClosedCylinder := ⟨(2 - p.1, p.2), hr, mem_univ _⟩
    have hq_cuff : q ∈ A_cuff₂ := by dsimp [A_cuff₂, q]; linarith
    have hq_not : ¬ q.1.1 ≤ 3 / 2 := by dsimp [q]; linarith [hp_eq', (hδ₂_bd p.2).2]
    refine ⟨GluedSpace.inr hb_inj q, ⟨q, hq_cuff, rfl⟩, ?_⟩
    rw [hf_inr_two q hq_not]
    dsimp [q]
    rw [sub_sub_cancel]

private theorem pinched_cylinder_maps_lower_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (hδ₁_cont : Continuous δ₁)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (δ₂ : Circle → ℝ)
    (hδ₂_cont : Continuous δ₂)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 0 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2})
    (e_pinch : ↑ClosedCylinder ≃ₜ ↑{p : ClosedCylinder | 1 + δ₁ p.1.2 ≤ p.1.1 ∧ p.1.1
      ≤ 2 - δ₂ p.1.2})
    (he_pinch : e_pinch = pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) :
    (fun p => GluedSpace.inr hb_inj ↑(e_pinch p)) '' range (cylEnd 1 m1) = C_XII 0 := by
  rw [hC]
  subst e_pinch
  let e_pinch := pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd
  let S' := GluedSpace hb_inj
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  let j_P₂ := fun p : ClosedCylinder => GluedSpace.inr hb_inj ↑(e_pinch p)
  change j_P₂ '' range (cylEnd 1 m1) = GluedSpace.inr hb_inj '' A_cuff₁
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(e_pinch (cylEnd 1 m1 z)).1, ?_, rfl⟩
    change ((e_pinch (cylEnd 1 m1 z)).1 : ClosedCylinder).1.1 =
      1 + δ₁ ((e_pinch (cylEnd 1 m1 z)).1 : ClosedCylinder).1.2
    rw [pinchCylHomeo_cylEnd_one]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨cylEnd 1 m1 q.1.2, ⟨q.1.2, rfl⟩, ?_⟩
    dsimp [j_P₂]
    congr 1
    apply Subtype.ext
    rw [pinchCylHomeo_cylEnd_one]
    exact Prod.ext (show 1 + δ₁ q.1.2 = q.1.1 from hq.symm) rfl

private theorem pinched_cylinder_maps_upper_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (δ₁ : Circle → ℝ)
    (hδ₁_cont : Continuous δ₁)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (δ₂ : Circle → ℝ)
    (hδ₂_cont : Continuous δ₂)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 1 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})
    (e_pinch : ↑ClosedCylinder ≃ₜ ↑{p : ClosedCylinder | 1 + δ₁ p.1.2 ≤ p.1.1 ∧ p.1.1
      ≤ 2 - δ₂ p.1.2})
    (he_pinch : e_pinch = pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2) :
    (fun p => GluedSpace.inr hb_inj ↑(e_pinch p)) '' range (cylEnd 2 m2) = C_XII 1 := by
  rw [hC]
  subst e_pinch
  let e_pinch := pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd
  let S' := GluedSpace hb_inj
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  let j_P₂ := fun p : ClosedCylinder => GluedSpace.inr hb_inj ↑(e_pinch p)
  change j_P₂ '' range (cylEnd 2 m2) = GluedSpace.inr hb_inj '' A_cuff₂
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(e_pinch (cylEnd 2 m2 z)).1, ?_, rfl⟩
    change ((e_pinch (cylEnd 2 m2 z)).1 : ClosedCylinder).1.1 =
      2 - δ₂ ((e_pinch (cylEnd 2 m2 z)).1 : ClosedCylinder).1.2
    rw [pinchCylHomeo_cylEnd_two]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨cylEnd 2 m2 q.1.2, ⟨q.1.2, rfl⟩, ?_⟩
    dsimp [j_P₂]
    congr 1
    apply Subtype.ext
    rw [pinchCylHomeo_cylEnd_two]
    exact Prod.ext (show 2 - δ₂ q.1.2 = q.1.1 from hq.symm) rfl

private theorem handle_complement_boundary_is_cuff_union
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (D₁ : Set S)
    (hD₁_open : IsOpen D₁)
    (hD₁_sub : D₁ ⊆ Λ₁)
    (D₂ : Set S)
    (hD₂_open : IsOpen D₂)
    (hD₂_sub : D₂ ⊆ Λ₂)
    (hcl_D₁_sub : closure D₁ ⊆ closure Λ₁)
    (hcl_D₂_sub : closure D₂ ⊆ closure Λ₂)
    (P₁_XII : Set (GluedSpace hb_inj))
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_img_C0 : f_XII '' C_XII 0 = subBd D₁)
    (hf_img_C1 : f_XII '' C_XII 1 = subBd D₂)
    (e_P₁ : ↑P₁_XII ≃ₜ ↑(univ \ (D₁ ∪ D₂)))
    (he_P₁ : ∀ x, (e_P₁ x).1 = f_XII x.1)
    (hXD_bd : bd ↑(univ \ (D₁ ∪ D₂)) = Subtype.val ⁻¹' (subBd D₁ ∪ subBd D₂))
    (hiUnion2 : ∀ {α : Type w} (f : Fin 2 → Set α), ⋃ i, f i = f 0 ∪ f 1)
    (hC0_sub_P₁ : C_XII 0 ⊆ P₁_XII)
    (hC1_sub_P₁ : C_XII 1 ⊆ P₁_XII)
    (hf_injOn_P₁ : InjOn f_XII P₁_XII) :
    Subtype.val '' bd ↑P₁_XII = ⋃ i, C_XII i := by
  let S' := GluedSpace hb_inj
  rw [hiUnion2 C_XII]
  have hsub1 : Subtype.val '' bd ↥P₁_XII ⊆ P₁_XII := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hsub2 : C_XII 0 ∪ C_XII 1 ⊆ P₁_XII := union_subset hC0_sub_P₁ hC1_sub_P₁
  refine (hf_injOn_P₁.image_eq_image_iff hsub1 hsub2).mp ?_
  rw [image_union, hf_img_C0, hf_img_C1]
  have hbd_e : e_P₁ '' bd ↥P₁_XII = bd ↥(univ \ (D₁ ∪ D₂) : Set S) :=
    image_bd_homeomorph e_P₁
  calc f_XII '' (Subtype.val '' bd ↥P₁_XII)
    _ = Subtype.val '' (e_P₁ '' bd ↥P₁_XII) := by
      rw [← image_comp, ← image_comp]
      exact congrArg (fun f => f '' bd ↥P₁_XII) (funext fun x => (he_P₁ x).symm)
    _ = Subtype.val '' bd ↥(univ \ (D₁ ∪ D₂) : Set S) := by rw [hbd_e]
    _ = subBd D₁ ∪ subBd D₂ := by
      rw [hXD_bd, Subtype.image_preimage_coe]
      refine inter_eq_right.mpr (union_subset ?_ ?_)
      · rw [subBd_eq_frontier, hD₁_open.frontier_eq]
        exact fun x hx => ⟨mem_univ _, fun h => h.elim hx.2 fun h2 =>
          Set.disjoint_left.mp hd (hcl_D₁_sub hx.1) (subset_closure (hD₂_sub h2))⟩
      · rw [subBd_eq_frontier, hD₂_open.frontier_eq]
        exact fun x hx => ⟨mem_univ _, fun h => h.elim (fun h1 =>
          Set.disjoint_left.mp hd (subset_closure (hD₁_sub h1)) (hcl_D₂_sub hx.1)) hx.2⟩

private theorem handle_map_image_of_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (D₁ : Set S)
    (hD₁_sub : D₁ ⊆ Λ₁)
    (D₂ : Set S)
    (hD₂_sub : D₂ ⊆ Λ₂)
    (S' : Type w)
    (P₁_XII : Set S')
    (f_XII : S' → S)
    (hf_img_P₁ : f_XII '' P₁_XII = closure Λ₁ \ D₁ ∪ univ \ (Λ₁ ∪ Λ₂) ∪ closure Λ₂ \ D₂) :
    f_XII '' P₁_XII = univ \ (D₁ ∪ D₂) := by
  rw [hf_img_P₁]
  ext y
  constructor
  · rintro ((hy | hy) | hy)
    · exact ⟨mem_univ _, fun h => h.elim hy.2 fun h2 =>
        Set.disjoint_left.mp hd hy.1 (subset_closure (hD₂_sub h2))⟩
    · exact ⟨mem_univ _, fun h => hy.2 (h.imp (fun h1 => hD₁_sub h1) (fun h2 => hD₂_sub h2))⟩
    · exact ⟨mem_univ _, fun h => h.elim (fun h1 =>
        Set.disjoint_left.mp hd (subset_closure (hD₁_sub h1)) hy.1) hy.2⟩
  · rintro ⟨_, hy⟩
    by_cases hy1 : y ∈ Λ₁
    · exact .inl (.inl ⟨subset_closure hy1, fun h1 => hy (.inl h1)⟩)
    · by_cases hy2 : y ∈ Λ₂
      · exact .inr ⟨subset_closure hy2, fun h2 => hy (.inr h2)⟩
      · exact .inl (.inr ⟨mem_univ _, fun h => h.elim hy1 hy2⟩)

private theorem union_two_indexed_sets : ∀ {α : Type w} (f : Fin 2 → Set α), (⋃ i : Fin 2, f i)
  = f 0 ∪ f 1 := by
  intro α f
  ext x
  simp [Fin.exists_fin_two]

private theorem pinched_handle_forms_capped_split
    {S : Type w}
    [TopologicalSpace S]
    (hS : IsClosedSurface S)
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    [hConn' : ConnectedSpace (GluedSpace hb_inj)]
    (δ₁ : Circle → ℝ)
    (D₁ : Set S)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (δ₂ : Circle → ℝ)
    (D₂ : Set S)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hd_D : Disjoint (closure D₁) (closure D₂))
    (hD₁_disc : IsOpenDisc D₁)
    (hD₂_disc : IsOpenDisc D₂)
    (P₁_XII : Set (GluedSpace hb_inj))
    (P₂_XII : Set (GluedSpace hb_inj))
    (f_XII : (GluedSpace hb_inj) → S)
    (hf_img_C0 : f_XII '' (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁
      q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 0 = subBd
      D₁)
    (hf_img_C1 : f_XII '' (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁
      q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 1 = subBd
      D₂)
    (hι_XII_emb : IsClosedEmbedding (fun x : ↥P₁_XII => f_XII x.1))
    (hι_XII_range : range (fun x : ↥P₁_XII => f_XII x.1) = univ \ (D₁ ∪ D₂))
    (hP₁_surf : IsSurface ↑P₁_XII)
    (j_P₂ : ↑ClosedCylinder → (GluedSpace hb_inj))
    (hj_P₂_emb : IsClosedEmbedding j_P₂)
    (hP₂_surf : IsSurface ↑P₂_XII)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (hj_P₂_cuff₁ : j_P₂ '' range (cylEnd 1 m1) = (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder
      | q.1.1 = 1 + δ₁ q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂
      q.1.2})]) 0)
    (hj_P₂_cuff₂ : j_P₂ '' range (cylEnd 2 m2) = (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder
      | q.1.1 = 1 + δ₁ q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂
      q.1.2})]) 1)
    (hiUnion2 : ∀ {α : Type w} (f : Fin 2 → Set α), ⋃ i, f i = f 0 ∪ f 1)
    (hbd_P₂ : Subtype.val '' bd ↑P₂_XII = ⋃ i, (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder |
      q.1.1 = 1 + δ₁ q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂
      q.1.2})]) i)
    (hC0_sub_P₁ : (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}),
      GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 0 ⊆ P₁_XII)
    (hC1_sub_P₁ : (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}),
      GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) 1 ⊆ P₁_XII)
    (hP12_union : P₁_XII ∪ P₂_XII = univ)
    (hP12_inter : P₁_XII ∩ P₂_XII = ⋃ i, (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1
      = 1 + δ₁ q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})])
      i)
    (hbd_P₁ : Subtype.val '' bd ↑P₁_XII = ⋃ i, (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder |
      q.1.1 = 1 + δ₁ q.1.2}), GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂
      q.1.2})]) i) :
    GM12.IsCappedSplit (![GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}),
      GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})]) P₁_XII P₂_XII (fun
      x : ↥P₁_XII => f_XII x.1) ![D₁, D₂] := by
  let S' := GluedSpace hb_inj
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  let C_XII := ![GluedSpace.inr hb_inj '' A_cuff₁, GluedSpace.inr hb_inj '' A_cuff₂]
  let ι_XII := fun x : ↥P₁_XII => f_XII x.1
  refine
    { surface := ⟨hS', hConn'⟩
      isOArc := ?_
      disjoint := ?_
      manifold₁ := hP₁_surf
      manifold₂ := hP₂_surf
      union := hP12_union
      inter := hP12_inter
      bd₁ := hbd_P₁
      bd₂ := hbd_P₂
      surface_hat := hS
      isEmbedding := hι_XII_emb.isEmbedding
      isOpenDisc := fun i => by fin_cases i <;> [exact hD₁_disc; exact hD₂_disc]
      bounds := ?_
      disjoint_D := fun i j hij => by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hd_D.mono subset_closure subset_closure
        · exact hd_D.symm.mono subset_closure subset_closure
        · exact (hij rfl).elim
      compl := ?_ }
  · intro i
    fin_cases i
    · change IsOArc (C_XII 0)
      apply (congrArg IsOArc hj_P₂_cuff₁).mp
      exact isOArc_image hj_P₂_emb.isEmbedding ⟨(isEmbedding_cylEnd 1 m1).toHomeomorph⟩
    · change IsOArc (C_XII 1)
      apply (congrArg IsOArc hj_P₂_cuff₂).mp
      exact isOArc_image hj_P₂_emb.isEmbedding ⟨(isEmbedding_cylEnd 2 m2).toHomeomorph⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [Set.disjoint_left]
      rintro _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, he⟩
      have hq_eq : q₂ = q₁ := GluedSpace.inr_injective hb_inj he
      rw [hq_eq] at hq₂
      linarith [show q₁.1.1 = 1 + δ₁ q₁.1.2 from hq₁, show q₁.1.1 = 2 - δ₂ q₁.1.2 from hq₂,
        (hδ₁_bd q₁.1.2).2, (hδ₂_bd q₁.1.2).2]
    · rw [Set.disjoint_left]
      rintro _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, he⟩
      have hq_eq : q₂ = q₁ := GluedSpace.inr_injective hb_inj he
      rw [hq_eq] at hq₂
      linarith [show q₁.1.1 = 2 - δ₂ q₁.1.2 from hq₁, show q₁.1.1 = 1 + δ₁ q₁.1.2 from hq₂,
        (hδ₁_bd q₁.1.2).2, (hδ₂_bd q₁.1.2).2]
    · exact (hij rfl).elim
  · intro i
    fin_cases i
    · change subBd D₁ = ι_XII '' (Subtype.val ⁻¹' (C_XII 0))
      rw [← hf_img_C0]
      ext y
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hC0_sub_P₁ hx⟩, hx, rfl⟩,
        by rintro ⟨⟨x, _⟩, hx, rfl⟩; exact ⟨x, hx, rfl⟩⟩
    · change subBd D₂ = ι_XII '' (Subtype.val ⁻¹' (C_XII 1))
      rw [← hf_img_C1]
      ext y
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hC1_sub_P₁ hx⟩, hx, rfl⟩,
        by rintro ⟨⟨x, _⟩, hx, rfl⟩; exact ⟨x, hx, rfl⟩⟩
  · rw [hiUnion2 ![D₁, D₂], hι_XII_range]
    ext x
    simp only [mem_compl_iff, mem_sdiff, mem_univ, mem_union, true_and, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto

private theorem handle_complement_off_original_surface_is_unmarked
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle}
    (δ₁ : Circle → ℝ)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₁_zero : ∀ (z : Circle), δ₁ z = 0 ↔ z ∈ W_pts)
    (δ₂ : Circle → ℝ)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hδ₂_zero : ∀ (z : Circle), δ₂ z = 0 ↔ z ∈ W_pts) :
    ((range (GluedSpace.inl hb_inj)) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | q.1.1 ≤ 1
      + δ₁ q.1.2})) ∪ (GluedSpace.inr hb_inj '' ({q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}))) \
      (range (GluedSpace.inl hb_inj)) ⊆ (GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1
      ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}) := by
  let b := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let CollarInt := GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉
    W_pts}
  let A_col₁ := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let C_col₁ := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII := S₁ ∪ C_col₁ ∪ C_col₂
  rintro x ⟨(hx1 | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩, hx_not_S₁⟩
  · exact (hx_not_S₁ hx1).elim
  · have hq_not_bd : q ∉ bd ↥ClosedCylinder := fun hbd =>
      hx_not_S₁ ⟨b ⟨q, hbd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd, rfl⟩⟩
    have hq1 : 1 < q.1.1 := lt_of_le_of_ne q.2.1.1 fun hr1 =>
      hq_not_bd (by rw [bd_cylinder]; exact .inl ⟨q.1.2, Subtype.ext (Prod.ext hr1 rfl)⟩)
    have hq2 : q.1.1 < 2 := by linarith [show q.1.1 ≤ 1 + δ₁ q.1.2 from hq, (hδ₁_bd q.1.2).2]
    have hqW : q.1.2 ∉ W_pts := fun hw => by
      have h0 := (hδ₁_zero q.1.2).mpr hw
      linarith [show q.1.1 ≤ 1 + δ₁ q.1.2 from hq]
    exact ⟨q, ⟨hq1, hq2, hqW⟩, rfl⟩
  · have hq_not_bd : q ∉ bd ↥ClosedCylinder := fun hbd =>
      hx_not_S₁ ⟨b ⟨q, hbd⟩, (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd, rfl⟩⟩
    have hq1 : 1 < q.1.1 := by linarith [show 2 - δ₂ q.1.2 ≤ q.1.1 from hq, (hδ₂_bd q.1.2).2]
    have hq2 : q.1.1 < 2 := lt_of_le_of_ne q.2.1.2 fun hr2 =>
      hq_not_bd (by rw [bd_cylinder]; exact .inr ⟨q.1.2, Subtype.ext (Prod.ext hr2.symm rfl)⟩)
    have hqW : q.1.2 ∉ W_pts := fun hw => by
      have h0 := (hδ₂_zero q.1.2).mpr hw
      linarith [show 2 - δ₂ q.1.2 ≤ q.1.1 from hq]
    exact ⟨q, ⟨hq1, hq2, hqW⟩, rfl⟩

private theorem marked_lower_cylinder_end_on_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle}
    (δ₁ : Circle → ℝ)
    (hδ₁_zero : ∀ (z : Circle), δ₁ z = 0 ↔ z ∈ W_pts)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 0 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2})
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) :
    GluedSpace.inr hb_inj '' cylEnd 1 m1 '' W_pts ⊆ C_XII 0 := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨cylEnd 1 m1 z, ?_, rfl⟩
  change (1 : ℝ) = 1 + δ₁ z
  linarith [(hδ₁_zero z).mpr hz]

private theorem unmarked_lower_pinched_cuff_inside_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle}
    (δ₁ : Circle → ℝ)
    (hδ₁_bd : ∀ (z : Circle), 0 ≤ δ₁ z ∧ δ₁ z ≤ 1 / 4)
    (hδ₁_zero : ∀ (z : Circle), δ₁ z = 0 ↔ z ∈ W_pts)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 0 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2})
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) :
    C_XII 0 \ GluedSpace.inr hb_inj '' cylEnd 1 m1 '' W_pts ⊆ (GluedSpace.inr hb_inj '' {q :
      ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}) := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let CollarInt := GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉
    W_pts}
  let A_cuff₁ := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  rintro _ ⟨⟨q, hq, rfl⟩, hnot_W⟩
  have hqW : q.1.2 ∉ W_pts := fun hw => hnot_W ⟨cylEnd 1 m1 q.1.2, ⟨q.1.2, hw, rfl⟩, by
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change (1 : ℝ) = q.1.1
      linarith [show q.1.1 = 1 + δ₁ q.1.2 from hq, (hδ₁_zero q.1.2).mpr hw]
    · rfl⟩
  have hpos : 0 < δ₁ q.1.2 := lt_of_le_of_ne (hδ₁_bd q.1.2).1 fun h0 =>
    hqW ((hδ₁_zero q.1.2).mp h0.symm)
  exact ⟨q, ⟨by linarith [show q.1.1 = 1 + δ₁ q.1.2 from hq],
    by linarith [show q.1.1 = 1 + δ₁ q.1.2 from hq, (hδ₁_bd q.1.2).2], hqW⟩, rfl⟩

private theorem marked_upper_cylinder_end_on_pinched_cuff
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle}
    (δ₂ : Circle → ℝ)
    (hδ₂_zero : ∀ (z : Circle), δ₂ z = 0 ↔ z ∈ W_pts)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 1 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2) :
    GluedSpace.inr hb_inj '' cylEnd 2 m2 '' W_pts ⊆ C_XII 1 := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨cylEnd 2 m2 z, ?_, rfl⟩
  change (2 : ℝ) = 2 - δ₂ z
  linarith [(hδ₂_zero z).mpr hz]

private theorem unmarked_upper_pinched_cuff_inside_collar
    {S : Type w}
    [TopologicalSpace S]
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle}
    (δ₂ : Circle → ℝ)
    (hδ₂_bd : ∀ (z : Circle), 0 ≤ δ₂ z ∧ δ₂ z ≤ 1 / 4)
    (hδ₂_zero : ∀ (z : Circle), δ₂ z = 0 ↔ z ∈ W_pts)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hC : C_XII 1 = GluedSpace.inr hb_inj '' {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2})
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2) :
    C_XII 1 \ GluedSpace.inr hb_inj '' cylEnd 2 m2 '' W_pts ⊆ (GluedSpace.inr hb_inj '' {q :
      ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}) := by
  rw [hC]
  let S' := GluedSpace hb_inj
  let CollarInt := GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉
    W_pts}
  let A_cuff₂ := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  rintro _ ⟨⟨q, hq, rfl⟩, hnot_W⟩
  have hqW : q.1.2 ∉ W_pts := fun hw => hnot_W ⟨cylEnd 2 m2 q.1.2, ⟨q.1.2, hw, rfl⟩, by
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change (2 : ℝ) = q.1.1
      linarith [show q.1.1 = 2 - δ₂ q.1.2 from hq, (hδ₂_zero q.1.2).mpr hw]
    · rfl⟩
  have hpos : 0 < δ₂ q.1.2 := lt_of_le_of_ne (hδ₂_bd q.1.2).1 fun h0 =>
    hqW ((hδ₂_zero q.1.2).mp h0.symm)
  exact ⟨q, ⟨by linarith [show q.1.1 = 2 - δ₂ q.1.2 from hq, (hδ₂_bd q.1.2).2],
    by linarith [show q.1.1 = 2 - δ₂ q.1.2 from hq], hqW⟩, rfl⟩

private theorem marked_radial_line_in_pinched_strip
    {S' : Type*} (inr : ClosedCylinder → S') {W : Set Circle} {δ₁ δ₂ : Circle → ℝ}
    (hδ₁_zero : ∀ z, δ₁ z = 0 ↔ z ∈ W) (hδ₂_zero : ∀ z, δ₂ z = 0 ↔ z ∈ W)
    {z : Circle} (hz : z ∈ W) :
    inr '' {q : ClosedCylinder | q.1.2 = z} ⊆
      inr '' {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2} := by
  rintro _ ⟨p, rfl, rfl⟩
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · linarith [p.2.1.1, (hδ₁_zero p.1.2).mpr hz]
  · linarith [p.2.1.2, (hδ₂_zero p.1.2).mpr hz]

/-- The pinched handle split on `GluedSpace hb_inj` touching `subBd Λ₁` and `subBd Λ₂` only at
`g₁ '' W_pts` and `g₂ '' W_pts`. -/
theorem exists_pinched_handleSplit {S : Type w} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hΛ₁ : IsOpenDisc Λ₁) (hΛ₂ : IsOpenDisc Λ₂)
    (hCD₁ : IsClosedDisc (closure Λ₁)) (hCD₂ : IsClosedDisc (closure Λ₂))
    (hdiscBd₁ : discBd (closure Λ₁) = subBd Λ₁)
    (hdiscBd₂ : discBd (closure Λ₂) = subBd Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {W_pts : Set Circle} (hW_cl : IsClosed W_pts) (hW_ne : W_pts.Nonempty) :
    let S' := GluedSpace hb_inj
    let S₁ : Set S' := range (GluedSpace.inl hb_inj)
    let CollarInt : Set S' :=
      GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}
    ∃ (C_XII : Fin 2 → Set S') (P₁_XII P₂_XII : Set S') (ι_XII : ↥P₁_XII → S)
      (D : Fin 2 → Set S) (f_XII : S' → S),
      GM12.IsHandleSplit C_XII P₁_XII P₂_XII ι_XII D ∧
      S₁ ⊆ P₁_XII ∧
      (∀ y : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S), f_XII (GluedSpace.inl hb_inj y) = y.1) ∧
      (∀ x : ↥P₁_XII, ι_XII x = f_XII x.1) ∧
      IsClosedEmbedding ι_XII ∧
      D 0 ⊆ Λ₁ ∧ D 1 ⊆ Λ₂ ∧
      closure (D 0) ⊆ closure Λ₁ ∧ closure (D 1) ⊆ closure Λ₂ ∧
      P₁_XII \ S₁ ⊆ CollarInt ∧
      GluedSpace.inr hb_inj '' (cylEnd 1 (by norm_num) '' W_pts) ⊆ C_XII 0 ∧
      C_XII 0 \ (GluedSpace.inr hb_inj '' (cylEnd 1 (by norm_num) '' W_pts)) ⊆ CollarInt ∧
      GluedSpace.inr hb_inj '' (cylEnd 2 (by norm_num) '' W_pts) ⊆ C_XII 1 ∧
      C_XII 1 \ (GluedSpace.inr hb_inj '' (cylEnd 2 (by norm_num) '' W_pts)) ⊆ CollarInt ∧
      (∀ z ∈ W_pts, GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = z} ⊆ P₂_XII) ∧
      f_XII '' (C_XII 0) = subBd (D 0) ∧
      f_XII '' (C_XII 1) = subBd (D 1) ∧
      f_XII '' P₁_XII = (closure Λ₁ \ D 0) ∪ (univ \ (Λ₁ ∪ Λ₂)) ∪ (closure Λ₂ \ D 1) ∧
      (∀ x ∈ P₁_XII, f_XII x ∈ univ \ (Λ₁ ∪ Λ₂) → x ∈ S₁) := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open)
  have : CompactSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isCompact_iff_compactSpace.mp hX_closed.isCompact
  have : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  have hb_cont := continuous_handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_range := range_handleGlueMap hS hΛ₁_open hΛ₂_open hOArc₁ hOArc₂ hout₁ hout₂ hd g₁ g₂
  have : T2Space (GluedSpace hb_inj) :=
    GluedSpace.t2Space (isClosed_bd ↥ClosedCylinder) hb_cont hb_inj
  obtain ⟨hS', hConn', _, _, hS₂_surf, hU_eq, _, _⟩ :=
    isClosedSurface_of_handle_glue hS hΛ₁ hΛ₂ hd hOArc₁ hOArc₂ hout₁ hout₂ hb_cont hb_inj hb_range
  obtain ⟨δ₁, D₁, cMap₁, hδ₁_cont, hδ₁_bd, hδ₁_zero, hD₁_open, hD₁_sub, hCD_D₁, hsubBd_D₁_eq,
    hOArc_D₁, hout_D₁, _, _, _, hcMap₁_cont, hcMap₁_inj, hcMap₁_zero, hcMap₁_collar, hcMap₁_bd, _⟩
      :=
    exists_pinched_subdisc_of_region hS hΛ₁_open hCD₁ hdiscBd₁ hout₁ g₁ hW_cl hW_ne
  obtain ⟨δ₂, D₂, cMap₂, hδ₂_cont, hδ₂_bd, hδ₂_zero, hD₂_open, hD₂_sub, hCD_D₂, hsubBd_D₂_eq,
    hOArc_D₂, hout_D₂, _, _, _, hcMap₂_cont, hcMap₂_inj, hcMap₂_zero, hcMap₂_collar, hcMap₂_bd, _⟩
      :=
    exists_pinched_subdisc_of_region hS hΛ₂_open hCD₂ hdiscBd₂ hout₂ g₂ hW_cl hW_ne
  have hcl_D₁_sub : closure D₁ ⊆ closure Λ₁ := closure_mono hD₁_sub
  have hcl_D₂_sub : closure D₂ ⊆ closure Λ₂ := closure_mono hD₂_sub
  have hd_D : Disjoint (closure D₁) (closure D₂) := hd.mono hcl_D₁_sub hcl_D₂_sub
  have hD₁_disc := isOpenDisc_of_isClosedDisc_closure hS hD₁_open hCD_D₁ hout_D₁
  have hD₂_disc := isOpenDisc_of_isClosedDisc_closure hS hD₂_open hCD_D₂ hout_D₂
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  let CollarInt : Set S' :=
    GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let e₂ : ClosedCylinder ≃ₜ ↥S₂ := hinr_emb.isEmbedding.toHomeomorph
  have hCyl_surf : IsSurface ClosedCylinder := isSurface_of_homeo e₂.symm hS₂_surf
  let A_col₁ : Set ClosedCylinder := {q : ClosedCylinder | q.1.1 ≤ 1 + δ₁ q.1.2}
  let A_col₂ : Set ClosedCylinder := {q : ClosedCylinder | 2 - δ₂ q.1.2 ≤ q.1.1}
  let A_mid : Set ClosedCylinder :=
    {q : ClosedCylinder | 1 + δ₁ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ 2 - δ₂ q.1.2}
  let A_cuff₁ : Set ClosedCylinder := {q : ClosedCylinder | q.1.1 = 1 + δ₁ q.1.2}
  let A_cuff₂ : Set ClosedCylinder := {q : ClosedCylinder | q.1.1 = 2 - δ₂ q.1.2}
  have hA_col₁_cl : IsClosed A_col₁ := lower_cylinder_collar_closed δ₁ hδ₁_cont
  have hA_col₂_cl : IsClosed A_col₂ := upper_cylinder_collar_closed δ₂ hδ₂_cont
  have hA_mid_cl : IsClosed A_mid := middle_cylinder_strip_closed δ₁ hδ₁_cont δ₂ hδ₂_cont
  let C_col₁ : Set S' := GluedSpace.inr hb_inj '' A_col₁
  let C_col₂ : Set S' := GluedSpace.inr hb_inj '' A_col₂
  let P₁_XII : Set S' := S₁ ∪ C_col₁ ∪ C_col₂
  let P₂_XII : Set S' := GluedSpace.inr hb_inj '' A_mid
  let C_XII : Fin 2 → Set S' :=
    ![GluedSpace.inr hb_inj '' A_cuff₁, GluedSpace.inr hb_inj '' A_cuff₂]
  let f_XII : S' → S :=
    handlePinchRetract hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂ hcMap₁_zero hcMap₂_zero
  have hf_inl : ∀ y, f_XII (GluedSpace.inl hb_inj y) = y.1 := fun _ => rfl
  have hf_inr_one : ∀ q : ClosedCylinder, q.1.1 ≤ 3 / 2 →
      f_XII (GluedSpace.inr hb_inj q) = cMap₁ (q.1.1 - 1, q.1.2) :=
    handlePinchRetract_inr_one hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂ hcMap₁_zero hcMap₂_zero
  have hf_inr_two : ∀ q : ClosedCylinder, ¬ q.1.1 ≤ 3 / 2 →
      f_XII (GluedSpace.inr hb_inj q) = cMap₂ (2 - q.1.1, q.1.2) :=
    handlePinchRetract_inr_two hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj cMap₁ cMap₂ hcMap₁_zero hcMap₂_zero
  let ι_XII : ↥P₁_XII → S := fun x => f_XII x.1
  have hS₁_cl : IsClosed S₁ := hinl_emb.isClosed_range
  have hC_col₁_cl : IsClosed C_col₁ := hinr_emb.isClosedMap _ hA_col₁_cl
  have hC_col₂_cl : IsClosed C_col₂ := hinr_emb.isClosedMap _ hA_col₂_cl
  have hP₁_cl : IsClosed P₁_XII := (hS₁_cl.union hC_col₁_cl).union hC_col₂_cl
  have : CompactSpace ↥P₁_XII := isCompact_iff_compactSpace.mp hP₁_cl.isCompact
  have hf_S₁_cont : ContinuousOn f_XII S₁ :=
    handle_map_continuous_on_original_surface (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj e₁ (fun _ => rfl) f_XII hf_inl
  have hf_col₁_cont : ContinuousOn f_XII C_col₁ :=
    handle_map_continuous_on_lower_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₁ cMap₁ hδ₁_bd hcMap₁_cont e₂ (fun _ => rfl) f_XII hf_inr_one
  have hf_col₂_cont : ContinuousOn f_XII C_col₂ :=
    handle_map_continuous_on_upper_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₂ cMap₂ hδ₂_bd hcMap₂_cont e₂ (fun _ => rfl) f_XII hf_inr_two
  have hf_P₁_cont : ContinuousOn f_XII P₁_XII :=
    (hf_S₁_cont.union_of_isClosed hf_col₁_cont hS₁_cl hC_col₁_cl).union_of_isClosed
      hf_col₂_cont (hS₁_cl.union hC_col₁_cl) hC_col₂_cl
  have hι_XII_cont : Continuous ι_XII := continuousOn_iff_continuous_domRestrict.mp hf_P₁_cont
  have hf_img_S₁ : f_XII '' S₁ = univ \ (Λ₁ ∪ Λ₂) :=
    handle_map_image_of_original_surface (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj f_XII hf_inl
  have hf_img_col₁ : f_XII '' C_col₁ = closure Λ₁ \ D₁ :=
    handle_map_image_of_lower_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd g₁
      g₂ hb_inj δ₁ D₁ cMap₁ hδ₁_bd hcMap₁_collar f_XII hf_inr_one
  have hf_img_col₂ : f_XII '' C_col₂ = closure Λ₂ \ D₂ :=
    handle_map_image_of_upper_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd g₁
      g₂ hb_inj δ₂ D₂ cMap₂ hδ₂_bd hcMap₂_collar f_XII hf_inr_two
  have hf_img_C0 : f_XII '' (C_XII 0) = subBd D₁ := by
    exact handle_map_image_of_lower_pinched_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₁ D₁ cMap₁ hδ₁_bd hcMap₁_bd C_XII rfl f_XII hf_inr_one
  have hf_img_C1 : f_XII '' (C_XII 1) = subBd D₂ := by
    exact handle_map_image_of_upper_pinched_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₂ D₂ cMap₂ hδ₂_bd hcMap₂_bd C_XII rfl f_XII hf_inr_two
  have hf_img_P₁ : f_XII '' P₁_XII = (closure Λ₁ \ D₁) ∪ (univ \ (Λ₁ ∪ Λ₂)) ∪ (closure Λ₂ \ D₂)
    := by
    change f_XII '' (S₁ ∪ C_col₁ ∪ C_col₂) = _
    rw [image_union, image_union, hf_img_S₁, hf_img_col₁, hf_img_col₂,
      union_comm (univ \ (Λ₁ ∪ Λ₂))]
  have hf_img_P₁_compl : f_XII '' P₁_XII = univ \ (D₁ ∪ D₂) := by
    exact handle_map_image_of_complement (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hd D₁ hD₁_sub D₂ hD₂_sub
      S' P₁_XII f_XII hf_img_P₁
  have hcol₁_interior : ∀ q ∈ A_col₁, 1 < q.1.1 → f_XII (GluedSpace.inr hb_inj q) ∈ Λ₁ := by
    exact lower_collar_interior_maps_inside_disc (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₁ D₁ cMap₁ hδ₁_bd hcMap₁_inj hcMap₁_zero f_XII hf_inr_one hf_img_col₁
  have hcol₂_interior : ∀ q ∈ A_col₂, q.1.1 < 2 → f_XII (GluedSpace.inr hb_inj q) ∈ Λ₂ := by
    exact upper_collar_interior_maps_inside_disc (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₂ D₂ cMap₂ hδ₂_bd hcMap₂_inj hcMap₂_zero f_XII hf_inr_two hf_img_col₂
  have hf_mem_S₁_of_compl : ∀ x ∈ P₁_XII, f_XII x ∈ univ \ (Λ₁ ∪ Λ₂) → x ∈ S₁ := by
    exact handle_map_complement_has_original_preimage (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj δ₁ δ₂ f_XII hcol₁_interior hcol₂_interior
  have hι_XII_inj : Function.Injective ι_XII := by
    exact handle_map_injective_on_complement (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj δ₁ D₁ cMap₁ hδ₁_bd hcMap₁_inj δ₂ D₂ cMap₂ hδ₂_bd hcMap₂_inj f_XII hf_inl
        hf_inr_one
      hf_inr_two hf_img_col₁ hf_img_col₂ hf_mem_S₁_of_compl
  have hι_XII_emb : IsClosedEmbedding ι_XII := hι_XII_cont.isClosedEmbedding hι_XII_inj
  have hι_XII_range : range ι_XII = univ \ (D₁ ∪ D₂) :=
    (image_eq_range f_XII P₁_XII).symm.trans hf_img_P₁_compl
  let e_P₁ : ↥P₁_XII ≃ₜ ↥(univ \ (D₁ ∪ D₂) : Set S) :=
    hι_XII_emb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hι_XII_range)
  obtain ⟨hXD_surf, _, hXD_bd⟩ :=
    compl_two_open_isSurface hS hD₁_open hD₂_open hOArc_D₁ hOArc_D₂ hout_D₁ hout_D₂ hd_D
  have hP₁_surf : IsSurface ↥P₁_XII := isSurface_of_homeo e_P₁.symm hXD_surf
  let e_pinch := pinchCylHomeo hδ₁_cont hδ₂_cont hδ₁_bd hδ₂_bd
  let j_P₂ : ClosedCylinder → S' := fun p => GluedSpace.inr hb_inj (e_pinch p).1
  have hj_P₂_emb : IsClosedEmbedding j_P₂ :=
    hinr_emb.comp (hA_mid_cl.isClosedEmbedding_subtypeVal.comp e_pinch.isClosedEmbedding)
  have hj_P₂_range : range j_P₂ = P₂_XII := by
    exact pinched_cylinder_maps_onto_middle_strip (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open
      hd g₁ g₂ hb_inj δ₁ δ₂ e_pinch
  let e_P₂ : ClosedCylinder ≃ₜ ↥P₂_XII :=
    hj_P₂_emb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hj_P₂_range)
  have hP₂_surf : IsSurface ↥P₂_XII := isSurface_of_homeo e_P₂ hCyl_surf
  have m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have hj_P₂_cuff₁ : j_P₂ '' range (cylEnd 1 m1) = C_XII 0 := by
    exact pinched_cylinder_maps_lower_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd g₁
      g₂ hb_inj δ₁ hδ₁_cont hδ₁_bd δ₂ hδ₂_cont hδ₂_bd C_XII rfl e_pinch rfl m1
  have hj_P₂_cuff₂ : j_P₂ '' range (cylEnd 2 m2) = C_XII 1 := by
    exact pinched_cylinder_maps_upper_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd g₁
      g₂ hb_inj δ₁ hδ₁_cont hδ₁_bd δ₂ hδ₂_cont hδ₂_bd C_XII rfl e_pinch rfl m2
  have hiUnion2 := @union_two_indexed_sets
  have hbd_P₂ : Subtype.val '' bd ↥P₂_XII = ⋃ i : Fin 2, C_XII i := by
    rw [hiUnion2 C_XII, ← hj_P₂_cuff₁, ← hj_P₂_cuff₂, ← image_union, ← bd_cylinder,
      ← image_bd_homeomorph e_P₂, image_image]
    rfl
  have hC0_sub_P₁ : C_XII 0 ⊆ P₁_XII := by
    rintro _ ⟨q, hq, rfl⟩
    exact .inl (.inr ⟨q, le_of_eq hq, rfl⟩)
  have hC1_sub_P₁ : C_XII 1 ⊆ P₁_XII := by
    rintro _ ⟨q, hq, rfl⟩
    exact .inr ⟨q, le_of_eq hq.symm, rfl⟩
  have hP12_union : P₁_XII ∪ P₂_XII = univ := by
    exact handle_pieces_cover_glued_surface (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd g₁
      g₂ hb_inj hU_eq δ₁ δ₂
  have hP12_inter : P₁_XII ∩ P₂_XII = ⋃ i : Fin 2, C_XII i := by
    exact handle_pieces_meet_at_pinched_cuffs (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj δ₁ hδ₁_bd δ₂ hδ₂_bd hiUnion2 hC0_sub_P₁ hC1_sub_P₁
  have hf_injOn_P₁ : Set.InjOn f_XII P₁_XII :=
    fun x₁ hx₁ x₂ hx₂ h => congrArg Subtype.val (@hι_XII_inj ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h)
  have hbd_P₁ : Subtype.val '' bd ↥P₁_XII = ⋃ i : Fin 2, C_XII i := by
    exact handle_complement_boundary_is_cuff_union (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj D₁ hD₁_open hD₁_sub D₂ hD₂_open hD₂_sub hcl_D₁_sub hcl_D₂_sub
      P₁_XII C_XII f_XII hf_img_C0 hf_img_C1 e_P₁ (fun _ => rfl) hXD_bd hiUnion2 hC0_sub_P₁
        hC1_sub_P₁
      hf_injOn_P₁
  have hhandle_split : GM12.IsCappedSplit C_XII P₁_XII P₂_XII ι_XII ![D₁, D₂] := by
    exact pinched_handle_forms_capped_split (S := S) hS (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj hS' δ₁ D₁ hδ₁_bd δ₂ D₂ hδ₂_bd hd_D hD₁_disc hD₂_disc P₁_XII P₂_XII f_XII
      hf_img_C0 hf_img_C1 hι_XII_emb hι_XII_range hP₁_surf j_P₂ hj_P₂_emb hP₂_surf m1 m2
      hj_P₂_cuff₁ hj_P₂_cuff₂ hiUnion2 hbd_P₂ hC0_sub_P₁ hC1_sub_P₁ hP12_union hP12_inter hbd_P₁
  have hcomplement_collar : P₁_XII \ S₁ ⊆ CollarInt := by
    exact handle_complement_off_original_surface_is_unmarked (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂)
      hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj (W_pts := W_pts) δ₁ hδ₁_bd hδ₁_zero δ₂ hδ₂_bd hδ₂_zero
  have hmarks_lower : GluedSpace.inr hb_inj '' (cylEnd 1 m1 '' W_pts) ⊆ C_XII 0 := by
    exact marked_lower_cylinder_end_on_pinched_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj (W_pts := W_pts) δ₁ hδ₁_zero C_XII rfl m1
  have hunmarked_lower : C_XII 0 \ (GluedSpace.inr hb_inj '' (cylEnd 1 m1 '' W_pts)) ⊆ CollarInt
    := by
    exact unmarked_lower_pinched_cuff_inside_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj (W_pts := W_pts) δ₁ hδ₁_bd hδ₁_zero C_XII rfl m1
  have hmarks_upper : GluedSpace.inr hb_inj '' (cylEnd 2 m2 '' W_pts) ⊆ C_XII 1 := by
    exact marked_upper_cylinder_end_on_pinched_cuff (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj (W_pts := W_pts) δ₂ hδ₂_zero C_XII rfl m2
  have hunmarked_upper : C_XII 1 \ (GluedSpace.inr hb_inj '' (cylEnd 2 m2 '' W_pts)) ⊆ CollarInt
    := by
    exact unmarked_upper_pinched_cuff_inside_collar (S := S) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ₁_open
      hΛ₂_open hd g₁ g₂ hb_inj (W_pts := W_pts) δ₂ hδ₂_bd hδ₂_zero C_XII rfl m2
  exact ⟨C_XII, P₁_XII, P₂_XII, ι_XII, ![D₁, D₂], f_XII,
    ⟨hhandle_split, inferInstance, ⟨e_P₂.symm.trans closedCylinderHomeoAnnulus⟩⟩,
    fun x hx => .inl (.inl hx),
    fun y => rfl, fun _ => rfl, hι_XII_emb, hD₁_sub, hD₂_sub, hcl_D₁_sub, hcl_D₂_sub,
    hcomplement_collar, hmarks_lower, hunmarked_lower, hmarks_upper, hunmarked_upper,
    fun z hz => marked_radial_line_in_pinched_strip (GluedSpace.inr hb_inj) hδ₁_zero hδ₂_zero hz,
    hf_img_C0, hf_img_C1, hf_img_P₁, hf_mem_S₁_of_compl⟩


/-! ## 3. Proof of Graph Minors XV, (3.5) -/

/-- Any rigid drawing `H'` with `H'.U.Nonempty` on a connected closed surface `S'` is 2-cell. -/
theorem isTwoCell_of_isRigid {S' : Type w} [TopologicalSpace S'] [T2Space S']
    (hS' : IsClosedSurface S') [hConn' : ConnectedSpace S']
    {H' : Drawing S'} (hRigid : IsRigid H') (hU_ne : H'.U.Nonempty) :
    (PaintingOrDrawing.drawing H').IsTwoCell := by
  have : LocallyConnectedSpace S' := IsClosedSurface.locallyConnectedSpace hS'
  refine ⟨hConn', fun r hr => ?_⟩
  have h_od := open_disc S' r hS' hConn'
    ⟨GM11.region_nonempty hr, GM11.region_isPreconnected hr⟩ (GM11.region_isOpen hr)
    (fun F hFr hF => by
      have hFU_emp : F ∩ H'.U = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxU⟩ => GM11.region_subset hr (hFr hxF) hxU
      have hFU : F ∩ H'.U ⊆ H'.V := by rw [hFU_emp]; exact empty_subset _
      have hFV_emp : F ∩ H'.V = ∅ :=
        eq_empty_of_subset (inter_subset_inter_right F H'.V_subset_U) hFU_emp
      have hFV_card : (F ∩ H'.V).ncard ≤ 2 := by rw [hFV_emp, Set.ncard_empty]; omega
      obtain ⟨Δ, hΔ, hbd_Δ, hDial_cases⟩ := hRigid F hF hFU hFV_card
      have hΔ_disj : Disjoint Δ H'.U := by
        rcases hDial_cases with h1 | ⟨u₁, u₂, hu12, hJV_eq, _⟩
        · exact disjoint_left.mpr fun x hxΔ hxU =>
            (eq_empty_iff_forall_notMem.mp hFU_emp x) ⟨h1 ⟨hxΔ, hxU⟩, hxU⟩
        · exfalso
          have h1 : (F ∩ H'.V).ncard = 0 := by rw [hFV_emp, Set.ncard_empty]
          have h2 : (F ∩ H'.V).ncard = 2 := by rw [hJV_eq, Set.ncard_pair hu12]
          omega
      obtain ⟨φ⟩ := hF
      have hpF : (φ 1).1 ∈ F := (φ 1).2
      have hpΔ : (φ 1).1 ∈ Δ := by
        have hp_bd : (φ 1).1 ∈ subBd Δ := hbd_Δ ▸ hpF
        exact hΔ.isClosed.closure_subset hp_bd.1
      have hΔ_r : Δ ⊆ r :=
        GM11.subset_region hr hΔ.isPathConnected.isConnected.isPreconnected hΔ_disj hpΔ (hFr hpF)
      exact ⟨Δ, hΔ_r, hΔ, (GM14.IsClosedDisc.subBd_eq_discBd hS' hΔ).symm.trans hbd_Δ⟩)
  rcases h_od with ⟨_, hr_univ⟩ | hr_disc
  · exfalso
    obtain ⟨x, hx⟩ := hU_ne
    exact GM11.region_subset hr (hr_univ ▸ mem_univ x) hx
  · exact hr_disc

/-- Lifting `exists_striped_disc_in_closedCylinder` to `S₂ = range (GluedSpace.inr hb_inj)` when a
closed subset `K_sub ⊆ S₂` avoids at least one radial line `L i₀`. -/
theorem exists_striped_disc_in_S₂ {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Λ₁ Λ₂ : Set S}
    (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↥(subBd Λ₁)) (g₂ : Circle ≃ₜ ↥(subBd Λ₂))
    (hb_inj : Function.Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    {φ : ℕ} {w : Fin φ → Circle} (hw_inj : Function.Injective w)
    {a' b' : Fin φ → GluedSpace hb_inj}
    (ha' : ∀ i, a' i = GluedSpace.inr hb_inj (cylEnd 1 (by norm_num) (w i)))
    (hb' : ∀ i, b' i = GluedSpace.inr hb_inj (cylEnd 2 (by norm_num) (w i)))
    {L : Fin φ → Set (GluedSpace hb_inj)}
    (hL : ∀ i, L i = GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i})
    {H_path : Fin φ → Drawing (GluedSpace hb_inj)}
    (hH_path_U : ∀ i, (H_path i).U = L i)
    {H' : Drawing (GluedSpace hb_inj)}
    (hS₂_U : range (GluedSpace.inr hb_inj) ∩ H'.U ⊆
      (range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj)) ∪ ⋃ i : Fin φ, L i)
    {K_sub : Set (GluedSpace hb_inj)} (hK_sub_cl : IsClosed K_sub)
    (hK_sub_S₂ : K_sub ⊆ range (GluedSpace.inr hb_inj))
    (i₀ : Fin φ) (hK_sub_disj : Disjoint K_sub (L i₀)) :
    let S₁ : Set (GluedSpace hb_inj) := range (GluedSpace.inl hb_inj)
    let S₂ : Set (GluedSpace hb_inj) := range (GluedSpace.inr hb_inj)
    ∃ D : Set (GluedSpace hb_inj),
      D ⊆ S₂ ∧
      IsClosedDisc D ∧
      K_sub ⊆ D ∧
      D ∩ (S₁ ∩ S₂) ⊆ discBd D ∧
      D ∩ H'.U ⊆ (D ∩ (S₁ ∩ S₂)) ∪ ⋃ j : {i : Fin φ // i ≠ i₀}, (H_path j.1).U ∧
      ∀ j : {i : Fin φ // i ≠ i₀},
        (H_path j.1).U ⊆ D ∧
        (H_path j.1).U ∩ discBd D = {a' j.1, b' j.1} := by
  have : CompactSpace S := hS.1
  have hX_closed : IsClosed (univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open)
  have : CompactSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isCompact_iff_compactSpace.mp hX_closed.isCompact
  have : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  have hb_cont := continuous_handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have : T2Space (GluedSpace hb_inj) :=
    GluedSpace.t2Space (isClosed_bd ↥ClosedCylinder) hb_cont hb_inj
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  obtain ⟨θ₀, _, hθ₀⟩ : w i₀ ∈ Circle.exp '' Icc 0 (0 + 2 * Real.pi) :=
    circle_exp_surjOn_Icc 0 ▸ mem_univ (w i₀)
  let K_all : Set ClosedCylinder :=
    (GluedSpace.inr hb_inj ⁻¹' K_sub) ∪
      ⋃ j : {i : Fin φ // i ≠ i₀}, {p : ClosedCylinder | p.1.2 = w j.1}
  have hK_all_cl : IsClosed K_all := by
    refine (hK_sub_cl.preimage (GluedSpace.continuous_inr hb_inj)).union ?_
    exact isClosed_iUnion_of_finite fun j =>
      isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hK_all_disj : Disjoint K_all {p : ClosedCylinder | p.1.2 = Circle.exp θ₀} := by
    rw [hθ₀]
    refine Set.disjoint_left.mpr ?_
    rintro p (hp_sub | hp_rad) hp_i₀
    · have hp_L : GluedSpace.inr hb_inj p ∈ L i₀ := by
        rw [hL i₀]
        exact ⟨p, hp_i₀, rfl⟩
      exact Set.disjoint_left.mp hK_sub_disj hp_sub hp_L
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp_rad
      exact j.2 (hw_inj (hj.symm.trans hp_i₀))
  obtain ⟨D_cyl, ⟨ψ_cyl⟩, hK_sub_D_cyl, hD_cyl_disj, hbd_sub_D_cyl, hrad_D_cyl⟩ :=
    exists_striped_disc_in_closedCylinder θ₀ hK_all_cl hK_all_disj
  let D : Set (GluedSpace hb_inj) := GluedSpace.inr hb_inj '' D_cyl
  have hD_S₂ : D ⊆ range (GluedSpace.inr hb_inj) := image_subset_range _ _
  let f_D : ↥D_cyl → GluedSpace hb_inj := fun p => GluedSpace.inr hb_inj p.1
  have hf_D_emb : IsEmbedding f_D := hinr_emb.isEmbedding.comp IsEmbedding.subtypeVal
  have hf_D_range : range f_D = D := by
    ext x
    exact ⟨by rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩,
      by rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩⟩
  let e_D : ↥D_cyl ≃ₜ ↥D := hf_D_emb.toHomeomorph.trans (Homeomorph.setCongr hf_D_range)
  have hD_disc : IsClosedDisc D := ⟨ψ_cyl.trans e_D⟩
  have hdiscBd_D : discBd D = GluedSpace.inr hb_inj '' discBd D_cyl := by
    change Subtype.val '' bd ↥D = GluedSpace.inr hb_inj '' (Subtype.val '' bd ↥D_cyl)
    rw [← image_bd_homeomorph e_D, image_image, image_image]
    rfl
  refine ⟨D, hD_S₂, hD_disc, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := hK_sub_S₂ hx
    exact ⟨p, hK_sub_D_cyl (.inl hx), rfl⟩
  · rintro _ ⟨⟨p, hpD, rfl⟩, ⟨y, hy_eq⟩, _⟩
    obtain ⟨hp_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
    rw [hdiscBd_D]
    exact ⟨p, hbd_sub_D_cyl ⟨hpD, hp_bd⟩, rfl⟩
  · rintro x ⟨hxD, hxU⟩
    rcases hS₂_U ⟨hD_S₂ hxD, hxU⟩ with hx12 | hxL
    · exact .inl ⟨hxD, hx12⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxL
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨p, hpD, rfl⟩ := hxD
        rw [hL i] at hxi
        obtain ⟨q, hq_w, hq_eq⟩ := hxi
        have hpq := GluedSpace.inr_injective hb_inj hq_eq
        subst hpq
        exact (Set.disjoint_left.mp hD_cyl_disj hpD (hθ₀.symm ▸ hq_w)).elim
      · right
        refine mem_iUnion.mpr ⟨⟨i, hi⟩, ?_⟩
        rwa [hH_path_U i]
  · intro j
    have hsub_j : {p : ClosedCylinder | p.1.2 = w j.1} ⊆ K_all :=
      fun p hp => .inr (mem_iUnion.mpr ⟨j, hp⟩)
    obtain ⟨hj_sub, hj_bd⟩ := hrad_D_cyl (w j.1) hsub_j
    rw [hH_path_U j.1, hL j.1, hdiscBd_D, ha' j.1, hb' j.1]
    refine ⟨image_mono hj_sub, ?_⟩
    rw [← Set.image_inter (GluedSpace.inr_injective hb_inj), hj_bd, image_pair]

/-- Truncation of a respectful tangle in a drawing (Graph Minors XV, Section 3, page 120). -/
theorem isRespectfulDrawingTangle_truncation {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {θ θ₁ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsRespectfulDrawingTangle H θ₁ (GM10.truncation T θ₁) := by
  exact GM12.IsRespectfulDrawingTangle.truncation hResp h1 hle

/-- A path on the interface and a chord meeting the drawing only at the ends of the path
avoid one of three or more disjoint stripes if the path meets at most two stripe ends. -/
theorem exists_stripe_avoiding_path_and_chord {X : Type*} [TopologicalSpace X] [T2Space X]
    {φ : ℕ} (hφ : 3 ≤ φ) {H P : Drawing X} {S₁ S₂ F : Set X} {u v : X}
    {a b : Fin φ → X} {L : Fin φ → Set X} (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂)
    (hL_ends : ∀ i, L i ∩ S₁ = {a i, b i})
    (hL_disj : Pairwise fun i j => Disjoint (L i) (L j))
    (hL_verts : ∀ i, a i ∈ H.V ∧ b i ∈ H.V) (hL_sub : ∀ i, L i ⊆ H.U)
    (hF_line : IsLineWithEnds F u v) (hF_U : F ∩ H.U ⊆ {u, v})
    (hP_sub : P.IsSubdrawing (H.interSet (S₁ ∩ S₂))) (hP_path : P.IsPathBetween u v)
    (hP_ends : (P.V ∩ (range a ∪ range b)).ncard ≤ 2) :
    P.IsSubdrawing H ∧ P.U ⊆ S₁ ∩ S₂ ∧ IsLineWithEnds P.U u v ∧ IsClosed (P.U ∪ F) ∧
      ∃ i₀ : Fin φ, Disjoint (P.U ∪ F) (L i₀) := by
  have hP' : P.IsSubdrawing H := by
    refine ⟨hP_sub.1.trans ?_, hP_sub.2.trans ?_⟩
    · rw [interSet_V_of_isClosed H (hS₁.inter hS₂)]
      exact inter_subset_left
    · rw [interSet_E H (S₁ ∩ S₂)]
      exact fun _ he => he.1
  have hPU : P.U ⊆ S₁ ∩ S₂ := by
    refine (isSubdrawing_U_subset hP_sub).trans ?_
    rw [(H.interSet (S₁ ∩ S₂)).U_eq, interSet_V_of_isClosed H (hS₁.inter hS₂), interSet_E]
    exact union_subset inter_subset_right
      (iUnion₂_subset fun e he => (hS₁.inter hS₂).closure_subset_iff.mpr he.2)
  have huv : u ≠ v := by
    obtain ⟨ψ, hψ₀, hψ₁⟩ := hF_line
    exact fun heq => zero_ne_one (ψ.injective (Subtype.ext (hψ₀.trans (heq.trans hψ₁.symm))))
  have hP_line := GM14.isLine_of_isPathBetween hP_path huv
  refine ⟨hP', hPU, hP_line, P.isClosed_U.union hF_line.isCompact.isClosed, ?_⟩
  have hpair_disj : Pairwise (fun i j => Disjoint ({a i, b i} : Set X) {a j, b j}) := by
    intro i j hij
    refine (hL_disj hij).mono ?_ ?_
    · rw [← hL_ends i]
      exact inter_subset_left
    · rw [← hL_ends j]
      exact inter_subset_left
  obtain ⟨i, hi⟩ := exists_disjoint_of_three_le hφ
    (P.finite_V.subset inter_subset_left) hP_ends hpair_disj (fun i =>
      inter_subset_inter_right _ (by
        rintro _ (rfl | rfl)
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, rfl⟩))
  have hPV : P.U ∩ H.V = P.V := isSubdrawing_U_inter_V hP'
  have hpath : Disjoint P.U (L i) := disjoint_left.mpr fun x hxP hxL => by
    have hx : x ∈ ({a i, b i} : Set X) := hL_ends i ▸ ⟨hxL, (hPU hxP).1⟩
    rcases hx with rfl | rfl
    · exact disjoint_left.mp hi (hPV ▸ ⟨hxP, (hL_verts i).1⟩) (Or.inl rfl)
    · exact disjoint_left.mp hi (hPV ▸ ⟨hxP, (hL_verts i).2⟩) (Or.inr rfl)
  obtain ⟨hu, hv⟩ := hP_line.ends_mem
  have hchord : Disjoint F (L i) := disjoint_left.mpr fun x hxF hxL => by
    rcases hF_U ⟨hxF, hL_sub i hxL⟩ with rfl | rfl
    · exact disjoint_left.mp hpath hu hxL
    · exact disjoint_left.mp hpath hv hxL
  exact ⟨i, hpath.union_left hchord⟩

/-- The path and chord lie in the striped disc, the path on its boundary. Reindexing the retained
stripes preserves the covering of the drawing inside the disc. -/
theorem reindex_striped_disc {X : Type*} [TopologicalSpace X] {φ n : ℕ} {i₀ : Fin φ}
    {P H : Drawing X} {F D S₁ S₂ : Set X} (paths : Fin φ → Drawing X)
    (e : Fin n ≃ {i : Fin φ // i ≠ i₀})
    (hPU : P.U ⊆ S₁ ∩ S₂) (hPF : P.U ∪ F ⊆ D) (hbd : D ∩ (S₁ ∩ S₂) ⊆ discBd D)
    (hcover : D ∩ H.U ⊆ (D ∩ (S₁ ∩ S₂)) ∪ ⋃ j : {i : Fin φ // i ≠ i₀}, (paths j.1).U) :
    P.U ⊆ D ∧ F ⊆ D ∧ P.U ⊆ discBd D ∧
      D ∩ H.U ⊆ discBd D ∪ ⋃ k, (paths (e k).1).U := by
  have hPD : P.U ⊆ D := subset_union_left.trans hPF
  refine ⟨hPD, subset_union_right.trans hPF, (subset_inter hPD hPU).trans hbd, ?_⟩
  refine hcover.trans (union_subset (hbd.trans subset_union_left) ?_)
  intro x hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  exact Or.inr (mem_iUnion.mpr ⟨e.symm j, by simpa using hxj⟩)

/-- Truncation of a controlling tangle (Graph Minors XV, Section 3, page 120). -/
theorem isControllingTangle_truncation {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ₁ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsControllingTangle G H η θ_star θ T_star T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsControllingTangle G H η θ_star θ₁ T_star (GM10.truncation T θ₁) :=
  IsControllingTangle.truncation h h1 hle

private theorem original_region_cannot_meet_both_handle_cuffs
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁ : Λ₁ ∈ H.R)
    (hΛ₂ : Λ₂ ∈ H.R)
    (hOArc₁ : IsOArc (subBd Λ₁))
    (hOArc₂ : IsOArc (subBd Λ₂))
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty → Disjoint (closure r)
      (H.V ∩ subBd Λ₂))
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hSubBd₁_sub_U : subBd Λ₁ ⊆ H.U)
    (hSubBd₂_sub_U : subBd Λ₂ ⊆ H.U)
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (hS₁_cl : IsClosed (range (GluedSpace.inl hb_inj)))
    (C_unp : Fin 2 → Set (GluedSpace hb_inj))
    (hC_unp_0 : C_unp 0 = GluedSpace.inr hb_inj '' range (cylEnd 1
      (by norm_num)))
    (hC_unp_1 : C_unp 1 = GluedSpace.inr hb_inj '' range (cylEnd 2
      (by norm_num)))
    (g_unp : S → (GluedSpace hb_inj))
    (f_unp : (GluedSpace hb_inj) → S)
    (hf_unp_cont : ContinuousOn f_unp (range (GluedSpace.inl hb_inj)))
    (hfg_unp_inv : LeftInvOn f_unp g_unp (univ \ (Λ₁ ∪ Λ₂)))
    (hgf_unp_inv : LeftInvOn g_unp f_unp (range (GluedSpace.inl hb_inj)))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_U : H₁.U = g_unp '' H.U)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hinr_cylEnd_one : ∀ (z : Circle), GluedSpace.inr hb_inj (cylEnd 1 m1 z) = g_unp ↑(g₁ z))
    (hinr_cylEnd_two : ∀ (z : Circle), GluedSpace.inr hb_inj (cylEnd 2 m2 z) = g_unp ↑(g₂ z)) :
    ∀ r ∈ H'.R, r ⊆ (range (GluedSpace.inl hb_inj)) → ∀ (i j : Fin 2), (closure r ∩ C_unp
      i).Nonempty → (closure r ∩ C_unp j).Nonempty → i = j := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro r hr hr_S₁ i j hi hj
  by_contra hij
  have hne_r := GM11.region_nonempty hr
  obtain ⟨x₀, hx₀⟩ := hne_r
  have hfr_disj : Disjoint (f_unp '' r) H.U := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hxr, rfl⟩ hyU
    have hx_S₁ : x ∈ S₁ := hr_S₁ hxr
    have hx_H₁U : x ∈ H₁.U := by
      rw [← hgf_unp_inv hx_S₁, hH₁_U]
      exact mem_image_of_mem g_unp hyU
    exact GM11.region_subset hr hxr (by rw [hH'_U]; exact .inl hx_H₁U)
  have hx₀_not_U : f_unp x₀ ∉ H.U :=
    Set.disjoint_left.mp hfr_disj (mem_image_of_mem f_unp hx₀)
  obtain ⟨r₀, hr₀, hx₀_r₀⟩ := GM11.exists_region_of_notMem hx₀_not_U
  have hfr_conn : IsPreconnected (f_unp '' r) :=
    (GM11.region_isPreconnected hr).image f_unp (hf_unp_cont.mono hr_S₁)
  have hfr_sub : f_unp '' r ⊆ r₀ :=
    GM11.subset_region hr₀ hfr_conn hfr_disj (mem_image_of_mem f_unp hx₀) hx₀_r₀
  have hcl_r_S₁ : closure r ⊆ S₁ := hS₁_cl.closure_subset_iff.mpr hr_S₁
  have hcl_sub : f_unp '' closure r ⊆ closure r₀ :=
    ((hf_unp_cont.mono hcl_r_S₁).image_closure).trans (closure_mono hfr_sub)
  have hC0_bd : ∀ w ∈ closure r ∩ C_unp 0, f_unp w ∈ closure r₀ ∩ subBd Λ₁ := by
    rintro w ⟨hw_cl, hw_C0⟩
    rw [hC_unp_0] at hw_C0
    obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hw_C0
    have hfg : f_unp (GluedSpace.inr hb_inj (cylEnd 1 m1 z)) = (g₁ z).1 := by
      rw [hinr_cylEnd_one z, hfg_unp_inv (hHU (hSubBd₁_sub_U (g₁ z).2))]
    exact ⟨hcl_sub (mem_image_of_mem f_unp hw_cl), hfg ▸ (g₁ z).2⟩
  have hC1_bd : ∀ w ∈ closure r ∩ C_unp 1, f_unp w ∈ closure r₀ ∩ subBd Λ₂ := by
    rintro w ⟨hw_cl, hw_C1⟩
    rw [hC_unp_1] at hw_C1
    obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hw_C1
    have hfg : f_unp (GluedSpace.inr hb_inj (cylEnd 2 m2 z)) = (g₂ z).1 := by
      rw [hinr_cylEnd_two z, hfg_unp_inv (hHU (hSubBd₂_sub_U (g₂ z).2))]
    exact ⟨hcl_sub (mem_image_of_mem f_unp hw_cl), hfg ▸ (g₂ z).2⟩
  have h01 : (closure r ∩ C_unp 0).Nonempty ∧ (closure r ∩ C_unp 1).Nonempty := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨hi, hj⟩
    · exact ⟨hj, hi⟩
    · exact (hij rfl).elim
  obtain ⟨w₀, hw₀⟩ := h01.1
  obtain ⟨w₁, hw₁⟩ := h01.2
  have hne1 : (closure r₀ ∩ (H.V ∩ subBd Λ₁)).Nonempty :=
    closure_region_inter_V_subBd_nonempty_of_inter_subBd_nonempty hS hr₀ hΛ₁ hOArc₁
      ⟨f_unp w₀, hC0_bd w₀ hw₀⟩
  have hne2 : (closure r₀ ∩ (H.V ∩ subBd Λ₂)).Nonempty :=
    closure_region_inter_V_subBd_nonempty_of_inter_subBd_nonempty hS hr₀ hΛ₂ hOArc₂
      ⟨f_unp w₁, hC1_bd w₁ hw₁⟩
  obtain ⟨z₂, hz₂_cl, hz₂_V⟩ := hne2
  exact Set.disjoint_left.mp (hNo_common_region r₀ hr₀ hne1) hz₂_cl hz₂_V

private theorem original_surface_dial
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (θ : ℕ)
    (φ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hΛ₁ : Λ₁ ∈ H.R)
    (hΛ₂ : Λ₂ ∈ H.R)
    (hOArc₁ : IsOArc (subBd Λ₁))
    (hOArc₂ : IsOArc (subBd Λ₂))
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty → Disjoint (closure r)
      (H.V ∩ subBd Λ₂))
    (hφ : 3 ≤ φ)
    (hab_mem : ∀ (i : Fin φ), a i ∈ H.V ∩ subBd Λ₁ ∧ b i ∈ H.V ∩ subBd Λ₂)
    (hFree_a : IsFreeSet H.toHypergraph T θ (range a))
    (hFree_b : IsFreeSet H.toHypergraph T θ (range b))
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRigid_H : IsRigid H)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (ha_inj : Injective a)
    (hb_inj_fn : Injective b)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (a' b' : Fin φ → GluedSpace hb_inj)
    (hι_unp_X : ι_unp '' Subtype.val ⁻¹' (range a' ∪ range b') = range a ∪ range b) :
    ∀ (F : Set S), IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 → ∃ Δ, IsDial H F Δ ∧ (ι_unp ''
      Subtype.val ⁻¹' (range a' ∪ range b') ∩ Δ).ncard ≤ (F ∩ H.V).ncard := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let X_unp := range a' ∪ range b'
  intro F hF hFU hFV
  rw [hι_unp_X]
  have ha_sub : range a ⊆ H.V ∩ subBd Λ₁ := by rintro _ ⟨i, rfl⟩; exact (hab_mem i).1
  have hb_sub : range b ⊆ H.V ∩ subBd Λ₂ := by rintro _ ⟨i, rfl⟩; exact (hab_mem i).2
  have ha_card : 2 < (range a).ncard := by
    rw [Set.ncard_range_of_injective ha_inj, Nat.card_fin]; omega
  have hb_card : 2 < (range b).ncard := by
    rw [Set.ncard_range_of_injective hb_inj_fn, Nat.card_fin]; omega
  exact theorem_3_5_claim_1 hS hRigid_H hT hθ hΛ₁ hΛ₂ hOArc₁ hOArc₂ hNo_common_region
    ha_sub hb_sub ha_card hb_card hFree_a hFree_b hF hFU hFV

private theorem cylinder_dial_of_normal_closed_curve
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hφ : 3 ≤ φ)
    (hS : IsClosedSurface S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hw_inj : Injective w)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    [T2Space (GluedSpace hb_inj)]
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    (H₁ : Drawing (GluedSpace hb_inj))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)))
    (hL_line : ∀ (i : Fin φ), IsLineWithEnds ((fun i => GluedSpace.inr hb_inj '' {p :
      ClosedCylinder | p.1.2 = w
      i}) i) (a' i) (b' i))
    (hL_disj : Pairwise fun i j => Disjoint ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder
      | p.1.2 = w
      i}) i) ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) j))
    (H_path : Fin φ → Drawing (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hH_path : ∀ (i : Fin φ), (H_path i).U = (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder
      | p.1.2 = w
      i}) i ∧ (H_path i).IsPathBetween (a' i) (b' i) ∧ (H_path i).IsSubdrawing H' ∧ a' i ∈ (H_path
      i).V ∧ b' i ∈ (H_path i).V)
    (hS₂_U : (range (GluedSpace.inr hb_inj)) ∩ H'.U ⊆ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder |
        p.1.2 = w i}) i) :
    ∀ F ⊆ (range (GluedSpace.inr hb_inj)), IsOArc F → F ∩ H'.U ⊆ H'.V → (F ∩ H'.V).ncard ≤ 2 → ∃ Δ
      ⊆ (range (GluedSpace.inr hb_inj)), IsDial H' F Δ := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro F hF_S₂ hF hFU hFV
  have hFU_eq : F ∩ H'.U = F ∩ H'.V :=
    Subset.antisymm (fun x hx => ⟨hx.1, hFU hx⟩) (inter_subset_inter_right _ H'.V_subset_U)
  have hF_fin : (F ∩ H'.U).Finite :=
    hFU_eq ▸ H'.finite_V.subset inter_subset_right
  have hF_card : (F ∩ H'.U).ncard ≤ 2 := hFU_eq ▸ hFV
  have hL_sub_U : ∀ i, L i ⊆ H'.U := fun i => by
    rw [hH'_U]; exact (subset_iUnion L i).trans subset_union_right
  obtain ⟨i₀, hF_disj_i₀⟩ :=
    exists_disjoint_of_three_le hφ hF_fin hF_card hL_disj
      (fun i => inter_subset_inter_right _ (hL_sub_U i))
  have hF_cl : IsClosed F := by
    obtain ⟨ψ⟩ := hF
    have hEq : F = range (fun z : Circle => (ψ z).1) := by
      ext x
      exact ⟨fun hx => ⟨ψ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (ψ z).2⟩
    rw [hEq]
    exact (isCompact_range (continuous_subtype_val.comp ψ.continuous)).isClosed
  obtain ⟨D, hD_S₂, hD_disc, hF_D, hD_bd, hD_U, hD_paths⟩ :=
    exists_striped_disc_in_S₂ hS hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj hw_inj
      ha'_inr hb'_inr (fun _ => rfl) (fun i => (hH_path i).1) hS₂_U hF_cl hF_S₂ i₀ hF_disj_i₀
  let e_sub := (Fintype.equivFin {i : Fin φ // i ≠ i₀}).symm
  have hD_U_fin : D ∩ H'.U ⊆ D ∩ (S₁ ∩ S₂) ∪ ⋃ k, (H_path (e_sub k).1).U := by
    refine hD_U.trans (union_subset_union_right _ ?_)
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨e_sub.symm j, by simpa using hxj⟩
  obtain ⟨Δ, hΔ_D, hDial⟩ :=
    dial_of_oArc_in_striped_disc hS' hD_disc hD_bd hD_U_fin
      (fun k => (hD_paths (e_sub k)).1)
      (fun k => (hH_path (e_sub k).1).1 ▸ hL_line (e_sub k).1)
      (fun k => (hH_path (e_sub k).1).2.2.1)
      (fun k => (hD_paths (e_sub k)).2)
      (fun k₁ k₂ hk => by
        change Disjoint (H_path (e_sub k₁).1).U (H_path (e_sub k₂).1).U
        rw [(hH_path (e_sub k₁).1).1, (hH_path (e_sub k₂).1).1]
        exact hL_disj (fun h => hk (e_sub.injective (Subtype.ext h))))
      hF_D hF hFU hFV
  exact ⟨Δ, hΔ_D.trans hD_S₂, hDial⟩

private theorem cylinder_disc_of_normal_chord
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hφ : 3 ≤ φ)
    (hS : IsClosedSurface S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hw_inj : Injective w)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    [T2Space (GluedSpace hb_inj)]
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    (hS₁_cl : IsClosed (range (GluedSpace.inl hb_inj)))
    (hS₂_cl : IsClosed (range (GluedSpace.inr hb_inj)))
    (C_unp : Fin 2 → Set (GluedSpace hb_inj))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (hSplit_unp : GM12.IsCappedSplit C_unp (range (GluedSpace.inl hb_inj)) (range (GluedSpace.inr
      hb_inj)) ι_unp ![Λ₁, Λ₂])
    (hS12_inter : (range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)) = C_unp 0 ∪
      C_unp 1)
    (H₁ : Drawing (GluedSpace hb_inj))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)))
    (hL_line : ∀ (i : Fin φ), IsLineWithEnds ((fun i => GluedSpace.inr hb_inj '' {p :
      ClosedCylinder | p.1.2 = w
      i}) i) (a' i) (b' i))
    (hL_disj : Pairwise fun i j => Disjoint ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder
      | p.1.2 = w
      i}) i) ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) j))
    (hL_S₁ : ∀ (i : Fin φ), (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i ∩ (range
      (GluedSpace.inl hb_inj)) = {a' i, b' i})
    (H_path : Fin φ → Drawing (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hSub_H₁ : H₁.IsSubdrawing H')
    (hH_path : ∀ (i : Fin φ), (H_path i).U = (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder
      | p.1.2 = w
      i}) i ∧ (H_path i).IsPathBetween (a' i) (b' i) ∧ (H_path i).IsSubdrawing H' ∧ a' i ∈ (H_path
      i).V ∧ b' i ∈ (H_path i).V)
    (ha'_C0 : ∀ (i : Fin φ), a' i ∈ C_unp 0)
    (hb'_C1 : ∀ (i : Fin φ), b' i ∈ C_unp 1)
    (hS₂_U : (range (GluedSpace.inr hb_inj)) ∩ H'.U ⊆ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder |
        p.1.2 = w i}) i) :
    ∀ (F : Set (GluedSpace hb_inj)) (u v : GluedSpace hb_inj) (P : Drawing (GluedSpace hb_inj)), F
      ⊆ (range (GluedSpace.inr hb_inj)) → u ∈ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∩ H'.V → v ∈ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∩ H'.V → IsLineWithEnds F u v → F ∩ H'.U ⊆ {u, v} → P.IsSubdrawing
      (H'.interSet ((range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)))) →
      P.IsPathBetween u v → (P.V ∩ (range a' ∪ range b')).ncard ≤ 2 → ∃ U₀, IsOpenDisc U₀ ∧
      IsClosedDisc (closure U₀) ∧ U₀ ⊆ (range (GluedSpace.inr hb_inj)) ∧ subBd U₀ = P.U ∪ F ∧
      Disjoint U₀ H'.U := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  let X_unp := range a' ∪ range b'
  intro F u v P hF_S₂ hu hv hF_line hF_U hP_sub_inter hP_path hPX_card
  obtain ⟨hP_sub_H', hPU_inter, hP_line, hK_sub_cl, i₀, havoid⟩ :=
    exists_stripe_avoiding_path_and_chord hφ hS₁_cl hS₂_cl hL_S₁ hL_disj
      (fun i => ⟨hSub_H₁.1 (ha'_V i), hSub_H₁.1 (hb'_V i)⟩)
      (fun i x hx => by rw [hH'_U]; exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
      hF_line hF_U hP_sub_inter hP_path hPX_card
  obtain ⟨ψ_P, -, -⟩ := hP_line
  have hPU_S₂ : P.U ⊆ S₂ := hPU_inter.trans inter_subset_right
  obtain ⟨D, hD_S₂, hD_disc, hPF_D, hD_bd, hD_U, hD_paths⟩ :=
    exists_striped_disc_in_S₂ hS hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj hw_inj
      ha'_inr hb'_inr (fun _ => rfl) (fun i => (hH_path i).1) hS₂_U hK_sub_cl
      (union_subset hPU_S₂ hF_S₂) i₀ havoid
  let e_sub := (Fintype.equivFin {i : Fin φ // i ≠ i₀}).symm
  obtain ⟨hPU_D, hF_D, hPU_bd, hD_U_fin⟩ :=
    reindex_striped_disc H_path e_sub hPU_inter hPF_D hD_bd hD_U
  have hNo_both : ∀ k, ¬ (a' (e_sub k).1 ∈ P.V ∧ b' (e_sub k).1 ∈ P.V) := by
    rintro k ⟨ha_j, hb_j⟩
    let j := e_sub k
    have hC0_cl : IsClosed (C_unp 0) := by
      obtain ⟨γ⟩ := hSplit_unp.isOArc 0
      have hEq : C_unp 0 = range (fun z : Circle => (γ z).1) := by
        ext x
        exact ⟨fun hx => ⟨γ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (γ z).2⟩
      rw [hEq]
      exact (isCompact_range (continuous_subtype_val.comp γ.continuous)).isClosed
    have hC1_cl : IsClosed (C_unp 1) := by
      obtain ⟨γ⟩ := hSplit_unp.isOArc 1
      have hEq : C_unp 1 = range (fun z : Circle => (γ z).1) := by
        ext x
        exact ⟨fun hx => ⟨γ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (γ z).2⟩
      rw [hEq]
      exact (isCompact_range (continuous_subtype_val.comp γ.continuous)).isClosed
    have hC01_disj : Disjoint (C_unp 0) (C_unp 1) :=
      hSplit_unp.disjoint 0 1 (by decide)
    have hPU_conn : IsPreconnected P.U := by
      have hEq : P.U = range (fun s : unitInterval => (ψ_P s).1) := by
        ext x
        exact ⟨fun hx => ⟨ψ_P.symm ⟨x, hx⟩, by simp⟩, fun ⟨s, hs⟩ => hs ▸ (ψ_P s).2⟩
      rw [hEq]
      exact isPreconnected_range (continuous_subtype_val.comp ψ_P.continuous)
    have hPU_sub_01 : P.U ⊆ C_unp 0 ∪ C_unp 1 := hS12_inter ▸ hPU_inter
    obtain ⟨z, hzPU, hz0, hz1⟩ :=
      hPU_conn (C_unp 0)ᶜ (C_unp 1)ᶜ hC0_cl.isOpen_compl hC1_cl.isOpen_compl
        (fun x hx => by
          rcases hPU_sub_01 hx with hx0 | hx1
          · exact .inr (Set.disjoint_left.mp hC01_disj hx0)
          · exact .inl (Set.disjoint_right.mp hC01_disj hx1))
        ⟨b' j.1, P.V_subset_U hb_j, Set.disjoint_right.mp hC01_disj (hb'_C1 j.1)⟩
        ⟨a' j.1, P.V_subset_U ha_j, Set.disjoint_left.mp hC01_disj (ha'_C0 j.1)⟩
    rcases hPU_sub_01 hzPU with hz_in0 | hz_in1
    · exact hz0 hz_in0
    · exact hz1 hz_in1
  obtain ⟨U₀, hU₀_open, hU₀_cl, hU₀_D, hU₀_bd, hU₀_disj⟩ :=
    openDisc_of_chord_in_striped_disc hS' hD_disc (Subset.refl _) hD_U_fin
      (fun k => (hH_path (e_sub k).1).1 ▸ hL_line (e_sub k).1)
      (fun k => (hH_path (e_sub k).1).2.2.1)
      (fun k => ⟨(hH_path (e_sub k).1).2.2.2.1, (hH_path (e_sub k).1).2.2.2.2⟩)
      (fun k => (hD_paths (e_sub k)).2)
      hPU_D hF_D hPU_bd hF_line hF_U hP_sub_H' hP_path hNo_both
  exact ⟨U₀, hU₀_open, hU₀_cl, hU₀_D.trans hD_S₂, hU₀_bd, hU₀_disj⟩

private theorem normal_line_between_pinched_cuffs_meets_many_vertices
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (h_lines : ∀ (F : Set S), IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) → (F ∩ subBd
      Λ₁).Nonempty → (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hK_cl : IsClosed (univ \ (Λ₁ ∪ Λ₂)))
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (f_unp : (GluedSpace hb_inj) → S)
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (hf_unp_inl : ∀ (y : ↑(univ \ (Λ₁ ∪ Λ₂))), f_unp (GluedSpace.inl hb_inj y) = ↑y)
    (hfg_unp_inv : LeftInvOn f_unp g_unp (univ \ (Λ₁ ∪ Λ₂)))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_U : H₁.U = g_unp '' H.U)
    (hH₁_V : H₁.V = g_unp '' H.V)
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hSub_H₁ : H₁.IsSubdrawing H')
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (P₁_XII : Set (GluedSpace hb_inj))
    (P₂_XII : Set (GluedSpace hb_inj))
    (ι_XII : ↑P₁_XII → S)
    (D_XII : Fin 2 → Set S)
    (f_XII : GluedSpace hb_inj → S)
    (hSplit_XII : GM12.IsHandleSplit C_XII P₁_XII P₂_XII ι_XII D_XII)
    (hf_XII_inl : ∀ (y : ↑(univ \ (Λ₁ ∪ Λ₂))), f_XII (GluedSpace.inl hb_inj y) = ↑y)
    (hι_XII_eq : ∀ (x : ↑P₁_XII), ι_XII x = f_XII ↑x)
    (hι_XII_emb : IsClosedEmbedding ι_XII)
    (hcl_D0_sub : closure (D_XII 0) ⊆ closure Λ₁)
    (hcl_D1_sub : closure (D_XII 1) ⊆ closure Λ₂)
    (hf_XII_C0 : f_XII '' C_XII 0 = subBd (D_XII 0))
    (hf_XII_C1 : f_XII '' C_XII 1 = subBd (D_XII 1))
    (hf_XII_P₁ : f_XII '' P₁_XII = closure Λ₁ \ D_XII 0 ∪ univ \ (Λ₁ ∪ Λ₂) ∪ closure Λ₂ \ D_XII 1)
    (hf_XII_mem_S₁ : ∀ x ∈ P₁_XII, f_XII x ∈ univ \ (Λ₁ ∪ Λ₂) → x ∈ range (GluedSpace.inl hb_inj))
    (hV_P₁_XII : H'.V ∩ P₁_XII = H₁.V) :
    ∀ (F : Set (GluedSpace hb_inj)), IsLine F → H'.IsNormal F → F ⊆ P₁_XII → (F ∩ C_XII
      0).Nonempty → (F ∩ C_XII 1).Nonempty → φ ≤ (F ∩ H'.V).ncard := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro F hF_line hF_norm hF_P₁ hF_C0 hF_C1
  have hf_injOn : InjOn f_XII P₁_XII := by
    intro x₁ hx₁ x₂ hx₂ h
    have hι : ι_XII ⟨x₁, hx₁⟩ = ι_XII ⟨x₂, hx₂⟩ := by
      rw [hι_XII_eq ⟨x₁, hx₁⟩, hι_XII_eq ⟨x₂, hx₂⟩]
      exact h
    exact congrArg Subtype.val (hι_XII_emb.injective hι)
  let F_S : Set S := f_XII '' F
  have hF_S_eq : F_S = ι_XII '' (Subtype.val ⁻¹' F) := by
    ext y
    exact ⟨by rintro ⟨x, hxF, rfl⟩; exact ⟨⟨x, hF_P₁ hxF⟩, hxF, hι_XII_eq ⟨x, hF_P₁ hxF⟩⟩,
      by rintro ⟨⟨x, hxP₁⟩, hxF, rfl⟩; exact ⟨x, hxF, (hι_XII_eq ⟨x, hxP₁⟩).symm⟩⟩
  have hF_S_line : IsLine F_S := by
    obtain ⟨ψ⟩ := hF_line
    let g_F : unitInterval → S := fun s => ι_XII ⟨(ψ s).1, hF_P₁ (ψ s).2⟩
    have hg_F_emb : IsEmbedding g_F :=
      hι_XII_emb.isEmbedding.comp
        ((IsEmbedding.subtypeVal.comp ψ.isEmbedding).codRestrict P₁_XII (fun s => hF_P₁ (ψ s).2))
    have hg_F_range : range g_F = F_S := by
      rw [hF_S_eq]
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨⟨(ψ s).1, hF_P₁ (ψ s).2⟩, (ψ s).2, rfl⟩
      · rintro ⟨⟨x, hxP₁⟩, hxF, rfl⟩
        exact ⟨ψ.symm ⟨x, hxF⟩, by dsimp [g_F]; rw [ψ.apply_symm_apply]⟩
    exact ⟨hg_F_emb.toHomeomorph.trans (Homeomorph.setCongr hg_F_range)⟩
  have hF_S_sub : F_S ⊆ (closure Λ₁ \ D_XII 0) ∪ K ∪ (closure Λ₂ \ D_XII 1) := by
    rw [← hf_XII_P₁]
    exact image_mono hF_P₁
  have hK₁_cl : IsClosed (closure Λ₁ \ D_XII 0) :=
    isClosed_closure.sdiff (hSplit_XII.1.isOpenDisc 0).1
  have hK₂_cl : IsClosed (closure Λ₂ \ D_XII 1) :=
    isClosed_closure.sdiff (hSplit_XII.1.isOpenDisc 1).1
  have hK₁₂_disj : Disjoint (closure Λ₁ \ D_XII 0) (closure Λ₂ \ D_XII 1) :=
    hd.mono sdiff_subset sdiff_subset
  have hF_S_K₁ : (F_S ∩ (closure Λ₁ \ D_XII 0)).Nonempty := by
    obtain ⟨x, hxF, hxC0⟩ := hF_C0
    refine ⟨f_XII x, mem_image_of_mem f_XII hxF, ?_⟩
    have hbd : f_XII x ∈ subBd (D_XII 0) := hf_XII_C0 ▸ mem_image_of_mem f_XII hxC0
    rw [subBd_eq_frontier, (hSplit_XII.1.isOpenDisc 0).1.frontier_eq] at hbd
    exact ⟨hcl_D0_sub hbd.1, hbd.2⟩
  have hF_S_K₂ : (F_S ∩ (closure Λ₂ \ D_XII 1)).Nonempty := by
    obtain ⟨x, hxF, hxC1⟩ := hF_C1
    refine ⟨f_XII x, mem_image_of_mem f_XII hxF, ?_⟩
    have hbd : f_XII x ∈ subBd (D_XII 1) := hf_XII_C1 ▸ mem_image_of_mem f_XII hxC1
    rw [subBd_eq_frontier, (hSplit_XII.1.isOpenDisc 1).1.frontier_eq] at hbd
    exact ⟨hcl_D1_sub hbd.1, hbd.2⟩
  obtain ⟨F₀, hF₀_sub_FS, hF₀_line, hF₀_K, hF₀_1, hF₀_2⟩ :=
    exists_subline_of_closed_cover hK₁_cl hK_cl hK₂_cl hK₁₂_disj hF_S_line
      hF_S_sub hF_S_K₁ hF_S_K₂
  have hK₁_inter : (closure Λ₁ \ D_XII 0) ∩ K ⊆ subBd Λ₁ := by
    rintro y ⟨⟨hy_cl, _⟩, _, hy_not⟩
    rw [subBd_eq_frontier, hΛ₁_open.frontier_eq]
    exact ⟨hy_cl, fun h => hy_not (.inl h)⟩
  have hK₂_inter : (closure Λ₂ \ D_XII 1) ∩ K ⊆ subBd Λ₂ := by
    rintro y ⟨⟨hy_cl, _⟩, _, hy_not⟩
    rw [subBd_eq_frontier, hΛ₂_open.frontier_eq]
    exact ⟨hy_cl, fun h => hy_not (.inr h)⟩
  have hF₀_bd₁ : (F₀ ∩ subBd Λ₁).Nonempty :=
    hF₀_1.mono (inter_subset_inter_right _ hK₁_inter)
  have hF₀_bd₂ : (F₀ ∩ subBd Λ₂).Nonempty :=
    hF₀_2.mono (inter_subset_inter_right _ hK₂_inter)
  have hF₀_norm : H.IsNormal F₀ := by
    intro y ⟨hyF₀, hyU⟩
    obtain ⟨x, hxF, rfl⟩ := hF₀_sub_FS hyF₀
    have hx_S₁ : x ∈ S₁ := hf_XII_mem_S₁ x (hF_P₁ hxF) (hF₀_K hyF₀)
    obtain ⟨⟨z, hzK⟩, rfl⟩ := hx_S₁
    rw [hf_XII_inl ⟨z, hzK⟩] at hyU ⊢
    have hg_z : g_unp z = GluedSpace.inl hb_inj ⟨z, hzK⟩ := hg_unp_mem z hzK
    have hx_H'U : GluedSpace.inl hb_inj ⟨z, hzK⟩ ∈ H'.U := by
      rw [hH'_U, hH₁_U, ← hg_z]
      exact .inl (mem_image_of_mem g_unp hyU)
    have hx_H'V : GluedSpace.inl hb_inj ⟨z, hzK⟩ ∈ H'.V := hF_norm ⟨hxF, hx_H'U⟩
    have hx_H₁V : GluedSpace.inl hb_inj ⟨z, hzK⟩ ∈ H₁.V :=
      hV_P₁_XII ▸ ⟨hx_H'V, hF_P₁ hxF⟩
    rw [hH₁_V] at hx_H₁V
    obtain ⟨w_v, hw_v, hw_eq⟩ := hx_H₁V
    have hzw : w_v = z := by
      have h := congrArg f_unp hw_eq
      rwa [hfg_unp_inv (hHU (H.V_subset_U hw_v)), hf_unp_inl ⟨z, hzK⟩] at h
    exact hzw ▸ hw_v
  have hφ_le_F₀ : φ ≤ (F₀ ∩ H.V).ncard :=
    h_lines F₀ hF₀_line hF₀_norm hF₀_K hF₀_bd₁ hF₀_bd₂
  have hF₀_sub_img : F₀ ∩ H.V ⊆ f_XII '' (F ∩ H'.V) := by
    intro y ⟨hyF₀, hyV⟩
    obtain ⟨x, hxF, rfl⟩ := hF₀_sub_FS hyF₀
    have hx_S₁ : x ∈ S₁ := hf_XII_mem_S₁ x (hF_P₁ hxF) (hF₀_K hyF₀)
    obtain ⟨⟨z, hzK⟩, rfl⟩ := hx_S₁
    rw [hf_XII_inl ⟨z, hzK⟩] at hyV ⊢
    have hg_z : g_unp z = GluedSpace.inl hb_inj ⟨z, hzK⟩ := hg_unp_mem z hzK
    have hx_H₁V : GluedSpace.inl hb_inj ⟨z, hzK⟩ ∈ H₁.V := by
      rw [hH₁_V, ← hg_z]
      exact mem_image_of_mem g_unp hyV
    exact ⟨GluedSpace.inl hb_inj ⟨z, hzK⟩, ⟨hxF, hSub_H₁.1 hx_H₁V⟩, hf_XII_inl ⟨z, hzK⟩⟩
  have h_img_card : (f_XII '' (F ∩ H'.V)).ncard = (F ∩ H'.V).ncard :=
    (hf_injOn.mono (inter_subset_left.trans hF_P₁)).ncard_image
  calc φ ≤ (F₀ ∩ H.V).ncard := hφ_le_F₀
    _ ≤ (f_XII '' (F ∩ H'.V)).ncard :=
      Set.ncard_le_ncard hF₀_sub_img ((H'.finite_V.subset inter_subset_right).image f_XII)
    _ = (F ∩ H'.V).ncard := h_img_card

private theorem handle_line_intersects_original_surface_only_at_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i))) :
    ∀ (i : Fin φ), (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) i ∩ (range
      (GluedSpace.inl hb_inj)) = {a' i, b' i} := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro i
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨y, hy_eq⟩⟩
    obtain ⟨hp_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
    rcases handleGlueMap_fst_eq_one_or_two ⟨p, hp_bd⟩ with hr1 | hr2
    · left
      rw [ha'_inr i]
      exact congrArg (GluedSpace.inr hb_inj) (Subtype.ext (Prod.ext hr1 hp))
    · right
      rw [hb'_inr i]
      exact congrArg (GluedSpace.inr hb_inj) (Subtype.ext (Prod.ext hr2 hp))
  · rintro (rfl | rfl)
    · exact ⟨by rw [ha'_inr i]; exact ⟨cylEnd 1 m1 (w i), rfl, rfl⟩,
        hH₁_sub_S₁ (H₁.V_subset_U (ha'_V i))⟩
    · exact ⟨by rw [hb'_inr i]; exact ⟨cylEnd 2 m2 (w i), rfl, rfl⟩,
        hH₁_sub_S₁ (H₁.V_subset_U (hb'_V i))⟩

private theorem original_drawing_meets_pinched_handle_at_marked_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (P₁_XII : Set (GluedSpace hb_inj))
    (P₂_XII : Set (GluedSpace hb_inj))
    (ι_XII : ↑P₁_XII → S)
    (D_XII : Fin 2 → Set S)
    (hSplit_XII : GM12.IsHandleSplit C_XII P₁_XII P₂_XII ι_XII D_XII)
    (hS₁_sub_P₁ : range (GluedSpace.inl hb_inj) ⊆ P₁_XII)
    (hNorm_C0_and_V : H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a')
    (hNorm_C1_and_V : H'.IsNormal (C_XII 1) ∧ H'.V ∩ C_XII 1 = range b') :
    H₁.U ∩ P₂_XII ⊆ ⋃ i, {a' i, b' i} := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro x ⟨hx1, hx2⟩
  have hx_inter : x ∈ P₁_XII ∩ P₂_XII := ⟨hS₁_sub_P₁ (hH₁_sub_S₁ hx1), hx2⟩
  rw [hSplit_XII.1.inter] at hx_inter
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx_inter
  fin_cases j
  · have hx_a' : x ∈ range a' := by
      have h : x ∈ H'.V ∩ C_XII 0 := ⟨hNorm_C0_and_V.1 ⟨hxj, by rw [hH'_U]; exact .inl hx1⟩, hxj⟩
      rwa [hNorm_C0_and_V.2] at h
    obtain ⟨i, rfl⟩ := hx_a'
    exact mem_iUnion.mpr ⟨i, .inl rfl⟩
  · have hx_b' : x ∈ range b' := by
      have h : x ∈ H'.V ∩ C_XII 1 := ⟨hNorm_C1_and_V.1 ⟨hxj, by rw [hH'_U]; exact .inl hx1⟩, hxj⟩
      rwa [hNorm_C1_and_V.2] at h
    obtain ⟨i, rfl⟩ := hx_b'
    exact mem_iUnion.mpr ⟨i, .inr rfl⟩

private theorem lower_pinched_cuff_is_normal
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (H_path : Fin φ → Drawing (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hH'_V : H'.V = H₁.V ∪ ⋃ i, (H_path i).V)
    (W_pts : Set Circle)
    (CollarInt : Set (GluedSpace hb_inj))
    (hCollar : CollarInt = GluedSpace.inr hb_inj ''
      {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hW1_sub_C0 : GluedSpace.inr hb_inj '' cylEnd 1 (by norm_num)
      '' W_pts ⊆ C_XII 0)
    (hC0_diff_W1 : C_XII 0 \ GluedSpace.inr hb_inj '' cylEnd 1
      (by norm_num) '' W_pts ⊆ GluedSpace.inr hb_inj '' {q | 1 <
      q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (hCollar_disj : Disjoint CollarInt H'.U)
    (hW1_eq_a' : GluedSpace.inr hb_inj '' cylEnd 1 m1 '' W_pts = range a') :
    H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' := by
  subst CollarInt
  let S' := GluedSpace hb_inj
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  refine glued_isNormal_and_V_inter ?_ ?_ ?_ hH'_U hH'_V
  · rintro _ ⟨i, rfl⟩; exact ha'_V i
  · refine Subset.antisymm ?_ ?_
    · intro x ⟨hx1, hxC0⟩
      by_contra hnot
      exact Set.disjoint_left.mp hCollar_disj
        (hC0_diff_W1 ⟨hxC0, hW1_eq_a'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inl hx1)
    · rintro _ ⟨i, rfl⟩
      exact ⟨H₁.V_subset_U (ha'_V i), hW1_sub_C0 (hW1_eq_a'.symm ▸ ⟨i, rfl⟩)⟩
  · intro x ⟨hxL, hxC0⟩
    by_contra hnot
    exact Set.disjoint_left.mp hCollar_disj
      (hC0_diff_W1 ⟨hxC0, hW1_eq_a'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inr hxL)

private theorem upper_pinched_cuff_is_normal
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (b' : Fin φ → (GluedSpace hb_inj))
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (H_path : Fin φ → Drawing (GluedSpace hb_inj))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hH'_V : H'.V = H₁.V ∪ ⋃ i, (H_path i).V)
    (W_pts : Set Circle)
    (CollarInt : Set (GluedSpace hb_inj))
    (hCollar : CollarInt = GluedSpace.inr hb_inj ''
      {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (hW2_sub_C1 : GluedSpace.inr hb_inj '' cylEnd 2 (by norm_num)
      '' W_pts ⊆ C_XII 1)
    (hC1_diff_W2 : C_XII 1 \ GluedSpace.inr hb_inj '' cylEnd 2
      (by norm_num) '' W_pts ⊆ GluedSpace.inr hb_inj '' {q | 1 <
      q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (hCollar_disj : Disjoint CollarInt H'.U)
    (hW2_eq_b' : GluedSpace.inr hb_inj '' cylEnd 2 m2 '' W_pts = range b') :
    H'.IsNormal (C_XII 1) ∧ H'.V ∩ C_XII 1 = range b' := by
  subst CollarInt
  let S' := GluedSpace hb_inj
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  refine glued_isNormal_and_V_inter ?_ ?_ ?_ hH'_U hH'_V
  · rintro _ ⟨i, rfl⟩; exact hb'_V i
  · refine Subset.antisymm ?_ ?_
    · intro x ⟨hx1, hxC1⟩
      by_contra hnot
      exact Set.disjoint_left.mp hCollar_disj
        (hC1_diff_W2 ⟨hxC1, hW2_eq_b'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inl hx1)
    · rintro _ ⟨i, rfl⟩
      exact ⟨H₁.V_subset_U (hb'_V i), hW2_sub_C1 (hW2_eq_b'.symm ▸ ⟨i, rfl⟩)⟩
  · intro x ⟨hxL, hxC1⟩
    by_contra hnot
    exact Set.disjoint_left.mp hCollar_disj
      (hC1_diff_W2 ⟨hxC1, hW2_eq_b'.symm ▸ hnot⟩) (by rw [hH'_U]; exact .inr hxL)

private theorem unpinched_embedding_maps_marked_nodes
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (g_unp : S → (GluedSpace hb_inj))
    (a' : Fin φ → (GluedSpace hb_inj))
    (hEnd : a' = fun i => g_unp (a i))
    (b' : Fin φ → (GluedSpace hb_inj))
    (hEnd : b' = fun i => g_unp (b i))
    (ha_K : ∀ (i : Fin φ), a i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (hb_K : ∀ (i : Fin φ), b i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (H' : Drawing (GluedSpace hb_inj))
    (hι_unp_g : ∀ y ∈ (univ \ (Λ₁ ∪ Λ₂)), ∀ (hy : g_unp y ∈ (range (GluedSpace.inl hb_inj))),
      ι_unp ⟨g_unp y, hy⟩ = y)
    (hX_unp_sub : (range a' ∪ range b') ⊆ H'.V ∩ ((range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)))) :
    ι_unp '' Subtype.val ⁻¹' (range a' ∪ range b') = range a ∪ range b := by
  subst b'
  let b' : Fin φ → GluedSpace hb_inj := fun i => g_unp (b i)
  subst a'
  let a' : Fin φ → GluedSpace hb_inj := fun i => g_unp (a i)
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let X_unp := range a' ∪ range b'
  ext y
  constructor
  · rintro ⟨⟨x, hxS₁⟩, ⟨i, rfl⟩ | ⟨i, rfl⟩, rfl⟩
    · rw [hι_unp_g (a i) (ha_K i) hxS₁]
      exact .inl ⟨i, rfl⟩
    · rw [hι_unp_g (b i) (hb_K i) hxS₁]
      exact .inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · have hxS₁ : a' i ∈ S₁ := (hX_unp_sub (.inl ⟨i, rfl⟩)).2.1
      exact ⟨⟨a' i, hxS₁⟩, .inl ⟨i, rfl⟩, hι_unp_g (a i) (ha_K i) hxS₁⟩
    · have hxS₁ : b' i ∈ S₁ := (hX_unp_sub (.inr ⟨i, rfl⟩)).2.1
      exact ⟨⟨b' i, hxS₁⟩, .inr ⟨i, rfl⟩, hι_unp_g (b i) (hb_K i) hxS₁⟩

private theorem upper_handle_end_maps_to_cylinder
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (b : Fin φ → S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hg₂_w : ∀ (i : Fin φ), ↑(g₂ (w i)) = b i)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (b' : Fin φ → (GluedSpace hb_inj))
    (hEnd : b' = fun i => g_unp (b i))
    (hb_K : ∀ (i : Fin φ), b i ∈ (univ \ (Λ₁ ∪ Λ₂))) :
    ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)) := by
  subst b'
  let b' : Fin φ → GluedSpace hb_inj := fun i => g_unp (b i)
  let b_glue := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro i
  have hbd2 : cylEnd 2 m2 (w i) ∈ bd ↥ClosedCylinder := by
    rw [bd_cylinder]; exact .inr ⟨w i, rfl⟩
  have hb2 : b_glue ⟨cylEnd 2 m2 (w i), hbd2⟩ = ⟨b i, hb_K i⟩ := by
    apply Subtype.ext
    change (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂ ⟨cylEnd 2 m2 (w i), hbd2⟩).1 = b i
    rw [handleGlueMap_cylEnd_two]
    exact hg₂_w i
  dsimp [b']
  rw [hg_unp_mem (b i) (hb_K i), ← hb2]
  exact (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd2, rfl⟩

private theorem lower_handle_end_maps_to_cylinder
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (a : Fin φ → S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hg₁_w : ∀ (i : Fin φ), ↑(g₁ (w i)) = a i)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (hEnd : a' = fun i => g_unp (a i))
    (ha_K : ∀ (i : Fin φ), a i ∈ (univ \ (Λ₁ ∪ Λ₂))) :
    ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)) := by
  subst a'
  let a' : Fin φ → GluedSpace hb_inj := fun i => g_unp (a i)
  let b_glue := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro i
  have hbd1 : cylEnd 1 m1 (w i) ∈ bd ↥ClosedCylinder := by
    rw [bd_cylinder]; exact .inl ⟨w i, rfl⟩
  have hb1 : b_glue ⟨cylEnd 1 m1 (w i), hbd1⟩ = ⟨a i, ha_K i⟩ := by
    apply Subtype.ext
    change (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂ ⟨cylEnd 1 m1 (w i), hbd1⟩).1 = a i
    rw [handleGlueMap_cylEnd_one]
    exact hg₁_w i
  dsimp [a']
  rw [hg_unp_mem (a i) (ha_K i), ← hb1]
  exact (GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd1, rfl⟩

private theorem unmarked_handle_collars_avoid_drawing
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (W_pts : Set Circle) (hW : W_pts = range w)
    (CollarInt : Set (GluedSpace hb_inj))
    (hCollar : CollarInt = GluedSpace.inr hb_inj ''
      {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}) :
    Disjoint CollarInt H'.U := by
  subst W_pts CollarInt
  let W_pts := range w
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨q, ⟨hq1, hq2, hqW⟩, rfl⟩ hxU
  rw [hH'_U] at hxU
  rcases hxU with hx1 | hxL
  · obtain ⟨y, hy_eq⟩ := hH₁_sub_S₁ hx1
    obtain ⟨hq_bd, _⟩ := (GluedSpace.inl_eq_inr hb_inj).mp hy_eq
    rcases handleGlueMap_fst_eq_one_or_two ⟨q, hq_bd⟩ with hr1 | hr2 <;> linarith
  · obtain ⟨i, ⟨p, hp, heq⟩⟩ := mem_iUnion.mp hxL
    have hpq := GluedSpace.inr_injective hb_inj heq
    subst hpq
    exact hqW ⟨i, hp.symm⟩

private theorem upper_pinch_cuff_vertices_map_to_original_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (b : Fin φ → S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (b' : Fin φ → (GluedSpace hb_inj))
    (hEnd : b' = fun i => g_unp (b i))
    (hb_K : ∀ (i : Fin φ), b i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (H' : Drawing (GluedSpace hb_inj))
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (P₁_XII : Set (GluedSpace hb_inj))
    (ι_XII : ↑P₁_XII → S)
    (hS₁_sub_P₁ : range (GluedSpace.inl hb_inj) ⊆ P₁_XII)
    (hι_XII_g : ∀ y ∈ (univ \ (Λ₁ ∪ Λ₂)), ∀ (hy : g_unp y ∈ P₁_XII), ι_XII ⟨g_unp y, hy⟩ = y)
    (hNorm_C1_and_V : H'.IsNormal (C_XII 1) ∧ H'.V ∩ C_XII 1 = range b') :
    ι_XII '' Subtype.val ⁻¹' (H'.V ∩ C_XII 1) = range b := by
  subst b'
  let b' : Fin φ → GluedSpace hb_inj := fun i => g_unp (b i)
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  rw [hNorm_C1_and_V.2]
  ext y
  constructor
  · rintro ⟨⟨x, hxP₁⟩, ⟨i, rfl⟩, rfl⟩
    rw [hι_XII_g (b i) (hb_K i) hxP₁]
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    have hxP₁ : b' i ∈ P₁_XII := hS₁_sub_P₁ (hH₁_sub_S₁ (H₁.V_subset_U (hb'_V i)))
    exact ⟨⟨b' i, hxP₁⟩, ⟨i, rfl⟩, hι_XII_g (b i) (hb_K i) hxP₁⟩

private theorem lower_pinch_cuff_vertices_map_to_original_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (a : Fin φ → S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (a' : Fin φ → (GluedSpace hb_inj))
    (hEnd : a' = fun i => g_unp (a i))
    (ha_K : ∀ (i : Fin φ), a i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (H' : Drawing (GluedSpace hb_inj))
    (C_XII : Fin 2 → Set (GluedSpace hb_inj))
    (P₁_XII : Set (GluedSpace hb_inj))
    (ι_XII : ↑P₁_XII → S)
    (hS₁_sub_P₁ : range (GluedSpace.inl hb_inj) ⊆ P₁_XII)
    (hι_XII_g : ∀ y ∈ (univ \ (Λ₁ ∪ Λ₂)), ∀ (hy : g_unp y ∈ P₁_XII), ι_XII ⟨g_unp y, hy⟩ = y)
    (hNorm_C0_and_V : H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a') :
    ι_XII '' Subtype.val ⁻¹' (H'.V ∩ C_XII 0) = range a := by
  subst a'
  let a' : Fin φ → GluedSpace hb_inj := fun i => g_unp (a i)
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  rw [hNorm_C0_and_V.2]
  ext y
  constructor
  · rintro ⟨⟨x, hxP₁⟩, ⟨i, rfl⟩, rfl⟩
    rw [hι_XII_g (a i) (ha_K i) hxP₁]
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    have hxP₁ : a' i ∈ P₁_XII := hS₁_sub_P₁ (hH₁_sub_S₁ (H₁.V_subset_U (ha'_V i)))
    exact ⟨⟨a' i, hxP₁⟩, ⟨i, rfl⟩, hι_XII_g (a i) (ha_K i) hxP₁⟩

private theorem upper_cylinder_end_equals_original_boundary_point
    {S : Type w}
    [TopologicalSpace S]
    (H : Drawing S)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hSubBd₂_sub_U : subBd Λ₂ ⊆ H.U)
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2) :
    ∀ (z : Circle), GluedSpace.inr hb_inj (cylEnd 2 m2 z) = g_unp ↑(g₂ z) := by
  let b_glue := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro z
  have hbd2 : cylEnd 2 m2 z ∈ bd ↥ClosedCylinder := by
    rw [bd_cylinder]; exact .inr ⟨z, rfl⟩
  have hzK : (g₂ z).1 ∈ K := hHU (hSubBd₂_sub_U (g₂ z).2)
  have hb2 : b_glue ⟨cylEnd 2 m2 z, hbd2⟩ = ⟨(g₂ z).1, hzK⟩ :=
    Subtype.ext (handleGlueMap_cylEnd_two hΛ₁_open hΛ₂_open hd g₁ g₂ z)
  rw [hg_unp_mem (g₂ z).1 hzK, ← hb2]
  exact ((GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd2, rfl⟩).symm

private theorem lower_cylinder_end_equals_original_boundary_point
    {S : Type w}
    [TopologicalSpace S]
    (H : Drawing S)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hSubBd₁_sub_U : subBd Λ₁ ⊆ H.U)
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) :
    ∀ (z : Circle), GluedSpace.inr hb_inj (cylEnd 1 m1 z) = g_unp ↑(g₁ z) := by
  let b_glue := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro z
  have hbd1 : cylEnd 1 m1 z ∈ bd ↥ClosedCylinder := by
    rw [bd_cylinder]; exact .inl ⟨z, rfl⟩
  have hzK : (g₁ z).1 ∈ K := hHU (hSubBd₁_sub_U (g₁ z).2)
  have hb1 : b_glue ⟨cylEnd 1 m1 z, hbd1⟩ = ⟨(g₁ z).1, hzK⟩ :=
    Subtype.ext (handleGlueMap_cylEnd_one hΛ₁_open hΛ₂_open hd g₁ g₂ z)
  rw [hg_unp_mem (g₁ z).1 hzK, ← hb1]
  exact ((GluedSpace.inl_eq_inr hb_inj).mpr ⟨hbd1, rfl⟩).symm

private theorem handle_embedding_agrees_on_original_edges
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (f_unp : (GluedSpace hb_inj) → S)
    (hfg_unp_inv : LeftInvOn f_unp g_unp (univ \ (Λ₁ ∪ Λ₂)))
    (H₁ : Drawing (GluedSpace hb_inj))
    (η₁ : SpanEmbedding H₁ G)
    (hE : H₁.E = (fun e => g_unp '' e) '' H.E)
    (hMap : ∀ e, η₁.eMap e = η.eMap (f_unp '' e))
    (H' : Drawing (GluedSpace hb_inj))
    (η' : SpanEmbedding H' G)
    (hem_H₁ : ∀ e ∈ H₁.E, η'.eMap e = η₁.eMap e) :
    ∀ e ∈ H.E, η'.eMap (g_unp '' e) = η.eMap e := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro e he
  have he₁ : g_unp '' e ∈ H₁.E := by
    rw [hE]
    exact ⟨e, he, rfl⟩
  rw [hem_H₁ (g_unp '' e) he₁]
  rw [hMap]
  have he_sub : e ⊆ K := fun x hx => hHU (he.2.1 hx).1
  rw [hfg_unp_inv.image_image' he_sub]

private theorem handle_line_meets_original_drawing_only_at_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_V : ∀ (i : Fin φ), a' i ∈ H₁.V)
    (hb'_V : ∀ (i : Fin φ), b' i ∈ H₁.V)
    (hL_S₁ : ∀ (i : Fin φ), (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i ∩ (range
      (GluedSpace.inl hb_inj)) = {a' i, b' i}) :
    ∀ (i : Fin φ), (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) i ∩ H₁.U
      = {a' i, b' i} := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro i
  refine Subset.antisymm ?_ ?_
  · exact (inter_subset_inter_right _ hH₁_sub_S₁).trans (hL_S₁ i).subset
  · rintro x (rfl | rfl)
    · have hmem : a' i ∈ L i ∩ S₁ := by rw [hL_S₁ i]; exact Or.inl rfl
      exact ⟨hmem.1, H₁.V_subset_U (ha'_V i)⟩
    · have hmem : b' i ∈ L i ∩ S₁ := by rw [hL_S₁ i]; exact Or.inr rfl
      exact ⟨hmem.1, H₁.V_subset_U (hb'_V i)⟩

private theorem original_complement_embeds_onto_first_piece
    {S : Type w}
    [TopologicalSpace S]
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (g_unp : S → (GluedSpace hb_inj))
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩) :
    g_unp '' (univ \ (Λ₁ ∪ Λ₂)) = (range (GluedSpace.inl hb_inj)) := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hg_unp_mem y hy]
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, hy, hg_unp_mem y hy⟩

private theorem unpinched_map_continuous_on_first_piece
    {S : Type w}
    [TopologicalSpace S]
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (C_unp : Fin 2 → Set (GluedSpace hb_inj))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (hSplit_unp : GM12.IsCappedSplit C_unp (range (GluedSpace.inl hb_inj)) (range (GluedSpace.inr
      hb_inj)) ι_unp ![Λ₁, Λ₂])
    (f_unp : (GluedSpace hb_inj) → S)
    (hf : ∀ x (hx : x ∈ range (GluedSpace.inl hb_inj)), f_unp x = ι_unp ⟨x, hx⟩) :
    ContinuousOn f_unp (range (GluedSpace.inl hb_inj)) := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : S₁.domRestrict f_unp = ι_unp := by
    ext ⟨x, hx⟩
    change f_unp x = ι_unp ⟨x, hx⟩
    exact hf x hx
  rw [hEq]
  exact hSplit_unp.isEmbedding.continuous

private theorem upper_pinched_marks_equal_path_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (b' : Fin φ → (GluedSpace hb_inj))
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)))
    (W_pts : Set Circle) (hW : W_pts = range w) :
    GluedSpace.inr hb_inj '' cylEnd 2 m2 '' W_pts = range b' := by
  rw [hW]
  let S' := GluedSpace hb_inj
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, hb'_inr i⟩
  · rintro ⟨i, rfl⟩
    rw [hb'_inr i]
    exact ⟨cylEnd 2 m2 (w i), ⟨w i, ⟨i, rfl⟩, rfl⟩, rfl⟩

private theorem lower_pinched_marks_equal_path_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (W_pts : Set Circle) (hW : W_pts = range w) :
    GluedSpace.inr hb_inj '' cylEnd 1 m1 '' W_pts = range a' := by
  rw [hW]
  let S' := GluedSpace hb_inj
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, ha'_inr i⟩
  · rintro ⟨i, rfl⟩
    rw [ha'_inr i]
    exact ⟨cylEnd 1 m1 (w i), ⟨w i, ⟨i, rfl⟩, rfl⟩, rfl⟩

private theorem pinched_complement_retains_original_vertices
    {S : Type w}
    [TopologicalSpace S]
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (H' : Drawing (GluedSpace hb_inj))
    (hSub_H₁ : H₁.IsSubdrawing H')
    (hV_S₁ : H'.V ∩ (range (GluedSpace.inl hb_inj)) = H₁.V)
    (W_pts : Set Circle)
    (CollarInt : Set (GluedSpace hb_inj))
    (hCollar : CollarInt = GluedSpace.inr hb_inj ''
      {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (P₁_XII : Set (GluedSpace hb_inj))
    (hS₁_sub_P₁ : range (GluedSpace.inl hb_inj) ⊆ P₁_XII)
    (hP₁_diff_S₁ : P₁_XII \ range (GluedSpace.inl hb_inj) ⊆ GluedSpace.inr hb_inj '' {q | 1 <
      q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (hCollar_disj : Disjoint CollarInt H'.U) :
    H'.V ∩ P₁_XII = H₁.V := by
  subst CollarInt
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  refine Subset.antisymm ?_ (subset_inter hSub_H₁.1
    ((H₁.V_subset_U.trans hH₁_sub_S₁).trans hS₁_sub_P₁))
  intro x ⟨hxV, hxP₁⟩
  by_cases hxS₁ : x ∈ S₁
  · exact hV_S₁ ▸ ⟨hxV, hxS₁⟩
  · exact (Set.disjoint_left.mp hCollar_disj
      (hP₁_diff_S₁ ⟨hxP₁, hxS₁⟩) (H'.V_subset_U hxV)).elim

private theorem upper_handle_parametrization_matches_path_ends
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₂ : Set S)
    (b : Fin φ → S)
    (t₁ : ℕ → ℝ)
    (f₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (t₂ : ℕ → ℝ)
    (ht₂_val : ∀ (i : ℕ) (h : i < (List.ofFn b).length), ↑(f₂ (Circle.exp (t₂ i))) = (List.ofFn
      b)[i])
    (h_circ : Circle ≃ₜ Circle)
    (hh_circ : ∀ i < φ, h_circ (Circle.exp (t₂ i)) = Circle.exp (t₁ i))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hg₂ : g₂ = h_circ.symm.trans f₂)
    (w : Fin φ → Circle) (hw : ∀ i : Fin φ, w i = Circle.exp (t₁ i.1)) :
    ∀ (i : Fin φ), ↑(g₂ (w i)) = b i := by
  intro i
  have h1 : h_circ.symm (w i) = Circle.exp (t₂ i.1) :=
    h_circ.symm_apply_eq.mpr ((hw i).trans (hh_circ i.1 i.2).symm)
  rw [hg₂]
  change (f₂ (h_circ.symm (w i))).1 = b i
  rw [h1]
  simpa using ht₂_val i.1 (by simp)

private theorem pinched_complement_retains_original_drawing
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i)
    (hU_S₁ : H'.U ∩ (range (GluedSpace.inl hb_inj)) = H₁.U)
    (W_pts : Set Circle)
    (CollarInt : Set (GluedSpace hb_inj))
    (hCollar : CollarInt = GluedSpace.inr hb_inj ''
      {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (P₁_XII : Set (GluedSpace hb_inj))
    (hS₁_sub_P₁ : range (GluedSpace.inl hb_inj) ⊆ P₁_XII)
    (hP₁_diff_S₁ : P₁_XII \ range (GluedSpace.inl hb_inj) ⊆ GluedSpace.inr hb_inj '' {q | 1 <
      q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts})
    (hCollar_disj : Disjoint CollarInt H'.U) :
    H'.U ∩ P₁_XII = H₁.U := by
  subst CollarInt
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  refine Subset.antisymm ?_ (subset_inter (by rw [hH'_U]; exact subset_union_left)
    (hH₁_sub_S₁.trans hS₁_sub_P₁))
  intro x ⟨hxU, hxP₁⟩
  by_cases hxS₁ : x ∈ S₁
  · exact hU_S₁ ▸ ⟨hxU, hxS₁⟩
  · exact (Set.disjoint_left.mp hCollar_disj (hP₁_diff_S₁ ⟨hxP₁, hxS₁⟩) hxU).elim

private theorem drawing_contains_region_boundary_of_boundary_subdrawing
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S) :
    ∀ {Λ : Set S}, (H.interSet (subBd Λ)).U = subBd Λ → subBd Λ ⊆ H.U := by
  intro Λ hU_eq
  have hcl : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
  rw [← hU_eq, (H.interSet (subBd Λ)).U_eq,
    interSet_V_of_isClosed H hcl, interSet_E]
  exact union_subset (inter_subset_left.trans H.V_subset_U)
    (iUnion₂_subset fun e he => H.closure_subset_U he.1)

private theorem original_paths_lift_to_glued_drawing
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (P : Fin φ → Graph α β)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hP_paths : ∀ (i : Fin φ), IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i)))
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (η₁ : SpanEmbedding H₁ G)
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (hG : η₁.imageGraph = η.imageGraph)
    (hA : ∀ i, η₁.vMap (a' i) = η.vMap (a i))
    (hB : ∀ i, η₁.vMap (b' i) = η.vMap (b i)) :
    ∀ (i : Fin φ), IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (a' i)) (η₁.vMap (b' i)) := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  intro i
  rw [hG, hA i, hB i]
  exact hP_paths i

private theorem distinct_handle_lines_are_disjoint
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hw_inj : Injective w)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂)) :
    Pairwise fun i j => Disjoint ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i) ((fun
      i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) j) := by
  let S' := GluedSpace hb_inj
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro i j hij
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  have hpq := GluedSpace.inr_injective hb_inj heq
  subst hpq
  exact hij (hw_inj (hp.symm.trans hq))

private theorem cylinder_drawing_is_in_cuffs_or_handle_lines
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (H₁ : Drawing (GluedSpace hb_inj))
    (hH₁_sub_S₁ : H₁.U ⊆ (range (GluedSpace.inl hb_inj)))
    (H' : Drawing (GluedSpace hb_inj))
    (hH'_U : H'.U = H₁.U ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i) :
    (range (GluedSpace.inr hb_inj)) ∩ H'.U ⊆ (range (GluedSpace.inl hb_inj)) ∩ (range
      (GluedSpace.inr hb_inj)) ∪ ⋃ i, (fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder |
        p.1.2 = w i}) i := by
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  rintro x ⟨hx2, hxU⟩
  rw [hH'_U] at hxU
  rcases hxU with hx1 | hxL
  · exact .inl ⟨hH₁_sub_S₁ hx1, hx2⟩
  · exact .inr hxL

private theorem handle_fibers_are_lines
    {S : Type w}
    [TopologicalSpace S]
    (φ : ℕ)
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    (hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj))
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2)
    (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (a' : Fin φ → (GluedSpace hb_inj))
    (b' : Fin φ → (GluedSpace hb_inj))
    (ha'_inr : ∀ (i : Fin φ), a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (hb'_inr : ∀ (i : Fin φ), b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i))) :
    ∀ (i : Fin φ), IsLineWithEnds ((fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2
      = w i}) i) (a'
      i) (b' i) := by
  let S' := GluedSpace hb_inj
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  intro i
  rw [ha'_inr i, hb'_inr i]
  obtain ⟨f, h0, h1⟩ := isLineWithEnds_cylRadial (w i)
  exact ⟨f.trans (hinr_emb.isEmbedding.homeomorphImage {p : ClosedCylinder | p.1.2 = w i}),
    congrArg (GluedSpace.inr hb_inj) h0, congrArg (GluedSpace.inr hb_inj) h1⟩

private theorem assemble_rigid_span_on_added_handle
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (η : SpanEmbedding H G)
    (θ_star : ℕ)
    (θ : ℕ)
    (φ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ₁ : Set S)
    (Λ₂ : Set S)
    (P : Fin φ → Graph α β)
    (a : Fin φ → S)
    (b : Fin φ → S)
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hΛ₁ : Λ₁ ∈ H.R)
    (hΛ₂ : Λ₂ ∈ H.R)
    (hOArc₁ : IsOArc (subBd Λ₁))
    (hOArc₂ : IsOArc (subBd Λ₂))
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty → Disjoint (closure r)
      (H.V ∩ subBd Λ₂))
    (h_lines : ∀ (F : Set S), IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) → (F ∩ subBd
      Λ₁).Nonempty → (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard)
    (hφ : 3 ≤ φ)
    (hφ_le : φ ≤ θ)
    (hab_mem : ∀ (i : Fin φ), a i ∈ H.V ∩ subBd Λ₁ ∧ b i ∈ H.V ∩ subBd Λ₂)
    (hP_disj : Pairwise fun i j => Disjoint V(P i) V(P j))
    (hFree_a : IsFreeSet H.toHypergraph T θ (range a))
    (hFree_b : IsFreeSet H.toHypergraph T θ (range b))
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRigid_H : IsRigid H)
    (hResp_H : IsRespectfulDrawingTangle H θ T)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ₁_open : IsOpen Λ₁)
    (hΛ₂_open : IsOpen Λ₂)
    (hΛ₁_disc : IsOpenDisc Λ₁)
    (hΛ₂_disc : IsOpenDisc Λ₂)
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hCD₁ : IsClosedDisc (closure Λ₁))
    (hdiscBd₁ : discBd (closure Λ₁) = subBd Λ₁)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    (hCD₂ : IsClosedDisc (closure Λ₂))
    (hdiscBd₂ : discBd (closure Λ₂) = subBd Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hSubBd₁_sub_U : subBd Λ₁ ⊆ H.U)
    (hSubBd₂_sub_U : subBd Λ₂ ⊆ H.U)
    (hK_cl : IsClosed (univ \ (Λ₁ ∪ Λ₂)))
    (hK_comp : IsCompact (univ \ (Λ₁ ∪ Λ₂)))
    (hHU : H.U ⊆ (univ \ (Λ₁ ∪ Λ₂)))
    (g₁ : Circle ≃ₜ ↑(subBd Λ₁))
    (g₂ : Circle ≃ₜ ↑(subBd Λ₂))
    (w : Fin φ → Circle)
    (ha_inj : Injective a)
    (hb_inj_fn : Injective b)
    (hw_inj : Injective w)
    (hb_inj : Injective (handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂))
    [this : T2Space (GluedSpace hb_inj)]
    (hS' : IsClosedSurface (GluedSpace hb_inj))
    [hConn' : ConnectedSpace (GluedSpace hb_inj)]
    (hHandle : IsObtainedByAddingHandle S (GluedSpace hb_inj))
    (hS₁_cl : IsClosed (range (GluedSpace.inl hb_inj)))
    (hS₂_cl : IsClosed (range (GluedSpace.inr hb_inj)))
    (C_unp : Fin 2 → Set (GluedSpace hb_inj))
    (ι_unp : ↑(range (GluedSpace.inl hb_inj)) → S)
    (hSplit_unp : GM12.IsCappedSplit C_unp (range (GluedSpace.inl hb_inj)) (range (GluedSpace.inr
      hb_inj)) ι_unp ![Λ₁, Λ₂])
    (hC_unp_0 : C_unp 0 = GluedSpace.inr hb_inj '' range (cylEnd 1 (by norm_num : (1 : ℝ) ∈ Icc 1
      2)))
    (hC_unp_1 : C_unp 1 = GluedSpace.inr hb_inj '' range (cylEnd 2 (by norm_num : (2 : ℝ) ∈ Icc 1
      2)))
    (hι_unp_inl : ∀ (y : ↑(univ \ (Λ₁ ∪ Λ₂))), ι_unp ⟨GluedSpace.inl hb_inj y, ⟨y, rfl⟩⟩ = ↑y)
    (hS12_inter : (range (GluedSpace.inl hb_inj)) ∩ (range (GluedSpace.inr hb_inj)) = C_unp 0 ∪
      C_unp 1)
    (g_unp : S → (GluedSpace hb_inj))
    (f_unp : (GluedSpace hb_inj) → S)
    (hg_unp_mem : ∀ (y : S) (hy : y ∈ (univ \ (Λ₁ ∪ Λ₂))), g_unp y = GluedSpace.inl hb_inj ⟨y,
      hy⟩)
    (hf_unp_inl : ∀ (y : ↑(univ \ (Λ₁ ∪ Λ₂))), f_unp (GluedSpace.inl hb_inj y) = ↑y)
    (hg_unp_cont : ContinuousOn g_unp (univ \ (Λ₁ ∪ Λ₂)))
    (hf_unp_cont : ContinuousOn f_unp (range (GluedSpace.inl hb_inj)))
    (hfg_unp_inv : LeftInvOn f_unp g_unp (univ \ (Λ₁ ∪ Λ₂)))
    (hgf_unp_inv : LeftInvOn g_unp f_unp (range (GluedSpace.inl hb_inj)))
    (hf_unp_cont' : ContinuousOn f_unp (g_unp '' (univ \ (Λ₁ ∪ Λ₂))))
    (hH₁_U : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U = g_unp '' H.U)
    (hH₁_V : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).V = g_unp '' H.V)
    (hH₁_sub_S₁ : (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U ⊆ (range
      (GluedSpace.inl hb_inj)))
    (m1 : (1 : ℝ) ∈ Icc 1 2)
    (m2 : (2 : ℝ) ∈ Icc 1 2)
    (ha_K : ∀ (i : Fin φ), a i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (hb_K : ∀ (i : Fin φ), b i ∈ (univ \ (Λ₁ ∪ Λ₂)))
    (ha'_V : ∀ i : Fin φ, g_unp (a i) ∈ (liftDrawingOn hK_comp hg_unp_cont
      hf_unp_cont' hfg_unp_inv H hHU).V)
    (hb'_V : ∀ i : Fin φ, g_unp (b i) ∈ (liftDrawingOn hK_comp hg_unp_cont
      hf_unp_cont' hfg_unp_inv H hHU).V)
    (ha'_inr : ∀ i : Fin φ, g_unp (a i) = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)))
    (hb'_inr : ∀ i : Fin φ, g_unp (b i) = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)))
    (hL_line : ∀ i : Fin φ, IsLineWithEnds
      (GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) (g_unp (a i)) (g_unp (b i)))
    (hL_disj : Pairwise fun i j => Disjoint
      (GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i})
      (GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w j}))
    (hL_S₁ : ∀ i : Fin φ, (GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) ∩
      range (GluedSpace.inl hb_inj) = {g_unp (a i), g_unp (b i)})
    (hL_H₁U : ∀ i : Fin φ, (GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}) ∩
      (liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU).U =
      {g_unp (a i), g_unp (b i)})
    (hP_paths' : ∀ i : Fin φ, IsHPathWithEnds G (liftSpanEmbeddingOn hK_comp hg_unp_cont
      hf_unp_cont' hfg_unp_inv hHU η).imageGraph (P i)
      ((liftSpanEmbeddingOn hK_comp hg_unp_cont
        hf_unp_cont' hfg_unp_inv hHU η).vMap (g_unp (a i)))
      ((liftSpanEmbeddingOn hK_comp hg_unp_cont
        hf_unp_cont' hfg_unp_inv hHU η).vMap (g_unp (b i)))) :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingHandle S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T' := by
  let K := univ \ (Λ₁ ∪ Λ₂)
  let S' := GluedSpace hb_inj
  let S₁ := range (GluedSpace.inl hb_inj)
  let S₂ := range (GluedSpace.inr hb_inj)
  let H₁ := liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  let η₁ := liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η
  let a' := fun i => g_unp (a i)
  let b' := fun i => g_unp (b i)
  let L := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  obtain ⟨H_path, H', η', hH'_U, hH'_V, hH'_E, hSub_H₁, hH_path, hH_path_disj,
    _, hvm_H₁, hem_H₁, _, _⟩ :=
    exists_glued_span_of_lines H₁ η₁ a' b' P L ha'_V hb'_V hP_paths' hP_disj
      hL_line hL_disj hL_H₁U
  obtain ⟨hU_S₁, hV_S₁, _⟩ :=
    glued_interSet_base_eq hS₁_cl ha'_V hb'_V hH₁_sub_S₁ hL_S₁ hH'_U hH'_V hH'_E hH_path
  have hι_unp_g : ∀ y ∈ K, ∀ hy : g_unp y ∈ S₁, ι_unp ⟨g_unp y, hy⟩ = y := by
    intro y hy hgy
    have hsub : (⟨g_unp y, hgy⟩ : ↥S₁) = ⟨GluedSpace.inl hb_inj ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ :=
      Subtype.ext (hg_unp_mem y hy)
    rw [hsub, hι_unp_inl ⟨y, hy⟩]
  have hCap_unp : GM12.IsCappedDrawing ι_unp H' H :=
    isCappedDrawing_of_glued hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU hU_S₁ hV_S₁ hι_unp_g
  -- Verify `IsRigid H'` using `theorem_3_2_proof` on the unpinched split.
  have hinr_cylEnd_one : ∀ z : Circle,
      GluedSpace.inr hb_inj (cylEnd 1 m1 z) = g_unp (g₁ z).1 := by
    exact lower_cylinder_end_equals_original_boundary_point (S := S) H Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd
      hSubBd₁_sub_U hHU g₁ g₂ hb_inj g_unp hg_unp_mem m1
  have hinr_cylEnd_two : ∀ z : Circle,
      GluedSpace.inr hb_inj (cylEnd 2 m2 z) = g_unp (g₂ z).1 := by
    exact upper_cylinder_end_equals_original_boundary_point (S := S) H Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd
      hSubBd₂_sub_U hHU g₁ g₂ hb_inj g_unp hg_unp_mem m2
  have hC_unp_0_sub_H₁ : C_unp 0 ⊆ H₁.U := by
    rw [hC_unp_0]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [hinr_cylEnd_one z, hH₁_U]
    exact mem_image_of_mem g_unp (hSubBd₁_sub_U (g₁ z).2)
  have hC_unp_1_sub_H₁ : C_unp 1 ⊆ H₁.U := by
    rw [hC_unp_1]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [hinr_cylEnd_two z, hH₁_U]
    exact mem_image_of_mem g_unp (hSubBd₂_sub_U (g₂ z).2)
  have hS12_sub_U : S₁ ∩ S₂ ⊆ H'.U := by
    rw [hS12_inter, hH'_U]
    exact (union_subset hC_unp_0_sub_H₁ hC_unp_1_sub_H₁).trans subset_union_left
  let X_unp : Set S' := range a' ∪ range b'
  have ha'_C0 : ∀ i, a' i ∈ C_unp 0 := by
    intro i
    change g_unp (a i) ∈ C_unp 0
    rw [ha'_inr i, hC_unp_0]
    exact ⟨cylEnd 1 m1 (w i), ⟨w i, rfl⟩, rfl⟩
  have hb'_C1 : ∀ i, b' i ∈ C_unp 1 := by
    intro i
    change g_unp (b i) ∈ C_unp 1
    rw [hb'_inr i, hC_unp_1]
    exact ⟨cylEnd 2 m2 (w i), ⟨w i, rfl⟩, rfl⟩
  have hX_unp_sub : X_unp ⊆ H'.V ∩ (S₁ ∩ S₂) := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨hSub_H₁.1 (ha'_V i), hS12_inter.symm ▸ Or.inl (ha'_C0 i)⟩
    · exact ⟨hSub_H₁.1 (hb'_V i), hS12_inter.symm ▸ Or.inr (hb'_C1 i)⟩
  have hι_unp_X : ι_unp '' ((↑) ⁻¹' X_unp) = range a ∪ range b := by
    exact unpinched_embedding_maps_marked_nodes (S := S) φ Λ₁ Λ₂ a b hΛ₁_open hΛ₂_open hd g₁ g₂
      hb_inj ι_unp g_unp a' rfl b' rfl ha_K hb_K H' hι_unp_g hX_unp_sub
  have hS₂_U : S₂ ∩ H'.U ⊆ (S₁ ∩ S₂) ∪ ⋃ i : Fin φ, L i := by
    exact cylinder_drawing_is_in_cuffs_or_handle_lines (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂
      w hb_inj H₁ hH₁_sub_S₁ H' hH'_U
  have hRigid_H' : IsRigid H' := by
    refine theorem_3_2_proof C_unp S₁ S₂ ι_unp ![Λ₁, Λ₂] H' H X_unp
      hSplit_unp hCap_unp hS12_sub_U hX_unp_sub ?_ ?_ ?_ ?_
    -- Condition (i): no region `r ⊆ S₁` of `H'` meets both `C_unp 0` and `C_unp 1`.
    · exact original_region_cannot_meet_both_handle_cuffs (S := S) H φ Λ₁ Λ₂ hΛ₁ hΛ₂ hOArc₁ hOArc₂
        hNo_common_region hS hΛ₁_open hΛ₂_open hd hSubBd₁_sub_U hSubBd₂_sub_U hHU g₁ g₂ w hb_inj
        hS₁_cl C_unp hC_unp_0 hC_unp_1 g_unp f_unp hf_unp_cont hfg_unp_inv hgf_unp_inv H₁ hH₁_U m1
        m2 H' hH'_U hinr_cylEnd_one hinr_cylEnd_two
    -- Condition (ii): dials in `S` via `theorem_3_5_claim_1`.
    · exact original_surface_dial (S := S) H θ φ T Λ₁ Λ₂ a b hΛ₁ hΛ₂ hOArc₁ hOArc₂
        hNo_common_region hφ hab_mem hFree_a hFree_b hS hRigid_H hT hθ hΛ₁_open hΛ₂_open hd g₁ g₂
        ha_inj hb_inj_fn hb_inj ι_unp a' b' hι_unp_X
    -- Condition (iii): dials in the cylinder.
    · exact cylinder_dial_of_normal_closed_curve (S := S) φ Λ₁ Λ₂ hφ hS hΛ₁_open hΛ₂_open hd g₁ g₂
        w hw_inj hb_inj hS' H₁ m1 m2 a' b' ha'_inr hb'_inr hL_line hL_disj H_path H' hH'_U hH_path
        hS₂_U
    -- Condition (iv): open discs cut out by normal chords in the cylinder.
    · exact cylinder_disc_of_normal_chord (S := S) φ Λ₁ Λ₂ hφ hS hΛ₁_open hΛ₂_open hd g₁ g₂ w
        hw_inj hb_inj hS' hS₁_cl hS₂_cl C_unp ι_unp hSplit_unp hS12_inter H₁ m1 m2 a' b' ha'_V
        hb'_V ha'_inr hb'_inr hL_line hL_disj hL_S₁ H_path H' hH'_U hSub_H₁ hH_path ha'_C0 hb'_C1
        hS₂_U
  have h2Cell_H' : (PaintingOrDrawing.drawing H').IsTwoCell :=
    isTwoCell_of_isRigid hS' hRigid_H'
      ⟨a' ⟨0, by omega⟩, H'.V_subset_U (hSub_H₁.1 (ha'_V ⟨0, by omega⟩))⟩
  -- Pinched handle split and `GM12Theorem51Statement`.
  let W_pts : Set Circle := range w
  have hW_cl : IsClosed W_pts := (Set.finite_range w).isClosed
  have hW_ne : W_pts.Nonempty := ⟨w ⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩
  let CollarInt : Set S' :=
    GluedSpace.inr hb_inj '' {q : ClosedCylinder | 1 < q.1.1 ∧ q.1.1 < 2 ∧ q.1.2 ∉ W_pts}
  obtain ⟨C_XII, P₁_XII, P₂_XII, ι_XII, D_XII, f_XII, hSplit_XII, hS₁_sub_P₁,
    hf_XII_inl, hι_XII_eq, hι_XII_emb, hD0_sub, hD1_sub, hcl_D0_sub, hcl_D1_sub,
    hP₁_diff_S₁, hW1_sub_C0, hC0_diff_W1, hW2_sub_C1, hC1_diff_W2, hW_sub_P₂,
    hf_XII_C0, hf_XII_C1, hf_XII_P₁, hf_XII_mem_S₁⟩ :=
    exists_pinched_handleSplit hS hΛ₁_open hΛ₂_open hΛ₁_disc hΛ₂_disc hCD₁ hCD₂
      hdiscBd₁ hdiscBd₂ hd hOArc₁ hOArc₂ hout₁ hout₂ g₁ g₂ hb_inj hW_cl hW_ne
  have hCollar_disj : Disjoint CollarInt H'.U := by
    exact unmarked_handle_collars_avoid_drawing (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w
      hb_inj H₁ hH₁_sub_S₁ H' hH'_U W_pts rfl CollarInt rfl
  have hU_P₁_XII : H'.U ∩ P₁_XII = H₁.U := by
    exact pinched_complement_retains_original_drawing (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂
      w hb_inj H₁ hH₁_sub_S₁ H' hH'_U hU_S₁ W_pts CollarInt rfl P₁_XII hS₁_sub_P₁ hP₁_diff_S₁
      hCollar_disj
  have hV_P₁_XII : H'.V ∩ P₁_XII = H₁.V := by
    exact pinched_complement_retains_original_vertices (S := S) Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂
      hb_inj H₁ hH₁_sub_S₁ H' hSub_H₁ hV_S₁ W_pts CollarInt rfl P₁_XII hS₁_sub_P₁ hP₁_diff_S₁
      hCollar_disj
  have hι_XII_g : ∀ y ∈ K, ∀ hy : g_unp y ∈ P₁_XII, ι_XII ⟨g_unp y, hy⟩ = y := by
    intro y hy hgy
    rw [hι_XII_eq ⟨g_unp y, hgy⟩]
    change f_XII (g_unp y) = y
    rw [hg_unp_mem y hy, hf_XII_inl ⟨y, hy⟩]
  have hCap_XII : GM12.IsCappedDrawing ι_XII H' H :=
    isCappedDrawing_of_glued hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU
      hU_P₁_XII hV_P₁_XII hι_XII_g
  have hW1_eq_a' : GluedSpace.inr hb_inj '' (cylEnd 1 m1 '' W_pts) = range a' := by
    exact lower_pinched_marks_equal_path_ends (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hb_inj
      m1 a' ha'_inr W_pts rfl
  have hW2_eq_b' : GluedSpace.inr hb_inj '' (cylEnd 2 m2 '' W_pts) = range b' := by
    exact upper_pinched_marks_equal_path_ends (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hb_inj
      m2 b' hb'_inr W_pts rfl
  have hNorm_C0_and_V : H'.IsNormal (C_XII 0) ∧ H'.V ∩ C_XII 0 = range a' := by
    exact lower_pinched_cuff_is_normal (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hb_inj H₁ m1
      a' ha'_V H_path H' hH'_U hH'_V W_pts CollarInt rfl C_XII hW1_sub_C0 hC0_diff_W1 hCollar_disj
      hW1_eq_a'
  have hNorm_C1_and_V : H'.IsNormal (C_XII 1) ∧ H'.V ∩ C_XII 1 = range b' := by
    exact upper_pinched_cuff_is_normal (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hb_inj H₁ m2
      b' hb'_V H_path H' hH'_U hH'_V W_pts CollarInt rfl C_XII hW2_sub_C1 hC1_diff_W2 hCollar_disj
      hW2_eq_b'
  have ha'_inj : Function.Injective a' :=
    fun i j hij => ha_inj (hfg_unp_inv.injOn (ha_K i) (ha_K j) hij)
  have hb'_inj : Function.Injective b' :=
    fun i j hij => hb_inj_fn (hfg_unp_inv.injOn (hb_K i) (hb_K j) hij)
  have hCard_C0 : (H'.V ∩ C_XII 0).ncard = φ := by
    rw [hNorm_C0_and_V.2, Set.ncard_range_of_injective ha'_inj, Nat.card_fin]
  have hCard_C1 : (H'.V ∩ C_XII 1).ncard = φ := by
    rw [hNorm_C1_and_V.2, Set.ncard_range_of_injective hb'_inj, Nat.card_fin]
  have hP₂_XII_cl : IsClosed P₂_XII :=
    (isCompact_iff_compactSpace.mpr hSplit_XII.1.manifold₂.1).isClosed
  have hH₁_P₂_XII : H₁.U ∩ P₂_XII ⊆ ⋃ i : Fin φ, ({a' i, b' i} : Set S') := by
    exact original_drawing_meets_pinched_handle_at_marked_ends (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open
      hd g₁ g₂ w hb_inj H₁ hH₁_sub_S₁ a' b' H' hH'_U C_XII P₁_XII P₂_XII ι_XII D_XII hSplit_XII
      hS₁_sub_P₁ hNorm_C0_and_V hNorm_C1_and_V
  obtain ⟨hH_path_sub_P₂, hInter_P₂_U⟩ :=
    glued_interSet_paths_eq hP₂_XII_cl (fun i => hW_sub_P₂ (w i) ⟨i, rfl⟩)
      hH₁_P₂_XII hH'_V hH'_E hH_path
  -- Line condition for `GM12Theorem51Statement`.
  have hLines_XII : ∀ F : Set S', IsLine F → H'.IsNormal F → F ⊆ P₁_XII →
      (F ∩ C_XII 0).Nonempty → (F ∩ C_XII 1).Nonempty → φ ≤ (F ∩ H'.V).ncard := by
    exact normal_line_between_pinched_cuffs_meets_many_vertices (S := S) H φ Λ₁ Λ₂ h_lines
      hΛ₁_open hΛ₂_open hd hK_cl hHU g₁ g₂ w hb_inj g_unp f_unp hg_unp_mem hf_unp_inl hfg_unp_inv
      H₁ hH₁_U hH₁_V H' hH'_U hSub_H₁ C_XII P₁_XII P₂_XII ι_XII D_XII f_XII hSplit_XII hf_XII_inl
      hι_XII_eq hι_XII_emb hcl_D0_sub hcl_D1_sub hf_XII_C0 hf_XII_C1 hf_XII_P₁ hf_XII_mem_S₁
      hV_P₁_XII
  -- Truncated tangle `T₁` and induced tangle `T'`.
  let T₁ := GM10.truncation T φ
  have hResp_T₁ : IsRespectfulDrawingTangle H φ T₁ :=
    isRespectfulDrawingTangle_truncation hResp_H (by omega) hφ_le
  have hCtrl_T₁ : IsControllingTangle G H η θ_star φ T_star T₁ :=
    isControllingTangle_truncation hSpan.isControlling (by omega) hφ_le
  have hι_XII_C0 : ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 0)) = range a := by
    exact lower_pinch_cuff_vertices_map_to_original_ends (S := S) φ Λ₁ Λ₂ a hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj g_unp H₁ hH₁_sub_S₁ a' rfl ha_K ha'_V H' C_XII P₁_XII ι_XII hS₁_sub_P₁ hι_XII_g
      hNorm_C0_and_V
  have hι_XII_C1 : ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 1)) = range b := by
    exact upper_pinch_cuff_vertices_map_to_original_ends (S := S) φ Λ₁ Λ₂ b hΛ₁_open hΛ₂_open hd
      g₁ g₂ hb_inj g_unp H₁ hH₁_sub_S₁ b' rfl hb_K hb'_V H' C_XII P₁_XII ι_XII hS₁_sub_P₁ hι_XII_g
      hNorm_C1_and_V
  have hFree_T₁_a : IsFreeSet H.toHypergraph T₁ φ (ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 0))) :=
    hι_XII_C0.symm ▸ theorem_3_3_claim_2 hT hFree_a Subset.rfl
      (by rw [Set.ncard_range_of_injective ha_inj, Nat.card_fin])
  have hFree_T₁_b : IsFreeSet H.toHypergraph T₁ φ (ι_XII '' ((↑) ⁻¹' (H'.V ∩ C_XII 1))) :=
    hι_XII_C1.symm ▸ theorem_3_3_claim_2 hT hFree_b Subset.rfl
      (by rw [Set.ncard_range_of_injective hb_inj_fn, Nat.card_fin])
  have hResp_T' : (PaintingOrDrawing.drawing H').IsRespectful φ
      (GM12.inducedAcross ι_XII H' H φ T₁) :=
    GraphMinor.GM12.theorem_5_1_proof.{w} C_XII P₁_XII P₂_XII ι_XII D_XII H' H φ T₁ H_path a' b'
      hS' hConn' hSplit_XII hCap_XII hNorm_C0_and_V.1 hNorm_C1_and_V.1 hCard_C0 hCard_C1
      (fun i => ⟨hNorm_C0_and_V.2.symm ▸ ⟨i, rfl⟩, hNorm_C1_and_V.2.symm ▸ ⟨i, rfl⟩,
        (hH_path i).2.1, hH_path_sub_P₂ i⟩)
      hH_path_disj hInter_P₂_U hLines_XII hResp_T₁.2.1 hResp_T₁.2.2 hFree_T₁_a hFree_T₁_b
  have hη'_v : ∀ v ∈ H.V, η'.vMap (g_unp v) = η.vMap v := by
    intro v hv
    rw [hvm_H₁ (g_unp v) (by rw [hH₁_V]; exact ⟨v, hv, rfl⟩)]
    change η.vMap (f_unp (g_unp v)) = η.vMap v
    rw [hfg_unp_inv (hHU (H.V_subset_U hv))]
  have hη'_e : ∀ e ∈ H.E, η'.eMap (g_unp '' e) = η.eMap e := by
    exact handle_embedding_agrees_on_original_edges (S := S) (α := α) (β := β) G H η Λ₁ Λ₂
      hΛ₁_open hΛ₂_open hd hHU g₁ g₂ hb_inj g_unp f_unp hfg_unp_inv H₁ η₁
      (liftDrawingOn_E hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU)
      (fun _ => rfl) H' η' hem_H₁
  obtain ⟨hT', hCtrl_T'⟩ :=
    isTangle_and_isControlling_inducedAcross hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv
      hHU η η' hSub_H₁ hU_P₁_XII hV_P₁_XII hι_XII_g hη'_v hη'_e hCtrl_T₁
  exact ⟨S', inferInstance, inferInstance, hHandle, H', η', GM12.inducedAcross ι_XII H' H φ T₁,
    { isSurface := IsClosedSurface.isSurface hS'
      isConnected := hConn'
      bd_empty := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS'.2.2 x)
      isRigid := hRigid_H'
      isRespectful := ⟨h2Cell_H', hT', hResp_T'⟩
      isControlling := hCtrl_T' }⟩

/-- **Graph Minors XV, (3.5)** (pages 123–124):
Adding a handle between two distinct regions `Λ₁, Λ₂` along `φ` disjoint `η(H)`-paths `P_i` yields
a `Σ'`-span `(H', η', T')` of order `φ`. -/
theorem theorem_3_5_proof :
    GM15Theorem35Statement.{u, v, w} := by
  intro S _ _ α β G H η θ_star θ φ T_star T Λ₁ Λ₂ P a b
    hSpan hΛ₁ hΛ₂ hne hOArc₁ hOArc₂ hCirc₁ _hCirc₂ hNo_common_region h_lines
    hφ hφ_le hNodup_a hNodup_b hOrder_a hOrder_b hab_mem hP_paths hP_disj hFree_a hFree_b
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : CompactSpace S := hS.1
  have hRigid_H : IsRigid H := hSpan.isRigid
  have hResp_H : IsRespectfulDrawingTangle H θ T := hSpan.isRespectful
  have hT : IsTangle H.toHypergraph θ T := hResp_H.2.1
  have hθ : 3 ≤ θ := le_trans hφ hφ_le
  have hΛ₁_open : IsOpen Λ₁ := GM11.region_isOpen hΛ₁
  have hΛ₂_open : IsOpen Λ₂ := GM11.region_isOpen hΛ₂
  have hΛ₁_disc : IsOpenDisc Λ₁ := hResp_H.1.2 Λ₁ hΛ₁
  have hΛ₂_disc : IsOpenDisc Λ₂ := hResp_H.1.2 Λ₂ hΛ₂
  obtain ⟨hout₁, hCD₁, hdiscBd₁, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ₁ hOArc₁
  obtain ⟨hout₂, hCD₂, hdiscBd₂, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ₂ hOArc₂
  have hd : Disjoint (closure Λ₁) (closure Λ₂) :=
    disjoint_closure_of_no_common_region hS hΛ₁ hΛ₂ hne hOArc₁ hOArc₂
      ⟨a ⟨0, by omega⟩, (hab_mem ⟨0, by omega⟩).1⟩ hNo_common_region
  obtain ⟨_, hSubBd₁_U, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ₁ hOArc₁
  obtain ⟨_, hSubBd₂_U, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ₂ hOArc₂
  have hSubBd_sub_U : ∀ {Λ : Set S}, (H.interSet (subBd Λ)).U = subBd Λ → subBd Λ ⊆ H.U := by
    exact drawing_contains_region_boundary_of_boundary_subdrawing (S := S) H
  have hSubBd₁_sub_U : subBd Λ₁ ⊆ H.U := hSubBd_sub_U hSubBd₁_U
  have hSubBd₂_sub_U : subBd Λ₂ ⊆ H.U := hSubBd_sub_U hSubBd₂_U
  let K : Set S := univ \ (Λ₁ ∪ Λ₂)
  have hK_cl : IsClosed K := isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open)
  have hK_comp : IsCompact K := hK_cl.isCompact
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK_comp
  have : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  have hHU : H.U ⊆ K := fun y hy =>
    ⟨mem_univ y, fun h => h.elim (fun h1 => GM11.region_subset hΛ₁ h1 hy)
      (fun h2 => GM11.region_subset hΛ₂ h2 hy)⟩
  -- Align the circle parametrizations of `subBd Λ₁` and `subBd Λ₂`.
  obtain ⟨f₁, t₁, ht₁_mono, ht₁_bd, ht₁_val⟩ := hOrder_a
  obtain ⟨f₂, t₂, ht₂_mono, ht₂_bd, ht₂_val⟩ := hOrder_b
  have ht₁_bd' : ∀ i < φ, t₁ i < t₁ 0 + 2 * Real.pi := fun i hi => ht₁_bd i (by simp [hi])
  have ht₂_bd' : ∀ i < φ, t₂ i < t₂ 0 + 2 * Real.pi := fun i hi => ht₂_bd i (by simp [hi])
  obtain ⟨h_circ, hh_circ⟩ :=
    exists_circle_homeo_matching_angles φ (by omega) t₂ t₁ ht₂_mono ht₁_mono ht₂_bd' ht₁_bd'
  let g₁ : Circle ≃ₜ ↥(subBd Λ₁) := f₁
  let g₂ : Circle ≃ₜ ↥(subBd Λ₂) := h_circ.symm.trans f₂
  let w : Fin φ → Circle := fun i => Circle.exp (t₁ i.1)
  have hg₁_w : ∀ i : Fin φ, (g₁ (w i)).1 = a i :=
    fun i => by simpa using ht₁_val i.1 (by simp)
  have hg₂_w : ∀ i : Fin φ, (g₂ (w i)).1 = b i := by
    exact upper_handle_parametrization_matches_path_ends (S := S) φ Λ₂ b t₁ f₂ t₂ ht₂_val h_circ
      hh_circ g₂ rfl w (fun _ => rfl)
  have ha_inj : Function.Injective a := List.nodup_ofFn.mp hNodup_a
  have hb_inj_fn : Function.Injective b := List.nodup_ofFn.mp hNodup_b
  have hw_inj : Function.Injective w :=
    fun i j hij => ha_inj (by rw [← hg₁_w i, ← hg₁_w j, hij])
  -- Construct the glued surface `S'`.
  let b_glue := handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_inj := injective_handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_cont := continuous_handleGlueMap hΛ₁_open hΛ₂_open hd g₁ g₂
  have hb_range := range_handleGlueMap hS hΛ₁_open hΛ₂_open hOArc₁ hOArc₂ hout₁ hout₂ hd g₁ g₂
  let S' := GluedSpace hb_inj
  have : T2Space S' := GluedSpace.t2Space (isClosed_bd ↥ClosedCylinder) hb_cont hb_inj
  obtain ⟨hS', hConn', hHandle, _, _, hU_S12_eq, _, _⟩ :=
    isClosedSurface_of_handle_glue hS hΛ₁_disc hΛ₂_disc hd hOArc₁ hOArc₂ hout₁ hout₂
      hb_cont hb_inj hb_range
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  have hS₁_cl : IsClosed S₁ := hinl_emb.isClosed_range
  have hS₂_cl : IsClosed S₂ := hinr_emb.isClosed_range
  -- Unpinched split on `S'`.
  obtain ⟨C_unp, ι_unp, _, _, _, hSplit_unp, hC_unp_0, hC_unp_1, _, hι_unp_inl⟩ :=
    isCappedSplit_handle_unpinched hS hΛ₁_open hΛ₂_open hΛ₁_disc hΛ₂_disc hd
      hOArc₁ hOArc₂ hout₁ hout₂ g₁ g₂ hb_inj
  have hS12_inter : S₁ ∩ S₂ = C_unp 0 ∪ C_unp 1 := by
    rw [hSplit_unp.inter]
    ext x
    simp [Fin.exists_fin_two]
  have ha0_K : a ⟨0, by omega⟩ ∈ K := hHU (H.V_subset_U (hab_mem ⟨0, by omega⟩).1.1)
  let g_unp : S → S' := by
    classical
    exact fun y => if hy : y ∈ K then GluedSpace.inl hb_inj ⟨y, hy⟩ else
      GluedSpace.inl hb_inj ⟨a ⟨0, by omega⟩, ha0_K⟩
  let f_unp : S' → S := by
    classical
    exact fun x => if hx : x ∈ S₁ then ι_unp ⟨x, hx⟩ else a ⟨0, by omega⟩
  have hg_unp_mem : ∀ y (hy : y ∈ K), g_unp y = GluedSpace.inl hb_inj ⟨y, hy⟩ := by
    intro y hy
    simp only [g_unp, hy, ↓reduceDIte]
  have hf_unp_inl : ∀ y : ↥K, f_unp (GluedSpace.inl hb_inj y) = y.1 := by
    intro y
    have hx : GluedSpace.inl hb_inj y ∈ S₁ := ⟨y, rfl⟩
    simp only [f_unp, hx, ↓reduceDIte]
    exact hι_unp_inl y
  have hg_unp_cont : ContinuousOn g_unp K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : K.domRestrict g_unp = GluedSpace.inl hb_inj := by
      ext ⟨y, hy⟩
      exact hg_unp_mem y hy
    rw [hEq]
    exact GluedSpace.continuous_inl hb_inj
  have hf_unp_cont : ContinuousOn f_unp S₁ := by
    exact unpinched_map_continuous_on_first_piece (S := S) Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj
      C_unp ι_unp hSplit_unp f_unp (fun _ hx => dite_eq_left hx)
  have hfg_unp_inv : Set.LeftInvOn f_unp g_unp K := by
    intro y hy
    rw [hg_unp_mem y hy, hf_unp_inl ⟨y, hy⟩]
  have hgf_unp_inv : Set.LeftInvOn g_unp f_unp S₁ := by
    rintro _ ⟨y, rfl⟩
    rw [hf_unp_inl y, hg_unp_mem y.1 y.2]
  have hg_unp_K : g_unp '' K = S₁ := by
    exact original_complement_embeds_onto_first_piece (S := S) Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂
      hb_inj g_unp hg_unp_mem
  have hf_unp_cont' : ContinuousOn f_unp (g_unp '' K) := hg_unp_K.symm ▸ hf_unp_cont
  let H₁ : Drawing S' := liftDrawingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  let η₁ : SpanEmbedding H₁ G :=
    liftSpanEmbeddingOn hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv hHU η
  have hH₁_U : H₁.U = g_unp '' H.U :=
    liftDrawingOn_U hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  have hH₁_V : H₁.V = g_unp '' H.V :=
    liftDrawingOn_V hK_comp hg_unp_cont hf_unp_cont' hfg_unp_inv H hHU
  have hH₁_sub_S₁ : H₁.U ⊆ S₁ := by
    rw [hH₁_U, ← hg_unp_K]
    exact image_mono hHU
  -- Radial lines `L i` and endpoints `a' i, b' i`.
  have m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  let a' : Fin φ → S' := fun i => g_unp (a i)
  let b' : Fin φ → S' := fun i => g_unp (b i)
  let L : Fin φ → Set S' := fun i => GluedSpace.inr hb_inj '' {p : ClosedCylinder | p.1.2 = w i}
  have ha_K : ∀ i, a i ∈ K := fun i => hHU (H.V_subset_U (hab_mem i).1.1)
  have hb_K : ∀ i, b i ∈ K := fun i => hHU (H.V_subset_U (hab_mem i).2.1)
  have ha'_V : ∀ i, a' i ∈ H₁.V := fun i => by rw [hH₁_V]; exact ⟨a i, (hab_mem i).1.1, rfl⟩
  have hb'_V : ∀ i, b' i ∈ H₁.V := fun i => by rw [hH₁_V]; exact ⟨b i, (hab_mem i).2.1, rfl⟩
  have ha'_inr : ∀ i, a' i = GluedSpace.inr hb_inj (cylEnd 1 m1 (w i)) := by
    exact lower_handle_end_maps_to_cylinder (S := S) φ Λ₁ Λ₂ a hΛ₁_open hΛ₂_open hd g₁ g₂ w hg₁_w
      hb_inj g_unp hg_unp_mem m1 a' rfl ha_K
  have hb'_inr : ∀ i, b' i = GluedSpace.inr hb_inj (cylEnd 2 m2 (w i)) := by
    exact upper_handle_end_maps_to_cylinder (S := S) φ Λ₁ Λ₂ b hΛ₁_open hΛ₂_open hd g₁ g₂ w hg₂_w
      hb_inj g_unp hg_unp_mem m2 b' rfl hb_K
  have hL_line : ∀ i, IsLineWithEnds (L i) (a' i) (b' i) := by
    exact handle_fibers_are_lines (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hb_inj hinr_emb m1
      m2 a' b' ha'_inr hb'_inr
  have hL_disj : Pairwise (fun i j => Disjoint (L i) (L j)) := by
    exact distinct_handle_lines_are_disjoint (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁ g₂ w hw_inj
      hb_inj
  have hL_S₁ : ∀ i, L i ∩ S₁ = {a' i, b' i} := by
    exact handle_line_intersects_original_surface_only_at_ends (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open
      hd g₁ g₂ w hb_inj H₁ hH₁_sub_S₁ m1 m2 a' b' ha'_V hb'_V ha'_inr hb'_inr
  have hL_H₁U : ∀ i, L i ∩ H₁.U = {a' i, b' i} := by
    exact handle_line_meets_original_drawing_only_at_ends (S := S) φ Λ₁ Λ₂ hΛ₁_open hΛ₂_open hd g₁
      g₂ w hb_inj H₁ hH₁_sub_S₁ a' b' ha'_V hb'_V hL_S₁
  have hP_paths' : ∀ i : Fin φ,
      IsHPathWithEnds G η₁.imageGraph (P i) (η₁.vMap (a' i)) (η₁.vMap (b' i)) := by
    exact original_paths_lift_to_glued_drawing (S := S) (α := α) (β := β) G H η φ Λ₁ Λ₂ P a b
      hP_paths hΛ₁_open hΛ₂_open hd g₁ g₂ hb_inj H₁ η₁ a' b' rfl (fun i => congrArg η.vMap
      (hfg_unp_inv (ha_K i))) (fun i => congrArg η.vMap (hfg_unp_inv (hb_K i)))
  exact assemble_rigid_span_on_added_handle (S := S) (α := α) (β := β) G H η θ_star θ φ T_star T
    Λ₁ Λ₂ P a b hSpan hΛ₁ hΛ₂ hOArc₁ hOArc₂ hNo_common_region h_lines hφ hφ_le hab_mem hP_disj
    hFree_a hFree_b hS hRigid_H hResp_H hT hθ hΛ₁_open hΛ₂_open hΛ₁_disc hΛ₂_disc hout₁ hCD₁
    hdiscBd₁ hout₂ hCD₂ hdiscBd₂ hd hSubBd₁_sub_U hSubBd₂_sub_U hK_cl hK_comp hHU
    g₁ g₂ w ha_inj hb_inj_fn hw_inj hb_inj hS' hHandle hS₁_cl hS₂_cl C_unp ι_unp hSplit_unp
    hC_unp_0 hC_unp_1 hι_unp_inl hS12_inter g_unp f_unp hg_unp_mem hf_unp_inl hg_unp_cont
    hf_unp_cont hfg_unp_inv hgf_unp_inv hf_unp_cont' hH₁_U hH₁_V hH₁_sub_S₁ m1 m2 ha_K hb_K
    ha'_V hb'_V ha'_inr hb'_inr hL_line hL_disj hL_S₁ hL_H₁U hP_paths'

end GraphMinor.GM15
