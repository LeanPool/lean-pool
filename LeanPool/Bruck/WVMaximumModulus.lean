/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Convex.Deriv

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-!
# Maximum modulus and its logarithmic convexity

Hadamard's three-lines theorem gives the convexity of
`x ↦ log M(exp x)` for every entire function that is not identically zero.
The local Wiman–Valiron estimates use this convexity.
-/

@[expose] public section

open Set Metric Filter Topology

namespace Bruck

/-- The supremum of the norm of `H` on the circle of radius `r` about zero. -/
noncomputable def wvMaximumModulus (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖H z‖) '' sphere (0 : ℂ) r)

/-- The log maximum modulus of `H` as a function of the log radius. -/
noncomputable def wvLogMaximum (H : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.log (wvMaximumModulus H (Real.exp x))

theorem wvMaximumModulus_nonneg (H : ℂ → ℂ) (r : ℝ) :
    0 ≤ wvMaximumModulus H r := by
  apply Real.sSup_nonneg
  rintro _ ⟨z, _, rfl⟩
  exact norm_nonneg _

theorem wvMaximumModulus_bddAbove {H : ℂ → ℂ} (hH : Continuous H) (r : ℝ) :
    BddAbove ((fun z => ‖H z‖) '' sphere (0 : ℂ) r) :=
  (isCompact_sphere (0 : ℂ) r).bddAbove_image hH.norm.continuousOn

theorem wv_norm_le_maximumModulus {H : ℂ → ℂ} (hH : Continuous H)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) : ‖H z‖ ≤ wvMaximumModulus H r := by
  exact le_csSup (wvMaximumModulus_bddAbove hH r)
    ⟨z, by simpa only [mem_sphere_iff_norm, sub_zero] using hz, rfl⟩

theorem wvMaximumModulus_attained {H : ℂ → ℂ} (hH : Continuous H)
    {r : ℝ} (hr : 0 ≤ r) : ∃ z : ℂ, ‖z‖ = r ∧ ‖H z‖ = wvMaximumModulus H r := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr) hH.norm.continuousOn
  refine ⟨z, by simpa only [mem_sphere_iff_norm, sub_zero] using hz, le_antisymm ?_ ?_⟩
  · exact le_csSup (wvMaximumModulus_bddAbove hH r) ⟨z, hz, rfl⟩
  · apply csSup_le
    · exact ⟨‖H z‖, ⟨z, hz, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hmax hw

theorem wv_norm_le_maximumModulus_of_le {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖H z‖ ≤ wvMaximumModulus H r := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)))
    hH.diffContOnCl
  · intro w hw
    rw [frontier_ball (0 : ℂ) hr.ne'] at hw
    apply wv_norm_le_maximumModulus hH.continuous
    simpa only [mem_sphere_iff_norm, sub_zero] using hw
  · rw [closure_ball (0 : ℂ) hr.ne']
    simpa only [mem_closedBall, dist_zero_right] using hz

theorem wvMaximumModulus_mono {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    MonotoneOn (wvMaximumModulus H) (Ioi 0) := by
  intro r hr R hR hrR
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained hH.continuous hr.le
  rw [← hmax]
  exact wv_norm_le_maximumModulus_of_le hH hR (hz.le.trans hrR)

theorem wvMaximumModulus_pos {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∃ z, H z ≠ 0) {r : ℝ} (hr : 0 < r) : 0 < wvMaximumModulus H r := by
  by_contra hpos
  have hzero : wvMaximumModulus H r = 0 :=
    le_antisymm (le_of_not_gt hpos) (wvMaximumModulus_nonneg H r)
  have hevent : H =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    apply norm_eq_zero.mp
    have hh := wv_norm_le_maximumModulus_of_le hH hr
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz))
    rw [hzero] at hh
    exact le_antisymm hh (norm_nonneg _)
  have hHa : AnalyticOnNhd ℂ H univ := fun z _ => hH.analyticAt z
  have hall := hHa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0 : ℂ)) hevent
  obtain ⟨z, hz⟩ := hne
  exact hz (hall (mem_univ z))

theorem wvLogMaximum_monotone {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∃ z, H z ≠ 0) : Monotone (wvLogMaximum H) := by
  intro x y hxy
  exact Real.log_le_log (wvMaximumModulus_pos hH hne (Real.exp_pos x))
    (wvMaximumModulus_mono hH (Real.exp_pos x) (Real.exp_pos y) (Real.exp_le_exp.mpr hxy))

theorem wvMaximumModulus_three_lines {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {l u x : ℝ} (hlu : l < u) (hx : x ∈ Icc l u) :
    wvMaximumModulus H (Real.exp x) ≤
      wvMaximumModulus H (Real.exp l) ^ (1 - (x - l) / (u - l)) *
        wvMaximumModulus H (Real.exp u) ^ ((x - l) / (u - l)) := by
  let F : ℂ → ℂ := H ∘ Complex.exp
  have hF : Differentiable ℂ F := hH.comp Complex.differentiable_exp
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨wvMaximumModulus H (Real.exp u), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    apply wv_norm_le_maximumModulus_of_le hH (Real.exp_pos u)
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hw.2
  have hedge (t : ℝ) : ∀ w ∈ Complex.re ⁻¹' {t},
      ‖F w‖ ≤ wvMaximumModulus H (Real.exp t) := by
    intro w hw
    apply wv_norm_le_maximumModulus hH.continuous
    rw [Complex.norm_exp, show w.re = t from hw]
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained hH.continuous (Real.exp_pos x).le
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact (Real.exp_pos x).ne' hz.symm
  have hre : (Complex.log z).re = x := by rw [Complex.log_re, hz, Real.log_exp]
  have hh := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu (z := Complex.log z)
      (by simpa only [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage, hre] using hx)
      hF.diffContOnCl hB (hedge l) (hedge u)
  rw [show F (Complex.log z) = H z by dsimp only [F, Function.comp_def]; rw [Complex.exp_log hz0],
    hmax, hre] at hh
  exact hh

theorem wvLogMaximum_three_lines {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∃ z, H z ≠ 0) {l u x : ℝ} (hlu : l < u) (hx : x ∈ Icc l u) :
    wvLogMaximum H x ≤ (1 - (x - l) / (u - l)) * wvLogMaximum H l +
      ((x - l) / (u - l)) * wvLogMaximum H u := by
  have hl := wvMaximumModulus_pos hH hne (Real.exp_pos l)
  have hu := wvMaximumModulus_pos hH hne (Real.exp_pos u)
  have hh := Real.log_le_log (wvMaximumModulus_pos hH hne (Real.exp_pos x))
    (wvMaximumModulus_three_lines hH hlu hx)
  rw [Real.log_mul (Real.rpow_pos_of_pos hl _).ne' (Real.rpow_pos_of_pos hu _).ne',
    Real.log_rpow hl, Real.log_rpow hu] at hh
  exact hh

theorem wvLogMaximum_convex {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∃ z, H z ≠ 0) : ConvexOn ℝ univ (wvLogMaximum H) := by
  apply convexOn_of_slope_mono_adjacent convex_univ
  intro x y z _ _ hxy hyz
  have hzx : 0 < z - x := sub_pos.mpr (hxy.trans hyz)
  have hh := wvLogMaximum_three_lines hH hne (hxy.trans hyz) ⟨hxy.le, hyz.le⟩
  have heq : (1 - (y - x) / (z - x)) * wvLogMaximum H x +
      ((y - x) / (z - x)) * wvLogMaximum H z =
      ((z - y) * wvLogMaximum H x + (y - x) * wvLogMaximum H z) / (z - x) := by
    field_simp
    ring
  rw [heq, le_div_iff₀ hzx] at hh
  apply (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hyz)).mpr
  nlinarith

end Bruck
