/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.MatchedPair.ScaledPoincare

/-!
# UnitCubeDirichletPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# An explicit Dirichlet Poincaré constant on the unit cube

The upstream general-domain theorem selects an unspecified constant.  On the unit axis cube,
integration by parts in one coordinate gives the closed constant `1`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity

open MeasureTheory HCPolySupport
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-- Closed Dirichlet Poincaré constant used by the small-contrast chain. -/
def unitCubeDirichletPoincareExplicit (_d : ℕ) : ℝ := 1

theorem unitCubeDirichletPoincareExplicit_nonneg (d : ℕ) :
    0 ≤ unitCubeDirichletPoincareExplicit d := by
  simp only [unitCubeDirichletPoincareExplicit]
  norm_num

private theorem smooth_unitCube_integral_sq_eq [NeZero d]
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, φ x ^ 2 ∂volume =
      -2 * ∫ x, (x (0 : Fin d) - 1 / 2) * φ x *
        (fderiv ℝ φ x) (basisVec (0 : Fin d)) ∂volume := by
  let i : Fin d := 0
  let q : Vec d → ℝ := fun x => x i - 1 / 2
  let φ2 : Vec d → ℝ := fun x => φ x ^ 2
  have hqSmooth : ContDiff ℝ (⊤ : ℕ∞) q := by
    dsimp only [q]
    fun_prop
  have hφ2Smooth : ContDiff ℝ (⊤ : ℕ∞) φ2 := by
    exact hφ.pow 2
  have hqDiff : Differentiable ℝ q := hqSmooth.differentiable (by simp)
  have hφ2Diff : Differentiable ℝ φ2 := hφ2Smooth.differentiable (by simp)
  have hφ2c : HasCompactSupport φ2 := by
    simpa only [φ2, pow_two] using! hφc.mul_left (f := φ)
  have hDφ2c : HasCompactSupport (fun x => (fderiv ℝ φ2 x) (basisVec i)) :=
    hφ2c.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hqφ2 : Integrable (fun x => q x * φ2 x) volume := by
    exact (hqDiff.continuous.mul hφ2Diff.continuous).integrable_of_hasCompactSupport
      hφ2c.mul_left
  have hDqφ2 : Integrable
      (fun x => (fderiv ℝ q x) (basisVec i) * φ2 x) volume := by
    exact ((hqSmooth.continuous_fderiv (by simp) |>.clm_apply continuous_const).mul
      hφ2Diff.continuous)
      |>.integrable_of_hasCompactSupport hφ2c.mul_left
  have hqDφ2 : Integrable
      (fun x => q x * (fderiv ℝ φ2 x) (basisVec i)) volume := by
    exact (hqDiff.continuous.mul
      (hφ2Smooth.continuous_fderiv (by simp) |>.clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport hDφ2c.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := q) (g := φ2) (v := basisVec i)
    hDqφ2 hqDφ2 hqφ2 (fun x _ => hqDiff x) (fun x _ => hφ2Diff x)
  have hDq : ∀ x : Vec d, (fderiv ℝ q x) (basisVec i) = 1 := by
    intro x
    have hderiv : HasFDerivAt q
        (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) x := by
      dsimp only [q]
      fun_prop
    rw [hderiv.fderiv]
    simp only [ContinuousLinearMap.proj_apply, basisVec_apply, ite_eq_left]
  have hDφ2 : ∀ x : Vec d,
      (fderiv ℝ φ2 x) (basisVec i) =
        2 * φ x * (fderiv ℝ φ x) (basisVec i) := by
    intro x
    have hφDiffAt : DifferentiableAt ℝ φ x :=
      hφ.differentiable (by simp) x
    have hderiv : HasFDerivAt φ2
        ((2 * φ x) • fderiv ℝ φ x) x := by
      simpa only [φ2, Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul, mul_one] using
        hφDiffAt.hasFDerivAt.pow 2
    rw [hderiv.fderiv]
    simp only [smul_apply, smul_eq_mul]
  simp_rw [hDq, hDφ2, one_mul] at hibp
  dsimp only [q, φ2, i] at hibp ⊢
  have hfactor :
      2 * ∫ x, (x 0 - 1 / 2) * φ x *
          (fderiv ℝ φ x) (basisVec 0) ∂volume =
        ∫ x, (x 0 - 1 / 2) *
          (2 * φ x * (fderiv ℝ φ x) (basisVec 0)) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hidentity :
      2 * ∫ x, (x 0 - 1 / 2) * φ x *
          (fderiv ℝ φ x) (basisVec 0) ∂volume =
        -∫ x, φ x ^ 2 ∂volume := hfactor.trans hibp
  linarith only [hidentity]

private theorem smooth_unitCube_dirichletPoincare [NeZero d]
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ)
    (hφQ : tsupport φ ⊆ axisCube (0 : Vec d) 1) :
    let u : H1Function (axisCube (0 : Vec d) 1) :=
      H1Function.ofContDiff (isOpen_axisCube 0 1) (hφ.of_le (by simp)) hφc
    ‖u.toScalarL2‖ ≤ u.gradientCoordL2NormSum := by
  let i : Fin d := 0
  let q : Vec d → ℝ := fun x => x i - 1 / 2
  let Dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let Wφ : Vec d → ℝ := fun x => q x * φ x
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hDφc : HasCompactSupport Dφ := by
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hDφcont : Continuous Dφ := by
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hWφcont : Continuous Wφ := by
    dsimp only [Wφ, q]
    exact (continuous_apply i |>.sub continuous_const).mul hφ.continuous
  have hWφc : HasCompactSupport Wφ := by
    exact hφc.mul_left
  have hφmem : MemLp φ 2 volume :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hDφmem : MemLp Dφ 2 volume :=
    hDφcont.memLp_of_hasCompactSupport hDφc
  have hWφmem : MemLp Wφ 2 volume :=
    hWφcont.memLp_of_hasCompactSupport hWφc
  let F : Lp ℝ 2 volume := hφmem.toLp φ
  let DF : Lp ℝ 2 volume := hDφmem.toLp Dφ
  let WF : Lp ℝ 2 volume := hWφmem.toLp Wφ
  have hq_bound : ∀ x : Vec d, |Wφ x| ≤ (1 / 2 : ℝ) * |φ x| := by
    intro x
    by_cases hx : φ x = 0
    · simp only [Wφ, hx, mul_zero, abs_zero, mul_zero, le_rfl]
    · have hxQ : x ∈ axisCube (0 : Vec d) 1 :=
        hφQ (subset_tsupport φ hx)
      have hxi := hxQ i (Set.mem_univ i)
      change 0 < x i ∧ x i < 0 + 1 at hxi
      have hqabs : |x i - 1 / 2| ≤ (1 / 2 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith only [hxi.1, hxi.2]
      dsimp only [Wφ, q]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hqabs (abs_nonneg (φ x))
  have hWF_le : ‖WF‖ ≤ (1 / 2 : ℝ) * ‖F‖ := by
    have hhalfF : ‖(1 / 2 : ℝ) • F‖ = (1 / 2 : ℝ) * ‖F‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← hhalfF]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hWφmem.coeFn_toLp, hφmem.coeFn_toLp,
      Lp.coeFn_smul (1 / 2 : ℝ) F]
      with x hW hF hhalf
    change WF x = Wφ x at hW
    change F x = φ x at hF
    change ((1 / 2 : ℝ) • F) x = (1 / 2 : ℝ) • F x at hhalf
    rw [hW, hhalf, hF]
    simpa only [smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hq_bound x
  have hinner : inner ℝ DF WF = ∫ x, Dφ x * Wφ x ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDφmem.coeFn_toLp, hWφmem.coeFn_toLp]
      with x hD hW
    change DF x = Dφ x at hD
    change WF x = Wφ x at hW
    rw [hD, hW]
    simp only [RCLike.inner_apply', RCLike.conj_to_real]
  have hnorm_sq : ‖F‖ ^ 2 = ∫ x, φ x ^ 2 ∂volume := by
    rw [show ‖F‖ = (eLpNorm φ 2 volume).toReal by
      simp only [F, Lp.norm_toLp]]
    exact HCPolySupport.toReal_eLpNorm_two_sq_eq_integral_sq hφmem
  have henergy : ‖F‖ ^ 2 = -2 * inner ℝ DF WF := by
    rw [hnorm_sq, hinner]
    have hsq := smooth_unitCube_integral_sq_eq hφ hφc
    dsimp only [Dφ, Wφ, q, i]
    calc
      ∫ x, φ x ^ 2 ∂volume =
          -2 * ∫ x, (x 0 - 1 / 2) * φ x *
            (fderiv ℝ φ x) (basisVec 0) ∂volume := hsq
      _ = -2 * ∫ x, (fderiv ℝ φ x) (basisVec 0) *
          ((x 0 - 1 / 2) * φ x) ∂volume := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        ring
  have henergy_le : ‖F‖ ^ 2 ≤ ‖DF‖ * ‖F‖ := by
    calc
      ‖F‖ ^ 2 = -2 * inner ℝ DF WF := henergy
      _ ≤ 2 * |inner ℝ DF WF| := by
        have h := neg_le_abs (inner ℝ DF WF)
        calc
          -2 * inner ℝ DF WF = 2 * (-inner ℝ DF WF) := by ring
          _ ≤ 2 * |inner ℝ DF WF| :=
            mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 2 * (‖DF‖ * ‖WF‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm DF WF) (by norm_num)
      _ ≤ ‖DF‖ * ‖F‖ := by
        have hDF0 : 0 ≤ ‖DF‖ := norm_nonneg _
        calc
          2 * (‖DF‖ * ‖WF‖) ≤ 2 * (‖DF‖ * ((1 / 2 : ℝ) * ‖F‖)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWF_le hDF0) (by norm_num)
          _ = ‖DF‖ * ‖F‖ := by ring
  have hFDF : ‖F‖ ≤ ‖DF‖ := by
    by_cases hFzero : ‖F‖ = 0
    · rw [hFzero]
      exact norm_nonneg _
    · have hFpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hFzero)
      have hmul : ‖F‖ * ‖F‖ ≤ ‖DF‖ * ‖F‖ := by
        simpa only [pow_two] using henergy_le
      exact (mul_le_mul_iff_left₀ hFpos).mp hmul
  let u : H1Function (axisCube (0 : Vec d) 1) :=
    H1Function.ofContDiff (isOpen_axisCube 0 1) hφ1 hφc
  have hFu : ‖u.toScalarL2‖ = ‖F‖ := by
    calc
      ‖u.toScalarL2‖ =
          (eLpNorm φ 2 (volume.restrict (axisCube (0 : Vec d) 1))).toReal := by
        rw [H1Function.toScalarL2, HCPolySupport.toScalarL2, Lp.norm_toLp]
        simp only [u, H1Function.ofContDiff]
      _ = (eLpNorm φ 2 volume).toReal := by
        rw [MeasureTheory.eLpNorm_restrict_eq_of_support_subset
          hφ.continuous.aestronglyMeasurable (fun x hx => hφQ (subset_tsupport φ hx))]
      _ = ‖F‖ := by simp only [F, Lp.norm_toLp]
  have hDFu : ‖DF‖ = ‖u.gradCoordToScalarL2 i‖ := by
    have hsupport : Function.support Dφ ⊆ axisCube (0 : Vec d) 1 := by
      intro x hx
      exact hφQ ((support_fderiv_subset (𝕜 := ℝ) (f := φ)) (by
        change fderiv ℝ φ x ≠ 0
        intro hzero
        apply hx
        simp only [Dφ, hzero, zero_apply]))
    calc
      ‖DF‖ = (eLpNorm Dφ 2 volume).toReal := by
        simp only [DF, Lp.norm_toLp]
      _ = (eLpNorm Dφ 2
          (volume.restrict (axisCube (0 : Vec d) 1))).toReal := by
        rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset
          hDφcont.aestronglyMeasurable hsupport]
      _ = ‖u.gradCoordToScalarL2 i‖ := by
        rw [H1Function.gradCoordToScalarL2, HCPolySupport.toScalarL2, Lp.norm_toLp]
        simp only [u, Dφ, H1Function.ofContDiff]
  change ‖u.toScalarL2‖ ≤ u.gradientCoordL2NormSum
  rw [hFu]
  calc
    ‖F‖ ≤ ‖DF‖ := hFDF
    _ = ‖u.gradCoordToScalarL2 i‖ := hDFu
    _ ≤ u.gradientCoordL2NormSum := by
      dsimp only [H1Function.gradientCoordL2NormSum]
      exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-- The unit axis cube has the explicit zero-trace Poincaré constant `1`. -/
theorem unitCubeDirichletPoincareExplicit_bound [NeZero d]
    (w : H10Function (axisCube (0 : Vec d) 1)) :
    ‖w.toH1Function.toScalarL2‖ ≤
      unitCubeDirichletPoincareExplicit d *
        w.toH1Function.gradientCoordL2NormSum := by
  let Q : Set (Vec d) := axisCube (0 : Vec d) 1
  let ψ : ℕ → H1Function Q := H10Function.approxH1 (isOpen_axisCube 0 1) w
  have hψ_bound : ∀ n, ‖(ψ n).toScalarL2‖ ≤ (ψ n).gradientCoordL2NormSum := by
    intro n
    simpa only [ψ, Q, H10Function.approxH1] using
      smooth_unitCube_dirichletPoincare
        (w.approx_smooth n) (w.approx_hasCompactSupport n)
        (w.approx_support_subset n)
  have hleft :
      Filter.Tendsto (fun n ↦ ‖(ψ n).toScalarL2‖) Filter.atTop
        (nhds ‖w.toH1Function.toScalarL2‖) := by
    simpa only [ψ, Q] using!
      ((continuous_norm.tendsto _).comp
        (H10Function.tendsto_approxH1_toScalarL2
          (hU := isOpen_axisCube 0 1) (u := w)))
  have hright :
      Filter.Tendsto (fun n ↦ (ψ n).gradientCoordL2NormSum) Filter.atTop
        (nhds w.toH1Function.gradientCoordL2NormSum) := by
    simpa only [ψ, Q] using
      (H10Function.tendsto_approxH1_gradientCoordL2NormSum
        (hU := isOpen_axisCube 0 1) (u := w))
  have hbound : ‖w.toH1Function.toScalarL2‖ ≤
      w.toH1Function.gradientCoordL2NormSum :=
    le_of_tendsto_of_tendsto' hleft hright hψ_bound
  simpa only [unitCubeDirichletPoincareExplicit, one_mul] using hbound

/-- Scaled zero-trace Poincaré inequality on an axis cube, with explicit
constant `1`. -/
theorem scaled_dirichlet_poincare_explicit_norm [NeZero d]
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (w : H10Function (axisCube z L)) :
    ‖w.toH1Function.toScalarL2‖ ≤
      unitCubeDirichletPoincareExplicit d * L *
        w.toH1Function.gradientCoordL2NormSum := by
  have heq1 : axisCube z L = translateSet z (axisCube (0 : Vec d) L) :=
    (translateSet_axisCube_zero z L).symm
  have heq2 : axisCube (0 : Vec d) L = L • axisCube (0 : Vec d) 1 :=
    (smul_axisCube_zero_one L hL).symm
  let w1 : H10Function (translateSet z (axisCube (0 : Vec d) L)) := heq1 ▸ w
  let w2 : H10Function (axisCube (0 : Vec d) L) := H10Function.untranslate z w1
  let w3 : H10Function (L • axisCube (0 : Vec d) 1) := heq2 ▸ w2
  let w4 : H10Function (axisCube (0 : Vec d) 1) := H10Function.unscale hL w3
  have hFpos : 0 < dilationL2Factor d L := dilationL2Factor_pos (d := d) hL
  have hvalNorm : ‖w4.toH1Function.toScalarL2‖ =
      dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖ := by
    have e1 : ‖w4.toH1Function.toScalarL2‖ =
        dilationL2Factor d L * ‖w3.toH1Function.toScalarL2‖ := by
      show ‖(H10Function.unscale hL w3).toH1Function.toScalarL2‖ = _
      rw [H10Function.unscale_toH1Function]
      exact H1Function.norm_toScalarL2_unscale_eq hL w3.toH1Function
    have e2 : ‖w3.toH1Function.toScalarL2‖ = ‖w2.toH1Function.toScalarL2‖ :=
      norm_toScalarL2_h10_congr heq2 w2
    have e3 : ‖w2.toH1Function.toScalarL2‖ = ‖w1.toH1Function.toScalarL2‖ := by
      show ‖(H10Function.untranslate z w1).toH1Function.toScalarL2‖ = _
      rw [H10Function.untranslate_toH1Function]
      exact norm_toScalarL2_untranslate_eq z w1.toH1Function
    have e4 : ‖w1.toH1Function.toScalarL2‖ = ‖w.toH1Function.toScalarL2‖ :=
      norm_toScalarL2_h10_congr heq1 w
    rw [e1, e2, e3, e4]
  have hgradNorm : w4.toH1Function.gradientCoordL2NormSum =
      L * dilationL2Factor d L * w.toH1Function.gradientCoordL2NormSum := by
    have e1 : w4.toH1Function.gradientCoordL2NormSum =
        L * dilationL2Factor d L * w3.toH1Function.gradientCoordL2NormSum := by
      show (H10Function.unscale hL w3).toH1Function.gradientCoordL2NormSum = _
      rw [H10Function.unscale_toH1Function]
      exact H1Function.gradientCoordL2NormSum_unscale_eq hL w3.toH1Function
    have e2 : w3.toH1Function.gradientCoordL2NormSum =
        w2.toH1Function.gradientCoordL2NormSum :=
      gradientCoordL2NormSum_h10_congr heq2 w2
    have e3 : w2.toH1Function.gradientCoordL2NormSum =
        w1.toH1Function.gradientCoordL2NormSum := by
      show (H10Function.untranslate z w1).toH1Function.gradientCoordL2NormSum = _
      rw [H10Function.untranslate_toH1Function]
      exact gradientCoordL2NormSum_untranslate_eq z w1.toH1Function
    have e4 : w1.toH1Function.gradientCoordL2NormSum =
        w.toH1Function.gradientCoordL2NormSum :=
      gradientCoordL2NormSum_h10_congr heq1 w
    rw [e1, e2, e3, e4]
  have hunit := unitCubeDirichletPoincareExplicit_bound (d := d) w4
  rw [hvalNorm, hgradNorm] at hunit
  have hcancel : dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖ ≤
      dilationL2Factor d L *
        (unitCubeDirichletPoincareExplicit d * L *
          w.toH1Function.gradientCoordL2NormSum) := by
    calc
      dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖
          ≤ unitCubeDirichletPoincareExplicit d *
              (L * dilationL2Factor d L *
                w.toH1Function.gradientCoordL2NormSum) := hunit
      _ = dilationL2Factor d L *
            (unitCubeDirichletPoincareExplicit d * L *
              w.toH1Function.gradientCoordL2NormSum) := by ring
  exact (mul_le_mul_iff_right₀ hFpos).mp hcancel

/-- Scaled zero-trace Poincaré inequality in `eLpNorm` form, with explicit
constant `1`. -/
theorem scaled_dirichlet_poincare_explicit [NeZero d]
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (w : H10Function (axisCube z L)) :
    (eLpNorm w.toH1Function.toFun 2
        (volumeMeasureOn (axisCube z L))).toReal ≤
      unitCubeDirichletPoincareExplicit d * L *
        ∑ i : Fin d,
          (eLpNorm (fun x ↦ w.toH1Function.grad x i) 2
            (volumeMeasureOn (axisCube z L))).toReal := by
  have h := scaled_dirichlet_poincare_explicit_norm z hL w
  rwa [norm_toScalarL2_eq, gradientCoordL2NormSum_eq_sum_eLpNorm] at h

end

end Algsuperdiff.StochasticProcess.Common.Regularity
