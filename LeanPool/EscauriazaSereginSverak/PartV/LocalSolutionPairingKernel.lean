/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Convolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# The heat kernel gradient against a fixed test field

For a smooth compactly supported test field `ψ`, the pairing
`K_ij(y, r) = ∫ ψ_i(x) ∂_jΓ(x - y, r) dx` is, after an integration by parts,
minus the heat semigroup applied to `∂_jψ_i`. It is therefore bounded by a
multiple of `(1 + |y|)^{-3}` uniformly in `r`, continuous in `r ≠ 0`, and
vanishes for `r ≤ 0`. Without the integration by parts, the absolute pairing
is bounded by `r^{-1/2} (1 + |y|)^{-3}`. These are the kernel estimates behind
the time continuity of the forced heat response in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem heatKernel_space_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (fun x : Vec3 => heatKernel x r) := by
  have heq : (fun x : Vec3 => heatKernel x r) = fun x : Vec3 =>
      (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / (4 * r)) := by
    funext x
    exact heatKernel_eq_formula_sum hr
  rw [heq]
  fun_prop

private theorem heatKernel_space_differentiable {r : ℝ} (hr : 0 < r) :
    Differentiable ℝ (fun x : Vec3 => heatKernel x r) := by
  have heq : (fun x : Vec3 => heatKernel x r) = fun x : Vec3 =>
      (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / (4 * r)) := by
    funext x
    exact heatKernel_eq_formula_sum hr
  rw [heq]
  fun_prop

private theorem heatKernel_space_even (w : Vec3) (r : ℝ) :
    heatKernel (-w) r = heatKernel w r := by
  simp only [heatKernel, Pi.neg_apply, neg_sq]

private theorem one_add_norm_rpow_neg_three (y : Vec3) :
    (1 + ‖y‖) ^ (-3 : ℝ) = ((1 + ‖y‖) ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- The heat semigroup applied to `|φ|`, for a continuous compactly supported
`φ`, decays like `(1 + |y|)^{-3}` uniformly in time. -/
theorem heatKernel_shift_abs_integral_le {φ : Vec3 → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Vec3) (r : ℝ), 0 < r →
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤ M * (1 + ‖y‖) ^ (-3 : ℝ) := by
  obtain ⟨R, hRone, hRball⟩ :=
    hφc.isCompact.isBounded.subset_closedBall_lt 1 (0 : Vec3)
  have hRpos : 0 < R := lt_trans zero_lt_one hRone
  have hBdd : BddAbove (Set.range (fun x : Vec3 => ‖φ x‖)) :=
    hφ.norm.bddAbove_range_of_hasCompactSupport hφc.norm
  set B : ℝ := ⨆ x : Vec3, ‖φ x‖ with hBdef
  have hB (x : Vec3) : |φ x| ≤ B := by
    rw [← Real.norm_eq_abs]
    exact le_ciSup hBdd x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsupp (x : Vec3) (hx : φ x ≠ 0) : ‖x‖ ≤ R := by
    have hmem := hRball (subset_tsupport φ hx)
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  set I : ℝ := ∫ x : Vec3, |φ x| with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => abs_nonneg _
  have habsint : Integrable (fun x : Vec3 => |φ x|) :=
    hφ.abs.integrable_of_hasCompactSupport hφc.abs
  have hint (y : Vec3) {r : ℝ} (hr : 0 < r) :
      Integrable (fun x : Vec3 => heatKernel (x - y) r * |φ x|) :=
    (((heatKernel_space_continuous hr).comp (continuous_id.sub continuous_const)).mul
      hφ.abs).integrable_of_hasCompactSupport hφc.abs.mul_left
  have hnear (y : Vec3) {r : ℝ} (hr : 0 < r) :
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤ B := by
    have hKint : Integrable (fun x : Vec3 => heatKernel (x - y) r * B) :=
      ((heatKernel_integrable hr).comp_sub_right y).mul_const B
    calc
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤ ∫ x : Vec3, heatKernel (x - y) r * B :=
        integral_mono (hint y hr) hKint fun x =>
          mul_le_mul_of_nonneg_left (hB x) (heatKernel_nonneg _ _)
      _ = B := by
        rw [integral_mul_const, integral_sub_right_eq_self (fun x : Vec3 => heatKernel x r) y,
          heatKernel_integral r hr, one_mul]
  have hfar (y : Vec3) (hy : 2 * R ≤ ‖y‖) {r : ℝ} (hr : 0 < r) :
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤ 64000 * I / (1 + ‖y‖) ^ 3 := by
    have hypos : 0 < ‖y‖ := by linarith only [hy, hRpos]
    have hpoint (x : Vec3) :
        heatKernel (x - y) r * |φ x| ≤ 64000 / (1 + ‖y‖) ^ 3 * |φ x| := by
      by_cases hx : φ x = 0
      · rw [hx, abs_zero, mul_zero, mul_zero]
      have hxR := hsupp x hx
      have hdist : ‖y‖ / 2 ≤ ‖x - y‖ := by
        have h1 := norm_sub_norm_le y x
        rw [norm_sub_rev] at h1
        linarith only [h1, hxR, hy]
      have hrho : ‖y‖ / 2 ≤ rhoTwo (x - y) r := by
        unfold rhoTwo
        have h1 := norm_le_vec3EuclideanNorm (x - y)
        have h2 := Real.sqrt_nonneg r
        linarith only [hdist, h1, h2]
      have hk : heatKernel (x - y) r ≤ 64000 / (1 + ‖y‖) ^ 3 := by
        calc
          heatKernel (x - y) r ≤ 1000 / rhoTwo (x - y) r ^ 3 := heatKernel_le_rho_inv_cube hr
          _ ≤ 1000 / (‖y‖ / 2) ^ 3 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact pow_le_pow_left₀ (by positivity) hrho 3
          _ ≤ 64000 / (1 + ‖y‖) ^ 3 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hn1 : 1 + ‖y‖ ≤ 2 * ‖y‖ := by linarith only [hy, hRone]
            have hcube : (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hn1 3
            nlinarith only [hcube]
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    calc
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤
          ∫ x : Vec3, 64000 / (1 + ‖y‖) ^ 3 * |φ x| :=
        integral_mono (hint y hr) (habsint.const_mul _) hpoint
      _ = 64000 * I / (1 + ‖y‖) ^ 3 := by
        rw [integral_const_mul]
        ring
  refine ⟨max (B * (1 + 2 * R) ^ 3) (64000 * I), by positivity, ?_⟩
  intro y r hr
  have hden : 0 < (1 + ‖y‖) ^ 3 := by positivity
  rw [one_add_norm_rpow_neg_three, ← div_eq_mul_inv]
  by_cases hy : ‖y‖ < 2 * R
  · rw [le_div_iff₀ hden]
    have hpow : (1 + ‖y‖) ^ 3 ≤ (1 + 2 * R) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hy]) 3
    calc
      (∫ x : Vec3, heatKernel (x - y) r * |φ x|) * (1 + ‖y‖) ^ 3 ≤
          B * (1 + 2 * R) ^ 3 :=
        mul_le_mul (hnear y hr) hpow hden.le hB0
      _ ≤ _ := le_max_left _ _
  · calc
      ∫ x : Vec3, heatKernel (x - y) r * |φ x| ≤ 64000 * I / (1 + ‖y‖) ^ 3 :=
        hfar y (le_of_not_gt hy) hr
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hden.le

/-- Each spatial derivative of the heat kernel is bounded by `r^{-1/2}` times the
heat kernel at the doubled time. -/
theorem heatKernelSpaceDerivative_abs_le_doubled {z : Vec3} {r : ℝ} (hr : 0 < r)
    (j : Fin 3) :
    |heatKernelSpaceDerivative z r j| ≤ 400 * (Real.sqrt r)⁻¹ * heatKernel z (2 * r) := by
  have hcomp : |heatKernelSpaceDerivative z r j| ≤ heatKernelGradientNorm z r := by
    unfold heatKernelGradientNorm
    exact Finset.single_le_sum (f := fun k => |heatKernelSpaceDerivative z r k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  refine hcomp.trans ((heatKernelGradientNorm_le_majorant hr).trans ?_)
  have h2r : 0 < 2 * r := by positivity
  rw [heatKernel_eq_formula_sum h2r]
  simp only [heatKernelGradientMajorant, hr, ↓reduceIte]
  have hexp : Real.exp (-(∑ i, z i ^ 2) / (8 * r)) =
      Real.exp (-(∑ i, z i ^ 2) / (4 * (2 * r))) := by
    congr 1
    ring
  rw [hexp]
  have hbase : 0 < 4 * Real.pi * r := by positivity
  have hpref : (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) ≤
      4 * (4 * Real.pi * (2 * r)) ^ (-(3 : ℝ) / 2) := by
    rw [show 4 * Real.pi * (2 * r) = 2 * (4 * Real.pi * r) by ring,
      Real.mul_rpow (by norm_num) hbase.le]
    have h2 : (1 : ℝ) ≤ 4 * (2 : ℝ) ^ (-(3 : ℝ) / 2) := by
      have hle : (2 : ℝ) ^ (-(2 : ℝ)) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h4 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_two]
        norm_num
      linarith only [hle, h4]
    have hp : 0 ≤ (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) := by positivity
    nlinarith only [h2, hp]
  have hs : 0 ≤ (Real.sqrt r)⁻¹ := by positivity
  have he : 0 ≤ Real.exp (-(∑ i, z i ^ 2) / (4 * (2 * r))) := (Real.exp_pos _).le
  calc
    100 * ((Real.sqrt r)⁻¹ * (4 * Real.pi * r) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, z i ^ 2) / (4 * (2 * r)))) ≤
        100 * ((Real.sqrt r)⁻¹ * (4 * (4 * Real.pi * (2 * r)) ^ (-(3 : ℝ) / 2)) *
          Real.exp (-(∑ i, z i ^ 2) / (4 * (2 * r)))) := by
      gcongr
    _ = 400 * (Real.sqrt r)⁻¹ * ((4 * Real.pi * (2 * r)) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, z i ^ 2) / (4 * (2 * r)))) := by ring

/-- The pairing `K_ij(y, r) = ∫ ψ_i(x) ∂_jΓ(x - y, r) dx` of the spatial
derivative of the heat kernel, centred at `y`, with a component of a test
field. -/
@[expose] def testKernelPairing (ψ : Vec3 → Vec3) (i j : Fin 3) (y : Vec3) (r : ℝ) : ℝ :=
  ∫ x : Vec3, ψ x i * heatKernelSpaceDerivative (x - y) r j

/-- The test pairing vanishes at nonpositive times. -/
theorem testKernelPairing_of_nonpos (ψ : Vec3 → Vec3) (i j : Fin 3) (y : Vec3) {r : ℝ}
    (hr : r ≤ 0) : testKernelPairing ψ i j y r = 0 := by
  simp [testKernelPairing, heatKernelSpaceDerivative, not_lt.2 hr]

/-- The test pairing is jointly measurable in the centre and the time. -/
theorem testKernelPairing_measurable (ψ : Vec3 → Vec3) (hψ : Continuous ψ) (i j : Fin 3) :
    Measurable (fun q : Vec3 × ℝ => testKernelPairing ψ i j q.1 q.2) := by
  have hf : StronglyMeasurable (Function.uncurry fun (q : Vec3 × ℝ) (x : Vec3) =>
      ψ x i * heatKernelSpaceDerivative (x - q.1) q.2 j) := by
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · exact ((continuous_apply i).comp hψ).measurable.comp measurable_snd
    · exact (heatKernelSpaceDerivative_vecTime_measurable j).comp
        ((measurable_snd.sub (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst))
  exact (StronglyMeasurable.integral_prod_right (ν := (volume : Measure Vec3)) hf).measurable

/-- The derivative field `x ↦ ∂_jψ_i(x)` of a test field. -/
private theorem testField_partial_contDiff {ψ : Vec3 → Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ (fun w : Vec3 => ψ w i) x (CKN.basisVec j)) :=
  ((contDiff_pi.1 hψ i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem testField_partial_hasCompactSupport {ψ : Vec3 → Vec3}
    (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    HasCompactSupport (fun x : Vec3 => fderiv ℝ (fun w : Vec3 => ψ w i) x (CKN.basisVec j)) :=
  (hψc.comp_left (g := fun v : Vec3 => v i) rfl).fderiv_apply (𝕜 := ℝ) _

/-- Integration by parts: at positive times the test pairing is minus the heat
semigroup applied to `∂_jψ_i`. -/
theorem testKernelPairing_eq_neg_heatConv {ψ : Vec3 → Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) (y : Vec3)
    {r : ℝ} (hr : 0 < r) :
    testKernelPairing ψ i j y r =
      -heatConv r (fun x : Vec3 => fderiv ℝ (fun w : Vec3 => ψ w i) x (CKN.basisVec j)) y := by
  set g : Vec3 → ℝ := fun w => ψ w i with hgdef
  set φ : Vec3 → ℝ := fun x => fderiv ℝ g x (CKN.basisVec j) with hφdef
  set f : Vec3 → ℝ := fun x => heatKernel (x - y) r with hfdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_pi.1 hψ i
  have hgc : HasCompactSupport g := hψc.comp_left (g := fun v : Vec3 => v i) rfl
  have hφ : Continuous φ := (testField_partial_contDiff hψ i j).continuous
  have hφc : HasCompactSupport φ := testField_partial_hasCompactSupport hψc i j
  have hfc : Continuous f :=
    (heatKernel_space_continuous hr).comp (continuous_id.sub continuous_const)
  have hfd (x : Vec3) : DifferentiableAt ℝ f x :=
    ((heatKernel_space_differentiable hr) (x - y)).comp x
      ((differentiableAt_id).sub_const y)
  have hDf (x : Vec3) : fderiv ℝ f x (CKN.basisVec j) = heatKernelSpaceDerivative (x - y) r j := by
    have hcomp : fderiv ℝ f x = (fderiv ℝ (fun z : Vec3 => heatKernel z r) (x - y)).comp
        (fderiv ℝ (fun w : Vec3 => w - y) x) :=
      fderiv_comp x ((heatKernel_space_differentiable hr) (x - y))
        ((differentiableAt_id).sub_const y)
    rw [hcomp, fderiv_sub_const, fderiv_fun_id, ContinuousLinearMap.comp_id]
    exact heatKernel_fderiv_apply_basisVec hr j
  have hDfc : Continuous (fun x : Vec3 => heatKernelSpaceDerivative (x - y) r j) := by
    have heq : (fun x : Vec3 => heatKernelSpaceDerivative (x - y) r j) =
        fun x => -((x - y) j) / (2 * r) * heatKernel (x - y) r := by
      funext x
      simp only [heatKernelSpaceDerivative, hr, ↓reduceIte]
    rw [heq]
    exact ((continuous_apply j).comp (continuous_id.sub continuous_const)).neg.div_const _
      |>.mul hfc
  have h1 : Integrable (fun x => fderiv ℝ g x (CKN.basisVec j) * f x) :=
    (hφ.mul hfc).integrable_of_hasCompactSupport hφc.mul_right
  have h2 : Integrable (fun x => g x * fderiv ℝ f x (CKN.basisVec j)) := by
    simp_rw [hDf]
    exact (hg.continuous.mul hDfc).integrable_of_hasCompactSupport hgc.mul_right
  have h3 : Integrable (fun x => g x * f x) :=
    (hg.continuous.mul hfc).integrable_of_hasCompactSupport hgc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hg.differentiable (by simp)) x) (fun x _ => hfd x)
  have hleft : testKernelPairing ψ i j y r = ∫ x, g x * fderiv ℝ f x (CKN.basisVec j) := by
    simp_rw [hDf]
    rfl
  rw [hleft, hibp, heatConv_eq_integral]
  congr 1
  rw [← integral_sub_left_eq_self (fun x : Vec3 => φ x * f x) volume y]
  congr 1
  funext w
  simp only [hfdef, hφdef, sub_sub_cancel_left, heatKernel_space_even]
  ring

/-- The test pairing is bounded by a multiple of `(1 + |y|)^{-3}`, uniformly in time. -/
theorem testKernelPairing_abs_le {ψ : Vec3 → Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Vec3) (r : ℝ),
      |testKernelPairing ψ i j y r| ≤ M * (1 + ‖y‖) ^ (-3 : ℝ) := by
  set φ : Vec3 → ℝ := fun x => fderiv ℝ (fun w : Vec3 => ψ w i) x (CKN.basisVec j) with hφdef
  have hφ : Continuous φ := (testField_partial_contDiff hψ i j).continuous
  have hφc : HasCompactSupport φ := testField_partial_hasCompactSupport hψc i j
  obtain ⟨M, hM0, hM⟩ := heatKernel_shift_abs_integral_le hφ hφc
  refine ⟨M, hM0, fun y r => ?_⟩
  by_cases hr : 0 < r
  · rw [testKernelPairing_eq_neg_heatConv hψ hψc i j y hr, abs_neg, heatConv_eq_integral]
    have hsub : (∫ w : Vec3, heatKernel w r * φ (y - w)) = ∫ x : Vec3, heatKernel (x - y) r * φ x := by
      rw [← integral_sub_left_eq_self (fun x : Vec3 => heatKernel (x - y) r * φ x) volume y]
      congr 1
      funext w
      simp only [sub_sub_cancel_left, heatKernel_space_even]
    rw [hsub, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans (le_of_eq ?_) (hM y r hr)
    congr 1
    funext x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _)]
  · rw [testKernelPairing_of_nonpos ψ i j y (le_of_not_gt hr), abs_zero]
    positivity

/-- The test pairing is continuous in time away from `r = 0`. -/
theorem testKernelPairing_continuousAt {ψ : Vec3 → Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) (y : Vec3)
    {r₀ : ℝ} (hr₀ : r₀ ≠ 0) :
    ContinuousAt (fun r : ℝ => testKernelPairing ψ i j y r) r₀ := by
  rcases lt_or_gt_of_ne hr₀ with hneg | hpos
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 r₀] fun r => testKernelPairing ψ i j y r := by
      filter_upwards [Iio_mem_nhds hneg] with r hr
      exact (testKernelPairing_of_nonpos ψ i j y (le_of_lt hr)).symm
    exact continuousAt_const.congr hev
  · have hev : (fun r : ℝ => -heatConv r (fun x : Vec3 =>
        fderiv ℝ (fun w : Vec3 => ψ w i) x (CKN.basisVec j)) y) =ᶠ[𝓝 r₀]
        fun r => testKernelPairing ψ i j y r := by
      filter_upwards [Ioi_mem_nhds hpos] with r hr
      exact (testKernelPairing_eq_neg_heatConv hψ hψc i j y hr).symm
    refine ContinuousAt.congr ?_ hev
    exact ((heatConv_hasDerivAt_integral_smooth (testField_partial_contDiff hψ i j)
      (testField_partial_hasCompactSupport hψc i j) hpos y).continuousAt).neg

/-- Without integration by parts, the absolute test pairing is bounded by
`r^{-1/2} (1 + |y|)^{-3}`. -/
theorem testKernelPairing_lintegral_le {ψ : Vec3 → Vec3}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Vec3) (r : ℝ),
      ∫⁻ x : Vec3, ‖ψ x i * heatKernelSpaceDerivative (x - y) r j‖ₑ ≤
        ENNReal.ofReal (M * (Real.sqrt r)⁻¹ * (1 + ‖y‖) ^ (-3 : ℝ)) := by
  set φ : Vec3 → ℝ := fun x => ψ x i with hφdef
  have hφ : Continuous φ := (continuous_apply i).comp hψ
  have hφc : HasCompactSupport φ := hψc.comp_left (g := fun v : Vec3 => v i) rfl
  obtain ⟨M, hM0, hM⟩ := heatKernel_shift_abs_integral_le hφ hφc
  refine ⟨400 * M, by positivity, fun y r => ?_⟩
  by_cases hr : 0 < r
  · have h2r : 0 < 2 * r := by positivity
    have hint : Integrable (fun x : Vec3 => 400 * (Real.sqrt r)⁻¹ *
        (heatKernel (x - y) (2 * r) * |φ x|)) :=
      ((((heatKernel_space_continuous h2r).comp (continuous_id.sub continuous_const)).mul
        hφ.abs).integrable_of_hasCompactSupport hφc.abs.mul_left).const_mul _
    have hpoint (x : Vec3) : ‖ψ x i * heatKernelSpaceDerivative (x - y) r j‖ₑ ≤
        ENNReal.ofReal (400 * (Real.sqrt r)⁻¹ * (heatKernel (x - y) (2 * r) * |φ x|)) := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hk := heatKernelSpaceDerivative_abs_le_doubled (z := x - y) hr j
      calc
        |ψ x i| * |heatKernelSpaceDerivative (x - y) r j| ≤
            |ψ x i| * (400 * (Real.sqrt r)⁻¹ * heatKernel (x - y) (2 * r)) :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg _)
        _ = 400 * (Real.sqrt r)⁻¹ * (heatKernel (x - y) (2 * r) * |φ x|) := by
          simp only [hφdef]
          ring
    calc
      ∫⁻ x : Vec3, ‖ψ x i * heatKernelSpaceDerivative (x - y) r j‖ₑ ≤
          ∫⁻ x : Vec3, ENNReal.ofReal (400 * (Real.sqrt r)⁻¹ *
            (heatKernel (x - y) (2 * r) * |φ x|)) := lintegral_mono hpoint
      _ = ENNReal.ofReal (∫ x : Vec3, 400 * (Real.sqrt r)⁻¹ *
            (heatKernel (x - y) (2 * r) * |φ x|)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by
          have := heatKernel_nonneg (x - y) (2 * r)
          positivity)).symm
      _ ≤ ENNReal.ofReal (400 * M * (Real.sqrt r)⁻¹ * (1 + ‖y‖) ^ (-3 : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        have hb := hM y (2 * r) h2r
        have hs : 0 ≤ 400 * (Real.sqrt r)⁻¹ := by positivity
        calc
          400 * (Real.sqrt r)⁻¹ * ∫ x : Vec3, heatKernel (x - y) (2 * r) * |φ x| ≤
              400 * (Real.sqrt r)⁻¹ * (M * (1 + ‖y‖) ^ (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hb hs
          _ = 400 * M * (Real.sqrt r)⁻¹ * (1 + ‖y‖) ^ (-3 : ℝ) := by ring
  · have hzero : (fun x : Vec3 => ‖ψ x i * heatKernelSpaceDerivative (x - y) r j‖ₑ) =
        fun _ => 0 := by
      funext x
      simp [heatKernelSpaceDerivative, hr]
    rw [hzero, lintegral_zero]
    exact zero_le

end ESS

end
