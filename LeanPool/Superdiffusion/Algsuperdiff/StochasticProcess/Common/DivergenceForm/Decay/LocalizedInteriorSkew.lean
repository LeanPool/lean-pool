/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SkewTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSplitMass
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# LocalizedInteriorSkew

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The local antisymmetric identity for bounded `H¹` functions

This file upgrades the antisymmetric transfer to the bounded `H¹` carrier
needed by an interior localization. No trace condition is imposed on the
function: every test is compactly supported in the domain.
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ}

/-- The clipped derivative used to form a square with bounded slope. -/
def clippedSquareSlope (M t : ℝ) : ℝ :=
  max (-2 * M) (min (2 * t) (2 * M))

private theorem continuous_clippedSquareSlope (M : ℝ) :
    Continuous (clippedSquareSlope M) := by
  exact continuous_const.max ((continuous_const.mul continuous_id).min continuous_const)

/-- The primitive of the clipped square slope, normalized to vanish at zero. -/
noncomputable def boundedSquare (M t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, clippedSquareSlope M s

private theorem boundedSquare_hasDerivAt (M t : ℝ) :
    HasDerivAt (boundedSquare M) (clippedSquareSlope M t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_clippedSquareSlope M).intervalIntegrable 0 t)
    ((continuous_clippedSquareSlope M).stronglyMeasurableAtFilter _ _)
    (continuous_clippedSquareSlope M).continuousAt

theorem boundedSquare_contDiff_one (M : ℝ) :
    ContDiff ℝ 1 (boundedSquare M) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (boundedSquare_hasDerivAt M t).differentiableAt, ?_⟩
  rw [show deriv (boundedSquare M) = clippedSquareSlope M from
    funext fun t => (boundedSquare_hasDerivAt M t).deriv]
  exact continuous_clippedSquareSlope M

theorem deriv_boundedSquare (M : ℝ) :
    deriv (boundedSquare M) = clippedSquareSlope M :=
  funext fun t => (boundedSquare_hasDerivAt M t).deriv

theorem abs_clippedSquareSlope_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    |clippedSquareSlope M t| ≤ 2 * M := by
  rw [abs_le]
  constructor
  · calc
      -(2 * M) = -2 * M := by ring
      _ ≤ max (-2 * M) (min (2 * t) (2 * M)) := le_max_left _ _
  · exact max_le (by linarith only [hM]) (min_le_right (2 * t) (2 * M))

private theorem clippedSquareSlope_eq {M t : ℝ}
    (ht : |t| ≤ M) : clippedSquareSlope M t = 2 * t := by
  have ht' := abs_le.mp ht
  rw [clippedSquareSlope, min_eq_left (by linarith only [ht'.2]),
    max_eq_right (by linarith only [ht'.1])]

theorem boundedSquare_eq_sq {M t : ℝ} (hM : 0 ≤ M)
    (ht : |t| ≤ M) : boundedSquare M t = t ^ 2 := by
  rw [boundedSquare]
  have hcongr : (∫ s in (0 : ℝ)..t, clippedSquareSlope M s) =
      ∫ s in (0 : ℝ)..t, 2 * s := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply clippedSquareSlope_eq
    rw [abs_le]
    rcases le_total 0 t with ht0 | ht0
    · rw [Set.uIcc_of_le ht0] at hs
      exact ⟨(neg_nonpos.mpr hM).trans hs.1, hs.2.trans (le_abs_self t |>.trans ht)⟩
    · rw [Set.uIcc_of_ge ht0] at hs
      exact ⟨(abs_le.mp ht).1.trans hs.1, hs.2.trans hM⟩
  rw [hcongr, intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The H¹ composition with the bounded-slope square function. -/
noncomputable def boundedSquareH1 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ᵐ x ∂volumeMeasureOn U, |u.toFun x| ≤ M) :
    H1Function U where
  toFun := fun x => boundedSquare M (u.toFun x)
  grad := fun x i => deriv (boundedSquare M) (u.toFun x) * u.grad x i
  memL2 := by
    refine MemLp.of_le (u.memL2.const_mul M)
      ((boundedSquare_contDiff_one M).continuous.comp_aestronglyMeasurable
        u.memL2.aestronglyMeasurable) ?_
    filter_upwards [hu] with x hx
    rw [boundedSquare_eq_sq hM hx]
    simp only [Real.norm_eq_abs, abs_mul, abs_sq, abs_of_nonneg hM]
    calc
      u.toFun x ^ 2 = |u.toFun x| * |u.toFun x| := by
        rw [← pow_two]
        exact (sq_abs (u.toFun x)).symm
      _ ≤ M * |u.toFun x| :=
        mul_le_mul_of_nonneg_right hx (abs_nonneg (u.toFun x))
  gradMemL2 := by
    intro i
    refine MemLp.of_le ((u.gradMemL2 i).const_mul (2 * M))
      ((((boundedSquare_contDiff_one M).continuous_deriv (by norm_num)).comp_aestronglyMeasurable
        u.memL2.aestronglyMeasurable).mul (u.gradMemL2 i).aestronglyMeasurable) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (by
        rw [deriv_boundedSquare]
        have hs := abs_clippedSquareSlope_le hM (u.toFun x)
        simpa only [abs_mul, abs_of_nonneg hM,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using hs)
      (abs_nonneg _)
  hasWeakGradient := hasWeakGradientOn_comp_of_deriv_bounded hU u
    (boundedSquare_contDiff_one M) (M := 2 * M) (by positivity)
    (fun t => by rw [deriv_boundedSquare]; exact abs_clippedSquareSlope_le hM t)

private theorem boundedSquareH1_toFun_ae {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ᵐ x ∂volumeMeasureOn U, |u.toFun x| ≤ M) :
    (boundedSquareH1 hU u M hM hu).toFun =ᵐ[volumeMeasureOn U]
      fun x => u.toFun x ^ 2 := by
  filter_upwards [hu] with x hx
  exact boundedSquare_eq_sq hM hx

private theorem boundedSquareH1_grad_ae {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ᵐ x ∂volumeMeasureOn U, |u.toFun x| ≤ M) :
    (boundedSquareH1 hU u M hM hu).grad =ᵐ[volumeMeasureOn U]
      fun x i => 2 * u.toFun x * u.grad x i := by
  filter_upwards [hu] with x hx
  funext i
  change deriv (boundedSquare M) (u.toFun x) * u.grad x i = _
  rw [deriv_boundedSquare, clippedSquareSlope_eq hx]

/-- For a bounded `H¹` function and a smooth multiplier supported in the
domain, a `C¹` skew field contributes only through its divergence. The
compactly supported multiplier removes the boundary term, so the function
itself need not have zero trace. -/
theorem integral_mul_vecDot_matVecMul_eq_half_interior
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {k : Vec d → Mat d} (hk : ∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q)
    (hskew : ∀ x : Vec d, matTranspose (k x) = -k x)
    (u : H1Function U) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U)
    {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volumeMeasureOn U, |u.toFun x| ≤ M) :
    (∫ x in U, u.toFun x *
        vecDot (matVecMul (k x) (u.grad x))
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume) =
      1 / 2 * ∫ x in U, u.toFun x ^ 2 *
        vecDot (skewFieldDiv k x)
          (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume := by
  classical
  let uSq : H1Function U := boundedSquareH1 hU u M hM hu
  let phi : H10Function U := H10Function.ofContDiff hU.isOpen hw hwc hwU
  have htransfer :=
    Algsuperdiff.Section5.Support.integral_vecDot_smul_matFieldDiv_eq_integral_vecDot_matVecMul
      hU hk hskew uSq phi
  have hval := boundedSquareH1_toFun_ae hU u hM hu
  have hgrad := boundedSquareH1_grad_ae hU u hM hu
  have hphiGrad : phi.toH1Function.grad =
      fun x i => (fderiv ℝ w x) (basisVec i) := rfl
  have hleft : (∫ x in U,
      vecDot (uSq.toFun x • Algsuperdiff.Section5.Support.matFieldDiv k x)
        (phi.toH1Function.grad x) ∂volume) =
      ∫ x in U, u.toFun x ^ 2 * vecDot (skewFieldDiv k x)
        (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hval] with x hx
    rw [hx, hphiGrad]
    change vecDot ((u.toFun x ^ 2) • skewFieldDiv k x)
      (fun i => (fderiv ℝ w x) (basisVec i)) = _
    rw [vecDot_smul_left]
  have hright : (∫ x in U,
      vecDot (matVecMul (k x) (uSq.grad x))
        (phi.toH1Function.grad x) ∂volume) =
      2 * ∫ x in U, u.toFun x * vecDot (matVecMul (k x) (u.grad x))
        (fun i => (fderiv ℝ w x) (basisVec i)) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx, hphiGrad]
    change vecDot (matVecMul (k x) ((2 * u.toFun x) • u.grad x))
      (fun i => (fderiv ℝ w x) (basisVec i)) = _
    rw [matVecMul_smul, vecDot_smul_left]
    ring
  rw [hleft, hright] at htransfer
  linarith only [htransfer]

end DivergenceFormProcess.Decay
