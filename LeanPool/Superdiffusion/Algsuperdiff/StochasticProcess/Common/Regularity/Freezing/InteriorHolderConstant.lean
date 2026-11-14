/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationInterior
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# InteriorHolderConstant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Quantitative interior Hoelder estimates for continuous skew coefficients.
-/

/-!
# The interior Hölder constant after freezing

`InteriorContinuity.lean` proves that a bounded solution with a continuous skew
part has a locally `C^{0,1/2}` representative, but its statements quantify the
Hölder constant existentially.  Several consumers need the constant itself: one
radius and one constant serving a whole family of data is what turns an
almost-everywhere statement into a pointwise one.

This file keeps the constant.  At an interior point the freezing radius comes
from the local contrast radius of `LocalContrast.lean`, which depends on the
coefficient, the point and the fixed Schauder threshold only, never on the
solution.  On the concentric half ball the constant returned by
`schauder_holder_euclideanBall_zerothOrder` is exactly
`penalizationInteriorHolderConstant d (1/2) (s/2) G (nu⁻¹ * M)`, where `G` is
any bound for the gradient size of the solution on the ball of radius `s` and
`2 * M` any bound for the essential size of the zeroth-order datum there.  The
constant therefore depends on the datum only through those two numbers, so it
is the same for every family of data with a common bound.

A compact subset of the domain admits one radius serving all of its points.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open DivergenceFormProcess.Form

noncomputable section

variable {d : ℕ}

/-- Rescaling a scalar datum rescales its essential-supremum size. -/
private theorem scalarLInfSizeOn_const_mul (W : Set (Vec d)) (c : ℝ)
    (g : Vec d → ℝ) :
    scalarLInfSizeOn W (fun x ↦ c * g x) = |c| * scalarLInfSizeOn W g := by
  unfold scalarLInfSizeOn
  have heq : (fun x ↦ c * g x) = c • g := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [heq, eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal (abs_nonneg c)]

open scoped Classical in
/-- The Schauder step of the freezing route on one ball, with the Hölder
constant kept.  The coefficient enters only through the frozen contrast data on
the ball and the measurability of the frozen coefficient truncated to it; its
ellipticity there is not needed, because the contrast bound already supplies
the Schauder estimate.  The solution and its datum enter only through the two
size bounds. -/
private theorem exists_holder_of_frozenContrast [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (z : Vec d) {s : ℝ} (hs : 0 < s)
    (hsmall : CoefficientIdentityDistanceLE (euclideanBall z s)
      (normalizedFrozenCoeff nu a z) (smallContrastThreshold d (1 / 2 : ℝ)))
    (hameas : Measurable fun x i j ↦
      if x ∈ euclideanBall z s then normalizedFrozenCoeff nu a z x i j else 0)
    (G M : ℝ) (u : H1Function (euclideanBall z s)) (g : Vec d → ℝ)
    (hgmem : MemScalarLInfOn (euclideanBall z s) g)
    (hgsize : scalarLInfSizeOn (euclideanBall z s) g ≤ 2 * M)
    (hgrad : vectorLpSizeOn (euclideanBall z s) 2 u.grad ≤ G)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall z s) u g 0) :
    ∃ v : Vec d → ℝ, ContinuousOn v (euclideanBall z (s / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall z s)] u.toFun ∧
      EuclideanHolderBoundOn (euclideanBall z (s / 2)) (1 / 2 : ℝ)
        (penalizationInteriorHolderConstant d (1 / 2 : ℝ) (s / 2) G
          (nu⁻¹ * M)) v := by
  classical
  have hk : matTranspose (a z - nu • (1 : Mat d)) =
      -(a z - nu • (1 : Mat d)) :=
    sub_scalar_one_isSkew_of_symmPart_eq (hsymm z)
  have hfrozen : IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x ↦ a x - (a z - nu • (1 : Mat d))) (euclideanBall z s) u g 0 :=
    (isMatrixDivFormWeakSolutionZerothOrderOn_sub_skew_const_iff hk).2 hu
  have hnormalized : IsMatrixDivFormWeakSolutionZerothOrderOn
      (normalizedFrozenCoeff nu a z) (euclideanBall z s) u
      (fun x ↦ nu⁻¹ * g x) 0 :=
    isMatrixDivFormWeakSolutionZerothOrderOn_const_smul_zero hfrozen
  have hgscaled : MemScalarLInfOn (euclideanBall z s) (fun x ↦ nu⁻¹ * g x) :=
    memScalarLInfOn_const_mul hgmem
  let aLocal : CoeffField d := fun x i j ↦
    if x ∈ euclideanBall z s then normalizedFrozenCoeff nu a z x i j else 0
  have hmeas : Measurable aLocal := by
    simpa only [aLocal] using! hameas
  have hsmallLocal : CoefficientIdentityDistanceLE (euclideanBall z s) aLocal
      (smallContrastThreshold d (1 / 2 : ℝ)) := by
    filter_upwards [hsmall, ae_restrict_mem (isOpen_euclideanBall z s).measurableSet]
      with x hx hxb
    simpa only [aLocal, hxb, ite_true] using hx
  have hnormalizedLocal : IsMatrixDivFormWeakSolutionZerothOrderOn
      aLocal (euclideanBall z s) u (fun x ↦ nu⁻¹ * g x) 0 := by
    intro phi
    have h := hnormalized phi
    have hlhs :
        (∫ x in euclideanBall z s, vecDot (matVecMul (aLocal x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          ∫ x in euclideanBall z s, vecDot
            (matVecMul (normalizedFrozenCoeff nu a z x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall z s).measurableSet]
        with x hx
      simp only [aLocal, hx, ite_true]
    rw [hlhs]
    exact h
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    schauder_holder_euclideanBall_zerothOrder z hs hd
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1)
      (smallContrastThreshold_nonneg d (by norm_num : (1 / 2 : ℝ) ≤ 1))
      le_rfl hmeas hsmallLocal hnormalizedLocal hgscaled
  refine ⟨v, hvcont, hvae, ?_⟩
  refine euclideanHolderBoundOn_mono ?_ hvholder
  have hpow1 : (0 : ℝ) ≤ s ^ (1 - (1 / 2 : ℝ) - (d : ℝ) / 2) :=
    Real.rpow_nonneg hs.le _
  have hpow2 : (0 : ℝ) ≤ s ^ (2 - (1 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hscaled : scalarLInfSizeOn (euclideanBall z s) (fun x ↦ nu⁻¹ * g x) ≤
      2 * (nu⁻¹ * M) := by
    rw [scalarLInfSizeOn_const_mul, abs_of_nonneg (inv_nonneg.mpr hnu.le)]
    calc nu⁻¹ * scalarLInfSizeOn (euclideanBall z s) g ≤ nu⁻¹ * (2 * M) :=
          mul_le_mul_of_nonneg_left hgsize (inv_nonneg.mpr hnu.le)
      _ = 2 * (nu⁻¹ * M) := by ring
  unfold penalizationInteriorHolderConstant
  rw [show 2 * (s / 2) = s by ring]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hgrad hpow1)
      (mul_le_mul_of_nonneg_left hscaled hpow2))
    (smallContrastZerothSchauderConstant_nonneg d)

/-- **Quantitative interior estimate at an interior point.**  At every point of
an open set carrying a coefficient with symmetric part `nu • 1` and continuous
skew part, one radius — the local contrast radius at that point — serves every
bounded zeroth-order weak solution on the ball of that radius: the Hölder
constant on the concentric half ball is the Schauder constant of the frozen
small-contrast estimate, and it depends on the solution and its datum only
through the gradient budget `G` and the essential budget `2 * M`. -/
theorem exists_frozenRadius_holder_of_continuousCoeff [NeZero d] (hd : 2 ≤ d)
    {U : Set (Vec d)} (hU : IsOpen U) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    {z : Vec d} (hz : z ∈ U) :
    ∃ s > 0, euclideanBall z s ⊆ U ∧
      ∀ (G M : ℝ) (u : H1Function (euclideanBall z s)) (g : Vec d → ℝ),
        MemScalarLInfOn (euclideanBall z s) g →
        scalarLInfSizeOn (euclideanBall z s) g ≤ 2 * M →
        vectorLpSizeOn (euclideanBall z s) 2 u.grad ≤ G →
        IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall z s) u g 0 →
        ∃ v : Vec d → ℝ, ContinuousOn v (euclideanBall z (s / 2)) ∧
          v =ᵐ[volume.restrict (euclideanBall z s)] u.toFun ∧
          EuclideanHolderBoundOn (euclideanBall z (s / 2)) (1 / 2 : ℝ)
            (penalizationInteriorHolderConstant d (1 / 2 : ℝ) (s / 2) G
              (nu⁻¹ * M)) v := by
  have hdelta : 0 < smallContrastThreshold d (1 / 2 : ℝ) := by
    unfold smallContrastThreshold
    positivity
  obtain ⟨R, hR, hRU, hsmall, hEllFrozen⟩ :=
    exists_ball_coefficientIdentityDistanceLE_normalizedFrozenCoeff
      hU hnu hsymm hcont hz hdelta
  exact ⟨R, hR, hRU, fun G M u g hgmem hgsize hgrad hu ↦
    exists_holder_of_frozenContrast hd hnu hsymm z hR hsmall hEllFrozen.1 G M u
      g hgmem hgsize hgrad hu⟩

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
