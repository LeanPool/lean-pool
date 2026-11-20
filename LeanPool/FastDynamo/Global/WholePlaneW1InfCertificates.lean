/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.BumpAffineScaling
public import LeanPool.FastDynamo.Global.ConstantCoefficientWeakForm

/-!
# Bounded `C¹` multipliers as `W¹,∞` certificates

This module builds quotient-level whole-plane `W¹,∞` certificates from bounded classically
differentiable functions on the transverse plane, recording actual representatives and their
actual coordinate derivatives rather than postulated Sobolev data.
`boundedC1WholePlaneW1InfCertificate` packages a bounded everywhere differentiable function and
its bounded classical coordinate derivatives, proves that the resulting quotient-level pair is a
weak-derivative jet, and identifies the stored value and derivatives almost everywhere with the
given functions.  `TorusSupportedH2Output` builds on it the `W²,∞` certificates of the input
and output bumps of the torus parametrix.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

namespace ConstantCoefficientBackground

/-! ## A bounded classical `C¹` function gives a `W¹,∞` certificate -/

/-- The `L∞` class represented by a bounded complex function. -/
def boundedComplexLInf (f : WholePlane → ℂ)
    (hf : AEStronglyMeasurable f volume) (bound : ℝ)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ bound) : WholePlaneScalarLInf :=
  (memLp_top_of_bound hf bound hbound).toLp f

/-- The `L∞` class built from a bounded measurable function is represented almost everywhere by
that very function. -/
theorem boundedComplexLInf_coe_ae (f : WholePlane → ℂ)
    (hf : AEStronglyMeasurable f volume) (bound : ℝ)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ bound) :
    (boundedComplexLInf f hf bound hbound : WholePlane → ℂ) =ᵐ[volume] f := by
  exact MemLp.coeFn_toLp _

/-- Package a bounded everywhere differentiable complex function and its
bounded classical coordinate derivatives as a whole-plane
`W¹,∞` multiplier. -/
def boundedC1WholePlaneW1InfCertificate
    (f : WholePlane → ℂ) (df : Fin 2 → WholePlane → ℂ)
    (f' : WholePlane → WholePlane →L[ℝ] ℂ)
    (hf' : ∀ x, HasFDerivAt f (f' x) x)
    (hcoord : ∀ x j, f' x (wholePlaneBasis j) = df j x)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ) (hdfBound : ∀ j x, ‖df j x‖ ≤ dfBound j)
    (hdfMeasurable : ∀ j, AEStronglyMeasurable (df j) volume) :
    WholePlaneScalarW1InfCertificate where
  value := boundedComplexLInf f
    ((continuous_iff_continuousAt.mpr fun x ↦
      (hf' x).continuousAt).aestronglyMeasurable) fBound
    (ae_of_all volume hfBound)
  deriv j := boundedComplexLInf (df j) (hdfMeasurable j) (dfBound j)
    (ae_of_all volume (hdfBound j))
  hasWeakDerivative j := by
    have hfContinuous : Continuous f :=
      continuous_iff_continuousAt.mpr fun x ↦ (hf' x).continuousAt
    let hfMem : MemLp f ∞ (volume : Measure WholePlane) :=
      memLp_top_of_bound hfContinuous.aestronglyMeasurable fBound
        (ae_of_all volume hfBound)
    let hdfMem : MemLp (df j) ∞ (volume : Measure WholePlane) :=
      memLp_top_of_bound (hdfMeasurable j) (dfBound j)
        (ae_of_all volume (hdfBound j))
    unfold HasWholePlaneLInfWeakDerivative
    ext phi
    simp only [TemperedDistribution.lineDerivOp_apply_apply,
      wholePlaneLInfToTempered,
      MeasureTheory.Lp.toTemperedDistributionCLM_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hphiDeriv : ∀ x,
        fderiv ℝ (fun y : WholePlane ↦ phi y) x (wholePlaneBasis j) =
          (∂_{wholePlaneBasis j} phi) x := by
      intro x
      rw [(phi.hasFDerivAt x).fderiv]
      rfl
    have hfDeriv : ∀ x,
        fderiv ℝ f x (wholePlaneBasis j) = df j x := by
      intro x
      rw [(hf' x).fderiv, hcoord]
    have hleft : Integrable (fun x : WholePlane ↦
        (fderiv ℝ (fun y : WholePlane ↦ phi y) x
          (wholePlaneBasis j)) • f x) volume := by
      rw [show (fun x : WholePlane ↦
          (fderiv ℝ (fun y : WholePlane ↦ phi y) x
            (wholePlaneBasis j)) • f x) =
          fun x ↦ (∂_{wholePlaneBasis j} phi) x • f x by
        funext x
        rw [hphiDeriv]]
      exact memLp_one_iff_integrable.mp <|
        (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).memLp_of_bilin
          1 ((∂_{wholePlaneBasis j} phi).memLp 1 volume) hfMem
    have hright : Integrable (fun x : WholePlane ↦
        phi x • fderiv ℝ f x (wholePlaneBasis j)) volume := by
      rw [show (fun x : WholePlane ↦
          phi x • fderiv ℝ f x (wholePlaneBasis j)) =
          fun x ↦ phi x • df j x by
        funext x
        rw [hfDeriv]]
      exact memLp_one_iff_integrable.mp <|
        (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).memLp_of_bilin
          1 (phi.memLp 1 volume) hdfMem
    have hprod : Integrable (fun x : WholePlane ↦ phi x • f x) volume := by
      exact memLp_one_iff_integrable.mp <|
        (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).memLp_of_bilin
          1 (phi.memLp 1 volume) hfMem
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := (volume : Measure WholePlane))
      (f := fun x : WholePlane ↦ phi x) (g := f)
      (v := wholePlaneBasis j) hleft hright hprod
      (fun x _hx ↦ phi.differentiableAt)
      (fun x _hx ↦ (hf' x).differentiableAt)
    rw [show (fun x : WholePlane ↦
        phi x • fderiv ℝ f x (wholePlaneBasis j)) =
        fun x ↦ phi x • df j x by
      funext x
      rw [hfDeriv]] at hibp
    rw [show (fun x : WholePlane ↦
        fderiv ℝ (fun y : WholePlane ↦ phi y) x
          (wholePlaneBasis j) • f x) =
        fun x ↦ (∂_{wholePlaneBasis j} phi) x • f x by
      funext x
      rw [hphiDeriv]] at hibp
    calc
      (∫ x : WholePlane,
          (-∂_{wholePlaneBasis j} phi) x •
            ((boundedComplexLInf f hfContinuous.aestronglyMeasurable fBound
              (ae_of_all volume hfBound) : WholePlaneScalarLInf) x)
          ∂volume) =
          ∫ x : WholePlane, (-∂_{wholePlaneBasis j} phi) x • f x
            ∂volume := by
        apply integral_congr_ae
        filter_upwards [boundedComplexLInf_coe_ae f
            hfContinuous.aestronglyMeasurable fBound
            (ae_of_all volume hfBound)] with x hx
        rw [hx]
      _ = -(∫ x : WholePlane,
          (∂_{wholePlaneBasis j} phi) x • f x ∂volume) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        simp
      _ = ∫ x : WholePlane, phi x • df j x ∂volume := hibp.symm
      _ = ∫ x : WholePlane, phi x •
          ((boundedComplexLInf (df j) (hdfMeasurable j) (dfBound j)
            (ae_of_all volume (hdfBound j)) : WholePlaneScalarLInf) x)
          ∂volume := by
        apply integral_congr_ae
        filter_upwards [boundedComplexLInf_coe_ae (df j)
            (hdfMeasurable j) (dfBound j)
            (ae_of_all volume (hdfBound j))] with x hx
        rw [hx]

/-- The value stored in a certificate built from a bounded `C¹` function is represented almost
everywhere by that function. -/
theorem boundedC1WholePlaneW1InfCertificate_value_coe_ae
    (f : WholePlane → ℂ) (df : Fin 2 → WholePlane → ℂ)
    (f' : WholePlane → WholePlane →L[ℝ] ℂ)
    (hf' : ∀ x, HasFDerivAt f (f' x) x)
    (hcoord : ∀ x j, f' x (wholePlaneBasis j) = df j x)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ) (hdfBound : ∀ j x, ‖df j x‖ ≤ dfBound j)
    (hdfMeasurable : ∀ j, AEStronglyMeasurable (df j) volume) :
    ((boundedC1WholePlaneW1InfCertificate f df f' hf' hcoord
      fBound hfBound dfBound hdfBound hdfMeasurable).value :
        WholePlane → ℂ) =ᵐ[volume] f := by
  change ((boundedComplexLInf f
    ((continuous_iff_continuousAt.mpr fun x ↦
      (hf' x).continuousAt).aestronglyMeasurable) fBound
    (ae_of_all volume hfBound) : WholePlaneScalarLInf) :
      WholePlane → ℂ) =ᵐ[volume] f
  exact boundedComplexLInf_coe_ae _ _ _ _

/-- The `j`-th weak derivative stored in a certificate built from a bounded `C¹` function is
represented almost everywhere by the given classical coordinate derivative. -/
theorem boundedC1WholePlaneW1InfCertificate_deriv_coe_ae
    (f : WholePlane → ℂ) (df : Fin 2 → WholePlane → ℂ)
    (f' : WholePlane → WholePlane →L[ℝ] ℂ)
    (hf' : ∀ x, HasFDerivAt f (f' x) x)
    (hcoord : ∀ x j, f' x (wholePlaneBasis j) = df j x)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ) (hdfBound : ∀ j x, ‖df j x‖ ≤ dfBound j)
    (hdfMeasurable : ∀ j, AEStronglyMeasurable (df j) volume)
    (j : Fin 2) :
    ((boundedC1WholePlaneW1InfCertificate f df f' hf' hcoord
      fBound hfBound dfBound hdfBound hdfMeasurable).deriv j :
        WholePlane → ℂ) =ᵐ[volume] df j := by
  change ((boundedComplexLInf (df j) (hdfMeasurable j) (dfBound j)
    (ae_of_all volume (hdfBound j)) : WholePlaneScalarLInf) :
      WholePlane → ℂ) =ᵐ[volume] df j
  exact boundedComplexLInf_coe_ae _ _ _ _

end ConstantCoefficientBackground

end

end FastDynamo
