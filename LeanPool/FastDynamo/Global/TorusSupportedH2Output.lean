/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.WholePlaneW1InfCertificates
public import LeanPool.FastDynamo.Analysis.WholePlaneScalarH2Leibniz
public import LeanPool.FastDynamo.Global.TorusChartH2Transfer

/-!
# Supported output localization on the periodic `H²` chart

This file supplies the output half of the domain-valued cutoff chart used by
the torus parametrix.  It has two analytic ingredients.

* The explicit input and output bumps are packaged as whole-plane
  scalar `W²,∞` certificates.  Their stored weak derivatives are the actual
  classical coordinate derivatives, with the radius-explicit bounds proved in
  `ParametrixExplicitCutoffDerivatives`.
* Multiplication by the output certificate sends every whole-plane `C3` `H²`
  jet into the chart-supported subspace when the closed support ball lies in
  the fundamental rectangle.  Composing with the supported chart transfer
  gives a bounded `WholePlaneC3H2 → TransverseC3H2` localization whose
  physical embedding is exactly the `L²` output localization
  `wholePlaneOutputLocalizationL2`.

Closed-ball containment is used.  It gives a strict exterior
inequality away from the chart, so the value and both classical derivative
rows are locally zero there without requiring a separate boundary-flatness
lemma for `ContDiffBump`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal LineDeriv

namespace TorusSupportedH2Output

open ConstantCoefficientBackground
open ParametrixExplicitCutoff
open TorusChartL2
open TorusChartH2

/-! ## A bounded classical `C²` real profile gives a `W²,∞` certificate -/

/-- The classical ordered derivative `∂_k (∂_j f)`.  The order is chosen
to agree with `WholePlaneScalarW2InfCertificate.secondDeriv j k`. -/
def realProfileSecondCoordinateDerivative (f : WholePlane → ℝ)
    (j k : Fin 2) (x : WholePlane) : ℝ :=
  fderiv ℝ (realProfileCoordinateDerivative f j) x (wholePlaneBasis k)

/-- A `C²` real profile has `C¹` coordinate derivatives, which is the regularity needed before
differentiating a second time.
-/
theorem realProfileCoordinateDerivative_contDiff
    {f : WholePlane → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    ContDiff ℝ 1 (realProfileCoordinateDerivative f j) := by
  unfold realProfileCoordinateDerivative
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- The ordered derivative above is the `(k,j)` entry of Mathlib's iterated
Fréchet derivative.  The reversal records that the outer derivative direction
is `k`, while the fixed argument of the first derivative is `j`. -/
theorem realProfileSecondCoordinateDerivative_eq_secondCoordinateDerivative
    {f : WholePlane → ℝ} (hf : ContDiff ℝ 2 f)
    (j k : Fin 2) (x : WholePlane) :
    realProfileSecondCoordinateDerivative f j k x =
      secondCoordinateDerivative f k j x := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hfdx : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hfd.differentiable (by norm_num) x
  unfold realProfileSecondCoordinateDerivative
    realProfileCoordinateDerivative secondCoordinateDerivative
  rw [fderiv_clm_apply hfdx (differentiableAt_const (c := wholePlaneBasis j))]
  rw [iteratedFDeriv_two_apply]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  rfl

/-- Package a bounded classical real `C²` profile, together with pointwise
bounds for its value and actual ordered derivatives, as a quotient-level
whole-plane `W²,∞` multiplier. -/
def boundedC2RealWholePlaneW2InfCertificate
    (f : WholePlane → ℝ) (hf : ContDiff ℝ 2 f)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ)
    (hdfBound : ∀ j x,
      ‖realProfileCoordinateDerivative f j x‖ ≤ dfBound j)
    (d2fBound : Fin 2 → Fin 2 → ℝ)
    (hd2fBound : ∀ j k x,
      ‖realProfileSecondCoordinateDerivative f j k x‖ ≤ d2fBound j k) :
    WholePlaneScalarW2InfCertificate := by
  let fc : WholePlane → ℂ := fun x ↦ (f x : ℂ)
  let dfc : Fin 2 → WholePlane → ℂ := fun j x ↦
    (realProfileCoordinateDerivative f j x : ℂ)
  let d2fc : Fin 2 → Fin 2 → WholePlane → ℂ := fun j k x ↦
    (realProfileSecondCoordinateDerivative f j k x : ℂ)
  have hdfc (j : Fin 2) : ContDiff ℝ 1 (dfc j) := by
    exact Complex.ofRealCLM.contDiff.comp
      (realProfileCoordinateDerivative_contDiff hf j)
  let base : WholePlaneScalarW1InfCertificate :=
    boundedC1WholePlaneW1InfCertificate
      fc dfc
      (fun x ↦ Complex.ofRealCLM.comp (fderiv ℝ f x))
      (fun x ↦ by
        simpa [fc, Function.comp_def] using
          Complex.ofRealCLM.hasFDerivAt.comp x
            ((hf.differentiable (by norm_num) x).hasFDerivAt))
      (fun _x _j ↦ rfl)
      fBound
      (fun x ↦ by simpa [fc, Complex.norm_real] using hfBound x)
      dfBound
      (fun j x ↦ by
        simpa [dfc, Complex.norm_real] using hdfBound j x)
      (fun j ↦ (hdfc j).continuous.aestronglyMeasurable)
  let row : Fin 2 → WholePlaneScalarW1InfCertificate := fun j ↦
    boundedC1WholePlaneW1InfCertificate
      (dfc j) (d2fc j)
      (fun x ↦ Complex.ofRealCLM.comp
        (fderiv ℝ (realProfileCoordinateDerivative f j) x))
      (fun x ↦ by
        simpa [dfc, Function.comp_def] using
          Complex.ofRealCLM.hasFDerivAt.comp x
            (((realProfileCoordinateDerivative_contDiff hf j).differentiable
              (by norm_num) x).hasFDerivAt))
      (fun _x _k ↦ rfl)
      (dfBound j)
      (fun x ↦ by
        simpa [dfc, Complex.norm_real] using hdfBound j x)
      (d2fBound j)
      (fun k x ↦ by
        simpa [d2fc, Complex.norm_real] using hd2fBound j k x)
      (fun k ↦ by
        exact (Complex.ofRealCLM.continuous.comp
          (((realProfileCoordinateDerivative_contDiff hf j).continuous_fderiv
            (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable)
  refine
    { toWholePlaneScalarW1InfCertificate := base
      secondDeriv := fun j k ↦ (row j).deriv k
      hasWeakSecondDerivative := ?_ }
  intro j k
  have hsource : base.deriv j = (row j).value := by
    apply Lp.ext
    exact (boundedC1WholePlaneW1InfCertificate_deriv_coe_ae
      fc dfc
      (fun x ↦ Complex.ofRealCLM.comp (fderiv ℝ f x))
      (fun x ↦ by
        simpa [fc, Function.comp_def] using
          Complex.ofRealCLM.hasFDerivAt.comp x
            ((hf.differentiable (by norm_num) x).hasFDerivAt))
      (fun _x _j ↦ rfl)
      fBound
      (fun x ↦ by simpa [fc, Complex.norm_real] using hfBound x)
      dfBound
      (fun j x ↦ by
        simpa [dfc, Complex.norm_real] using hdfBound j x)
      (fun j ↦ (hdfc j).continuous.aestronglyMeasurable) j).trans <|
      (boundedC1WholePlaneW1InfCertificate_value_coe_ae
        (dfc j) (d2fc j)
        (fun x ↦ Complex.ofRealCLM.comp
          (fderiv ℝ (realProfileCoordinateDerivative f j) x))
        (fun x ↦ by
          simpa [dfc, Function.comp_def] using
            Complex.ofRealCLM.hasFDerivAt.comp x
              (((realProfileCoordinateDerivative_contDiff hf j).differentiable
                (by norm_num) x).hasFDerivAt))
        (fun _x _k ↦ rfl)
        (dfBound j)
        (fun x ↦ by
          simpa [dfc, Complex.norm_real] using hdfBound j x)
        (d2fBound j)
        (fun k x ↦ by
          simpa [d2fc, Complex.norm_real] using hd2fBound j k x)
        (fun k ↦ by
          exact (Complex.ofRealCLM.continuous.comp
            (((realProfileCoordinateDerivative_contDiff hf j).continuous_fderiv
              (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable)).symm
  rw [hsource]
  exact (row j).hasWeakDerivative k

/-- The value stored in the `W²,∞` certificate of a bounded `C²` real profile is, almost everywhere,
the complexification of that profile.
-/
theorem boundedC2RealWholePlaneW2InfCertificate_value_coe_ae
    (f : WholePlane → ℝ) (hf : ContDiff ℝ 2 f)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ)
    (hdfBound : ∀ j x,
      ‖realProfileCoordinateDerivative f j x‖ ≤ dfBound j)
    (d2fBound : Fin 2 → Fin 2 → ℝ)
    (hd2fBound : ∀ j k x,
      ‖realProfileSecondCoordinateDerivative f j k x‖ ≤ d2fBound j k) :
    ((boundedC2RealWholePlaneW2InfCertificate f hf fBound hfBound
      dfBound hdfBound d2fBound hd2fBound).value : WholePlane → ℂ)
        =ᵐ[volume] fun x ↦ (f x : ℂ) := by
  unfold boundedC2RealWholePlaneW2InfCertificate
  dsimp only
  apply boundedC1WholePlaneW1InfCertificate_value_coe_ae

/-- The `j`-th stored weak derivative in the `W²,∞` certificate of a bounded `C²` real profile is,
almost everywhere, the complexification of the classical coordinate derivative `∂_j f`.
-/
theorem boundedC2RealWholePlaneW2InfCertificate_deriv_coe_ae
    (f : WholePlane → ℝ) (hf : ContDiff ℝ 2 f)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ)
    (hdfBound : ∀ j x,
      ‖realProfileCoordinateDerivative f j x‖ ≤ dfBound j)
    (d2fBound : Fin 2 → Fin 2 → ℝ)
    (hd2fBound : ∀ j k x,
      ‖realProfileSecondCoordinateDerivative f j k x‖ ≤ d2fBound j k)
    (j : Fin 2) :
    ((boundedC2RealWholePlaneW2InfCertificate f hf fBound hfBound
      dfBound hdfBound d2fBound hd2fBound).deriv j : WholePlane → ℂ)
        =ᵐ[volume] fun x ↦
          (realProfileCoordinateDerivative f j x : ℂ) := by
  unfold boundedC2RealWholePlaneW2InfCertificate
  dsimp only
  apply boundedC1WholePlaneW1InfCertificate_deriv_coe_ae

/-- The stored weak second derivative `(j, k)` in the `W²,∞` certificate of a bounded `C²` real
profile is, almost everywhere, the complexification of the classical ordered derivative `∂_k(∂_j
f)`.
-/
theorem boundedC2RealWholePlaneW2InfCertificate_secondDeriv_coe_ae
    (f : WholePlane → ℝ) (hf : ContDiff ℝ 2 f)
    (fBound : ℝ) (hfBound : ∀ x, ‖f x‖ ≤ fBound)
    (dfBound : Fin 2 → ℝ)
    (hdfBound : ∀ j x,
      ‖realProfileCoordinateDerivative f j x‖ ≤ dfBound j)
    (d2fBound : Fin 2 → Fin 2 → ℝ)
    (hd2fBound : ∀ j k x,
      ‖realProfileSecondCoordinateDerivative f j k x‖ ≤ d2fBound j k)
    (j k : Fin 2) :
    ((boundedC2RealWholePlaneW2InfCertificate f hf fBound hfBound
      dfBound hdfBound d2fBound hd2fBound).secondDeriv j k :
        WholePlane → ℂ) =ᵐ[volume] fun x ↦
          (realProfileSecondCoordinateDerivative f j k x : ℂ) := by
  unfold boundedC2RealWholePlaneW2InfCertificate
  dsimp only
  apply boundedC1WholePlaneW1InfCertificate_deriv_coe_ae

/-! ## The two explicit parametrix cutoff certificates -/

/-- The paper's larger output cutoff as a `W²,∞` multiplier. -/
def outputCutoffW2InfCertificate
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    WholePlaneScalarW2InfCertificate :=
  boundedC2RealWholePlaneW2InfCertificate
    (outputCutoff p R hR)
    ((outputCutoff_contDiff p R hR).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    1
    (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (outputCutoff_mem_Icc p R hR x).1]
      exact (outputCutoff_mem_Icc p R hR x).2)
    (fun _ ↦ firstDerivativeConstant / R)
    (norm_outputCutoff_coordinateDerivative_le p R hR)
    (fun _ _ ↦ secondDerivativeConstant / R ^ 2)
    (fun j k x ↦ by
      rw [realProfileSecondCoordinateDerivative_eq_secondCoordinateDerivative
        ((outputCutoff_contDiff p R hR).of_le (by
          exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
      exact norm_outputCutoff_secondCoordinateDerivative_le p R hR k j x)

/-- The value stored in the output-cutoff `W²,∞` certificate is, almost everywhere, the complexified
explicit output cutoff profile.
-/
theorem outputCutoffW2InfCertificate_value_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ((outputCutoffW2InfCertificate p R hR).value : WholePlane → ℂ)
      =ᵐ[volume] outputCutoffComplex p R hR := by
  change ((outputCutoffW2InfCertificate p R hR).value : WholePlane → ℂ)
    =ᵐ[volume] fun x ↦ (outputCutoff p R hR x : ℂ)
  unfold outputCutoffW2InfCertificate
  exact boundedC2RealWholePlaneW2InfCertificate_value_coe_ae
      (outputCutoff p R hR)
      ((outputCutoff_contDiff p R hR).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      1
      (fun x ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (outputCutoff_mem_Icc p R hR x).1]
        exact (outputCutoff_mem_Icc p R hR x).2)
      (fun _ ↦ firstDerivativeConstant / R)
      (norm_outputCutoff_coordinateDerivative_le p R hR)
      (fun _ _ ↦ secondDerivativeConstant / R ^ 2)
      (fun j k x ↦ by
        rw [realProfileSecondCoordinateDerivative_eq_secondCoordinateDerivative
          ((outputCutoff_contDiff p R hR).of_le (by
            exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
        exact norm_outputCutoff_secondCoordinateDerivative_le p R hR k j x)

/-- The `j`-th stored derivative of the output-cutoff certificate is, almost everywhere, the
classical coordinate derivative of the output cutoff profile.
-/
theorem outputCutoffW2InfCertificate_deriv_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j : Fin 2) :
    ((outputCutoffW2InfCertificate p R hR).deriv j : WholePlane → ℂ)
      =ᵐ[volume] fun x ↦
        (realProfileCoordinateDerivative (outputCutoff p R hR) j x : ℂ) := by
  unfold outputCutoffW2InfCertificate
  apply boundedC2RealWholePlaneW2InfCertificate_deriv_coe_ae

/-- The stored second derivative `(j, k)` of the output-cutoff certificate is, almost everywhere,
the classical ordered second derivative of the output cutoff profile.
-/
theorem outputCutoffW2InfCertificate_secondDeriv_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j k : Fin 2) :
    ((outputCutoffW2InfCertificate p R hR).secondDeriv j k :
        WholePlane → ℂ) =ᵐ[volume] fun x ↦
      (realProfileSecondCoordinateDerivative
        (outputCutoff p R hR) j k x : ℂ) := by
  unfold outputCutoffW2InfCertificate
  apply boundedC2RealWholePlaneW2InfCertificate_secondDeriv_coe_ae

/-- As `L∞` classes the value of the output-cutoff certificate equals the multiplier
`outputCutoffLInf`; this is what makes the physical embedding of the `H²` output localization
the `L²` output localization.
-/
theorem outputCutoffW2InfCertificate_value_eq_outputCutoffLInf
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    (outputCutoffW2InfCertificate p R hR).value =
      outputCutoffLInf p R hR := by
  apply Lp.ext
  exact (outputCutoffW2InfCertificate_value_coe_ae p R hR).trans
    (outputCutoffLInf_coe_ae p R hR).symm

/-! ## Exterior vanishing of all output-cutoff coefficient rows -/

/-- Each classical coordinate derivative of the output cutoff vanishes strictly outside the closed
ball of radius `R/2`, where the cutoff is identically zero.
-/
theorem outputCutoff_coordinateDerivative_eq_zero_of_radius_lt_dist
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j : Fin 2)
    {x : WholePlane} (hx : R / 2 < dist x p) :
    realProfileCoordinateDerivative (outputCutoff p R hR) j x = 0 := by
  unfold realProfileCoordinateDerivative outputCutoff
  rw [contDiffBump_fderiv_eq_zero_of_rOut_lt_dist
    (outputBump p R hR) (by simpa [outputBump] using hx)]
  rfl

/-- Each classical ordered second derivative of the output cutoff vanishes strictly outside the
closed ball of radius `R/2`, since the first derivative vanishes on that open exterior.
-/
theorem outputCutoff_secondCoordinateDerivative_eq_zero_of_radius_lt_dist
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (j k : Fin 2)
    {x : WholePlane} (hx : R / 2 < dist x p) :
    realProfileSecondCoordinateDerivative
      (outputCutoff p R hR) j k x = 0 := by
  have hopen : IsOpen {y : WholePlane | R / 2 < dist y p} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hmem : {y : WholePlane | R / 2 < dist y p} ∈ nhds x :=
    hopen.mem_nhds hx
  have heq : realProfileCoordinateDerivative (outputCutoff p R hR) j
      =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hmem] with y hy
    exact outputCutoff_coordinateDerivative_eq_zero_of_radius_lt_dist
      p R hR j hy
  unfold realProfileSecondCoordinateDerivative
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  simp only [fderiv_const_apply, zero_apply]

/-- If the closed ball of radius `R/2` around `p` lies in the fundamental box, then every point
outside the box is at distance strictly more than `R/2` from `p`. This strict exterior
inequality is what makes all cutoff rows locally zero off the chart.
-/
theorem radius_lt_dist_of_not_mem_fundamentalBox
    (p : WholePlane) (R : ℝ)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox)
    {x : WholePlane} (hx : x ∉ wholePlaneFundamentalBox) :
    R / 2 < dist x p := by
  by_contra hnot
  apply hx
  apply hclosedBall
  simpa [Metric.mem_closedBall, dist_comm] using le_of_not_gt hnot

/-- A scalar `L∞` multiplier vanishes almost everywhere outside the canonical whole-plane
fundamental box, the support condition required of every row of a chart multiplier.
-/
private def IsSupportedScalarInWholePlaneFundamentalBox
    (a : WholePlaneScalarLInf) : Prop :=
  ∀ᵐ x ∂volume, x ∉ wholePlaneFundamentalBox → a x = 0

/-- When the closed support ball lies in the fundamental box, the value of the output-cutoff
certificate vanishes almost everywhere off the box.
-/
private theorem outputCutoffCertificate_value_supported
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) :
    IsSupportedScalarInWholePlaneFundamentalBox
      (outputCutoffW2InfCertificate p R hR).value := by
  filter_upwards [outputCutoffW2InfCertificate_value_coe_ae p R hR]
    with x hcoe hx
  rw [hcoe]
  unfold outputCutoffComplex
  rw [outputCutoff_eq_zero_of_radius_le_dist p R hR
    (radius_lt_dist_of_not_mem_fundamentalBox p R hclosedBall hx).le]
  norm_num

/-- Under the same closed-ball containment, each stored first derivative of the output-cutoff
certificate vanishes almost everywhere off the fundamental box.
-/
private theorem outputCutoffCertificate_deriv_supported
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) (j : Fin 2) :
    IsSupportedScalarInWholePlaneFundamentalBox
      ((outputCutoffW2InfCertificate p R hR).deriv j) := by
  filter_upwards [outputCutoffW2InfCertificate_deriv_coe_ae p R hR j]
    with x hcoe hx
  rw [hcoe, outputCutoff_coordinateDerivative_eq_zero_of_radius_lt_dist
    p R hR j (radius_lt_dist_of_not_mem_fundamentalBox
      p R hclosedBall hx)]
  norm_num

/-- Under the same closed-ball containment, each stored second derivative of the output-cutoff
certificate vanishes almost everywhere off the fundamental box.
-/
private theorem outputCutoffCertificate_secondDeriv_supported
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) (j k : Fin 2) :
    IsSupportedScalarInWholePlaneFundamentalBox
      ((outputCutoffW2InfCertificate p R hR).secondDeriv j k) := by
  filter_upwards [outputCutoffW2InfCertificate_secondDeriv_coe_ae
    p R hR j k] with x hcoe hx
  rw [hcoe, outputCutoff_secondCoordinateDerivative_eq_zero_of_radius_lt_dist
    p R hR j k (radius_lt_dist_of_not_mem_fundamentalBox
      p R hclosedBall hx)]
  norm_num

/-- Multiplying any vector `L²` field by a scalar multiplier supported in the fundamental box
produces a field supported there.
-/
private theorem scalarMulC3L2_supported
    (a : WholePlaneScalarLInf)
    (ha : IsSupportedScalarInWholePlaneFundamentalBox a)
    (u : WholePlaneC3L2) :
    IsSupportedInWholePlaneFundamentalBox
      (wholePlaneScalarMulC3L2 a u) := by
  filter_upwards [ha, scalarVectorMulL2_coe_ae volume a u]
    with x hax hmul hx
  rw [show wholePlaneScalarMulC3L2 a u x = a x • u x by
    simpa only [wholePlaneScalarMulC3L2] using hmul, hax hx, zero_smul]

/-- Support in the fundamental box is preserved by addition, which is what lets the Leibniz
expansion of each jet row stay supported.
-/
private theorem supported_add
    {u v : WholePlaneC3L2}
    (hu : IsSupportedInWholePlaneFundamentalBox u)
    (hv : IsSupportedInWholePlaneFundamentalBox v) :
    IsSupportedInWholePlaneFundamentalBox (u + v) := by
  filter_upwards [hu, hv, Lp.coeFn_add u v] with x hux hvx hadd hx
  rw [hadd]
  change u x + v x = 0
  rw [hux hx, hvx hx, add_zero]

/-! ## Supported multiplier and the output `H²` chart map -/

/-- Multiplication by the output-cutoff certificate sends every whole-plane `C³`-valued `H²` jet
into the chart-supported subspace, provided the closed ball of radius `R/2` lies in the
fundamental box: every row of the resulting jet vanishes off the chart. This is the containment
that makes the supported chart transfer applicable and yields the bounded output localization
`WholePlaneC3H2 → TransverseC3H2`.
-/
theorem outputCutoffMulC3H2_mem_chartSupported
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) (u : WholePlaneC3H2) :
    wholePlaneScalarMulC3H2 (outputCutoffW2InfCertificate p R hR) u
      ∈ chartSupportedWholePlaneH2Submodule := by
  intro q
  rcases q with r | jk
  · rcases r with _ | j
    · change IsSupportedInWholePlaneFundamentalBox
        (wholePlaneH2Embedding C3
          (wholePlaneScalarMulC3H2
            (outputCutoffW2InfCertificate p R hR) u))
      rw [wholePlaneH2Embedding_scalarMulC3H2]
      exact scalarMulC3L2_supported _
        (outputCutoffCertificate_value_supported p R hR hclosedBall) _
    · change IsSupportedInWholePlaneFundamentalBox
        (wholePlaneH2FirstDerivative C3 j
          (wholePlaneScalarMulC3H2
            (outputCutoffW2InfCertificate p R hR) u))
      rw [wholePlaneH2FirstDerivative_scalarMulC3H2]
      unfold wholePlaneScalarMulC3H2FirstJet
      exact supported_add
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_deriv_supported
            p R hR hclosedBall j) _)
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_value_supported
            p R hR hclosedBall) _)
  · rcases jk with ⟨j, k⟩
    change IsSupportedInWholePlaneFundamentalBox
      (wholePlaneH2SecondDerivative C3 j k
        (wholePlaneScalarMulC3H2
          (outputCutoffW2InfCertificate p R hR) u))
    rw [wholePlaneH2SecondDerivative_scalarMulC3H2]
    unfold wholePlaneScalarMulC3H2SecondJet
    exact supported_add
      (supported_add
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_secondDeriv_supported
            p R hR hclosedBall j k) _)
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_deriv_supported
            p R hR hclosedBall j) _))
      (supported_add
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_deriv_supported
            p R hR hclosedBall k) _)
        (scalarMulC3L2_supported _
          (outputCutoffCertificate_value_supported
            p R hR hclosedBall) _))

/-- Multiplication by the larger cutoff, with the complete resulting jet
restricted to the chart-supported whole-plane `H²` subspace. -/
def outputCutoffToChartSupportedH2
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) :
    WholePlaneC3H2 →L[ℂ] ChartSupportedWholePlaneC3H2 :=
  (wholePlaneScalarMulC3H2
    (outputCutoffW2InfCertificate p R hR)).codRestrict
      chartSupportedWholePlaneH2Submodule
      (outputCutoffMulC3H2_mem_chartSupported p R hR hclosedBall)

/-- Domain-valued output localization: multiply a whole-plane `H²` field by
the explicit larger cutoff and descend its supported weak jet to periodic
Fourier `H²`. -/
def wholePlaneOutputLocalizationH2
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) :
    WholePlaneC3H2 →L[ℂ] TransverseC3H2 :=
  wholePlaneChartToTransverseH2.comp
    (outputCutoffToChartSupportedH2 p R hR hclosedBall)

/-- The physical value of the `H²` output localization is exactly the
cutoff-and-restriction map on `L²`. -/
theorem transverseH2Embedding_wholePlaneOutputLocalizationH2
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hclosedBall : Metric.closedBall p (R / 2) ⊆
      wholePlaneFundamentalBox) (u : WholePlaneC3H2) :
    transverseH2Embedding
        (wholePlaneOutputLocalizationH2 p R hR hclosedBall u) =
      wholePlaneOutputLocalizationL2 p R hR
        (wholePlaneH2Embedding C3 u) := by
  rw [show wholePlaneOutputLocalizationH2 p R hR hclosedBall u =
      wholePlaneChartToTransverseH2
        (outputCutoffToChartSupportedH2 p R hR hclosedBall u) from rfl,
    transverseH2Embedding_wholePlaneChartToTransverseH2]
  change wholePlaneToTorusL2
      (wholePlaneH2Embedding C3
        (wholePlaneScalarMulC3H2
          (outputCutoffW2InfCertificate p R hR) u)) = _
  rw [wholePlaneH2Embedding_scalarMulC3H2,
    outputCutoffW2InfCertificate_value_eq_outputCutoffLInf]
  rfl

end TorusSupportedH2Output

end

end FastDynamo
