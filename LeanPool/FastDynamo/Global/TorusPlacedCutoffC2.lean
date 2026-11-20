/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusSchwartzPeriodicCutoff
public import LeanPool.FastDynamo.Global.HorizontalCutoffMultiplier

/-!
# The three placed parametrix cut-offs of Section 7, as `ℂ²` multipliers

The paper (§7.1, `sec:parametrix`) attaches to the selected cell, of centre `p_n` and reserved
radius `R_n`, three smooth scalar cut-offs, the *input cut-off* `φ_n` and the *output cut-offs*
`ψ_n` (selected summand) and `χ_n` (background summand):

* `φ_n = 1` on `D(p_n, R_n/5)`, `supp φ_n ⊂ D(p_n, R_n/4)`;
* `ψ_n = 1` on `D(p_n, R_n/3)`, `supp ψ_n ⊂ D(p_n, R_n/2)`;
* `χ_n = 0` on `D(p_n, R_n/10)`, `χ_n = 1` outside `D(p_n, R_n/6)`,

subject to `eq:parametrix-cutoff-bounds` (a bound on `ψ_n` and `χ_n` only) and
`eq:parametrix-cutoff-identities`.  The plane profiles, their scale bounds and
the two identities are
`FastDynamo/Global/ParametrixCutoffs.lean`.  This module turns them into bounded
multipliers of the periodic two-component `H²` Fourier graph and assembles the bundle
`ParametrixCutoffs.HorizontalParametrixCutoffs R` that the two-summand parametrix consumes.

The route is: complexify each profile as a Schwartz function on the plane, complete its lattice
Fourier samples into a periodic second-order cut-off
(`FastDynamo/Global/TorusSchwartzPeriodicCutoff.lean`), descend it to the two-component fibre
(`FastDynamo/Global/HorizontalCutoffMultiplier.lean`), and read off the `L∞` bounds and the two
identities from the plane statements through the no-wrap periodization.  The background cut-off
`χ_n` is `1` near infinity, so it is not itself a periodized bump: it is built as the complement
`1 - b_n` of the compactly supported bump `b_n` of inner radius `R_n/10` and outer radius
`R_n/6`.

The single geometric hypothesis is `Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox`:
the largest of the three supports must not wrap around the transverse torus.  For a cell of a
`ScaleFamily.TorusCellPlacement` this is the placement's chart containment, `eq:chart-packing`
and the placement of the discs in the fixed chart that follows it (§3.3).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

namespace TorusPlacedCutoffC2

open ConstantCoefficientBackground
open HorizontalCutoffMultiplier
open ParametrixCutoffs
open ParametrixExplicitCutoff
open PeriodicSecondOrderCutoffs
open SchwartzPeriodicCutoff
open TransverseSmoothBumpPeriodization
open TransverseVecMultiplierAlgebra

/-! ## The three complexified placed profiles -/

/-- The closed support of a complexified real profile is that of the profile. -/
theorem tsupport_realSchwartz (f : WholePlane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    tsupport ((realSchwartz f hf hc : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) =
      tsupport f := by
  have hsupp : Function.support
      ((realSchwartz f hf hc : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) =
      Function.support f := by
    ext x
    simp [Function.mem_support, realSchwartz_apply]
  rw [tsupport, tsupport, hsupp]

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-- The complexified smaller input cut-off `φ` as a Schwartz function. -/
def inputSchwartz : SchwartzMap WholePlane ℂ :=
  realSchwartz (inputCutoff p R hR) (inputCutoff_contDiff p R hR)
    (inputCutoff_hasCompactSupport p R hR)

/-- The complexified larger output cut-off `ψ` as a Schwartz function. -/
def outputSchwartz : SchwartzMap WholePlane ℂ :=
  realSchwartz (outputCutoff p R hR) (outputCutoff_contDiff p R hR)
    (outputCutoff_hasCompactSupport p R hR)

/-- The complexified background bump `b = 1 - χ` as a Schwartz function. -/
def backgroundSchwartz : SchwartzMap WholePlane ℂ :=
  realSchwartz ((backgroundBump p R hR : WholePlane → ℝ)) (backgroundBump_contDiff p R hR)
    (backgroundBump p R hR).hasCompactSupport

/-- The input profile is supported in the closed quarter-buffer. -/
theorem tsupport_inputSchwartz :
    tsupport ((inputSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
      Metric.closedBall p (R / 2) := by
  rw [inputSchwartz, tsupport_realSchwartz, tsupport, inputCutoff_support_eq]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_ball] at hx
  simp only [Metric.mem_closedBall]
  linarith

/-- The output profile is supported in the closed half-buffer. -/
theorem tsupport_outputSchwartz :
    tsupport ((outputSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
      Metric.closedBall p (R / 2) := by
  rw [outputSchwartz, tsupport_realSchwartz, tsupport, outputCutoff_support_eq]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_ball] at hx
  simp only [Metric.mem_closedBall]
  linarith

/-- The background bump is supported in the closed sixth-buffer. -/
theorem tsupport_backgroundSchwartz :
    tsupport ((backgroundSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) ⊆
      Metric.closedBall p (R / 2) := by
  rw [backgroundSchwartz, tsupport_realSchwartz, tsupport,
    (backgroundBump p R hR).support_eq]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hout : (backgroundBump p R hR).rOut = R / 6 := rfl
  rw [Metric.mem_ball, hout] at hx
  simp only [Metric.mem_closedBall]
  linarith

/-! ## The no-wrap hypotheses -/

/-- The input profile wraps onto the torus without overlap. -/
theorem nowrap_inputSchwartz
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox
      ((inputSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  supportedInIocFundamentalBox_of_tsupport_subset _ (tsupport_inputSchwartz p R hR) hbox

/-- The output profile wraps onto the torus without overlap. -/
theorem nowrap_outputSchwartz
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox
      ((outputSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  supportedInIocFundamentalBox_of_tsupport_subset _ (tsupport_outputSchwartz p R hR) hbox

/-- The background bump wraps onto the torus without overlap. -/
theorem nowrap_backgroundSchwartz
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox
      ((backgroundSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  supportedInIocFundamentalBox_of_tsupport_subset _ (tsupport_backgroundSchwartz p R hR) hbox

/-- Every coordinate derivative of the output profile wraps without overlap. -/
theorem nowrap_outputSchwartz_deriv
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) (j : Fin 2) :
    SupportedInIocFundamentalBox
      ((∂_{wholePlaneBasis j} (outputSchwartz p R hR) :
        SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  supportedInIocFundamentalBox_of_tsupport_subset _
    ((tsupport_lineDerivOp_subset _ j).trans (tsupport_outputSchwartz p R hR)) hbox

/-- Every coordinate derivative of the background bump wraps without overlap. -/
theorem nowrap_backgroundSchwartz_deriv
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) (j : Fin 2) :
    SupportedInIocFundamentalBox
      ((∂_{wholePlaneBasis j} (backgroundSchwartz p R hR) :
        SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  supportedInIocFundamentalBox_of_tsupport_subset _
    ((tsupport_lineDerivOp_subset _ j).trans (tsupport_backgroundSchwartz p R hR)) hbox

/-- The Laplacian of the output profile wraps without overlap. -/
theorem nowrap_outputSchwartz_laplacian
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox
      ((schwartzLaplacian (outputSchwartz p R hR) :
        SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  fun _ hx ↦ hbox (tsupport_outputSchwartz p R hR
    (support_schwartzLaplacian_subset (outputSchwartz p R hR) hx))

/-- The Laplacian of the background bump wraps without overlap. -/
theorem nowrap_backgroundSchwartz_laplacian
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    SupportedInIocFundamentalBox
      ((schwartzLaplacian (backgroundSchwartz p R hR) :
        SchwartzMap WholePlane ℂ) : WholePlane → ℂ) :=
  fun _ hx ↦ hbox (tsupport_backgroundSchwartz p R hR
    (support_schwartzLaplacian_subset (backgroundSchwartz p R hR) hx))

/-! ## The three placed two-component multipliers -/

/-- The placed input multiplier `φ_n` on the two-component periodic `H²` graph. -/
def inputMul : HorizontalCutoffCommutator.HorizontalSecondOrderCutoff :=
  ofPeriodic (SchwartzPeriodicCutoff.cutoff (inputSchwartz p R hR))

/-- The placed output multiplier `ψ_n` on the two-component periodic `H²` graph. -/
def outputMul : HorizontalCutoffCommutator.HorizontalSecondOrderCutoff :=
  ofPeriodic (SchwartzPeriodicCutoff.cutoff (outputSchwartz p R hR))

/-- The placed background multiplier `χ_n = 1 - b_n` on the two-component periodic `H²`
graph. -/
def backgroundMul : HorizontalCutoffCommutator.HorizontalSecondOrderCutoff :=
  complement (ofPeriodic (SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)))

/-! ## Almost-everywhere representatives of the three values -/

/-- The placed input value is the input profile at the canonical representative. -/
theorem inputMul_value_ae
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ((inputMul p R hR).value : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ ((inputCutoff p R hR (wholePlaneIocRepresentative q) : ℝ) : ℂ) :=
  cutoff_value_ae_representative _ (nowrap_inputSchwartz p R hR hbox)

/-- The placed output value is the output profile at the canonical representative. -/
theorem outputMul_value_ae
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ((outputMul p R hR).value : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ ((outputCutoff p R hR (wholePlaneIocRepresentative q) : ℝ) : ℂ) :=
  cutoff_value_ae_representative _ (nowrap_outputSchwartz p R hR hbox)

/-- The placed background value is the background cut-off at the canonical representative. -/
theorem backgroundMul_value_ae
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ((backgroundMul p R hR).value : TransverseTorus → ℂ) =ᵐ[transverseMeasure]
      fun q ↦ ((backgroundCutoff p R hR (wholePlaneIocRepresentative q) : ℝ) : ℂ) := by
  have hbump := cutoff_value_ae_representative (backgroundSchwartz p R hR)
    (nowrap_backgroundSchwartz p R hR hbox)
  have hsub := Lp.coeFn_sub constOneLInf
    (SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).value
  filter_upwards [hbump, hsub, constOneLInf_coe_ae] with q hq hs h1
  change ((constOneLInf -
    (SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).value :
      TransverseScalarLInf) : TransverseTorus → ℂ) q = _
  rw [hs]
  change (constOneLInf : TransverseTorus → ℂ) q -
    ((SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).value :
      TransverseTorus → ℂ) q = _
  rw [h1, hq, backgroundSchwartz, realSchwartz_apply, backgroundCutoff]
  push_cast
  ring

/-! ## Sup and derivative bounds for the three placed multipliers

The paper's `eq:parametrix-cutoff-bounds` bounds the derivatives of `ψ_n` and
`χ_n` only; `φ_n` enters through the two sup-norm bounds below. -/

/-- `|φ_n| ≤ 1`. -/
theorem norm_inputMul_value_le_one
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖(inputMul p R hR).value‖ ≤ 1 := by
  refine norm_cutoff_value_le _ (nowrap_inputSchwartz p R hR hbox) zero_le_one fun x ↦ ?_
  rw [inputSchwartz, realSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inputCutoff_mem_Icc p R hR x).1]
  exact (inputCutoff_mem_Icc p R hR x).2

/-- `‖1 - φ_n‖_∞ ≤ 1`: the placed input profile takes values in `[0,1]`, so its complement
does as well.  This is the bound on `φ_n` that the parametrix consumes; the paper's
`eq:parametrix-cutoff-bounds` carries no `φ_n` summand at all (the paper only requires
`φ_n` to take values in `[0,1]`). -/
theorem norm_inputMul_complement_value_le_one
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖constOneLInf - (inputMul p R hR).value‖ ≤ 1 := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ zero_le_one
  have hsub := Lp.coeFn_sub constOneLInf (inputMul p R hR).value
  filter_upwards [hsub, constOneLInf_coe_ae, inputMul_value_ae p R hR hbox]
    with q hs h1 hin
  rw [hs]
  change ‖(constOneLInf : TransverseTorus → ℂ) q -
    ((inputMul p R hR).value : TransverseTorus → ℂ) q‖ ≤ 1
  rw [h1, hin]
  have hmem := inputCutoff_mem_Icc p R hR (wholePlaneIocRepresentative q)
  have : ((1 : ℂ) - ((inputCutoff p R hR (wholePlaneIocRepresentative q) : ℝ) : ℂ)) =
      ((1 - inputCutoff p R hR (wholePlaneIocRepresentative q) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hmem.2])]
  linarith [hmem.1]

/-- `‖1 - φ_n‖ ≤ 1` as an operator bound on `L²`: multiplication by the complement of the
placed input cut-off is a contraction, which is what the background summand of `eq:Rapp`
consumes. -/
theorem norm_inputMul_complement_le_one
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖ContinuousLinearMap.id ℂ TransverseC2L2 - (inputMul p R hR).stateMul‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ ?_
  have hEq : (ContinuousLinearMap.id ℂ TransverseC2L2 - (inputMul p R hR).stateMul) f =
      scalarVectorMulTransverseVec (Fin 2)
        (constOneLInf - (inputMul p R hR).value) f := by
    rw [scalarVectorMulTransverseVec_constOne_sub]
    rfl
  rw [hEq]
  calc
    ‖scalarVectorMulTransverseVec (Fin 2)
        (constOneLInf - (inputMul p R hR).value) f‖ ≤
        ‖constOneLInf - (inputMul p R hR).value‖ * ‖f‖ :=
      norm_scalarVectorMulTransverseVec_apply_le _ _
    _ ≤ 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (norm_inputMul_complement_value_le_one p R hR hbox) (norm_nonneg f)

/-- `|ψ_n| ≤ 1`. -/
theorem norm_outputMul_value_le_one
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖(outputMul p R hR).value‖ ≤ 1 := by
  refine norm_cutoff_value_le _ (nowrap_outputSchwartz p R hR hbox) zero_le_one fun x ↦ ?_
  rw [outputSchwartz, realSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (outputCutoff_mem_Icc p R hR x).1]
  exact (outputCutoff_mem_Icc p R hR x).2

/-- `|χ_n| ≤ 1`. -/
theorem norm_backgroundMul_value_le_one
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖(backgroundMul p R hR).value‖ ≤ 1 := by
  apply norm_transverseScalarLInf_le_of_ae_bound _ zero_le_one
  filter_upwards [backgroundMul_value_ae p R hR hbox] with q hq
  rw [hq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (backgroundCutoff_mem_Icc p R hR _).1]
  exact (backgroundCutoff_mem_Icc p R hR _).2

/-- The coordinate derivative of the background bump is minus that of the background
cut-off. -/
theorem realProfileCoordinateDerivative_backgroundBump (j : Fin 2) (x : WholePlane) :
    realProfileCoordinateDerivative ((backgroundBump p R hR : WholePlane → ℝ)) j x =
      -realProfileCoordinateDerivative (backgroundCutoff p R hR) j x := by
  have hfd : fderiv ℝ (backgroundCutoff p R hR) x =
      -fderiv ℝ ((backgroundBump p R hR : WholePlane → ℝ)) x := by
    change fderiv ℝ (fun y ↦ (1 : ℝ) - (backgroundBump p R hR) y) x = _
    exact fderiv_const_sub (1 : ℝ)
  change _ = -(fderiv ℝ (backgroundCutoff p R hR) x (wholePlaneBasis j))
  rw [hfd]
  simp [realProfileCoordinateDerivative]

/-- `‖∂_jψ_n‖_∞ ≤ C₁/R_n` (`eq:parametrix-cutoff-bounds`). -/
theorem norm_outputMul_gradient_le
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) (j : Fin 2) :
    ‖(outputMul p R hR).gradient j‖ ≤ cutoffFirstDerivativeConstant / R := by
  have hC : (0 : ℝ) ≤ cutoffFirstDerivativeConstant / R :=
    le_of_lt (div_pos cutoffFirstDerivativeConstant_pos hR)
  refine norm_cutoff_gradient_le _ j (nowrap_outputSchwartz_deriv p R hR hbox j) hC fun x ↦ ?_
  rw [outputSchwartz, lineDerivOp_realSchwartz_apply, Complex.norm_real]
  have hsum := norm_cutoff_coordinateDerivative_sum_le p R hR j x
  have h1 := norm_nonneg (realProfileCoordinateDerivative (inputCutoff p R hR) j x)
  have h3 := norm_nonneg (realProfileCoordinateDerivative (backgroundCutoff p R hR) j x)
  linarith

/-- `‖∂_jχ_n‖_∞ ≤ C₁/R_n` (`eq:parametrix-cutoff-bounds`). -/
theorem norm_backgroundMul_gradient_le
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) (j : Fin 2) :
    ‖(backgroundMul p R hR).gradient j‖ ≤ cutoffFirstDerivativeConstant / R := by
  have hC : (0 : ℝ) ≤ cutoffFirstDerivativeConstant / R :=
    le_of_lt (div_pos cutoffFirstDerivativeConstant_pos hR)
  change ‖-(SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).gradient j‖ ≤ _
  rw [norm_neg]
  refine norm_cutoff_gradient_le _ j (nowrap_backgroundSchwartz_deriv p R hR hbox j) hC
    fun x ↦ ?_
  rw [backgroundSchwartz, lineDerivOp_realSchwartz_apply, Complex.norm_real,
    realProfileCoordinateDerivative_backgroundBump, norm_neg]
  have hsum := norm_cutoff_coordinateDerivative_sum_le p R hR j x
  have h1 := norm_nonneg (realProfileCoordinateDerivative (inputCutoff p R hR) j x)
  have h2 := norm_nonneg (realProfileCoordinateDerivative (outputCutoff p R hR) j x)
  linarith

/-- `‖Δψ_n‖_∞ ≤ 2C₂/R_n²` (`eq:parametrix-cutoff-bounds`). -/
theorem norm_outputMul_laplacian_le
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖(outputMul p R hR).laplacian‖ ≤ 2 * cutoffSecondDerivativeConstant / R ^ 2 := by
  have hden : (0 : ℝ) < R ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ 2 * (cutoffSecondDerivativeConstant / R ^ 2) :=
    mul_nonneg (by norm_num) (le_of_lt (div_pos cutoffSecondDerivativeConstant_pos hden))
  have hsecond : ∀ x, ‖iteratedFDeriv ℝ 2
      ((outputSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) x‖ ≤
      cutoffSecondDerivativeConstant / R ^ 2 := by
    intro x
    rw [outputSchwartz, norm_iteratedFDeriv_realSchwartz]
    have hsum := norm_cutoff_iteratedFDeriv_two_sum_le p R hR x
    have h1 := norm_nonneg (iteratedFDeriv ℝ 2 (inputCutoff p R hR) x)
    have h3 := norm_nonneg (iteratedFDeriv ℝ 2 (backgroundCutoff p R hR) x)
    linarith
  have hmain := norm_cutoff_laplacian_le (outputSchwartz p R hR)
    (nowrap_outputSchwartz_laplacian p R hR hbox) hC
    (fun x ↦ norm_schwartzLaplacian_apply_le _ hsecond x)
  calc ‖(outputMul p R hR).laplacian‖ ≤ 2 * (cutoffSecondDerivativeConstant / R ^ 2) := hmain
    _ = 2 * cutoffSecondDerivativeConstant / R ^ 2 := by ring

/-- `‖Δχ_n‖_∞ ≤ 2C₂/R_n²` (`eq:parametrix-cutoff-bounds`). -/
theorem norm_backgroundMul_laplacian_le
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ‖(backgroundMul p R hR).laplacian‖ ≤ 2 * cutoffSecondDerivativeConstant / R ^ 2 := by
  have hden : (0 : ℝ) < R ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ 2 * (cutoffSecondDerivativeConstant / R ^ 2) :=
    mul_nonneg (by norm_num) (le_of_lt (div_pos cutoffSecondDerivativeConstant_pos hden))
  have hsecond : ∀ x, ‖iteratedFDeriv ℝ 2
      ((backgroundSchwartz p R hR : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) x‖ ≤
      cutoffSecondDerivativeConstant / R ^ 2 := by
    intro x
    rw [backgroundSchwartz, norm_iteratedFDeriv_realSchwartz]
    have hneg : ‖iteratedFDeriv ℝ 2 ((backgroundBump p R hR : WholePlane → ℝ)) x‖ =
        ‖iteratedFDeriv ℝ 2 (backgroundCutoff p R hR) x‖ := by
      rw [backgroundCutoff_iteratedFDeriv_two_eq, norm_neg]
    rw [hneg]
    have hsum := norm_cutoff_iteratedFDeriv_two_sum_le p R hR x
    have h1 := norm_nonneg (iteratedFDeriv ℝ 2 (inputCutoff p R hR) x)
    have h2 := norm_nonneg (iteratedFDeriv ℝ 2 (outputCutoff p R hR) x)
    linarith
  have hmain := norm_cutoff_laplacian_le (backgroundSchwartz p R hR)
    (nowrap_backgroundSchwartz_laplacian p R hR hbox) hC
    (fun x ↦ norm_schwartzLaplacian_apply_le _ hsecond x)
  have hval : ‖(backgroundMul p R hR).laplacian‖ =
      ‖(SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).laplacian‖ := by
    change ‖-(SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).laplacian‖ = _
    rw [norm_neg]
  calc ‖(backgroundMul p R hR).laplacian‖ ≤
        2 * (cutoffSecondDerivativeConstant / R ^ 2) := by rw [hval]; exact hmain
    _ = 2 * cutoffSecondDerivativeConstant / R ^ 2 := by ring

/-! ## `eq:parametrix-cutoff-identities` for the three placed multipliers -/

/-- Multiplying by `a` after subtracting the `b`-multiple is multiplying by `a - ab`. -/
private theorem scalarVectorMul_sub_comp (a b : TransverseScalarLInf) (f : TransverseC2L2) :
    scalarVectorMulTransverseVec (Fin 2) a
        (f - scalarVectorMulTransverseVec (Fin 2) b f) =
      scalarVectorMulTransverseVec (Fin 2) (a - scalarMulTransverseLInf a b) f := by
  have h1 : scalarVectorMulTransverseVec (Fin 2) a
      (f - scalarVectorMulTransverseVec (Fin 2) b f) =
      scalarVectorMulTransverseVec (Fin 2) a f -
        scalarVectorMulTransverseVec (Fin 2) a
          (scalarVectorMulTransverseVec (Fin 2) b f) :=
    map_sub _ _ _
  have h2 : scalarVectorMulTransverseVec (Fin 2) (a - scalarMulTransverseLInf a b) f =
      scalarVectorMulTransverseVec (Fin 2) a f -
        scalarVectorMulTransverseVec (Fin 2) (scalarMulTransverseLInf a b) f := by
    rw [map_sub, sub_apply]
  rw [h1, h2, TransverseVecMultiplierAlgebra.scalarVectorMulTransverseVec_mulLInf]

/-- **`ψ_nφ_n = φ_n`** (`eq:parametrix-cutoff-identities`), at the level of the placed
`L²` multipliers. -/
theorem outputMul_comp_inputMul
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (outputMul p R hR).stateMul.comp (inputMul p R hR).stateMul =
      (inputMul p R hR).stateMul := by
  have hprod : scalarMulTransverseLInf (outputMul p R hR).value (inputMul p R hR).value =
      (inputMul p R hR).value := by
    apply Lp.ext
    filter_upwards [scalarMulTransverseLInf_coe_ae (outputMul p R hR).value
        (inputMul p R hR).value, outputMul_value_ae p R hR hbox,
      inputMul_value_ae p R hR hbox] with q hmul hout hin
    rw [hmul, hout, hin]
    norm_cast
    exact outputCutoff_mul_inputCutoff p R hR _
  apply ContinuousLinearMap.ext
  intro f
  change scalarVectorMulTransverseVec (Fin 2) (outputMul p R hR).value
      (scalarVectorMulTransverseVec (Fin 2) (inputMul p R hR).value f) = _
  rw [← TransverseVecMultiplierAlgebra.scalarVectorMulTransverseVec_mulLInf, hprod]
  rfl

/-- **`χ_n(1 - φ_n) = 1 - φ_n`** (`eq:parametrix-cutoff-identities`), at the level of
the placed `L²` multipliers. -/
theorem backgroundMul_comp_inputComplement
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (backgroundMul p R hR).stateMul.comp
        (ContinuousLinearMap.id ℂ TransverseC2L2 - (inputMul p R hR).stateMul) =
      ContinuousLinearMap.id ℂ TransverseC2L2 - (inputMul p R hR).stateMul := by
  have hLInf : (backgroundMul p R hR).value -
      scalarMulTransverseLInf (backgroundMul p R hR).value (inputMul p R hR).value =
      constOneLInf - (inputMul p R hR).value := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (backgroundMul p R hR).value
        (scalarMulTransverseLInf (backgroundMul p R hR).value (inputMul p R hR).value),
      Lp.coeFn_sub constOneLInf (inputMul p R hR).value,
      scalarMulTransverseLInf_coe_ae (backgroundMul p R hR).value (inputMul p R hR).value,
      constOneLInf_coe_ae, backgroundMul_value_ae p R hR hbox,
      inputMul_value_ae p R hR hbox] with q hs1 hs2 hmul hone hbg hin
    rw [hs1, hs2]
    change (backgroundMul p R hR).value q -
      (scalarMulTransverseLInf (backgroundMul p R hR).value (inputMul p R hR).value) q =
        (constOneLInf : TransverseTorus → ℂ) q - (inputMul p R hR).value q
    rw [hmul, hone, hbg, hin]
    norm_cast
    have h := backgroundCutoff_mul_one_sub_inputCutoff p R hR
      (wholePlaneIocRepresentative q)
    nlinarith [h]
  apply ContinuousLinearMap.ext
  intro f
  change scalarVectorMulTransverseVec (Fin 2) (backgroundMul p R hR).value
      (f - scalarVectorMulTransverseVec (Fin 2) (inputMul p R hR).value f) = _
  rw [scalarVectorMul_sub_comp, hLInf, scalarVectorMulTransverseVec_constOne_sub]
  rfl

/-! ## The placed bundle -/

/-- **The three placed parametrix cut-offs of one cell**, as the bundle consumed by the
two-summand parametrix of `FastDynamo/Global/TorusTwoSummandParametrix.lean`
(§7.1, `sec:parametrix`). -/
def placedCutoffs (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    HorizontalParametrixCutoffs R where
  radius_pos := hR
  input := inputMul p R hR
  output := outputMul p R hR
  background := backgroundMul p R hR
  norm_input_value_le_one := norm_inputMul_value_le_one p R hR hbox
  norm_inputComplement_le_one := norm_inputMul_complement_le_one p R hR hbox
  norm_output_value_le_one := norm_outputMul_value_le_one p R hR hbox
  norm_background_value_le_one := norm_backgroundMul_value_le_one p R hR hbox
  norm_output_gradient_le := norm_outputMul_gradient_le p R hR hbox
  norm_output_laplacian_le := norm_outputMul_laplacian_le p R hR hbox
  norm_background_gradient_le := norm_backgroundMul_gradient_le p R hR hbox
  norm_background_laplacian_le := norm_backgroundMul_laplacian_le p R hR hbox
  background_mul_inputComplement := backgroundMul_comp_inputComplement p R hR hbox
  output_mul_input := outputMul_comp_inputMul p R hR hbox

/-- The input cut-off of the placed bundle. -/
@[simp] theorem placedCutoffs_input
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (placedCutoffs p R hR hbox).input = inputMul p R hR :=
  rfl

/-- The output cut-off of the placed bundle. -/
@[simp] theorem placedCutoffs_output
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (placedCutoffs p R hR hbox).output = outputMul p R hR :=
  rfl

/-- The background cut-off of the placed bundle. -/
@[simp] theorem placedCutoffs_background
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (placedCutoffs p R hR hbox).background = backgroundMul p R hR :=
  rfl

end TorusPlacedCutoffC2

end

end FastDynamo
