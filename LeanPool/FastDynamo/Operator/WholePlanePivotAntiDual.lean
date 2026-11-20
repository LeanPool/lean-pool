/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.FourierMultiplierSub
public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Operator.WholePlaneLocal
public import LeanPool.FastDynamo.Analysis.WholePlaneH1AntiDual

/-!
# Ambient `H¹` anti-dual semantics of pivot functionals

A local form tested against whole-plane `H¹` produces pivot functionals
`φ ↦ ⟪j φ, f⟫` with `f ∈ L²`.  This module identifies them, through the canonical `H⁻¹`
realization, with explicit tempered distributions: for the value embedding the pivot is the
distribution represented by `f`
(`wholePlaneH1AntiDualToTempered_associatedFormPivot_embedding`), and for the `j`-th weak
derivative it is the negative distributional derivative `-∂_j f`
(`wholePlaneH1AntiDualToTempered_associatedFormPivot_firstDerivative`).  Both statements are
generic in the fibre.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped FourierTransform LineDeriv

/-! ## Ambient `H¹` anti-dual semantics -/

/-- The order-minus-one Bessel coefficient of an ambient pivot functional is
the inverse order-one weight times the Fourier transform of the represented
`L²` field.  This is the coefficient calculation behind the literal
distributional pivot bridge below. -/
private theorem
    wholePlaneH1AntiDualToSobolevMinusOne_associatedFormPivot_embedding_coeff
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [CompleteSpace F] (f : WholePlaneL2 F) :
    wholePlaneSobolevCoeff (-1) F
        (wholePlaneH1AntiDualToSobolevMinusOne F
          (associatedFormPivot (wholePlaneH1Embedding F) f)) =
      scalarVectorMulL2 (E := F) volume h1RecoverMassLInf
        (wholePlaneFourierAnalysis F f) := by
  apply ext_inner_left Complex
  intro c
  rw [← wholePlaneH1AntiDualToSobolevMinusOne_pair]
  change inner Complex (h1CoeffToValueL2 F c) f = _
  rw [← inner_wholePlaneFourierAnalysis F]
  rw [h1CoeffToValueL2_fourier]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf c,
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf
      (wholePlaneFourierAnalysis F f),
    h1RecoverMassLInf_coe_ae] with xi hc hf hm
  rw [hc, hf, hm]
  rw [inner_smul_left, inner_smul_right]
  simp [h1RecoverMass]

/-- The complex-valued order-one Bessel weight has temperate growth. -/
private theorem wholePlaneBesselOneWeight_complex_hasTemperateGrowth :
    (fun xi : WholePlane =>
      (wholePlaneBesselOneWeight xi : Complex)).HasTemperateGrowth := by
  unfold wholePlaneBesselOneWeight
  rw [show (fun xi : WholePlane =>
      (Real.sqrt (1 + ‖xi‖ ^ 2) : Complex)) =
      fun xi : WholePlane =>
        (((1 + ‖xi‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : Complex) by
    funext xi
    rw [← Real.sqrt_eq_rpow]]
  exact (Complex.ofRealCLM.hasTemperateGrowth).comp
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow
      WholePlane (1 / 2 : ℝ))

private theorem negativeOrderRecoveryWeight :
    (fun xi : WholePlane ↦
      (((1 + ‖xi‖ ^ 2) ^ (-(-1 : ℝ) / 2) : ℝ) : Complex)) =
      fun xi ↦ (wholePlaneBesselOneWeight xi : Complex) := by
  funext xi
  norm_cast
  unfold wholePlaneBesselOneWeight
  rw [Real.sqrt_eq_rpow]
  congr 1
  rw [Rat.cast_divInt]
  norm_num

/-- The canonical `H⁻¹` realization of an ambient `L²` pivot functional is
exactly the tempered distribution represented by that same `L²` field.

This compatibility is the zero-order semantic bridge needed to identify a form
residual with its literal differential distribution. -/
theorem wholePlaneH1AntiDualToTempered_associatedFormPivot_embedding
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [CompleteSpace F] (f : WholePlaneL2 F) :
    wholePlaneH1AntiDualToTempered F
        (associatedFormPivot (wholePlaneH1Embedding F) f) =
      wholePlaneL2ToTempered F f := by
  apply (FourierTransform.fourierCLE Complex
    (TemperedDistribution WholePlane F)).injective
  change FourierTransform.fourier (wholePlaneSobolevToTempered (-1) F
      (wholePlaneH1AntiDualToSobolevMinusOne F
        (associatedFormPivot (wholePlaneH1Embedding F) f))) =
    FourierTransform.fourier (wholePlaneL2ToTempered F f)
  rw [fourier_wholePlaneSobolevToTempered,
    wholePlaneH1AntiDualToSobolevMinusOne_associatedFormPivot_embedding_coeff,
    fourier_wholePlaneL2ToTempered]
  simp only [negativeOrderRecoveryWeight]
  apply smulLeftCLM_wholePlaneL2ToTempered_eq_of_ae
      (hg := wholePlaneBesselOneWeight_complex_hasTemperateGrowth)
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf
      (wholePlaneFourierAnalysis F f),
    h1RecoverMassLInf_coe_ae] with xi hmul hmass
  rw [hmul, hmass]
  rw [smul_smul]
  have hs : ((Real.sqrt (1 + ‖xi‖ ^ 2) : ℝ) : Complex) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  simp [wholePlaneBesselOneWeight, h1RecoverMass, hs]

/-- The order-minus-one Bessel coefficient of a coordinate-derivative pivot
functional is the negative derivative-recovery multiplier applied to the
Fourier transform of the represented `L²` field.  The sign comes from
conjugate-linearity in the first argument of Mathlib's inner product. -/
private theorem
    wholePlaneH1AntiDualToSobolevMinusOne_associatedFormPivot_firstDerivative_coeff
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [CompleteSpace F] (j : Fin 2) (f : WholePlaneL2 F) :
    wholePlaneSobolevCoeff (-1) F
        (wholePlaneH1AntiDualToSobolevMinusOne F
          (associatedFormPivot (wholePlaneH1FirstDerivative F j) f)) =
      -scalarVectorMulL2 (E := F) volume (h1CoeffDerivSymbolLInf j)
        (wholePlaneFourierAnalysis F f) := by
  apply ext_inner_left Complex
  intro c
  rw [← wholePlaneH1AntiDualToSobolevMinusOne_pair]
  change inner Complex
      (wholePlaneH1FirstDerivative F j (h1CoeffToGraph F c)) f = _
  rw [wholePlaneH1FirstDerivative_h1CoeffToGraph]
  rw [← inner_wholePlaneFourierAnalysis F]
  rw [h1CoeffToDerivL2_fourier]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1CoeffDerivSymbolLInf j) c,
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1CoeffDerivSymbolLInf j) (wholePlaneFourierAnalysis F f),
    MeasureTheory.Lp.coeFn_neg
      (scalarVectorMulL2 (E := F) volume
        (h1CoeffDerivSymbolLInf j) (wholePlaneFourierAnalysis F f)),
    h1CoeffDerivSymbolLInf_coe_ae j] with xi hc hf hneg hq
  rw [hc, hneg, Pi.neg_apply, hf, hq]
  simp [inner_smul_left, inner_smul_right, h1CoeffDerivSymbol,
    h1RecoverMass, map_ofNat]

/-- Embedding the negative derivative-recovery coefficient into tempered
distributions is multiplication by the corresponding negative symbol. -/
private theorem wholePlaneL2ToTempered_neg_h1CoeffDerivSymbol
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [CompleteSpace F] (j : Fin 2) (f : WholePlaneL2 F) :
    wholePlaneL2ToTempered F
        (-scalarVectorMulL2 (E := F) volume
          (h1CoeffDerivSymbolLInf j) (wholePlaneFourierAnalysis F f)) =
      TemperedDistribution.smulLeftCLM F
        (-h1CoeffDerivSymbol j)
        (wholePlaneL2ToTempered F (wholePlaneFourierAnalysis F f)) := by
  symm
  apply smulLeftCLM_wholePlaneL2ToTempered_eq_of_ae
    (hg := (h1CoeffDerivSymbol_hasTemperateGrowth j).neg)
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1CoeffDerivSymbolLInf j) (wholePlaneFourierAnalysis F f),
    MeasureTheory.Lp.coeFn_neg
      (scalarVectorMulL2 (E := F) volume
        (h1CoeffDerivSymbolLInf j) (wholePlaneFourierAnalysis F f)),
    h1CoeffDerivSymbolLInf_coe_ae j] with xi hmul hneg hsym
  rw [hneg, Pi.neg_apply, hmul, hsym]
  simp

/-- The canonical `H⁻¹` realization of the pivot functional
`phi ↦ inner Complex (∂_j phi) f` is the negative distributional derivative
of the tempered distribution represented by `f`.

This is the generic first-order semantic bridge.  In particular, the minus
sign and the physical `2π` Fourier normalization are proved rather than
inserted as conventions. -/
theorem wholePlaneH1AntiDualToTempered_associatedFormPivot_firstDerivative
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [CompleteSpace F] (j : Fin 2) (f : WholePlaneL2 F) :
    wholePlaneH1AntiDualToTempered F
        (associatedFormPivot (wholePlaneH1FirstDerivative F j) f) =
      -(LineDeriv.lineDerivOp (wholePlaneBasis j)
        (wholePlaneL2ToTempered F f)) := by
  apply (FourierTransform.fourierCLE Complex
    (TemperedDistribution WholePlane F)).injective
  change FourierTransform.fourier (wholePlaneSobolevToTempered (-1) F
      (wholePlaneH1AntiDualToSobolevMinusOne F
        (associatedFormPivot (wholePlaneH1FirstDerivative F j) f))) =
    FourierTransform.fourier
      (-(LineDeriv.lineDerivOp (wholePlaneBasis j)
        (wholePlaneL2ToTempered F f)))
  rw [fourier_wholePlaneSobolevToTempered,
    wholePlaneH1AntiDualToSobolevMinusOne_associatedFormPivot_firstDerivative_coeff,
    wholePlaneL2ToTempered_neg_h1CoeffDerivSymbol]
  simp only [negativeOrderRecoveryWeight]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (h1CoeffDerivSymbol_hasTemperateGrowth j).neg
    wholePlaneBesselOneWeight_complex_hasTemperateGrowth]
  rw [FourierTransform.fourier_neg,
    fourier_lineDeriv_wholePlaneBasis_eq_momentum,
    fourier_wholePlaneL2ToTempered]
  have hsymbols :
      (-h1CoeffDerivSymbol j) *
          (fun xi : WholePlane =>
            (wholePlaneBesselOneWeight xi : Complex)) =
        -(fun xi : WholePlane =>
          Complex.I * wholePlaneMomentum xi j) := by
    funext xi
    have hs : ((Real.sqrt (1 + ‖xi‖ ^ 2) : ℝ) : Complex) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    simp [h1CoeffDerivSymbol, wholePlaneBesselOneWeight, h1RecoverMass,
      wholePlaneMomentum_apply, hs]
    ring
  rw [hsymbols]
  have hp : (fun xi : WholePlane =>
      Complex.I * wholePlaneMomentum xi j).HasTemperateGrowth := by
    have hnegp : (-(fun xi : WholePlane =>
        Complex.I * wholePlaneMomentum xi j)).HasTemperateGrowth := by
      rw [← hsymbols]
      exact (h1CoeffDerivSymbol_hasTemperateGrowth j).neg.mul
        wholePlaneBesselOneWeight_complex_hasTemperateGrowth
    simpa using hnegp.neg
  rw [TemperedDistribution.smulLeftCLM_neg hp]
  simp

end

end FastDynamo
