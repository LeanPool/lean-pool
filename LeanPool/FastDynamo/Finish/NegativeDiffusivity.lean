/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductVectorCalculus
public import LeanPool.FastDynamo.Operator.Product

/-!
# Negative diffusivity counterexample

This module records the sharp obstruction behind the sign hypothesis `0 ≤ ε` that the
formalisation adds to its auxiliary solenoidality theorem: if diffusivity is negative, already the
zero velocity has a positive eigenvalue with a non-solenoidal eigenfunction.

The paper has no such theorem — it recovers the axial component in `lem:axial-recovery`
(Lemma 8.1) — so the counterexample below is a result of the formalisation.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The zero transverse frequency, at which the counterexample mode is supported. -/
def zeroFrequency : TransverseFrequency := 0

/-- The Fourier coefficient array supported at transverse frequency zero. -/
def transverseConstantCoeff : TransverseScalarFourierL2 :=
  lp.single 2 zeroFrequency 1

/-- Three scalar coordinate fields, with only the axial coordinate nonzero. -/
def transverseVerticalCoords : TransverseC3CoordinateL2 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = (2 : Fin 3) then
      transverseScalarFourierSynthesis transverseConstantCoeff
    else 0)

/--
The `L²` vector field on the transverse torus obtained from `transverseVerticalCoords`: the
spatially constant field pointing along the axial direction `e₃`.
-/
def transverseVerticalPhysical : TransverseC3L2 :=
  transverseC3OfCoordsL2 transverseVerticalCoords

/-- The weighted coefficient certificate for the constant vertical field. -/
def transverseVerticalWeighted : WeightedTransverseC3Coeffs :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = (2 : Fin 3) then transverseConstantCoeff else 0)

/--
The transverse `H²` weight is normalized to `1` at the zero frequency, since the frequency
energy vanishes there.
-/
private lemma transverseH2Weight_zero :
    transverseH2Weight zeroFrequency = 1 := by
  simp [zeroFrequency, transverseH2Weight, transverseFrequencyEnergy]

/-- The constant vertical transverse amplitude as an element of the Fourier
graph `H²` domain. -/
def transverseConstantVerticalH2 : TransverseC3H2 :=
  ⟨(transverseVerticalPhysical, transverseVerticalWeighted), by
    rw [mem_transverseH2Submodule_iff]
    intro n i
    rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply]
    change (transverseVerticalWeighted i) n =
      (transverseH2Weight n : ℂ) *
        transverseScalarCoeffCLM n
          (transverseCoordL2 i
            (transverseC3OfCoordsL2 transverseVerticalCoords))
    rw [
      transverseCoordL2_transverseC3OfCoordsL2]
    change (if i = (2 : Fin 3) then transverseConstantCoeff else 0) n =
      (transverseH2Weight n : ℂ) *
        transverseScalarCoeffCLM n
          (if i = (2 : Fin 3) then
            transverseScalarFourierSynthesis transverseConstantCoeff else 0)
    by_cases hi : i = (2 : Fin 3)
    · subst i
      simp only [ite_true, transverseScalarCoeffCLM_synthesis]
      by_cases hn : n = zeroFrequency
      · subst n
        rw [transverseH2Weight_zero]
        simp [transverseConstantCoeff]
      · simp [transverseConstantCoeff, hn]
    · simp [hi] ⟩

/--
The constant vertical amplitude has Fourier coefficient `1` in the third component at the zero
transverse frequency; this is what makes it a nonzero element of the graph `H²` space.
-/
theorem transverseConstantVerticalH2_coeff :
    transverseCoeffCLM zeroFrequency (2 : Fin 3)
        (transverseH2Embedding transverseConstantVerticalH2) = 1 := by
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply]
  change transverseScalarCoeffCLM zeroFrequency
      (transverseCoordL2 (2 : Fin 3)
        (transverseC3OfCoordsL2 transverseVerticalCoords)) = 1
  rw [transverseCoordL2_transverseC3OfCoordsL2]
  change transverseScalarCoeffCLM zeroFrequency
      (transverseScalarFourierSynthesis transverseConstantCoeff) = 1
  rw [transverseScalarCoeffCLM_synthesis]
  simp [transverseConstantCoeff]

/--
The constant vertical amplitude `transverseConstantVerticalH2` is a nonzero element of
`TransverseC3H2`, since one of its Fourier coefficients equals `1`.
-/
theorem transverseConstantVerticalH2_ne_zero :
    transverseConstantVerticalH2 ≠ 0 := by
  intro hzero
  have hcoeff := transverseConstantVerticalH2_coeff
  rw [hzero, map_zero, map_zero] at hcoeff
  exact one_ne_zero hcoeff.symm

/--
The transverse Laplacian annihilates the constant vertical amplitude: its only nonvanishing
Fourier coefficient sits at frequency zero, where the Laplacian symbol is zero.
-/
theorem transverseLaplacian_constantVerticalH2 :
    transverseLaplacianFromH2 transverseConstantVerticalH2 = 0 := by
  apply transverseC3L2_ext_coeff
  intro n i
  rw [transverseCoeffCLM_transverseLaplacianFromH2, map_zero]
  by_cases hn : n = zeroFrequency
  · subst n
    simp [zeroFrequency, transverseFrequencyEnergy]
  · have hcoeff :
        transverseCoeffCLM n i
            (transverseH2Embedding transverseConstantVerticalH2) = 0 := by
      rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply]
      change transverseScalarCoeffCLM n
          (transverseCoordL2 i
            (transverseC3OfCoordsL2 transverseVerticalCoords)) = 0
      rw [transverseCoordL2_transverseC3OfCoordsL2]
      by_cases hi : i = (2 : Fin 3)
      · subst i
        change transverseScalarCoeffCLM n
            (transverseScalarFourierSynthesis transverseConstantCoeff) = 0
        rw [transverseScalarCoeffCLM_synthesis]
        simp [transverseConstantCoeff, hn]
      · simp [transverseVerticalCoords, hi]
    rw [hcoeff, mul_zero]

/-- The positive eigenvalue created by a negative diffusivity at unit axial
frequency. -/
def negativeDiffusivityEigenvalue (ε : ℝ) : ℂ :=
  -(ε : ℂ) * (2 * Real.pi : ℂ) ^ 2

/--
At zero velocity, axial index `K = 1`, and diffusivity `ε`, the reduced induction action sends
the constant vertical amplitude to `negativeDiffusivityEigenvalue ε` times itself: the transport
and stretching terms vanish with `u = 0`, and only the axial diffusion symbol `-ε(2π)²` survives.
-/
private theorem reducedInductionAction_zero_constantVertical
    (ε : ℝ) :
    reducedInductionAction (0 : TransverseRealW1Inf) ε 1
        transverseConstantVerticalH2 =
      negativeDiffusivityEigenvalue ε •
        transverseH2Embedding transverseConstantVerticalH2 := by
  rw [reducedInductionAction_apply,
    transverseLaplacian_constantVerticalH2]
  simp [negativeDiffusivityEigenvalue, axialMultiplier, smul_smul]

/-- At zero velocity and negative diffusivity, the unit axial Fourier mode
with vertical polarization is an eigenpair of the auxiliary induction
operator. -/
theorem negativeDiffusivity_auxiliary_eigenpair (ε : ℝ) :
    (productInductionOperator (0 : TransverseRealW1Inf) ε).IsEigenpair
      (negativeDiffusivityEigenvalue ε)
      (axialLiftH2 1 transverseConstantVerticalH2) := by
  rw [productInductionEigenpair_axialLiftH2_iff_reduced]
  constructor
  · change transverseH2Embedding transverseConstantVerticalH2 ≠ 0
    intro hzero
    apply transverseConstantVerticalH2_ne_zero
    exact transverseH2Embedding_injective (by simpa using hzero)
  · exact reducedInductionAction_zero_constantVertical ε

/-- The real part of the counterexample eigenvalue is `-ε (2π)²`. -/
theorem negativeDiffusivityEigenvalue_re (ε : ℝ) :
    (negativeDiffusivityEigenvalue ε).re =
      -ε * (2 * Real.pi) ^ 2 := by
  simp [negativeDiffusivityEigenvalue, Complex.mul_re, pow_two]

/--
For negative diffusivity `ε < 0` the counterexample eigenvalue has strictly positive real part,
so the mode is growing.
-/
theorem negativeDiffusivityEigenvalue_pos {ε : ℝ} (hε : ε < 0) :
    0 < (negativeDiffusivityEigenvalue ε).re := by
  rw [negativeDiffusivityEigenvalue_re]
  exact mul_pos (neg_pos.mpr hε) (sq_pos_of_pos (mul_pos two_pos Real.pi_pos))

/-- The counterexample eigenfunction has nonzero divergence. -/
theorem negativeDiffusivity_mode_not_solenoidal :
    productDivergenceFromH2
        (axialLiftH2 1 transverseConstantVerticalH2) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (productScalarCoeffCLM zeroFrequency 1) hzero
  rw [map_zero,
    productScalarCoeffCLM_productDivergenceFromH2] at hcoeff
  simp only [productCoeffCLM_productH2Embedding_axialLiftH2, ite_true,
    transverseConstantVerticalH2_coeff] at hcoeff
  simp [zeroFrequency] at hcoeff

/--
The counterexample eigenfunction is not solenoidal in the predicate form `IsProductSolenoidal`
used for `L²` fields on the three-torus; this is `negativeDiffusivity_mode_not_solenoidal`
transported along `productDivergenceFromH2_eq_zero_iff`. It shows the hypothesis `0 ≤ ε` cannot
be dropped from the auxiliary solenoidality theorem.
-/
theorem negativeDiffusivity_mode_not_productSolenoidal :
    ¬ IsProductSolenoidal
      (productH2Embedding (axialLiftH2 1 transverseConstantVerticalH2)) := by
  rw [← productDivergenceFromH2_eq_zero_iff]
  exact negativeDiffusivity_mode_not_solenoidal

/-- Sharp counterexample to the auxiliary solenoidality theorem without `0 ≤ ε`.

For every negative real diffusivity, zero velocity has a positive-real-part
auxiliary induction eigenpair whose eigenfunction is not divergence-free. -/
theorem exists_positive_nonsolenoidal_eigenpair_of_negative_diffusivity
    {ε : ℝ} (hε : ε < 0) :
    ∃ (eigenvalue : ℂ) (B : ProductC3H2),
      0 < eigenvalue.re ∧
      (productInductionOperator (0 : TransverseRealW1Inf) ε).IsEigenpair eigenvalue B ∧
      productDivergenceFromH2 B ≠ 0 := by
  exact ⟨negativeDiffusivityEigenvalue ε,
    axialLiftH2 1 transverseConstantVerticalH2,
    negativeDiffusivityEigenvalue_pos hε,
    negativeDiffusivity_auxiliary_eigenpair ε,
    negativeDiffusivity_mode_not_solenoidal⟩

end

end FastDynamo
