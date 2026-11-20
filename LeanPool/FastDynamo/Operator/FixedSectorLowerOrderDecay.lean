/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.FixedSectorDiffusionInverse

/-!
# Fourier decay estimates for fixed-sector lower-order terms

This module turns the positive-real diffusion symbol bounds into bounded
coefficient multipliers.  The final vector-valued transport estimate is kept
separate from the scalar diagonal calculation so that every assembly norm is
visible.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The scalar Fourier multiplier for one transverse derivative after the
positive-real diffusion inverse. -/
def reducedInductionDiffusionInverseDerivCoeffMultiplier
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (n : TransverseFrequency) : ℂ :=
  (2 * Real.pi * Complex.I * (n j : ℂ)) *
    reducedInductionDiffusionInverseCoeffMultiplier ε σ K n

/--
The squared modulus `(2π|n_j|)²` of one transverse derivative symbol is dominated by the full
frequency energy `(2π)²|n|²`.
-/
private theorem norm_transverseDerivativeNumerator_sq_le_energy
    (j : Fin 2) (n : TransverseFrequency) :
    ‖(2 * Real.pi * Complex.I * (n j : ℂ))‖ ^ 2 ≤
      transverseFrequencyEnergy n := by
  have hsum : (n j : ℝ) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 := by
    exact Finset.single_le_sum (fun i _ => sq_nonneg (n i : ℝ))
      (Finset.mem_univ j)
  have hnorm : ‖(2 * Real.pi * Complex.I * (n j : ℂ))‖ =
      2 * Real.pi * |(n j : ℝ)| := by
    calc
      ‖(2 * Real.pi * Complex.I * (n j : ℂ))‖ =
          ‖(2 * Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(n j : ℂ)‖ := by
        rw [norm_mul, norm_mul]
      _ = 2 * Real.pi * |(n j : ℝ)| := by
        simp [abs_of_pos Real.pi_pos]
  rw [hnorm]
  unfold transverseFrequencyEnergy
  calc
    (2 * Real.pi * |(n j : ℝ)|) ^ 2 =
        (2 * Real.pi) ^ 2 * (n j : ℝ) ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤ (2 * Real.pi) ^ 2 * ∑ i, (n i : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

/--
The squared modulus of the derivative-after-diffusion-inverse multiplier is at most `(4εσ)⁻¹`,
uniformly in the transverse frequency; this is the `O(σ^{-1/2})` gain of one derivative.
-/
theorem norm_reducedInductionDiffusionInverseDerivCoeffMultiplier_sq_le
    (j : Fin 2) {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    ‖reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n‖ ^ 2 ≤
      (4 * ε * σ)⁻¹ := by
  rw [reducedInductionDiffusionInverseDerivCoeffMultiplier, norm_mul,
    mul_pow]
  have hnum := norm_transverseDerivativeNumerator_sq_le_energy j n
  have hinv : ‖reducedInductionDiffusionInverseCoeffMultiplier ε σ K n‖ ^ 2 =
      (reducedInductionDiffusionInverseSymbol ε σ K n) ^ 2 := by
    simp only [reducedInductionDiffusionInverseCoeffMultiplier,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (reducedInductionDiffusionInverseSymbol_nonneg hε.le hσ K n)]
  rw [hinv]
  exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg _)).trans
    (transverseFrequencyEnergy_mul_inverseSymbol_sq_le hε hσ K n)

/--
Square-root form of the previous bound: the derivative multiplier has modulus at most
`√((4εσ)⁻¹)` at every transverse frequency.
-/
theorem norm_reducedInductionDiffusionInverseDerivCoeffMultiplier_le
    (j : Fin 2) {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (K : ℤ) (n : TransverseFrequency) :
    ‖reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n‖ ≤
      Real.sqrt ((4 * ε * σ)⁻¹) := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (Real.sqrt_nonneg ((4 * ε * σ)⁻¹))).mp
  rw [Real.sq_sqrt]
  · exact norm_reducedInductionDiffusionInverseDerivCoeffMultiplier_sq_le
      j hε hσ K n
  · exact inv_nonneg.mpr (by positivity)

/-- The scalar `ℓ²` multiplier for one derivative after the diffusion
inverse. Its operator bound is the Fourier `O(σ^{-1/2})` estimate. -/
def reducedInductionDiffusionInverseDerivCoeffMap
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n))
    (Real.sqrt_nonneg _)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n)).trans
        (norm_reducedInductionDiffusionInverseDerivCoeffMultiplier_le
          j hε hσ K n))

/--
The derivative-after-inverse coefficient map acts diagonally, multiplying the `n`-th coefficient
by `reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n`.
-/
@[simp] theorem reducedInductionDiffusionInverseDerivCoeffMap_apply
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    reducedInductionDiffusionInverseDerivCoeffMap j ε σ K hε hσ a n =
      reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n * a n :=
  rfl

/--
Operator-norm form of the derivative decay estimate: the diagonal map has norm at most
`√((4εσ)⁻¹)`.
-/
theorem norm_reducedInductionDiffusionInverseDerivCoeffMap_le
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖reducedInductionDiffusionInverseDerivCoeffMap j ε σ K hε hσ‖ ≤
      Real.sqrt ((4 * ε * σ)⁻¹) := by
  exact lp.norm_mapCLM_le 2 _ (Real.sqrt_nonneg _)
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (reducedInductionDiffusionInverseDerivCoeffMultiplier j ε σ K n)).trans
        (norm_reducedInductionDiffusionInverseDerivCoeffMultiplier_le
          j hε hσ K n))

section FibreGeneric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector-valued transverse Fourier multiplier on the fibre `ℂ^ι`, assembled
coordinatewise from a scalar coefficient map. -/
def transverseVecFourierMultiplier (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    TransverseVecL2 ι →L[ℂ] TransverseVecL2 ι :=
  (transverseVecFourierSynthesis ι).comp
    ((mapWeightedVecFourierCoords ι T).comp (transverseVecFourierAnalysis ι))

/-- A vector-valued transverse Fourier multiplier assembled coordinatewise
from a scalar coefficient map. -/
abbrev transverseC3FourierMultiplier
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    TransverseC3L2 →L[ℂ] TransverseC3L2 :=
  transverseVecFourierMultiplier (Fin 3) T

/--
The Fourier coefficients of a coordinatewise vector multiplier are obtained by applying the
scalar coefficient map `T` to the analyzed components of `f`.
-/
theorem transverseCoeff_transverseVecFourierMultiplier
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2)
    (f : TransverseVecL2 ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i (transverseVecFourierMultiplier ι T f) =
      T (transverseVecFourierAnalysis ι f i) n := by
  simp only [transverseVecFourierMultiplier, ContinuousLinearMap.comp_apply,
    transverseCoeffCLM_transverseVecFourierSynthesis,
    mapWeightedVecFourierCoords_apply]

/-- Three-component form of the coefficient formula for a vector Fourier multiplier. -/
theorem transverseCoeff_transverseC3FourierMultiplier
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2)
    (f : TransverseC3L2) (n : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM n i (transverseC3FourierMultiplier T f) =
      T (transverseC3FourierAnalysis f i) n :=
  transverseCoeff_transverseVecFourierMultiplier T f n i

omit [DecidableEq ι] in
/-- Coordinatewise scalar multipliers on the fibre `ℓ²` product have no larger norm than
their scalar multiplier. -/
theorem norm_mapWeightedVecFourierCoords_le
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    ‖mapWeightedVecFourierCoords ι T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg T) (norm_nonneg a))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  calc
    ∑ i, ‖mapWeightedVecFourierCoords ι T a i‖ ^ 2 ≤
        ∑ i, (‖T‖ * ‖a i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mapWeightedVecFourierCoords_apply]
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg T) (norm_nonneg (a i)))).2 (T.le_opNorm _)
    _ = ‖T‖ ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

/-- The vector Fourier assembly costs only fixed analysis/synthesis norms. -/
theorem norm_transverseVecFourierMultiplier_le
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    ‖transverseVecFourierMultiplier ι T‖ ≤
      ‖transverseVecFourierSynthesis ι‖ *
        (‖T‖ * ‖transverseVecFourierAnalysis ι‖) := by
  calc
    ‖transverseVecFourierMultiplier ι T‖ ≤
        ‖transverseVecFourierSynthesis ι‖ *
          ‖(mapWeightedVecFourierCoords ι T).comp
            (transverseVecFourierAnalysis ι)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖transverseVecFourierSynthesis ι‖ *
        (‖mapWeightedVecFourierCoords ι T‖ *
          ‖transverseVecFourierAnalysis ι‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖transverseVecFourierSynthesis ι‖ *
        (‖T‖ * ‖transverseVecFourierAnalysis ι‖) := by
      gcongr
      exact norm_mapWeightedVecFourierCoords_le T

/-- Three-component form of the vector Fourier multiplier norm bound. -/
theorem norm_transverseC3FourierMultiplier_le
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2) :
    ‖transverseC3FourierMultiplier T‖ ≤
      ‖transverseC3FourierSynthesis‖ * (‖T‖ * ‖transverseC3FourierAnalysis‖) :=
  norm_transverseVecFourierMultiplier_le T

/--
The diffusion inverse followed by the `H² → L²` embedding is exactly the vector Fourier
multiplier with symbol `reducedInductionDiffusionInverseCoeffMap ε σ K`.
-/
theorem transverseH2Embedding_comp_transverseVecDiffusionInverse_eq
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    transverseH2Embedding.comp
      (transverseVecDiffusionInverse ι ε σ K hε hσ) =
      transverseVecFourierMultiplier ι
        (reducedInductionDiffusionInverseCoeffMap ε σ K hε.le hσ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply transverseVecL2_ext_coeff
  intro n i
  rw [ContinuousLinearMap.comp_apply,
    transverseCoeff_transverseVecDiffusionInverse,
    transverseCoeff_transverseVecFourierMultiplier,
    reducedInductionDiffusionInverseCoeffMap_apply,
    transverseVecFourierAnalysisCoeff]

/--
The diffusion inverse followed by one transverse derivative is exactly the vector Fourier
multiplier with symbol `reducedInductionDiffusionInverseDerivCoeffMap j ε σ K`.
-/
theorem transverseVecDerivFromH2_comp_transverseVecDiffusionInverse_eq
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    (transverseVecDerivFromH2 ι j).comp
      (transverseVecDiffusionInverse ι ε σ K hε hσ) =
      transverseVecFourierMultiplier ι
        (reducedInductionDiffusionInverseDerivCoeffMap j ε σ K hε hσ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply transverseVecL2_ext_coeff
  intro n i
  rw [ContinuousLinearMap.comp_apply,
    transverseCoeffCLM_transverseDerivFromH2,
    transverseCoeff_transverseVecDiffusionInverse,
    transverseCoeff_transverseVecFourierMultiplier,
    reducedInductionDiffusionInverseDerivCoeffMap_apply,
    transverseVecFourierAnalysisCoeff,
    reducedInductionDiffusionInverseDerivCoeffMultiplier,
    reducedInductionDiffusionInverseCoeffMultiplier]
  ring

/-- Operator-norm bound of order `σ⁻¹` for the diffusion inverse read back in physical `L²`. -/
theorem norm_transverseH2Embedding_comp_transverseVecDiffusionInverse_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖transverseH2Embedding.comp
      (transverseVecDiffusionInverse ι ε σ K hε hσ)‖ ≤
      ‖transverseVecFourierSynthesis ι‖ *
        (σ⁻¹ * ‖transverseVecFourierAnalysis ι‖) := by
  rw [transverseH2Embedding_comp_transverseVecDiffusionInverse_eq]
  calc
    ‖transverseVecFourierMultiplier ι
        (reducedInductionDiffusionInverseCoeffMap ε σ K hε.le hσ)‖ ≤
        ‖transverseVecFourierSynthesis ι‖ *
          (‖reducedInductionDiffusionInverseCoeffMap ε σ K hε.le hσ‖ *
            ‖transverseVecFourierAnalysis ι‖) :=
      norm_transverseVecFourierMultiplier_le _
    _ ≤ ‖transverseVecFourierSynthesis ι‖ *
        (σ⁻¹ * ‖transverseVecFourierAnalysis ι‖) := by
      gcongr
      exact norm_reducedInductionDiffusionInverseCoeffMap_le ε σ K hε.le hσ

/-- Three-component form of the order-`σ⁻¹` bound. -/
theorem norm_transverseH2Embedding_comp_reducedInductionDiffusionInverse_le
    (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖transverseH2Embedding.comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      ‖transverseC3FourierSynthesis‖ *
        (σ⁻¹ * ‖transverseC3FourierAnalysis‖) :=
  norm_transverseH2Embedding_comp_transverseVecDiffusionInverse_le ε σ K hε hσ

/--
Operator-norm bound of order `√((4εσ)⁻¹)` for one transverse derivative of the diffusion
inverse.
-/
theorem norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverse_le
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(transverseVecDerivFromH2 ι j).comp
      (transverseVecDiffusionInverse ι ε σ K hε hσ)‖ ≤
      ‖transverseVecFourierSynthesis ι‖ *
        (Real.sqrt ((4 * ε * σ)⁻¹) *
          ‖transverseVecFourierAnalysis ι‖) := by
  rw [transverseVecDerivFromH2_comp_transverseVecDiffusionInverse_eq]
  calc
    ‖transverseVecFourierMultiplier ι
        (reducedInductionDiffusionInverseDerivCoeffMap j ε σ K hε hσ)‖ ≤
        ‖transverseVecFourierSynthesis ι‖ *
          (‖reducedInductionDiffusionInverseDerivCoeffMap j ε σ K hε hσ‖ *
            ‖transverseVecFourierAnalysis ι‖) :=
      norm_transverseVecFourierMultiplier_le _
    _ ≤ ‖transverseVecFourierSynthesis ι‖ *
        (Real.sqrt ((4 * ε * σ)⁻¹) *
          ‖transverseVecFourierAnalysis ι‖) := by
      gcongr
      exact norm_reducedInductionDiffusionInverseDerivCoeffMap_le
        j ε σ K hε hσ

/-- Three-component form of the order-`√((4εσ)⁻¹)` derivative bound. -/
theorem norm_transverseDerivFromH2_comp_reducedInductionDiffusionInverse_le
    (j : Fin 2) (ε σ : ℝ) (K : ℤ) (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(transverseDerivFromH2 j).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      ‖transverseC3FourierSynthesis‖ *
        (Real.sqrt ((4 * ε * σ)⁻¹) *
          ‖transverseC3FourierAnalysis‖) :=
  norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverse_le j ε σ K hε hσ

/-- A total positive-real ray of diffusion inverses on the fibre `ℂ^ι`. -/
def transverseVecDiffusionInverseRay (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    TransverseVecL2 ι →L[ℂ] TransverseVecH2 ι :=
  transverseVecDiffusionInverse ι ε (Real.exp t) K hε (Real.exp_pos t)

/-- A total positive-real ray of diffusion inverses. -/
abbrev reducedInductionDiffusionInverseRay
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    TransverseC3L2 →L[ℂ] TransverseC3H2 :=
  transverseVecDiffusionInverseRay (Fin 3) ε K hε t

end FibreGeneric

/--
The transverse transport term composed with the diffusion inverse is bounded by the sum of the
velocity multiplication norms times the `O(σ^{-1/2})` derivative bound.

Public because the right-hand side never mentions the axial sector `K`: the axially uniform
assembly of `FastDynamo/Dynamics/Assembly/UniformSectorResolvent.lean` consumes this estimate
unchanged rather than restating it.
-/
theorem norm_reducedInductionTransport_comp_inverse_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ)
    (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(reducedInductionTransport u).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      (∑ j : Fin 2,
        ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)‖) *
        (‖transverseC3FourierSynthesis‖ *
          (Real.sqrt ((4 * ε * σ)⁻¹) *
            ‖transverseC3FourierAnalysis‖)) := by
  let T := reducedInductionDiffusionInverse ε σ K hε hσ
  let C := ‖transverseC3FourierSynthesis‖ *
    (Real.sqrt ((4 * ε * σ)⁻¹) * ‖transverseC3FourierAnalysis‖)
  have hfac : (reducedInductionTransport u).comp T =
      ∑ j : Fin 2,
        (scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
          ((transverseDerivFromH2 j).comp T) := by
    ext f
    simp [reducedInductionTransport, T, ContinuousLinearMap.comp_assoc]
  rw [hfac]
  calc
    ‖∑ j : Fin 2,
        (scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
          ((transverseDerivFromH2 j).comp T)‖ ≤
        ∑ j : Fin 2, ‖(scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
          ((transverseDerivFromH2 j).comp T)‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ j : Fin 2, ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)‖ * C := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖(scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
          ((transverseDerivFromH2 j).comp T)‖ ≤
            ‖scalarVectorMulTransverse
              (transverseW1InfComplexValueCoordLInf j.castSucc u)‖ *
              ‖(transverseDerivFromH2 j).comp T‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖scalarVectorMulTransverse
              (transverseW1InfComplexValueCoordLInf j.castSucc u)‖ * C := by
          gcongr
          exact norm_transverseDerivFromH2_comp_reducedInductionDiffusionInverse_le
            j ε σ K hε hσ
    _ = (∑ j : Fin 2, ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)‖) * C := by
      rw [Finset.sum_mul]

/--
The axial transport term composed with the diffusion inverse is bounded by `|2πK|` times the
norm of multiplication by `u₃` times the `O(σ⁻¹)` physical bound.
-/
private theorem norm_reducedInductionAxialTransport_comp_inverse_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ)
    (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(reducedInductionAxialTransport u K).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      ‖axialMultiplier K‖ *
        ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)‖ *
        (‖transverseC3FourierSynthesis‖ *
          (σ⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
  let T := reducedInductionDiffusionInverse ε σ K hε hσ
  have hfac : (reducedInductionAxialTransport u K).comp T =
      axialMultiplier K •
        (scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)).comp
          (transverseH2Embedding.comp T) := by
    ext f
    simp [reducedInductionAxialTransport, T, ContinuousLinearMap.comp_assoc]
  rw [hfac, norm_smul]
  calc
    ‖axialMultiplier K‖ *
        ‖(scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)).comp
          (transverseH2Embedding.comp T)‖ ≤
        ‖axialMultiplier K‖ *
          (‖scalarVectorMulTransverse
            (transverseW1InfComplexValueCoordLInf 2 u)‖ *
            ‖transverseH2Embedding.comp T‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖axialMultiplier K‖ * ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)‖ *
        (‖transverseC3FourierSynthesis‖ *
          (σ⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
      rw [mul_assoc]
      gcongr
      exact norm_transverseH2Embedding_comp_reducedInductionDiffusionInverse_le
        ε σ K hε hσ

/--
The stretching term composed with the diffusion inverse is bounded by the sum of the
velocity-gradient multiplication norms times the `O(σ⁻¹)` physical bound.

Public for the same reason as `norm_reducedInductionTransport_comp_inverse_le`: the constant
is already free of the axial sector `K`, so the uniform assembly reuses it as it stands.
-/
theorem norm_reducedInductionStretching_comp_inverse_le
    (u : TransverseRealW1Inf) (ε σ : ℝ) (K : ℤ)
    (hε : 0 < ε) (hσ : 0 < σ) :
    ‖(reducedInductionStretching u).comp
      (reducedInductionDiffusionInverse ε σ K hε hσ)‖ ≤
      (∑ j : Fin 2, ‖vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)‖ *
        ‖transverseCoordL2 j.castSucc‖) *
        (‖transverseC3FourierSynthesis‖ *
          (σ⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
  let T := reducedInductionDiffusionInverse ε σ K hε hσ
  let C := ‖transverseC3FourierSynthesis‖ *
    (σ⁻¹ * ‖transverseC3FourierAnalysis‖)
  have hfac : (reducedInductionStretching u).comp T =
      ∑ j : Fin 2, (vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)).comp
          ((transverseCoordL2 j.castSucc).comp
            (transverseH2Embedding.comp T)) := by
    ext f
    simp [reducedInductionStretching, T, ContinuousLinearMap.comp_assoc]
  rw [hfac]
  calc
    ‖∑ j : Fin 2, (vectorScalarMulTransverse
      (transverseW1InfComplexDerivLInf j u)).comp
        ((transverseCoordL2 j.castSucc).comp
          (transverseH2Embedding.comp T))‖ ≤
        ∑ j : Fin 2, ‖(vectorScalarMulTransverse
          (transverseW1InfComplexDerivLInf j u)).comp
            ((transverseCoordL2 j.castSucc).comp
              (transverseH2Embedding.comp T))‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ j : Fin 2, (‖vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)‖ *
        ‖transverseCoordL2 j.castSucc‖) * C := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖(vectorScalarMulTransverse
          (transverseW1InfComplexDerivLInf j u)).comp
            ((transverseCoordL2 j.castSucc).comp
              (transverseH2Embedding.comp T))‖ ≤
            ‖vectorScalarMulTransverse
              (transverseW1InfComplexDerivLInf j u)‖ *
              (‖transverseCoordL2 j.castSucc‖ *
                ‖transverseH2Embedding.comp T‖) := by
          calc
            _ ≤ ‖vectorScalarMulTransverse
              (transverseW1InfComplexDerivLInf j u)‖ *
                ‖(transverseCoordL2 j.castSucc).comp
                  (transverseH2Embedding.comp T)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ _ := by
              gcongr
              exact ContinuousLinearMap.opNorm_comp_le _ _
        _ = (‖vectorScalarMulTransverse
            (transverseW1InfComplexDerivLInf j u)‖ *
            ‖transverseCoordL2 j.castSucc‖) *
            ‖transverseH2Embedding.comp T‖ := by
          ring
        _ ≤ (‖vectorScalarMulTransverse
            (transverseW1InfComplexDerivLInf j u)‖ *
            ‖transverseCoordL2 j.castSucc‖) * C := by
          gcongr
          exact norm_transverseH2Embedding_comp_reducedInductionDiffusionInverse_le
            ε σ K hε hσ
    _ = (∑ j : Fin 2, ‖vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)‖ *
        ‖transverseCoordL2 j.castSucc‖) * C := by
      rw [Finset.sum_mul]

/-- The reciprocal exponential tends to zero at infinity. -/
theorem tendsto_exp_inverse_zero :
    Filter.Tendsto (fun t : ℝ ↦ (Real.exp t)⁻¹)
      Filter.atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop

/-- For fixed `ε > 0` the derivative bound `√((4ε e^t)⁻¹)` tends to zero as `t → ∞`. -/
private theorem tendsto_sqrt_inverse_positive_exp_zero
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun t : ℝ ↦ Real.sqrt ((4 * ε * Real.exp t)⁻¹))
      Filter.atTop (nhds 0) := by
  have hlinear : Filter.Tendsto (fun t : ℝ ↦ (4 * ε) * Real.exp t)
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by positivity)
  have hinverse : Filter.Tendsto (fun t : ℝ ↦ ((4 * ε) * Real.exp t)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlinear
  simpa only [mul_assoc, Real.sqrt_zero] using hinverse.sqrt

/-- The assembled `O(σ⁻¹)` physical bound tends to zero along the exponential ray `σ = e^t`,
at every fibre. -/
theorem tendsto_vecPhysical_inverse_bound_zero (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖transverseVecFourierSynthesis ι‖ *
        ((Real.exp t)⁻¹ * ‖transverseVecFourierAnalysis ι‖))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ ↦ ‖transverseVecFourierSynthesis ι‖)
      Filter.atTop (nhds ‖transverseVecFourierSynthesis ι‖)).mul
    (tendsto_exp_inverse_zero.mul_const ‖transverseVecFourierAnalysis ι‖)
  simpa using h

/-- The assembled `O(σ⁻¹)` physical bound tends to zero along the exponential ray `σ = e^t`. -/
private theorem tendsto_physical_inverse_bound_zero :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖transverseC3FourierSynthesis‖ *
        ((Real.exp t)⁻¹ * ‖transverseC3FourierAnalysis‖))
      Filter.atTop (nhds 0) :=
  tendsto_vecPhysical_inverse_bound_zero (Fin 3)

/-- The assembled `O(σ^{-1/2})` derivative bound tends to zero along the exponential ray
`σ = e^t`, at every fibre. -/
theorem tendsto_vecDerivative_inverse_bound_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι] (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖transverseVecFourierSynthesis ι‖ *
        (Real.sqrt ((4 * ε * Real.exp t)⁻¹) *
          ‖transverseVecFourierAnalysis ι‖))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ ↦ ‖transverseVecFourierSynthesis ι‖)
      Filter.atTop (nhds ‖transverseVecFourierSynthesis ι‖)).mul
    ((tendsto_sqrt_inverse_positive_exp_zero ε hε).mul_const
      ‖transverseVecFourierAnalysis ι‖)
  simpa using h

/-- The assembled `O(σ^{-1/2})` derivative bound tends to zero along the exponential ray
`σ = e^t`. -/
private theorem tendsto_derivative_inverse_bound_zero
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖transverseC3FourierSynthesis‖ *
        (Real.sqrt ((4 * ε * Real.exp t)⁻¹) *
          ‖transverseC3FourierAnalysis‖))
      Filter.atTop (nhds 0) :=
  tendsto_vecDerivative_inverse_bound_zero (Fin 3) ε hε

/-- The physical `L²` norm of the diffusion inverse tends to zero along the exponential ray,
at every fibre.  This is the fibre-blind half of the lower-order decay estimates: every
zeroth-order coefficient term of a torus sector operator is dominated by it. -/
theorem tendsto_norm_transverseH2Embedding_comp_transverseVecDiffusionInverseRay_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι] (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖transverseH2Embedding.comp
        (transverseVecDiffusionInverseRay ι ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_transverseH2Embedding_comp_transverseVecDiffusionInverse_le
      ε (Real.exp t) K hε (Real.exp_pos t)
  · exact tendsto_vecPhysical_inverse_bound_zero ι

/-- One transverse derivative of the diffusion inverse tends to zero along the exponential ray,
at every fibre.  This is the fibre-blind half of the first-order decay estimate. -/
theorem tendsto_norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverseRay_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι] (j : Fin 2) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(transverseVecDerivFromH2 ι j).comp
        (transverseVecDiffusionInverseRay ι ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_transverseVecDerivFromH2_comp_transverseVecDiffusionInverse_le
      j ε (Real.exp t) K hε (Real.exp_pos t)
  · exact tendsto_vecDerivative_inverse_bound_zero ι ε hε

/-- Transverse transport is relatively small along the positive exponential
diffusion ray, with the Fourier `O(\sigma^{-1/2})` derivative estimate. -/
theorem tendsto_norm_reducedInductionTransport_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionTransport u).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_reducedInductionTransport_comp_inverse_le u ε (Real.exp t) K
      hε (Real.exp_pos t)
  · have h := (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ ∑ j : Fin 2,
          ‖scalarVectorMulTransverse
            (transverseW1InfComplexValueCoordLInf j.castSucc u)‖)
        Filter.atTop
          (nhds (∑ j : Fin 2,
            ‖scalarVectorMulTransverse
              (transverseW1InfComplexValueCoordLInf j.castSucc u)‖))).mul
      (tendsto_derivative_inverse_bound_zero ε hε)
    simpa using h

/-- Axial transport is relatively small along the positive exponential
diffusion ray, using the order-zero Fourier multiplier estimate. -/
theorem tendsto_norm_reducedInductionAxialTransport_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionAxialTransport u K).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_reducedInductionAxialTransport_comp_inverse_le
      u ε (Real.exp t) K hε (Real.exp_pos t)
  · have hvalue := (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ ‖scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)‖)
        Filter.atTop
          (nhds ‖scalarVectorMulTransverse
            (transverseW1InfComplexValueCoordLInf 2 u)‖)).mul
      tendsto_physical_inverse_bound_zero
    have h := (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ ‖axialMultiplier K‖) Filter.atTop
          (nhds ‖axialMultiplier K‖)).mul hvalue
    simpa only [mul_assoc, zero_mul, mul_zero] using h

/-- Stretching is relatively small along the positive exponential diffusion
ray, again through the order-zero Fourier estimate. -/
theorem tendsto_norm_reducedInductionStretching_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionStretching u).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_reducedInductionStretching_comp_inverse_le
      u ε (Real.exp t) K hε (Real.exp_pos t)
  · have h := (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ ∑ j : Fin 2,
          ‖vectorScalarMulTransverse
            (transverseW1InfComplexDerivLInf j u)‖ *
            ‖transverseCoordL2 j.castSucc‖)
        Filter.atTop
          (nhds (∑ j : Fin 2,
            ‖vectorScalarMulTransverse
              (transverseW1InfComplexDerivLInf j u)‖ *
              ‖transverseCoordL2 j.castSucc‖))).mul
      tendsto_physical_inverse_bound_zero
    simpa using h

/-- The complete lower-order correction tends to zero through the explicit
positive-real diffusion inverse ray. -/
theorem tendsto_norm_reducedInductionLowerOrder_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionLowerOrder u K).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  exact tendsto_norm_reducedInductionLowerOrder_comp_zero_of_terms u K
    (reducedInductionDiffusionInverseRay ε K hε)
    (tendsto_norm_reducedInductionTransport_comp_diffusionInverseRay_zero
      u ε K hε)
    (tendsto_norm_reducedInductionAxialTransport_comp_diffusionInverseRay_zero
      u ε K hε)
    (tendsto_norm_reducedInductionStretching_comp_diffusionInverseRay_zero
      u ε K hε)

/--
At every point `σ = e^t` of the exponential ray, the diffusion inverse is a left inverse of the
fixed-sector diffusion pencil.
-/
theorem transverseVecDiffusionInverseRay_left_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    (transverseVecDiffusionInverseRay ι ε K hε t).comp
      (transverseVecDiffusionPencil ι ε K ((Real.exp t : ℝ) : ℂ)) =
        ContinuousLinearMap.id ℂ (TransverseVecH2 ι) :=
  inverse_comp_transverseVecDiffusionPencil ε (Real.exp t) K hε (Real.exp_pos t)

private theorem diffusionInverseRay_left_inverse
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    (reducedInductionDiffusionInverseRay ε K hε t).comp
      (reducedInductionDiffusionPencil ε K ((Real.exp t : ℝ) : ℂ)) =
        ContinuousLinearMap.id ℂ TransverseC3H2 :=
  transverseVecDiffusionInverseRay_left_inverse ε K hε t

/--
At every point `σ = e^t` of the exponential ray, the diffusion inverse is a right inverse of the
fixed-sector diffusion pencil.
-/
theorem transverseVecDiffusionInverseRay_right_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    (transverseVecDiffusionPencil ι ε K ((Real.exp t : ℝ) : ℂ)).comp
      (transverseVecDiffusionInverseRay ι ε K hε t) =
        ContinuousLinearMap.id ℂ (TransverseVecL2 ι) :=
  transverseVecDiffusionPencil_comp_inverse ε (Real.exp t) K hε (Real.exp_pos t)

private theorem diffusionInverseRay_right_inverse
    (ε : ℝ) (K : ℤ) (hε : 0 < ε) (t : ℝ) :
    (reducedInductionDiffusionPencil ε K ((Real.exp t : ℝ) : ℂ)).comp
      (reducedInductionDiffusionInverseRay ε K hε t) =
        ContinuousLinearMap.id ℂ TransverseC3L2 :=
  transverseVecDiffusionInverseRay_right_inverse ε K hε t

/-- The exact Neumann smallness threshold is eventually attained on the
positive exponential diffusion ray. -/
theorem eventually_norm_reducedInductionLowerOrder_comp_diffusionInverseRay_lt_one
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      ‖(reducedInductionLowerOrder u K).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖ < 1 := by
  exact (tendsto_order.1
    (tendsto_norm_reducedInductionLowerOrder_comp_diffusionInverseRay_zero
      u ε K hε)).2 (1 : ℝ) zero_lt_one

/-- Every sufficiently far point on the concrete positive-real exponential
ray is a reduced fixed-sector resolvent point. -/
theorem eventually_hasResolventOn_reducedInductionOperator_expRay
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Nonempty (HasResolventOn
        (reducedInductionOperator u ε K) {((Real.exp t : ℝ) : ℂ)}) := by
  filter_upwards [
    eventually_norm_reducedInductionLowerOrder_comp_diffusionInverseRay_lt_one
      u ε K hε] with t ht
  exact ⟨reducedInductionHasResolventOnSingletonOfDiffusionInverse
    u ε K ((Real.exp t : ℝ) : ℂ)
    (reducedInductionDiffusionInverseRay ε K hε t)
    (diffusionInverseRay_left_inverse ε K hε t)
    (diffusionInverseRay_right_inverse ε K hε t) ht⟩

/-! ## Fibre-generic large-real-point resolvent -/

/--
Fibre-generic large-real-point resolvent.  If the pencil of a torus sector operator `A` on the
fibre `ℂ^ι` splits, at every point `σ = eᵗ` of the positive exponential ray, as the fixed-sector
diffusion pencil minus one lower-order part `B`, and if the normalized correction
`B ∘ D(eᵗ)` tends to zero, then every sufficiently far point of the ray is a resolvent point
of `A`.

Together with the Rellich embedding and the fibre-generic clauses of
`FastDynamo/Operator/FixedSectorBasic.lean` this supplies, for any fibre, the four
velocity-free clauses of Paper Lemma 5.1 (`lem:torus-sector-basic`).
-/
theorem eventually_hasResolventOn_of_transverseVecDiffusionSplitting
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : DomainOperator (TransverseVecL2 ι) (TransverseVecH2 ι))
    (ε : ℝ) (K : ℤ) (hε : 0 < ε)
    (B : TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι)
    (hsplit : ∀ t : ℝ, A.pencil ((Real.exp t : ℝ) : ℂ) =
      transverseVecDiffusionPencil ι ε K ((Real.exp t : ℝ) : ℂ) - B)
    (hdecay : Filter.Tendsto
      (fun t : ℝ ↦ ‖B.comp (transverseVecDiffusionInverseRay ι ε K hε t)‖)
      Filter.atTop (nhds 0)) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Nonempty (HasResolventOn A {((Real.exp t : ℝ) : ℂ)}) := by
  filter_upwards [(tendsto_order.1 hdecay).2 (1 : ℝ) zero_lt_one] with t ht
  exact ⟨DomainOperator.hasResolventOnSingletonOfPencilSplitting A
    ((Real.exp t : ℝ) : ℂ)
    (transverseVecDiffusionPencil ι ε K ((Real.exp t : ℝ) : ℂ)) B (hsplit t)
    (transverseVecDiffusionInverseRay ι ε K hε t)
    (transverseVecDiffusionInverseRay_left_inverse ε K hε t)
    (transverseVecDiffusionInverseRay_right_inverse ε K hε t) ht⟩

end

end FastDynamo
