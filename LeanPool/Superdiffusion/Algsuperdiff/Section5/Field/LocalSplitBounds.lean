/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.ScaleDecompositionBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.DivergenceContraction
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Geometry
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSkewDivergence

/-!
# LocalSplitBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Local constants for the split stream field

This module converts the logarithmic ball estimates for the two scale ranges
into the precise layer hypotheses used by the localized weighted estimate.
The negative shells are controlled through matrix action, while the
divergence of the continuously differentiable nonnegative shells costs the
explicit contraction factor `sqrt d * d`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open HCPolySupport
open HCPolySupport.Book.Ch02
open DivergenceFormProcess.Decay
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-- An origin-centred observation radius containing `euclideanBall x rho`. -/
def streamSplitObservationRadius (x : Vec d) (rho : ℝ) : ℝ :=
  1 + euclideanNorm x + rho

/-- The local size constant for the negative-shell part. -/
def streamFieldSmallLocalConst (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) (rho : ℝ) : ℝ :=
  streamFieldSmallBallConst M omega *
    streamLogWeight (streamSplitObservationRadius x rho)

/-- The local divergence constant for the nonnegative-shell part. -/
def streamFieldLargeDivLocalConst (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) (rho : ℝ) : ℝ :=
  Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega *
    streamLogWeight (streamSplitObservationRadius x rho)

theorem one_le_streamSplitObservationRadius {x : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) : 1 ≤ streamSplitObservationRadius x rho := by
  unfold streamSplitObservationRadius
  have hx := euclideanNorm_nonneg x
  linarith only [hx, hrho]

private theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec, show HilbertVec.ofVec (x + y) =
      HilbertVec.ofVec x + HilbertVec.ofVec y by rfl]
  exact norm_add_le _ _

theorem euclideanNorm_lt_streamSplitObservationRadius_of_mem
    {x y : Vec d} {rho : ℝ} (hrho : 0 ≤ rho)
    (hy : y ∈ euclideanBall x rho) :
    euclideanNorm y < streamSplitObservationRadius x rho := by
  have hdist := euclideanNorm_sub_lt_of_mem_euclideanBall hrho hy
  calc
    euclideanNorm y = euclideanNorm ((y - x) + x) := by congr 1; abel
    _ ≤ euclideanNorm (y - x) + euclideanNorm x := euclideanNorm_add_le _ _
    _ < rho + euclideanNorm x := by
      simpa only [add_comm] using add_lt_add_right hdist (euclideanNorm x)
    _ < streamSplitObservationRadius x rho := by
      unfold streamSplitObservationRadius
      linarith only

theorem streamFieldSmallLocalConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) {x : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) : 0 ≤ streamFieldSmallLocalConst M omega x rho := by
  unfold streamFieldSmallLocalConst
  exact mul_nonneg (streamFieldSmallBallConst_nonneg M omega)
    (streamLogWeight_pos (one_le_streamSplitObservationRadius hrho)).le

theorem streamFieldLargeDivLocalConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) {x : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) : 0 ≤ streamFieldLargeDivLocalConst M omega x rho := by
  unfold streamFieldLargeDivLocalConst
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg d))
        (streamFieldLargeGradientConst_nonneg M omega))
    (streamLogWeight_pos (one_le_streamSplitObservationRadius hrho)).le

/-- The negative-shell part has the matrix-action bound required on a local
transition layer. -/
theorem vecNormSq_matVecMul_streamFieldSmall_le (M : ABKModel d)
    (omega : FullSample d M.gamma) {x y : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) (hy : y ∈ euclideanBall x rho) (v : Vec d) :
    vecNormSq (matVecMul (streamFieldSmall omega y) v) ≤
      streamFieldSmallLocalConst M omega x rho ^ 2 * vecNormSq v := by
  let R := streamSplitObservationRadius x rho
  let K := streamFieldSmallLocalConst M omega x rho
  have hR : 1 ≤ R := one_le_streamSplitObservationRadius hrho
  have hyR : euclideanNorm y ≤ R :=
    (euclideanNorm_lt_streamSplitObservationRadius_of_mem hrho hy).le
  have hOp : matrixOperatorNorm (streamFieldSmall omega y) ≤ K := by
    exact matrixOperatorNorm_streamFieldSmall_le M omega hR
      (by simpa only [euclideanNorm] using hyR)
  have hK : 0 ≤ K := streamFieldSmallLocalConst_nonneg M omega hrho
  calc
    vecNormSq (matVecMul (streamFieldSmall omega y) v) ≤
        matrixOperatorNorm (streamFieldSmall omega y) ^ 2 * vecNormSq v :=
      vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ _
    _ ≤ K ^ 2 * vecNormSq v :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) hOp 2)
        (vecNormSq_nonneg v)

private theorem vecNormSq_le_dim_mul_sq_norm (v : Vec d) :
    vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
  simp only [vecNormSq, vecDot]
  calc
    ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
      gcongr with i
      calc
        v i * v i = |v i| ^ 2 := by rw [sq_abs]; ring
        _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i) 2
    _ = (d : ℝ) * ‖v‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem hasFDerivAt_streamFieldLarge_local
    (omega : FullSample d gamma) (x : Vec d) :
    HasFDerivAt (streamFieldLarge omega) (streamFieldLargeDeriv omega x) x := by
  have hdiff := (streamFieldLarge_contDiff_one omega).differentiable (by norm_num)
  have hf : fderiv ℝ (streamFieldLarge omega) x = streamFieldLargeDeriv omega x :=
    fderiv_streamFieldLarge omega x
  rw [← hf]
  exact (hdiff x).hasFDerivAt

/-- The divergence of the nonnegative-shell part has the local squared-size
bound required by the integration-by-parts estimate. -/
theorem vecNormSq_skewFieldDiv_streamFieldLarge_le (M : ABKModel d)
    (omega : FullSample d M.gamma) {x y : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) (hy : y ∈ euclideanBall x rho) :
    vecNormSq (skewFieldDiv
        (streamFieldLarge omega) y) ≤
      streamFieldLargeDivLocalConst M omega x rho ^ 2 := by
  let R := streamSplitObservationRadius x rho
  let G := streamFieldLargeGradientConst M omega * streamLogWeight R
  have hR : 1 ≤ R := one_le_streamSplitObservationRadius hrho
  have hyR : euclideanNorm y ≤ R :=
    (euclideanNorm_lt_streamSplitObservationRadius_of_mem hrho hy).le
  have hD : ‖streamFieldLargeDeriv omega y‖ ≤ G :=
    norm_streamFieldLargeDeriv_le M omega hR
      (by simpa only [euclideanNorm] using hyR)
  have hG : 0 ≤ G := mul_nonneg (streamFieldLargeGradientConst_nonneg M omega)
    (streamLogWeight_pos hR).le
  have hdivNorm :
      ‖skewFieldDiv (streamFieldLarge omega) y‖ ≤
        (d : ℝ) * G := by
    change ‖Algsuperdiff.Section5.Support.matFieldDiv (streamFieldLarge omega) y‖ ≤ _
    exact (Algsuperdiff.Section5.Provider.norm_matFieldDiv_le
      (hasFDerivAt_streamFieldLarge_local omega y)).trans
        (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg d))
  have hnormSq :
      ‖skewFieldDiv (streamFieldLarge omega) y‖ ^ 2 ≤
        ((d : ℝ) * G) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdivNorm 2
  calc
    vecNormSq (skewFieldDiv
        (streamFieldLarge omega) y) ≤
        (d : ℝ) *
          ‖skewFieldDiv (streamFieldLarge omega) y‖ ^ 2 :=
      vecNormSq_le_dim_mul_sq_norm _
    _ ≤ (d : ℝ) * ((d : ℝ) * G) ^ 2 :=
      mul_le_mul_of_nonneg_left hnormSq (Nat.cast_nonneg d)
    _ = streamFieldLargeDivLocalConst M omega x rho ^ 2 := by
      unfold streamFieldLargeDivLocalConst G R
      symm
      calc
        (Real.sqrt (d : ℝ) * (d : ℝ) *
            streamFieldLargeGradientConst M omega *
              streamLogWeight (streamSplitObservationRadius x rho)) ^ 2 =
            Real.sqrt (d : ℝ) ^ 2 * (d : ℝ) ^ 2 *
              streamFieldLargeGradientConst M omega ^ 2 *
                streamLogWeight (streamSplitObservationRadius x rho) ^ 2 := by ring
        _ = _ := by
          rw [Real.sq_sqrt (Nat.cast_nonneg d)]
          ring

end

end Algsuperdiff.Section5.Field
