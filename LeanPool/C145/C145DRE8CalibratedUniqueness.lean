/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8OrthogonalTransport
public import LeanPool.C145.C145DRE8SliceRigidity

/-! The source's quantitative calibrated-tensor endpoint: actual response
contraction joined to physical Lemma B through an explicit shared orthogonal
modal-to-vertex map. This does not claim the original graph/ODE reconstruction
or infer H1 calibration. Q,U,common unit and the actual tensor-frame identity
are named structural assumptions, not supplied moment/norm certificates. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ}

/-- Zero literal tensor energy is entrywise zero. -/
theorem tensorSq_zero (E : Tensor n) (h : tensorSq E = 0) : E = 0 := by
  classical
  funext i j k
  have hi : (∑ j, ∑ k, E i j k ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by positivity)).mp h i (Finset.mem_univ i)
  have hj : (∑ k, E i j k ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by positivity)).mp hi j (Finset.mem_univ j)
  exact (Finset.sum_sq_eq_zero_iff (Finset.univ : Finset (Fin n))
    (fun k => E i j k)).mp hj k (Finset.mem_univ k)

/-- The accepted global Lemma B specialized to one actual separating signature. -/
theorem physical_single_slice_rigidity
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (h : Fin (n + 1) → ℝ) (delta : ℝ)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (h j - h k) ^ 2) :
    delta ^ 2 * tensorSq (physicalDifference Q) ≤
      ((n + 1 : ℕ) + 2 : ℝ) * matrixSq (tensorSlice (physicalDifference Q) h) := by
  have hh := physical_slice_rigidity Q hQ hunit (fun _ : Unit => h) delta
    (by intro j k hjk; simpa [signatureSq] using hsep j k hjk)
  simpa [sliceSq] using hh

/-- Exact modal rigidity bound. Tensor and signature both use the same U.
The hPhysical identity is a source-frame identity, not a target norm estimate. -/
theorem calibrated_modal_rigidity
    (U Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U.transpose * U = 1) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (E : Tensor n) (a : Fin n → ℝ)
    (hPhysical : physicalDifference Q = rotateTensor U (groundZero E))
    (delta : ℝ)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      ((U.mulVec (residualVector a)) j - (U.mulVec (residualVector a)) k) ^ 2) :
    delta ^ 2 * tensorSq E ≤ ((n + 1 : ℕ) + 2 : ℝ) * matrixSq (tensorSlice E a) := by
  have hh := physical_single_slice_rigidity Q hQ hunit
    (U.mulVec (residualVector a)) delta hsep
  rw [hPhysical, tensorSq_rotateTensor U hU, tensorSq_groundZero,
    matrixSq_slice_rotateTensor U hU, matrixSq_slice_groundZero] at hh
  exact hh

/-- Source q_Ch<1 in exact squared form forces a calibrated physical secant
with actual zero weighted H2 to vanish. No unrestricted all-size inverse. -/
theorem calibrated_H2_kernel_zero
    (a rates : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (U Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U.transpose * U = 1) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1)
    (hPhysical : physicalDifference Q = rotateTensor U (groundZero E))
    (delta : ℝ)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      ((U.mulVec (residualVector a)) j - (U.mulVec (residualVector a)) k) ^ 2)
    (hq : ((n + 1 : ℕ) + 2 : ℝ) * (u - ell) ^ 6 * (∑ i, a i ^ 2) <
      1024 * delta ^ 2 * (2 * ell - u) ^ 6) : E = 0 := by
  have hc := actual_H2_chebyshev_contraction a rates ha hRates E hSym hData
    ell u hw hband hlo hhi
  have hr := calibrated_modal_rigidity U Q hU hQ hunit E a hPhysical delta hsep
  have hg : 0 ≤ 1024 * (2 * ell-u) ^ 6 := by positivity
  have hN : 0 ≤ ((n + 1 : ℕ) + 2 : ℝ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hr hg
  have h2 := mul_le_mul_of_nonneg_left hc hN
  have hcombined : (1024 * delta ^ 2 * (2 * ell-u) ^ 6) * tensorSq E ≤
      (((n + 1 : ℕ) + 2 : ℝ) * (u-ell) ^ 6 * (∑ i, a i ^ 2)) * tensorSq E := by
    calc
      _ = (1024 * (2 * ell-u) ^ 6) * (delta ^ 2 * tensorSq E) := by ring
      _ ≤ (1024 * (2 * ell-u) ^ 6) *
          (((n + 1 : ℕ) + 2 : ℝ) * matrixSq (tensorSlice E a)) := h1
      _ = ((n + 1 : ℕ) + 2 : ℝ) *
          (1024 * (2 * ell-u) ^ 6 * matrixSq (tensorSlice E a)) := by ring
      _ ≤ ((n + 1 : ℕ) + 2 : ℝ) *
          ((u-ell) ^ 6 * (∑ i, a i ^ 2) * tensorSq E) := h2
      _ = _ := by ring
  apply tensorSq_zero E
  apply le_antisymm _ (tensorSq_nonneg E)
  by_contra h
  have hp : 0 < tensorSq E := lt_of_not_ge h
  exact (not_lt_of_ge hcombined) (mul_lt_mul_of_pos_right hq hp)

/-- The criterion really is q_Ch<1: squared exact arithmetic, no square-root
choice or denominator ambiguity. The spectral band supplies a positive gap. -/
def qChebyshevSq (a : Fin n → ℝ) (ell u delta : ℝ) : ℝ :=
  (((n + 1 : ℕ) + 2 : ℝ) * (∑ i, a i ^ 2) / (1024 * delta ^ 2)) *
    ((u-ell) / (2 * ell-u)) ^ 6

theorem qChebyshevSq_lt_one_iff (a : Fin n → ℝ) (ell u delta : ℝ)
    (hband : u < 2 * ell) (hd : delta ≠ 0) :
    qChebyshevSq a ell u delta < 1 ↔
      ((n + 1 : ℕ) + 2 : ℝ) * (u-ell) ^ 6 * (∑ i, a i ^ 2) <
        1024 * delta ^ 2 * (2 * ell-u) ^ 6 := by
  have hg : 0 < 2 * ell-u := by linarith
  have hden : 0 < 1024 * delta ^ 2 * (2 * ell-u) ^ 6 := by positivity
  have heq : qChebyshevSq a ell u delta =
      (((n + 1 : ℕ) + 2 : ℝ) * (u-ell) ^ 6 * (∑ i, a i ^ 2)) /
        (1024 * delta ^ 2 * (2 * ell-u) ^ 6) := by
    dsimp [qChebyshevSq]
    field_simp
  rw [heq, div_lt_one hden]

/-- Actual equality of positive weighted H2 data gives the null response used
above. This linearly normalizes the observed coefficients, preserving direction. -/
theorem samePositive_weighted_difference (a rates : Fin n → ℝ)
    (hPos : ∀ i, 0 < rates i) (C1 C2 : Tensor n)
    (hData : SamePositive rates (weightedTensor a C1) (weightedTensor a C2)) :
    NullRegular rates (weightedTensor a (C2-C1)) := by
  apply (nullPositive_iff_nullRegular rates hPos _).mp
  intro s t hs ht
  have hh := hData s t hs ht
  have hW : weightedTensor a (C2-C1) = weightedTensor a C2 - weightedTensor a C1 := by
    funext i j k; simp only [weightedTensor, Pi.sub_apply]; ring
  rw [hW, H_sub, hh, sub_self]

/-- Calibrated modal tensor uniqueness from actual equal positive H2 under
source q_Ch<1. Calibration/H1 and graph idempotent reconstruction stay outside
this theorem's exact boundary; no physical norm or moment is supplied. -/
theorem calibrated_tensors_unique
    (a rates : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (C1 C2 : Tensor n) (hC1 : FullSymTensor C1) (hC2 : FullSymTensor C2)
    (hData : SamePositive rates (weightedTensor a C1) (weightedTensor a C2))
    (_hn : 2 ≤ n) (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (U Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U.transpose * U = 1) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1)
    (hPhysical : physicalDifference Q = rotateTensor U (groundZero (C2 - C1)))
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      ((U.mulVec (residualVector a)) j - (U.mulVec (residualVector a)) k) ^ 2)
    (hq : qChebyshevSq a ell u delta < 1) : C2 = C1 := by
  have hPos : ∀ i, 0 < rates i := by
    intro i
    have hell : 0 < ell := by linarith
    exact hell.trans_le (hlo i)
  have hz := calibrated_H2_kernel_zero a rates ha hRates (C2-C1)
    (fullSymTensor_sub C2 C1 hC2 hC1)
    (samePositive_weighted_difference a rates hPos C1 C2 hData)
    ell u hw hband hlo hhi U Q hU hQ hunit hPhysical delta hsep
    ((qChebyshevSq_lt_one_iff a ell u delta hband (ne_of_gt hd)).mp hq)
  exact sub_eq_zero.mp hz

/-- Inherited n<=3 ordinary response injectivity after nonzero calibration.
No spectral width, band, separation, Q, or selected index is required, so
this retains n=0 and the source N=2/w=0 branch. -/
theorem small_actual_H2_kernel_zero (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates) (hn : n ≤ 3)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E)) : E = 0 := by
  have hz := (small_n_kernel_iff_zero rates hRates hn (weightedTensor a E)
    (weightedTensor_symmetric a E hSym)).mp hData
  calc
    E = unweightedTensor a (weightedTensor a E) := (unweighted_weighted a ha E).symm
    _ = 0 := by rw [hz]; funext i j k; simp [unweightedTensor]

/-- The positive-H2 small-size uniqueness theorem is independent of w and
therefore remains available at w=0, including the inherited N=2 case. -/
theorem small_calibrated_tensors_unique (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (hPos : ∀ i, 0 < rates i) (hn : n ≤ 3)
    (C1 C2 : Tensor n) (hC1 : FullSymTensor C1) (hC2 : FullSymTensor C2)
    (hData : SamePositive rates (weightedTensor a C1) (weightedTensor a C2)) :
    C2 = C1 := by
  exact sub_eq_zero.mp (small_actual_H2_kernel_zero a rates ha hRates hn (C2-C1)
    (fullSymTensor_sub C2 C1 hC2 hC1)
    (samePositive_weighted_difference a rates hPos C1 C2 hData))

end C145DRE8

end
