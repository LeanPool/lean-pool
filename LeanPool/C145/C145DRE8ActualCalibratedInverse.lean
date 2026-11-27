/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8ActualFrame

/-! Source Theorem A for actual calibrated full frames. All structural
identities are derived from the supplied physical frames and actual port.
Only the source spectral interval, source port separation and source q_Ch
criterion remain as scientific restrictions. The competitor has none of them. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ}

/-- Exact square of the source q_Ch, expressed in original vertex coordinates. -/
def sourceQChebyshevSq (b : Fin (n + 1) → ℝ) (ell u delta : ℝ) : ℝ :=
  (((n + 1 : ℕ) + 2 : ℝ) * (∑ v, centeredPort b v ^ 2) / (1024 * delta ^ 2))*
    ((u-ell) / (2 * ell-u)) ^ 6

theorem sourceQ_eq_modal
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) (hG : ∀ v, U v 0 = c)
    (ell u delta : ℝ) :
    sourceQChebyshevSq b ell u delta =
      qChebyshevSq (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ) ell u delta := by
  unfold sourceQChebyshevSq qChebyshevSq
  rw [actual_residual_energy U b c hU hG]

/-- Actual common calibration plus actual full H2 determine the full cubic
under the source scalar-signature condition, in arbitrary dimension. -/
theorem actual_calibrated_H2_cubic_equality
    (μ : ℝ) (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (ha : ∀ i, C145.Pulse.modalOverlap U b i ≠ 0)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (C145PhysicalFrame.T V (C145.Pulse.modalOverlap U b)))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (b j - b k) ^ 2)
    (hq : sourceQChebyshevSq b ell u delta < 1) :
    C145PhysicalFrame.C U = C145PhysicalFrame.C V := by
  let a : Fin (n + 1) → ℝ := C145.Pulse.modalOverlap U b
  let ar : Fin n → ℝ := fun i => a i.succ
  let C0 : Tensor n := residual (C145PhysicalFrame.C U)
  let C1 : Tensor n := residual (C145PhysicalFrame.C V)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of U * (Matrix.of V).transpose
  have hCG := actual_cubic_common_ground U V c hU hV hGU hGV
  have hDiff : C145PhysicalFrame.C V-C145PhysicalFrame.C U = groundZero (C1-C0) :=
    commonGround_difference _ _ hCG
  have hPhys : physicalDifference Q = rotateTensor (Matrix.of U) (groundZero (C1-C0)) := by
    rw [← hDiff]
    exact actual_frame_physical_difference U V hU
  have hQ : Q.transpose * Q = 1 := by
    have h := columnOrthonormal_matrix (C145CoordinatePermutation.transport V U)
      (C145CoordinatePermutation.transport_columnOrthonormal V U hV hU)
    rw [C145CoordinatePermutation.transport_eq_matrix_mul_transpose] at h
    exact h
  have hunit : ∀ i, ∑ v, Q i v = 1 := actual_frame_common_unit U V c hU hV hGU hGV
  have hData := actual_weighted_residual_data μ rates U V a c hU hV hGU hGV hH
  have hSig := actual_residual_signature U b c hU hGU
  have hSep : ∀ j k, j ≠ k → delta ^ 2≤
      (((Matrix.of U).mulVec (residualVector ar)) j-
        ((Matrix.of U).mulVec (residualVector ar)) k) ^ 2 := by
    intro j k hjk
    change delta ^ 2≤
      (((Matrix.of U).mulVec (residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b
        i.succ))) j-
        ((Matrix.of U).mulVec (residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b
          i.succ))) k) ^ 2
    rw [hSig]
    simpa only [centeredPort, sub_sub_sub_cancel_right] using hsep j k hjk
  have hqM : qChebyshevSq ar ell u delta < 1 := by
    rw [sourceQ_eq_modal U b c hU hGU ell u delta] at hq
    exact hq
  have hPos : ∀ i, 0 < rates i := by
    intro i
    have hell : 0 < ell := by linarith
    exact hell.trans_le (hlo i)
  have hz : C1-C0 = 0 := calibrated_H2_kernel_zero ar rates (fun i => ha i.succ) hRates
    (C1-C0) (fullSymTensor_sub C1 C0
      (residual_fullSym _ (actual_cubic_fullSym V))
      (residual_fullSym _ (actual_cubic_fullSym U)))
    (samePositive_weighted_difference ar rates hPos C0 C1 hData)
    ell u hw hband hlo hhi (Matrix.of U) Q (columnOrthonormal_matrix U hU)
    hQ hunit hPhys delta hSep
    ((qChebyshevSq_lt_one_iff ar ell u delta hband (ne_of_gt hd)).mp hqM)
  have hzero : groundZero (0 : Tensor n) = 0 := by
    funext i j k
    refine Fin.cases ?_ (fun x => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun y => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun z => ?_) k <;> rfl
  rw [hz,hzero] at hDiff
  exact (sub_eq_zero.mp hDiff).symm

/-- The vertex bijection is derived by the existing primitive coordinate
idempotent theorem; it is not a supplied reconstruction certificate. -/
theorem actual_calibrated_H2_vertex_identification
    (μ : ℝ) (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (ha : ∀ i, C145.Pulse.modalOverlap U b i ≠ 0)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (C145PhysicalFrame.T V (C145.Pulse.modalOverlap U b)))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (b j - b k) ^ 2)
    (hq : sourceQChebyshevSq b ell u delta < 1) :
    ∃ π : Equiv.Perm (Fin (n + 1)),
      (∀ w v, C145CoordinatePermutation.transport U V w v = if w = π v then 1 else 0) ∧
      (∀ v i, V (π v) i = U v i) := by
  exact C145CoordinatePermutation.cubic_equality_vertex_permutation U V hU hV
    (actual_calibrated_H2_cubic_equality μ rates hRates U V b c hU hV ha hGU hGV hH
      ell u hw hband hlo hhi delta hd hsep hq)

end C145DRE8

end
