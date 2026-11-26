/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8CalibratedUniqueness
public import LeanPool.C145.C145GraphSpectralRealization

/-! Derive the physical common-unit secant from two actual calibrated frames.
No tensor-frame certificate, common-unit certificate, or residual-H2 premise
is supplied to the eventual calibrated frame inverse. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ}

theorem columnOrthonormal_matrix (U : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) :
    (Matrix.of U).transpose * Matrix.of U = 1 := by
  ext i j
  exact hU i j

theorem rotateTensor_sub {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (A B : ι → ι → ι → ℝ) :
    rotateTensor U (A-B) = rotateTensor U A - rotateTensor U B := by
  funext i j k
  simp only [rotateTensor, rotateFirst, rotateSecond, rotateThird,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem sum_cubic_factor (f g : Fin (n + 1) → ℝ) (x y : ℝ) :
    (∑ r, f r * (g r * x * y)) = (∑ r, f r * g r) * x * y := by
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro r hr; ring

theorem rotateTensor_cubic (U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    rotateTensor U (C145PhysicalFrame.C V) = competitorTensor (U * V.transpose) := by
  have h3 (i j k : Fin (n + 1)) :
      rotateThird U (C145PhysicalFrame.C V) i j k =
      ∑ v, (∑ r, U k r * V v r) * V v i * V v j := by
    simp only [rotateThird, C145PhysicalFrame.C, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v hv
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      sum_cubic_factor (fun r => U k r) (fun r => V v r) (V v i) (V v j)
  have h2 (i j k : Fin (n + 1)) :
      rotateSecond U (rotateThird U (C145PhysicalFrame.C V)) i j k =
      ∑ v, (∑ r, U j r * V v r) * V v i * (∑ r, U k r * V v r) := by
    unfold rotateSecond
    simp_rw [h3]
    calc
      _ = ∑ r, ∑ v, U j r * ((∑ s, U k s * V v s) * V v i * V v r) := by
        apply Finset.sum_congr rfl; intro r hr; rw [Finset.mul_sum]
      _ = ∑ v, ∑ r, U j r * ((∑ s, U k s * V v s) * V v i * V v r) := Finset.sum_comm
      _ = _ := ?_
    apply Finset.sum_congr rfl; intro v hv
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      sum_cubic_factor (fun r => U j r) (fun r => V v r) (V v i)
        (∑ r, U k r * V v r)
  funext i j k
  change (∑ r, U i r * rotateSecond U (rotateThird U (C145PhysicalFrame.C V)) r j k) = _
  simp_rw [h2]
  calc
    _ = ∑ r, ∑ v, U i r * ((∑ s, U j s * V v s) * V v r *
        (∑ s, U k s * V v s)) := by
      apply Finset.sum_congr rfl; intro r hr; rw [Finset.mul_sum]
    _ = ∑ v, ∑ r, U i r * ((∑ s, U j s * V v s) * V v r *
        (∑ s, U k s * V v s)) := Finset.sum_comm
    _ = _ := ?_
  apply Finset.sum_congr rfl; intro v hv
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm, mul_left_comm, mul_assoc] using
    sum_cubic_factor (fun r => U i r) (fun r => V v r)
      (∑ r, U j r * V v r) (∑ r, U k r * V v r)

theorem competitorTensor_one :
    competitorTensor (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = coordinateTensor := by
  funext i j k
  classical
  simp only [competitorTensor, Matrix.one_apply, coordinateTensor]
  by_cases hij : i = j
  · subst j
    simp [mul_ite]
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    by_cases hjk : j = k
    · have hik : i ≠ k := fun hik => hij (hik.trans hjk.symm)
      simp [hjk, hik]
    · simp [hij, hjk]

theorem actual_frame_physical_difference
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) :
    physicalDifference (Matrix.of U * (Matrix.of V).transpose) =
      rotateTensor (Matrix.of U) (C145PhysicalFrame.C V-C145PhysicalFrame.C U) := by
  change physicalDifference (Matrix.of U * (Matrix.of V).transpose) =
    rotateTensor (Matrix.of U) (C145PhysicalFrame.C (Matrix.of V)-C145PhysicalFrame.C (Matrix.of U))
  rw [rotateTensor_sub, rotateTensor_cubic, rotateTensor_cubic,
    orthogonal_rows (Matrix.of U) (columnOrthonormal_matrix U hU), competitorTensor_one]
  rfl

theorem actual_frame_common_unit
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c) :
    ∀ i, ∑ v, (Matrix.of U * (Matrix.of V).transpose) i v = 1 := by
  intro i
  have hc := C145PhysicalFrame.ground_ne_zero U c hU hGU
  apply mul_right_cancel₀ hc
  have h := C145CoordinatePermutation.transport_frame_column V U hV i 0
  change (∑ v, C145CoordinatePermutation.transport V U i v * V v 0) = U i 0 at h
  simp_rw [hGV, hGU] at h
  rw [← Finset.sum_mul] at h
  simpa only [mul_one, one_mul, C145CoordinatePermutation.transport,
    Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply] using h

theorem actual_cubic_common_ground
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c) :
    CommonGround (C145PhysicalFrame.C U) (C145PhysicalFrame.C V) := by
  intro i j k hg
  have h := physical_commonGround U V (fun _ => 1) c hU hV hGU hGV i j k hg
  simpa only [C145PhysicalFrame.T, one_mul] using h

private theorem residual_physical_weightedTensor
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) :
    residual (C145PhysicalFrame.T U a) =
      weightedTensor (fun i : Fin n => a i.succ) (residual (C145PhysicalFrame.C U)) := rfl

/-- Restrict calibrated positive H2 equality to the weighted non-ground tensors. -/
theorem actual_weighted_residual_data
    (μ : ℝ) (rates : Fin n → ℝ)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (hH : SamePositive (fullRates μ rates) (C145PhysicalFrame.T U a)
      (C145PhysicalFrame.T V a)) :
    SamePositive rates
      (weightedTensor (fun i : Fin n => a i.succ) (residual (C145PhysicalFrame.C U)))
      (weightedTensor (fun i : Fin n => a i.succ) (residual (C145PhysicalFrame.C V))) := by
  have hGround := physical_commonGround U V a c hU hV hGU hGV
  have hData := samePositive_residual_of_commonGround μ rates
    (C145PhysicalFrame.T U a) (C145PhysicalFrame.T V a) hGround hH
  rw [residual_physical_weightedTensor U a, residual_physical_weightedTensor V a] at hData
  exact hData

theorem actual_cubic_fullSym (U : Fin (n + 1) → Fin (n + 1) → ℝ) :
    FullSymTensor (C145PhysicalFrame.C U) := by
  intro e v
  have h := physical_fullSym U (fun _ => 1) e v
  change C145PhysicalFrame.T U (fun _ => 1) (v (e 1)) (v (e 2)) (v (e 0)) =
    C145PhysicalFrame.T U (fun _ => 1) (v 1) (v 2) (v 0) at h
  change C145PhysicalFrame.C U (v (e 1)) (v (e 2)) (v (e 0)) =
    C145PhysicalFrame.C U (v 1) (v 2) (v 0)
  simpa only [C145PhysicalFrame.T, one_mul] using h

/-- The actual port with its constant component removed. -/
def centeredPort (b : Fin (n + 1) → ℝ) (v : Fin (n + 1)) : ℝ :=
  b v - (∑ w, b w) / (n + 1 : ℝ)

theorem actual_residual_signature
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) (hG : ∀ v, U v 0 = c) :
    (Matrix.of U).mulVec (residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ)) =
      centeredPort b := by
  have hnorm := C145PhysicalFrame.ground_normalization U c hU hG
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  have ha : C145.Pulse.modalOverlap U b 0 = c * (∑ v, b v) := by
    simp only [C145.Pulse.modalOverlap, hG, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v hv; ring
  have hmean : C145.Pulse.modalOverlap U b 0 * c = (∑ v,b v) / (n + 1 : ℝ) := by
    apply (eq_div_iff hN).mpr
    rw [ha]
    calc
      _ = ((n + 1 : ℝ) * c ^ 2) * (∑ v,b v) := by ring
      _ = _ := by rw [hnorm, one_mul]
  funext v
  have hr := congrFun (C145.UncalibratedSmallH2.spectralPort_modalOverlap U b hU) v
  change (∑ i, C145.Pulse.modalOverlap U b i * U v i) = b v at hr
  rw [Fin.sum_univ_succ, hG, hmean] at hr
  change (∑ i, U v i * residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ) i) = _
  simp only [Fin.sum_univ_succ, residualVector, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add]
  dsimp [centeredPort]
  have hs : (∑ i : Fin n, U v i.succ * C145.Pulse.modalOverlap U b i.succ) =
      ∑ i : Fin n, C145.Pulse.modalOverlap U b i.succ * U v i.succ := by
    apply Finset.sum_congr rfl; intro i hi; ring
  rw [hs]
  linarith

theorem actual_residual_energy
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) (hG : ∀ v, U v 0 = c) :
    (∑ i : Fin n, (C145.Pulse.modalOverlap U b i.succ) ^ 2) = ∑ v, centeredPort b v ^ 2 := by
  have h := orthogonal_energy (Matrix.of U) (columnOrthonormal_matrix U hU)
    (residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ))
  change (∑ i, ((Matrix.of U).mulVec (residualVector (fun i : Fin n => C145.Pulse.modalOverlap U b
    i.succ)) i) ^ 2) = _ at h
  rw [actual_residual_signature U b c hU hG] at h
  simpa only [Fin.sum_univ_succ, residualVector, Fin.cases_zero, Fin.cases_succ,
    zero_pow (by omega : 2 ≠ 0), zero_add] using h.symm

end C145DRE8

end
