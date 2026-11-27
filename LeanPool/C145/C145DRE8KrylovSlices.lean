/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8ActualFrame

/-! Actual quadratic-Krylov slice identities for source Theorem C. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

/-- The overlap vector weighted by a normalized spectral power. -/
def krylovModal (a rates : Fin n → ℝ) (ell w : ℝ) (r : ℕ) : Fin n → ℝ :=
  fun i => a i * ((rates i-ell) / w) ^ r

/-- The index-dependent constant term in the cubic cancellation polynomial. -/
def xiConstant (theta y z : ℝ) : ℝ :=
  theta ^ 3-((theta + y) + (theta + z)) * theta ^ 2-(y-z) ^ 2 * theta +
    (theta + y) ^ 3 + (theta + z) ^ 3-(theta + y) ^ 2 * (theta + z)-(theta + z) ^ 2 * (theta + y)

theorem xi_band_expansion (x y z ell w : ℝ) (hw : w ≠ 0) :
    MvPolynomial.eval ![-z,-x,-y] Xi = w ^ 3 *
      (((x-ell) / w) ^ 3 + (ell / w-(y-ell) / w-(z-ell) / w) * ((x-ell) / w) ^ 2 -
        ((ell / w) ^ 2 + 2 * (ell / w) * ((y-ell) / w + (z-ell) / w)+
          ((y-ell) / w-(z-ell) / w) ^ 2) * ((x-ell) / w) +
        xiConstant (ell / w) ((y-ell) / w) ((z-ell) / w)) := by
  rw [xi_cubic_first]
  unfold xiConstant
  field_simp; ring

/-- The h1 slice is the literal fourth moment plus its variable cubic coefficient. -/
theorem krylov_slice_one (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell w : ℝ) (hw : w ≠ 0) :
    tensorSlice (xiWeighted rates V) (krylovModal a rates ell w 1) =
      fun j k => w ^ 3 * (tensorSlice V (krylovModal a rates ell w 4) j k +
        (ell / w-(rates j-ell) / w-(rates k-ell) / w)*
          tensorSlice V (krylovModal a rates ell w 3) j k) := by
  classical
  funext j k
  have ht := shifted_weighted_moments a rates V hm ell w
  have h1 := ht.1 1 (by omega) j k
  have h2 := ht.1 2 (by omega) j k
  calc
    _ = w ^ 3 * (tensorSlice V (krylovModal a rates ell w 4) j k +
        (ell / w-(rates j-ell) / w-(rates k-ell) / w)*
          tensorSlice V (krylovModal a rates ell w 3) j k -
        ((ell / w) ^ 2 + 2 * (ell / w) * ((rates j-ell) / w + (rates k-ell) / w)+
          ((rates j-ell) / w-(rates k-ell) / w) ^ 2)*
          (∑ i, (a i * ((rates i-ell) / w) ^ 2) * V i j k) +
        xiConstant (ell / w) ((rates j-ell) / w) ((rates k-ell) / w)*
          (∑ i, (a i * ((rates i-ell) / w) ^ 1) * V i j k)) := by
      simp only [tensorSlice, xiWeighted, krylovModal, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [xi_band_expansion _ _ _ ell w hw]
      ring
    _ = _ := by rw [h1,h2]; ring

/-- The h2 slice retains the exact fifth, fourth and cubic moment terms. -/
theorem krylov_slice_two (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell w : ℝ) (hw : w ≠ 0) :
    tensorSlice (xiWeighted rates V) (krylovModal a rates ell w 2) =
      fun j k => w ^ 3 * (tensorSlice V (krylovModal a rates ell w 5) j k +
        (ell / w-(rates j-ell) / w-(rates k-ell) / w)*
          tensorSlice V (krylovModal a rates ell w 4) j k -
        ((ell / w) ^ 2 + 2 * (ell / w) * ((rates j-ell) / w + (rates k-ell) / w)+
          ((rates j-ell) / w-(rates k-ell) / w) ^ 2)*
          tensorSlice V (krylovModal a rates ell w 3) j k) := by
  classical
  funext j k
  have ht := shifted_weighted_moments a rates V hm ell w
  have h2 := ht.1 2 (by omega) j k
  calc
    _ = w ^ 3 * (tensorSlice V (krylovModal a rates ell w 5) j k +
        (ell / w-(rates j-ell) / w-(rates k-ell) / w)*
          tensorSlice V (krylovModal a rates ell w 4) j k -
        ((ell / w) ^ 2 + 2 * (ell / w) * ((rates j-ell) / w + (rates k-ell) / w)+
          ((rates j-ell) / w-(rates k-ell) / w) ^ 2)*
          tensorSlice V (krylovModal a rates ell w 3) j k +
        xiConstant (ell / w) ((rates j-ell) / w) ((rates k-ell) / w)*
          (∑ i, (a i * ((rates i-ell) / w) ^ 2) * V i j k)) := by
      simp only [tensorSlice, xiWeighted, krylovModal, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [xi_band_expansion _ _ _ ell w hw]
      ring
    _ = _ := by rw [h2]; ring

end C145DRE8

namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ}

/-- B=-A is the full decay matrix, including the known decay mu. -/
def shiftedDecayAction (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ell w : ℝ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun v => (-(A.mulVec x) v-ell * x v) / w

/-- Literal source h0,h1,h2. No spectral certificate is part of this definition. -/
def physicalKrylov (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) (ell w : ℝ) : Fin 3 → Fin (n + 1) → ℝ :=
  ![centeredPort b, shiftedDecayAction A ell w (centeredPort b),
    shiftedDecayAction A ell w (shiftedDecayAction A ell w (centeredPort b))]

theorem eigenframe_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (rates x : Fin (n + 1) → ℝ)
    (hEig : ∀ i, A.mulVec (fun v => U v i) = (-rates i) • (fun v => U v i)) :
    A.mulVec ((Matrix.of U).mulVec x) =
      (Matrix.of U).mulVec (fun i => -rates i * x i) := by
  classical
  funext v
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, x i * (∑ u, A v u * U u i) := by
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u hu; ring
    _ = _ := by
      apply Finset.sum_congr rfl; intro i hi
      have h := congrFun (hEig i) v
      change (∑ u, A v u * U u i) = (-rates i) * U v i at h
      rw [h]; ring

theorem shiftedDecayAction_eigenframe
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (rates x : Fin (n + 1) → ℝ)
    (hEig : ∀ i, A.mulVec (fun v => U v i) = (-rates i) • (fun v => U v i))
    (ell w : ℝ) :
    shiftedDecayAction A ell w ((Matrix.of U).mulVec x) =
      (Matrix.of U).mulVec (fun i => x i * ((rates i-ell) / w)) := by
  unfold shiftedDecayAction
  rw [eigenframe_mulVec A U rates x hEig]
  funext v
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply,
    ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl; intro i hi; ring

/-- Physical powers of (B-ell I)/w are the actual modal weighted powers.
The ground coordinate remains zero because the port was centered. -/
theorem physicalKrylov_modal
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (U : Fin (n + 1) → Fin (n + 1) → ℝ) (rates b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U) (hG : ∀ v, U v 0 = c)
    (hEig : ∀ i, A.mulVec (fun v => U v i) = (-rates i) • (fun v => U v i))
    (ell w : ℝ) (r : Fin 3) :
    physicalKrylov A b ell w r =
      (Matrix.of U).mulVec (residualVector (krylovModal
        (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ)
        (fun i : Fin n => rates i.succ) ell w r.val)) := by
  let a : Fin n → ℝ := fun i => C145.Pulse.modalOverlap U b i.succ
  have h0 := actual_residual_signature U b c hU hG
  have hstep (p : ℕ) :
      shiftedDecayAction A ell w ((Matrix.of U).mulVec (residualVector
        (krylovModal a (fun i : Fin n => rates i.succ) ell w p))) =
      (Matrix.of U).mulVec (residualVector
        (krylovModal a (fun i : Fin n => rates i.succ) ell w (p + 1))) := by
    rw [shiftedDecayAction_eigenframe A U rates _ hEig]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [residualVector]
    · simp only [residualVector, Fin.cases_succ, krylovModal, pow_succ]
      ring
  have h0' : centeredPort b = (Matrix.of U).mulVec (residualVector
      (krylovModal a (fun i : Fin n => rates i.succ) ell w 0)) := by
    have hk : krylovModal a (fun i : Fin n => rates i.succ) ell w 0 = a := by
      funext i; simp [krylovModal]
    rw [hk]
    exact h0.symm
  fin_cases r
  · exact h0'
  · change shiftedDecayAction A ell w (centeredPort b) = _
    rw [h0', hstep 0]
  · change shiftedDecayAction A ell w (shiftedDecayAction A ell w (centeredPort b)) = _
    rw [h0', hstep 0, hstep 1]

end C145DRE8

end
