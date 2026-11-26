/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8KrylovSlices
public import LeanPool.C145.C145DRE8OptimalContraction

/-!
# The joint signature criterion for calibrated graph identification.
-/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ}

/-- View a matrix as a vector indexed by ordered pairs with the Euclidean norm. -/
def matrixVector (M : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => M p.1 p.2)

theorem matrixVector_energy (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixVector M‖ ^ 2 = matrixSq M := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [matrixVector, matrixSq, Fintype.sum_prod_type]

theorem matrixVector_add (M N : Matrix (Fin n) (Fin n) ℝ) :
    matrixVector (M + N) = matrixVector M + matrixVector N := rfl

theorem matrixVector_sub (M N : Matrix (Fin n) (Fin n) ℝ) :
    matrixVector (M-N) = matrixVector M-matrixVector N := rfl

theorem matrixVector_scale (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    matrixVector (fun j k => c * M j k) = c • matrixVector M := rfl

theorem matrixVector_coeff_bound (M : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ j k, |f j k| ≤ c) :
    ‖matrixVector (fun j k => f j k * M j k)‖ ≤ c * ‖matrixVector M‖ := by
  have hh : matrixSq (fun j k => f j k * M j k) ≤ c ^ 2 * matrixSq M := by
    simp only [matrixSq, Finset.mul_sum]
    apply Finset.sum_le_sum; intro j hj
    apply Finset.sum_le_sum; intro k hk
    have hf2 : (f j k) ^ 2 ≤ c ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f j k)) hc).mpr (hf j k)
    have h := mul_le_mul_of_nonneg_right hf2 (sq_nonneg (M j k))
    simpa only [mul_pow] using h
  rw [← matrixVector_energy M, ← matrixVector_energy (fun j k => f j k * M j k), ← mul_pow] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hh

theorem krylov_coefficient_bounds (theta y z : ℝ) (ht : 1 < theta)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |theta-y-z|≤theta ∧
      |theta ^ 2 + 2 * theta * (y + z) + (y-z) ^ 2|≤theta ^ 2 + 4 * theta + 1 := by
  have ht0 : 0 ≤ theta := by linarith
  have hs : (y-z) ^ 2 ≤ 1 := by
    have h : |y-z|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg (y - z)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
  constructor
  · exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [abs_of_nonneg (by positivity)]
    nlinarith



/-- The three numerator bounds formed from residual powers three, four, and five. -/
def jointNumerator (a t : Fin n → ℝ) (theta : ℝ) : Fin 3 → ℝ :=
  ![kappa a t 3, kappa a t 4 + theta * kappa a t 3,
    kappa a t 5 + theta * kappa a t 4 + (theta ^ 2 + 4 * theta + 1) * kappa a t 3]

/-- Literal source beta_r, retaining the three distinct projection norms. -/
def jointBeta (a t : Fin n → ℝ) (theta : ℝ) (r : Fin 3) : ℝ :=
  jointNumerator a t theta r / (theta-1) ^ 3

/-- Sum of the squares of the three separate contraction coefficients. -/
def jointBetaSq (a t : Fin n → ℝ) (theta : ℝ) : ℝ :=
  ∑ r : Fin 3, jointBeta a t theta r ^ 2

/-- The Euclidean norm of the three contraction coefficients. -/
def jointBetaNorm (a t : Fin n → ℝ) (theta : ℝ) : ℝ :=
  Real.sqrt (jointBetaSq a t theta)

theorem power_slice_norm_bound (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (p : ℕ) :
    ‖matrixVector (tensorSlice V (fun i => a i * t i ^ p))‖ ≤
      kappa a t p * Real.sqrt (tensorSq V) := by
  have h := power_slice_kappa_bound a t V hm p
  rw [← matrixVector_energy] at h
  have hs : (Real.sqrt (tensorSq V)) ^ 2 = tensorSq V := Real.sq_sqrt (tensorSq_nonneg V)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (kappa_nonneg a t p) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, hs] using h

/-- Exact Minkowski estimate for the two surviving terms in source (7.2). -/
theorem joint_one_norm_bound (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (theta : ℝ) (ht : 1 < theta)
    (hlo : ∀ i, 0 ≤ t i) (hhi : ∀ i, t i ≤ 1) :
    ‖matrixVector (fun j k => tensorSlice V (fun i => a i * t i ^ 4) j k +
      (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 3) j k)‖ ≤
      (kappa a t 4 + theta * kappa a t 3) * Real.sqrt (tensorSq V) := by
  have htheta : 0 ≤ theta := by linarith
  have hc := matrixVector_coeff_bound (tensorSlice V (fun i => a i * t i ^ 3))
    (fun j k => theta-t j-t k) theta htheta
    (fun j k => (krylov_coefficient_bounds theta (t j) (t k) ht
      (hlo j) (hhi j) (hlo k) (hhi k)).1)
  have h3 := power_slice_norm_bound a t V hm 3
  have h4 := power_slice_norm_bound a t V hm 4
  calc
    _ ≤ ‖matrixVector (tensorSlice V (fun i => a i * t i ^ 4))‖+
      ‖matrixVector (fun j k => (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 3) j k)‖ :=
        norm_add_le _ _
    _ ≤ kappa a t 4 * Real.sqrt (tensorSq V) + theta * (kappa a t 3 * Real.sqrt (tensorSq V)) :=
      add_le_add h4 (hc.trans (mul_le_mul_of_nonneg_left h3 htheta))
    _ = _ := by ring

/-- Exact three-term estimate for source (7.3), with its stated coefficient. -/
theorem joint_two_norm_bound (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (theta : ℝ) (ht : 1 < theta)
    (hlo : ∀ i, 0 ≤ t i) (hhi : ∀ i, t i ≤ 1) :
    ‖matrixVector (fun j k => tensorSlice V (fun i => a i * t i ^ 5) j k +
      (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 4) j k -
      (theta ^ 2 + 2 * theta * (t j + t k) + (t j-t k) ^ 2)*
        tensorSlice V (fun i => a i * t i ^ 3) j k)‖ ≤
      (kappa a t 5 + theta * kappa a t 4 + (theta ^ 2 + 4 * theta + 1) * kappa a t 3)*
        Real.sqrt (tensorSq V) := by
  have htheta : 0 ≤ theta := by linarith
  have hC : 0 ≤ theta ^ 2 + 4 * theta + 1 := by positivity
  have hc4 := matrixVector_coeff_bound (tensorSlice V (fun i => a i * t i ^ 4))
    (fun j k => theta-t j-t k) theta htheta
    (fun j k => (krylov_coefficient_bounds theta (t j) (t k) ht
      (hlo j) (hhi j) (hlo k) (hhi k)).1)
  have hc3 := matrixVector_coeff_bound (tensorSlice V (fun i => a i * t i ^ 3))
    (fun j k => theta ^ 2 + 2 * theta * (t j + t k) + (t j-t k) ^ 2) (theta ^ 2 + 4 * theta + 1) hC
    (fun j k => (krylov_coefficient_bounds theta (t j) (t k) ht
      (hlo j) (hhi j) (hlo k) (hhi k)).2)
  have h3 := power_slice_norm_bound a t V hm 3
  have h4 := power_slice_norm_bound a t V hm 4
  have h5 := power_slice_norm_bound a t V hm 5
  calc
    _ ≤ (‖matrixVector (tensorSlice V (fun i => a i * t i ^ 5))‖+
      ‖matrixVector (fun j k => (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 4) j k)‖)+
      ‖matrixVector (fun j k => (theta ^ 2 + 2 * theta * (t j + t k) + (t j-t k) ^ 2)*
        tensorSlice V (fun i => a i * t i ^ 3) j k)‖ :=
      (norm_sub_le
        (matrixVector (tensorSlice V (fun i => a i * t i ^ 5)) +
          matrixVector (fun j k => (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 4) j k))
        (matrixVector (fun j k => (theta ^ 2 + 2 * theta * (t j + t k) + (t j-t k) ^ 2)*
          tensorSlice V (fun i => a i * t i ^ 3) j k))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (kappa a t 5 * Real.sqrt (tensorSq V) + theta * (kappa a t 4 * Real.sqrt (tensorSq V)))+
      (theta ^ 2 + 4 * theta + 1) * (kappa a t 3 * Real.sqrt (tensorSq V)) :=
      add_le_add (add_le_add h5 (hc4.trans (mul_le_mul_of_nonneg_left h4 htheta)))
        (hc3.trans (mul_le_mul_of_nonneg_left h3 hC))
    _ = _ := by ring



/-- The three tensor-slice matrices used in the modal joint-signature bound. -/
def krylovCore (a t : Fin n → ℝ) (V : Tensor n) (theta : ℝ) :
    Fin 3 → Matrix (Fin n) (Fin n) ℝ :=
  ![tensorSlice V (fun i => a i * t i ^ 3),
    (fun j k => tensorSlice V (fun i => a i * t i ^ 4) j k +
      (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 3) j k),
    (fun j k => tensorSlice V (fun i => a i * t i ^ 5) j k +
      (theta-t j-t k) * tensorSlice V (fun i => a i * t i ^ 4) j k -
      (theta ^ 2 + 2 * theta * (t j + t k) + (t j-t k) ^ 2)*
        tensorSlice V (fun i => a i * t i ^ 3) j k)]

theorem krylov_core_norm_bound (a t : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a t V) (theta : ℝ) (ht : 1 < theta)
    (hlo : ∀ i, 0 ≤ t i) (hhi : ∀ i, t i ≤ 1) (r : Fin 3) :
    ‖matrixVector (krylovCore a t V theta r)‖ ≤
      jointNumerator a t theta r * Real.sqrt (tensorSq V) := by
  fin_cases r
  · exact power_slice_norm_bound a t V hm 3
  · exact joint_one_norm_bound a t V hm theta ht hlo hhi
  · exact joint_two_norm_bound a t V hm theta ht hlo hhi

theorem jointNumerator_nonneg (a t : Fin n → ℝ) (theta : ℝ) (ht : 0 ≤ theta) (r : Fin 3) :
    0 ≤ jointNumerator a t theta r := by
  have h3 := kappa_nonneg a t 3
  have h4 := kappa_nonneg a t 4
  have h5 := kappa_nonneg a t 5
  fin_cases r
  · exact h3
  · exact add_nonneg h4 (mul_nonneg ht h3)
  · exact add_nonneg (add_nonneg h5 (mul_nonneg ht h4))
      (mul_nonneg (by positivity) h3)

theorem krylov_slice_core (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell w : ℝ) (hw : w ≠ 0) (r : Fin 3) :
    tensorSlice (xiWeighted rates V) (krylovModal a rates ell w r.val) =
      fun j k => w ^ 3 * krylovCore a (fun i => (rates i-ell) / w) V (ell / w) r j k := by
  fin_cases r
  · have ha : krylovModal a rates ell w 0 = a := by funext i; simp [krylovModal]
    rw [ha, cubic_cancellation a rates V hm ell w hw]
    rfl
  · exact krylov_slice_one a rates V hm ell w hw
  · exact krylov_slice_two a rates V hm ell w hw

theorem krylov_slice_scaled_bound (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) (r : Fin 3) :
    matrixSq (tensorSlice (xiWeighted rates V) (krylovModal a rates ell (u-ell) r.val)) ≤
      (u-ell) ^ 6 * jointNumerator a (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) r ^ 2 *
        tensorSq V := by
  have ht : 1 < ell / (u-ell) := (one_lt_div (sub_pos.mpr hw)).mpr (by linarith)
  have hnorm := krylov_core_norm_bound a (fun i => (rates i-ell) / (u-ell)) V
    (shifted_weighted_moments a rates V hm ell (u-ell)) (ell / (u-ell)) ht
    (fun i => (band_coordinate rates ell u hw hlo hhi i).1)
    (fun i => (band_coordinate rates ell u hw hlo hhi i).2) r
  have hn := jointNumerator_nonneg a (fun i => (rates i - ell) / (u - ell))
    (ell / (u - ell)) (by linarith) r
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (Real.sqrt_nonneg _))).mpr hnorm
  rw [matrixVector_energy, mul_pow, Real.sq_sqrt (tensorSq_nonneg V)] at hs
  rw [krylov_slice_core a rates V hm ell (u-ell) (ne_of_gt (sub_pos.mpr hw)), matrixSq_scale]
  calc
    _ ≤ ((u-ell) ^ 3) ^ 2 *
        (jointNumerator a (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) r ^ 2 * tensorSq V) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

/-- Cancel the positive spectral width without strengthening the source beta. -/
theorem scaled_gap_transfer (w d c ev ee m : ℝ) (_hw : 0 < w) (hd : 0 < d)
    (hm : m ≤ w ^ 6 * c ^ 2 * ev) (he : (w * d) ^ 6 * ev ≤ ee) :
    m ≤ (c / d ^ 3) ^ 2 * ee := by
  have h1 := mul_le_mul_of_nonneg_left hm (le_of_lt (pow_pos hd 6))
  have h2 := mul_le_mul_of_nonneg_left he (sq_nonneg c)
  have hh : d ^ 6 * m ≤ c ^ 2 * ee := by
    calc
      _ ≤ d ^ 6 * (w ^ 6 * c ^ 2 * ev) := h1
      _ = c ^ 2 * ((w * d) ^ 6 * ev) := by ring
      _ ≤ _ := h2
  have hh' : m ≤ c ^ 2 * ee / d ^ 6 := (le_div_iff₀ (pow_pos hd 6)).mpr (by nlinarith only [hh])
  convert hh' using 1; field_simp [ne_of_gt hd]

/-- Each literal beta_r controls its own actual quadratic-Krylov slice. -/
theorem krylov_slice_beta_bound (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) (r : Fin 3) :
    matrixSq (tensorSlice (xiWeighted rates V) (krylovModal a rates ell (u-ell) r.val)) ≤
      jointBeta a (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) r ^ 2 *
        tensorSq (xiWeighted rates V) := by
  have ht : 1 < ell / (u-ell) := (one_lt_div (sub_pos.mpr hw)).mpr (by linarith)
  have hg : (u-ell) * (ell / (u-ell)-1) = 2 * ell-u := by
    field_simp [ne_of_gt (sub_pos.mpr hw)]; ring
  have he := spectral_tensor_bound rates V ell u hband hlo hhi
  rw [← hg] at he
  exact scaled_gap_transfer (u-ell) (ell / (u-ell)-1) _ _ _ _
    (sub_pos.mpr hw) (sub_pos.mpr ht)
    (krylov_slice_scaled_bound a rates V hm ell u hw hband hlo hhi r) he



/-- Joint physical rigidity transported through the very same actual frame. -/
theorem calibrated_modal_joint_rigidity
    (U Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U.transpose * U = 1) (hQ : Q.transpose * Q = 1)
    (hunit : ∀ i, ∑ v, Q i v = 1) (E : Tensor n) (a rates : Fin n → ℝ)
    (ell w : ℝ) (hPhysical : physicalDifference Q = rotateTensor U (groundZero E))
    (delta : ℝ)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq
      (fun r : Fin 3 => U.mulVec (residualVector (krylovModal a rates ell w r.val))) j k) :
    delta ^ 2 * tensorSq E ≤ ((n + 1 : ℕ) + 2 : ℝ)*
      ∑ r : Fin 3, matrixSq (tensorSlice E (krylovModal a rates ell w r.val)) := by
  have hh := physical_slice_rigidity Q hQ hunit
    (fun r : Fin 3 => U.mulVec (residualVector (krylovModal a rates ell w r.val))) delta hsep
  rw [hPhysical, tensorSq_rotateTensor U hU, tensorSq_groundZero] at hh
  simp only [sliceSq, matrixSq_slice_rotateTensor U hU, matrixSq_slice_groundZero,
    Fintype.card_fin] at hh
  exact hh

/-- Actual H2 null data provides all three literal source beta bounds. -/
theorem actual_H2_joint_contraction (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    (∑ r : Fin 3, matrixSq (tensorSlice E (krylovModal a rates ell (u-ell) r.val))) ≤
      jointBetaSq a (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) * tensorSq E := by
  obtain ⟨R,hR,hAdm,hE,hm,_⟩ :=
    actual_H2_physical_kernel a rates ha hRates E hSym hData ell (u-ell)
  rw [hE]
  unfold jointBetaSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  exact krylov_slice_beta_bound a rates _ hm ell u hw hband hlo hhi r

/-- Source squared q_H<1 kills the actual calibrated physical secant. -/
theorem calibrated_joint_H2_kernel_zero
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
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq
      (fun r : Fin 3 => U.mulVec (residualVector (krylovModal a rates ell (u-ell) r.val))) j k)
    (hq : ((n + 1 : ℕ) + 2 : ℝ) * jointBetaSq a
      (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2) : E = 0 := by
  have hc := actual_H2_joint_contraction a rates ha hRates E hSym hData ell u hw hband hlo hhi
  have hr := calibrated_modal_joint_rigidity U Q hU hQ hunit E a rates ell (u-ell) hPhysical delta
    hsep
  have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) + 2 : ℝ) := by positivity
  have hh := hr.trans (mul_le_mul_of_nonneg_left hc hN)
  have hcombined : delta ^ 2 * tensorSq E ≤ (((n + 1 : ℕ) + 2 : ℝ) * jointBetaSq a
      (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell))) * tensorSq E := by
    simpa only [mul_assoc] using hh
  apply tensorSq_zero E
  apply le_antisymm _ (tensorSq_nonneg E)
  by_contra h
  have hp : 0 < tensorSq E := lt_of_not_ge h
  exact (not_lt_of_ge hcombined) (mul_lt_mul_of_pos_right hq hp)

theorem actual_calibrated_H2_joint_cubic_equality
    (μ : ℝ) (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (ha : ∀ i, C145.Pulse.modalOverlap U b i ≠ 0)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (C145PhysicalFrame.T V (C145.Pulse.modalOverlap U b)))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hEig : ∀ i, A.mulVec (fun v => U v i) = (-fullRates μ rates i) • (fun v => U v i))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (delta : ℝ) (_hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq (physicalKrylov A b ell (u - ell)) j k)
    (hq : ((n + 1 : ℕ) + 2 : ℝ) * jointBetaSq
      (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ)
      (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2) :
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
  have hSig (r : Fin 3) : physicalKrylov A b ell (u-ell) r =
      (Matrix.of U).mulVec (residualVector (krylovModal ar rates ell (u-ell) r.val)) :=
    physicalKrylov_modal A U (fullRates μ rates) b c hU hGU hEig ell (u-ell) r
  have hSep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq
      (fun r : Fin 3 => (Matrix.of U).mulVec
        (residualVector (krylovModal ar rates ell (u-ell) r.val))) j k := by
    intro j k hjk
    simpa only [signatureSq, hSig] using hsep j k hjk
  have hPos : ∀ i, 0 < rates i := by
    intro i
    have hell : 0 < ell := by linarith
    exact hell.trans_le (hlo i)
  have hz : C1-C0 = 0 := calibrated_joint_H2_kernel_zero ar rates (fun i => ha i.succ) hRates
    (C1-C0) (fullSymTensor_sub C1 C0
      (residual_fullSym _ (actual_cubic_fullSym V))
      (residual_fullSym _ (actual_cubic_fullSym U)))
    (samePositive_weighted_difference ar rates hPos C0 C1 hData)
    ell u hw hband hlo hhi (Matrix.of U) Q (columnOrthonormal_matrix U hU)
    hQ hunit hPhys delta hSep
    hq
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
theorem actual_calibrated_H2_joint_vertex_identification
    (μ : ℝ) (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (ha : ∀ i, C145.Pulse.modalOverlap U b i ≠ 0)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (hH : SamePositive (fullRates μ rates)
      (C145PhysicalFrame.T U (C145.Pulse.modalOverlap U b))
      (C145PhysicalFrame.T V (C145.Pulse.modalOverlap U b)))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hEig : ∀ i, A.mulVec (fun v => U v i) = (-fullRates μ rates i) • (fun v => U v i))
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ signatureSq (physicalKrylov A b ell (u - ell)) j k)
    (hq : ((n + 1 : ℕ) + 2 : ℝ) * jointBetaSq
      (fun i : Fin n => C145.Pulse.modalOverlap U b i.succ)
      (fun i => (rates i-ell) / (u-ell)) (ell / (u-ell)) < delta ^ 2) :
    ∃ π : Equiv.Perm (Fin (n + 1)),
      (∀ w v, C145CoordinatePermutation.transport U V w v = if w = π v then 1 else 0) ∧
      (∀ v i, V (π v) i = U v i) := by
  exact C145CoordinatePermutation.cubic_equality_vertex_permutation U V hU hV
    (actual_calibrated_H2_joint_cubic_equality μ rates hRates U V b c hU hV ha hGU hGV hH
      A hEig ell u hw hband hlo hhi delta hd hsep hq)


end C145DRE8

end
