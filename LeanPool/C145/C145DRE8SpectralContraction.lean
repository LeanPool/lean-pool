/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8CubicCancellation

/-! DRE8 (6.4), squared Frobenius form, in orthonormal modal coordinates.
The spectral band is an explicit premise: ell <= full rates <= u < 2ell.
All norms are literal finite sums. No target norm bound is a certificate. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

/-- The cubic monomial minus the quadratic approximation used in the spectral bound. -/
def chebyshevResidual (t : ℝ) : ℝ :=
  t ^ 3 - (1 / 32 - 9 / 16 * t + 3 / 2 * t ^ 2)

/-- Standard monic Chebyshev residual, with exact rational coefficients. -/
theorem chebyshev_residual_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chebyshevResidual t ^ 2 ≤ (1 / 1024 : ℝ) := by
  have hlow := mul_nonneg ht0 (sq_nonneg (t-3 / 4))
  have hhigh := mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg (t-1 / 4))
  have hlo : -(1 / 32 : ℝ) ≤ chebyshevResidual t := by
    dsimp [chebyshevResidual]; nlinarith [hlow]
  have hhi : chebyshevResidual t ≤ (1 / 32 : ℝ) := by
    dsimp [chebyshevResidual]; nlinarith [hhigh]
  nlinarith [sq_nonneg (chebyshevResidual t)]

theorem tensorSq_nonneg (V : Tensor n) : 0 ≤ tensorSq V := by
  unfold tensorSq; positivity

/-- Cauchy--Schwarz followed by the exact three-index Frobenius sum. -/
theorem tensorSlice_cauchy (V : Tensor n) (x : Fin n → ℝ) :
    matrixSq (tensorSlice V x) ≤ (∑ i, x i ^ 2) * tensorSq V := by
  classical
  have hsum : (∑ j, ∑ k, ∑ i, V i j k ^ 2) = tensorSq V := by
    unfold tensorSq
    calc
      _ = ∑ j, ∑ i, ∑ k, V i j k ^ 2 := by
        apply Finset.sum_congr rfl; intro j hj
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  calc
    _ ≤ ∑ j, ∑ k, (∑ i, x i ^ 2) * (∑ i, V i j k ^ 2) := by
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro k hk
      simpa only [tensorSlice, Finset.mem_univ, Finset.sum_const_zero,
        Finset.sum_filter, Finset.filter_true_of_mem, true_and] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x
          (fun i => V i j k))
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [hsum]

/-- The interval-normalized modal coordinate really lies in [0,1]. -/
theorem band_coordinate (rates : Fin n → ℝ) (ell u : ℝ) (hw : ell < u)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) (i : Fin n) :
    0 ≤ (rates i-ell) / (u-ell) ∧ (rates i-ell) / (u-ell) ≤ 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hlo i)) (sub_nonneg.mpr hw.le)
  · exact (div_le_one (sub_pos.mpr hw)).mpr (by linarith [hhi i])

/-- Every positive triangle gap is at least 2ell-u. Rates include mu already. -/
theorem spectral_triangle_gap (rates : Fin n → ℝ) (ell u : ℝ)
    (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) (i j k : Fin n) :
    2 * ell-u ≤ rates i + rates j-rates k := by linarith [hlo i,hlo j,hhi k]

/-- Literal Xi is bounded away from zero only under the stated source band. -/
theorem spectral_xi_square (rates : Fin n → ℝ) (ell u : ℝ)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (i j k : Fin n) :
    (2 * ell-u) ^ 6 ≤ (MvPolynomial.eval ![-rates k,-rates i,-rates j] Xi) ^ 2 := by
  let g := 2 * ell-u
  have hg : 0 ≤ g := by dsimp [g]; linarith
  have h1 := spectral_triangle_gap rates ell u hlo hhi i j k
  have h2 := spectral_triangle_gap rates ell u hlo hhi i k j
  have h3 := spectral_triangle_gap rates ell u hlo hhi j k i
  have hg1 : 0 ≤ rates i + rates j-rates k := hg.trans h1
  have hg2 : 0 ≤ rates i + rates k-rates j := hg.trans h2
  have hp : g ^ 3 ≤ (rates i + rates j-rates k) *
      (rates i + rates k-rates j) * (rates j + rates k-rates i) := by
    have hh := mul_le_mul h1 h2 hg (hg.trans h1)
    have hh2 := mul_le_mul hh h3 hg (mul_nonneg hg1 hg2)
    simpa [g, pow_succ] using hh2
  rw [xi_negative_node_factors, neg_sq]
  have hg3 : 0 ≤ g ^ 3 := by positivity
  have hp2 := pow_le_pow_left₀ hg3 hp 2
  simpa only [← pow_mul] using hp2

/-- Full orthonormal tensor energy is controlled by Xi multiplication. -/
theorem spectral_tensor_bound (rates : Fin n → ℝ) (V : Tensor n) (ell u : ℝ)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    (2 * ell-u) ^ 6 * tensorSq V ≤ tensorSq (xiWeighted rates V) := by
  classical
  unfold tensorSq
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i hi
  apply Finset.sum_le_sum; intro j hj
  apply Finset.sum_le_sum; intro k hk
  have h := mul_le_mul_of_nonneg_right
    (spectral_xi_square rates ell u hband hlo hhi i j k) (sq_nonneg (V i j k))
  simpa only [xiWeighted, mul_pow] using h

/-- Residual weighted-vector energy has the exact source factor 1/32 squared. -/
theorem chebyshev_vector_bound (a t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    1024 * (∑ i, (a i * chebyshevResidual (t i)) ^ 2) ≤ ∑ i, a i ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i hi
  have h := mul_le_mul_of_nonneg_left
    (chebyshev_residual_bound (t i) (ht0 i) (ht1 i)) (sq_nonneg (a i))
  rw [mul_pow]
  nlinarith

/-- Exact scaled slice energy, avoiding any default matrix/Pi norm. -/
theorem matrixSq_scale (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    matrixSq (fun j k => c * M j k) = c ^ 2 * matrixSq M := by
  unfold matrixSq
  simp only [mul_pow, Finset.mul_sum]

/-- Quantitative kernel contraction for any explicit quadratic residual.
Choosing a least-squares projection gives source kappa_3; its existence or
minimization is not presumed by this finite-coordinate theorem. -/
theorem kernel_residual_contraction (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u)
    (c0 c1 c2 : ℝ) :
    (2 * ell-u) ^ 6 * matrixSq (tensorSlice (xiWeighted rates V) a) ≤
      (u-ell) ^ 6 *
      (∑ i, (a i * (((rates i-ell) / (u-ell)) ^ 3 -
        (c0 + c1 * ((rates i-ell) / (u-ell)) + c2 * ((rates i-ell) / (u-ell)) ^ 2))) ^ 2) *
      tensorSq (xiWeighted rates V) := by
  let t := fun i => (rates i-ell) / (u-ell)
  let r := fun i => a i * (t i ^ 3-(c0 + c1 * t i + c2 * t i ^ 2))
  have hshift := shifted_weighted_moments a rates V hm ell (u-ell)
  have hs : tensorSlice (xiWeighted rates V) a =
      fun j k => (u-ell) ^ 3 * tensorSlice V r j k := by
    rw [cubic_cancellation a rates V hm ell (u-ell) (sub_ne_zero.mpr (ne_of_gt hw))]
    rw [cubic_residual_slice a t V hshift c0 c1 c2]
  have he : matrixSq (tensorSlice (xiWeighted rates V) a) =
      (u-ell) ^ 6 * matrixSq (tensorSlice V r) := by
    rw [hs, matrixSq_scale]; ring
  have hc := tensorSlice_cauchy V r
  have hb := spectral_tensor_bound rates V ell u hband hlo hhi
  have hw6 : 0 ≤ (u-ell) ^ 6 := by positivity
  have hg6 : 0 ≤ (2 * ell-u) ^ 6 := by positivity
  have hr : 0 ≤ ∑ i, r i ^ 2 := by positivity
  calc
    _ = (u-ell) ^ 6 * ((2 * ell-u) ^ 6 * matrixSq (tensorSlice V r)) := by rw [he]; ring
    _ ≤ (u-ell) ^ 6 * ((2 * ell-u) ^ 6 * ((∑ i, r i ^ 2) * tensorSq V)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hg6) hw6
    _ = (u-ell) ^ 6 * (∑ i, r i ^ 2) * ((2 * ell-u) ^ 6 * tensorSq V) := by ring
    _ ≤ (u-ell) ^ 6 * (∑ i, r i ^ 2) * tensorSq (xiWeighted rates V) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hw6 hr)

/-- DRE8 explicit Chebyshev bound (6.4), squared, with source factor 1/1024. -/
theorem kernel_chebyshev_contraction (a rates : Fin n → ℝ) (V : Tensor n)
    (hm : WeightedMoments a rates V) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    1024 * (2 * ell-u) ^ 6 * matrixSq (tensorSlice (xiWeighted rates V) a) ≤
      (u-ell) ^ 6 * (∑ i, a i ^ 2) * tensorSq (xiWeighted rates V) := by
  let t := fun i => (rates i-ell) / (u-ell)
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := band_coordinate rates ell u hw hlo hhi
  have hc := kernel_residual_contraction a rates V hm ell u hw hband hlo hhi
    (1 / 32) (-9 / 16) (3 / 2)
  have hpoly : (∑ i, (a i * (t i ^ 3 - ((1 / 32 : ℝ) + (-9 / 16) * t i + (3 / 2) * t i ^ 2))) ^ 2) =
      ∑ i, (a i * chebyshevResidual (t i)) ^ 2 := by
    apply Finset.sum_congr rfl; intro i hi
    dsimp [chebyshevResidual]; ring
  change (2 * ell-u) ^ 6 * matrixSq (tensorSlice (xiWeighted rates V) a) ≤
    (u - ell) ^ 6 *
      (∑ i, (a i * (t i ^ 3 - ((1 / 32 : ℝ) + (-9 / 16) * t i + (3 / 2) * t i ^ 2))) ^ 2) *
      tensorSq (xiWeighted rates V) at hc
  rw [hpoly] at hc
  have hr := chebyshev_vector_bound a t (fun i => (ht i).1) (fun i => (ht i).2)
  have hw6 : 0 ≤ (u-ell) ^ 6 := by positivity
  have hE := tensorSq_nonneg (xiWeighted rates V)
  have h1 := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1024)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hw6) hE
  calc
    _ = 1024 * ((2 * ell-u) ^ 6 * matrixSq (tensorSlice (xiWeighted rates V) a)) := by ring
    _ ≤ 1024 * ((u-ell) ^ 6 * (∑ i, (a i * chebyshevResidual (t i)) ^ 2) *
        tensorSq (xiWeighted rates V)) := h1
    _ = ((u-ell) ^ 6 * (1024 * ∑ i, (a i * chebyshevResidual (t i)) ^ 2)) *
        tensorSq (xiWeighted rates V) := by ring
    _ ≤ _ := h2

/-- Actual ordinary H2 data implies the quantitative physical modal estimate.
No moment, Xi factorization, or desired norm inequality is an input. -/
theorem actual_H2_chebyshev_contraction (a rates : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hRates : Function.Injective rates)
    (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates (weightedTensor a E)) (ell u : ℝ) (hw : ell < u)
    (hband : u < 2 * ell) (hlo : ∀ i, ell ≤ rates i) (hhi : ∀ i, rates i ≤ u) :
    1024 * (2 * ell-u) ^ 6 * matrixSq (tensorSlice E a) ≤
      (u-ell) ^ 6 * (∑ i, a i ^ 2) * tensorSq E := by
  obtain ⟨R,_,_,hE,hm,_⟩ := actual_H2_physical_kernel a rates ha hRates E hSym hData ell (u-ell)
  rw [hE]
  exact kernel_chebyshev_contraction a rates _ hm ell u hw hband hlo hhi

end C145DRE8

end
