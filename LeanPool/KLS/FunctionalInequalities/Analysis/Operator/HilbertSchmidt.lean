/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Standard trace and Hilbert–Schmidt norm

`stdTrace` and `hsNormSq` in the standard basis of a finite-dimensional inner-product space, with
operator norm ≤
Hilbert–Schmidt ≤ trace for positive operators and the Cauchy–Schwarz and composition bounds
(Lyapunov estimates of the
cutoff localization).
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {n : ℕ}

private theorem basis_sum_inner_sq (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  calc
    (∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ ^ 2) =
        ∑ i, ⟪x, EuclideanSpace.basisFun (Fin n) ℝ i⟫ *
          ⟪EuclideanSpace.basisFun (Fin n) ℝ i, x⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm x (EuclideanSpace.basisFun (Fin n) ℝ i), pow_two]
    _ = ⟪x, x⟫ :=
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner x x
    _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

private theorem positive_inner_sq_le
    {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hM : M.IsPositive) (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, M v⟫ ^ 2 ≤ ⟪u, M u⟫ * ⟪v, M v⟫ := by
  have hsym : ⟪v, M u⟫ = ⟪u, M v⟫ := by
    calc
      ⟪v, M u⟫ = ⟪M u, v⟫ := (real_inner_comm v (M u)).symm
      _ = ⟪u, M v⟫ := hM.isSymmetric u v
  have hquad :
      ∀ t : ℝ, 0 ≤ ⟪u, M u⟫ * (t * t) + (2 * ⟪u, M v⟫) * t +
        ⟪v, M v⟫ := by
    intro t
    have hp := hM.inner_nonneg_right (t • u + v)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right] at hp
    rw [hsym] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- The coordinate trace `tr M = Σ_i ⟪e_i, M e_i⟫` of an operator on `ℝⁿ`. -/
def stdTrace (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ i)⟫

/-- The squared Hilbert–Schmidt norm `‖M‖²_HS = Σ_{i,j} ⟪e_i, M e_j⟫²`. -/
def hsNormSq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ^ 2

theorem hsNormSq_nonneg (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    0 ≤ hsNormSq M := by
  unfold hsNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Parseval: `‖M‖²_HS = Σ_j ‖M e_j‖²`. -/
theorem hsNormSq_eq_sum_norm_sq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    hsNormSq M = ∑ j, ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2 := by
  unfold hsNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact basis_sum_inner_sq (M (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- `‖M x‖² ≤ ‖M‖²_HS ‖x‖²`. -/
theorem norm_apply_sq_le_hsNormSq_mul (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ‖M x‖ ^ 2 ≤ hsNormSq M * ‖x‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hx : (∑ j, ⟪b j, x⟫ • b j) = x := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr x
  have hMx : M x = ∑ j, ⟪b j, x⟫ • M (b j) := by
    calc
      M x = M (∑ j, ⟪b j, x⟫ • b j) := congrArg M hx.symm
      _ = ∑ j, ⟪b j, x⟫ • M (b j) := by
        simp only [map_sum, map_smul]
  have hnorm : ‖M x‖ ≤ ∑ j, |⟪b j, x⟫| * ‖M (b j)‖ := by
    calc
      ‖M x‖ = ‖∑ j, ⟪b j, x⟫ • M (b j)‖ := congrArg norm hMx
      _ ≤ ∑ j, ‖⟪b j, x⟫ • M (b j)‖ :=
        norm_sum_le Finset.univ _
      _ = ∑ j, |⟪b j, x⟫| * ‖M (b j)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
  have hCS :
      (∑ j, |⟪b j, x⟫| * ‖M (b j)‖) ^ 2 ≤
        ‖x‖ ^ 2 * hsNormSq M := by
    simpa only [sq_abs, b, basis_sum_inner_sq, ← hsNormSq_eq_sum_norm_sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => |⟪b j, x⟫|) (fun j => ‖M (b j)‖))
  calc
    ‖M x‖ ^ 2 ≤ (∑ j, |⟪b j, x⟫| * ‖M (b j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ‖x‖ ^ 2 * hsNormSq M := hCS
    _ = hsNormSq M * ‖x‖ ^ 2 := mul_comm _ _

/-- The operator norm is dominated by the Hilbert–Schmidt norm. -/
theorem opNorm_sq_le_hsNormSq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖M‖ ^ 2 ≤ hsNormSq M := by
  have hbound : ‖M‖ ≤ Real.sqrt (hsNormSq M) := by
    apply M.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    calc
      ‖M x‖ ^ 2 ≤ hsNormSq M * ‖x‖ ^ 2 :=
        norm_apply_sq_le_hsNormSq_mul M x
      _ = (Real.sqrt (hsNormSq M) * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hsNormSq_nonneg M)]
  calc
    ‖M‖ ^ 2 ≤ Real.sqrt (hsNormSq M) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = hsNormSq M := Real.sq_sqrt (hsNormSq_nonneg M)

/-- `‖M ∘ N‖²_HS ≤ ‖M‖² ‖N‖²_HS`. -/
theorem hsNormSq_comp_le (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    hsNormSq (M.comp N) ≤ ‖M‖ ^ 2 * hsNormSq N := by
  rw [hsNormSq_eq_sum_norm_sq, hsNormSq_eq_sum_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖M (N (EuclideanSpace.basisFun (Fin n) ℝ j))‖ ^ 2 ≤
    ‖M‖ ^ 2 * ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2
  calc
    ‖M (N (EuclideanSpace.basisFun (Fin n) ℝ j))‖ ^ 2 ≤
        (‖M‖ * ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm _) 2
    _ = ‖M‖ ^ 2 * ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2 :=
      mul_pow _ _ 2

/-- The trace of a positive operator is nonnegative. -/
theorem stdTrace_nonneg {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hM : M.IsPositive) : 0 ≤ stdTrace M := by
  unfold stdTrace
  exact Finset.sum_nonneg fun i _ => hM.inner_nonneg_right (EuclideanSpace.basisFun (Fin n) ℝ i)

/--
For a positive operator, `‖M‖²_HS ≤ (tr M)²` (Cauchy–Schwarz for the semi-inner product `⟪M·,·⟫`).
-/
theorem hsNormSq_le_stdTrace_sq {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hM : M.IsPositive) : hsNormSq M ≤ stdTrace M ^ 2 := by
  unfold hsNormSq stdTrace
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact
    positive_inner_sq_le hM (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing `Σ_j ⟪M e_j, N e_j⟫`. -/
theorem sum_inner_apply_le_sqrt_hsNormSq_mul
    (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
      Real.sqrt (hsNormSq M) * Real.sqrt (hsNormSq N) := by
  calc
    (∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫) ≤
        ∑ j,
          ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ *
            ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact real_inner_le_norm _ _
    _ ≤
        Real.sqrt (∑ j, ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2) *
          Real.sqrt (∑ j, ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun j => ‖M (EuclideanSpace.basisFun (Fin n) ℝ j)‖)
        (fun j => ‖N (EuclideanSpace.basisFun (Fin n) ℝ j)‖)
    _ = Real.sqrt (hsNormSq M) * Real.sqrt (hsNormSq N) := by
      rw [← hsNormSq_eq_sum_norm_sq, ← hsNormSq_eq_sum_norm_sq]

end FunctionalInequalities.Analysis

/-! ### Hilbert–Schmidt sum of a symmetric operator

For a symmetric continuous linear operator `A` and any finite orthonormal basis, `Σᵢⱼ ⟪A bᵢ, bⱼ⟫² =
tr (A ∘ A)`. -/

section
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

theorem sum_inner_apply_sq_eq_trace_comp_of_isSymmetric {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →L[ℝ] E)
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric) (b : OrthonormalBasis ι ℝ E) :
    (∑ i, ∑ j, ⟪A (b i), b j⟫ ^ 2) = LinearMap.trace ℝ E (A.toLinearMap * A.toLinearMap) := by
  simp_rw [b.sum_sq_inner_left]
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq (A (b i))]
  exact hA (b i) (A (b i))

end FunctionalInequalities.Analysis

end
