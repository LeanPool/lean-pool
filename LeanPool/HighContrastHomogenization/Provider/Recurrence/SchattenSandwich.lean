/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.DetOrder
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSpectral

/-!
# High-contrast homogenization: Provider.Recurrence.SchattenSandwich

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Schatten size and the scalar Loewner sandwich

The fixed-grid section measures a symmetric doubled block by the Schatten size
`|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}`.  Squaring folds the sign away — for every
real `x` one has `(x²)^{Q/2} = |x|^Q` — so the Schatten trace of a symmetric
matrix is `Σ|λ_i|^Q`, its absolute eigenvalues raised to the `Q`-th power and
summed.  That identity is proved first, with no positivity hypothesis, and
everything else in this file reads off it.

What the identity gives is a two-sided comparison between the Schatten size and
the scalar Loewner sandwich `-tI ≤ H ≤ tI`.  In one direction a single term of a
sum of nonnegative terms is at most the whole, so `|λ_i| ≤ |H|_{S_Q}` for every
`i` and `H` is caught between `∓|H|_{S_Q}I`.  In the other, `2d` terms each at
most `t^Q` sum to at most `2d·t^Q`, so a block caught between `∓tI` has Schatten
size at most `(2d)^{1/Q}t`.  The dimensional factor is the whole gap between the
two directions, and the fixed-grid constants absorb it.

The passage between an eigenvalue bound and a Loewner bound runs both ways
through the spectral theorem: the quadratic form of `tI ∓ H` at the `i`-th unit
eigenvector is `t ∓ λ_i`, and conversely `tI ∓ H` is the conjugate of the
diagonal matrix `t ∓ diag(λ)` by the eigenvector unitary.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix

noncomputable section

/-! ## The Schatten trace of a symmetric matrix -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Schatten trace is the sum of the `Q`-th powers of the absolute
eigenvalues.**  Squaring folds the sign away: `(x²)^{Q/2} = |x|^Q` for every
real `x`, so no positivity hypothesis is needed on the matrix. -/
theorem trace_cfc_rpow_mul_self_eq_sum_abs {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : ℝ}
    (hQ : 0 < Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ (Q / 2)) (A * A)) = ∑ i, |hA.eigenvalues i| ^ Q := by
  have hsa : IsSelfAdjoint A := hA
  have hsq : cfc (fun x : ℝ => x ^ (2 : ℕ)) A = A * A := by
    have h1 := cfc_pow (R := ℝ) (fun x : ℝ => x) 2 A
    rw [cfc_id' ℝ A hsa] at h1
    rw [h1, pow_two]
  have hcont : ContinuousOn (fun x : ℝ => x ^ (Q / 2))
      ((fun x : ℝ => x ^ (2 : ℕ)) '' spectrum ℝ A) := fun x _ =>
    (Real.continuousAt_rpow_const x (Q / 2) (Or.inr (by linarith only [hQ]))).continuousWithinAt
  have hcomp : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => x ^ (Q / 2)) (A * A) := by
    rw [cfc_comp (R := ℝ) (fun x : ℝ => x ^ (Q / 2)) (fun x : ℝ => x ^ (2 : ℕ)) A hsa hcont, hsq]
  have hcongr : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => |x| ^ Q) A := by
    refine cfc_congr (R := ℝ) fun x _ => ?_
    have hnat : (x ^ (2 : ℕ) : ℝ) = |x| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    simp only [Function.comp_apply, hnat]
    rw [← Real.rpow_mul (abs_nonneg x), show (2 : ℝ) * (Q / 2) = Q by ring]
  rw [← hcomp, hcongr, trace_cfc_eq_sum_eigenvalues hA]

/-! ## Eigenvalues and the scalar Loewner sandwich -/

/-- **A two-sided scalar bound bounds every eigenvalue in absolute value.**  The
quadratic forms of `t I - A` and `t I + A` at the `i`-th unit eigenvector are
`t - λ_i` and `t + λ_i`. -/
theorem abs_eigenvalues_le_of_posSemidef {A : Matrix n n ℝ} (hA : A.IsHermitian) {t : ℝ}
    (hsub : (t • (1 : Matrix n n ℝ) - A).PosSemidef)
    (hadd : (t • (1 : Matrix n n ℝ) + A).PosSemidef) (i : n) :
    |hA.eigenvalues i| ≤ t := by
  have h1 := hsub.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : n → ℝ)
  have h2 := hadd.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : n → ℝ)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul,
    HCPolySupport.HighContrast.dotProduct_eigenvectorBasis_self hA i] at h1
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul,
    HCPolySupport.HighContrast.dotProduct_eigenvectorBasis_self hA i] at h2
  have hval : hA.eigenvalues i
      = star (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) := by
    simpa using hA.eigenvalues_eq i
  simp only [smul_eq_mul, mul_one] at h1 h2
  rw [hval, abs_le]
  exact ⟨by linarith only [h2], by linarith only [h1]⟩

/-- **A bound on the absolute eigenvalues is a two-sided scalar bound.**  This is
the spectral theorem read as a congruence: the diagonal matrices
`t I ∓ diag(eigenvalues)` have nonnegative entries. -/
theorem posSemidef_smul_one_sub_add_of_abs_eigenvalues_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {t : ℝ} (h : ∀ i, |hA.eigenvalues i| ≤ t) :
    (t • (1 : Matrix n n ℝ) - A).PosSemidef ∧ (t • (1 : Matrix n n ℝ) + A).PosSemidef := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal hA.eigenvalues * (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hconj : ∀ g : n → ℝ, (∀ i, 0 ≤ g i) →
      ((hA.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal g *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ).PosSemidef := by
    intro g hg
    have hc := (Matrix.PosSemidef.diagonal hg).conjTranspose_mul_mul_same
      ((hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ)
    rwa [Matrix.conjTranspose_conjTranspose] at hc
  constructor
  · have hd : Matrix.diagonal (fun i => t - hA.eigenvalues i)
        = t • (1 : Matrix n n ℝ) - Matrix.diagonal hA.eigenvalues := by
      ext j k
      by_cases hjk : j = k <;> simp [Matrix.diagonal, hjk]
    have hrw : t • (1 : Matrix n n ℝ) - A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => t - hA.eigenvalues i) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, ← hspec]
      congr 1
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
    rw [hrw]
    exact hconj _ fun i => by have := (abs_le.mp (h i)).2; linarith only [this]
  · have hd : Matrix.diagonal (fun i => t + hA.eigenvalues i)
        = t • (1 : Matrix n n ℝ) + Matrix.diagonal hA.eigenvalues := by
      ext j k
      by_cases hjk : j = k <;> simp [Matrix.diagonal, hjk]
    have hrw : t • (1 : Matrix n n ℝ) + A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal (fun i => t + hA.eigenvalues i) *
        (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
      rw [hd, Matrix.mul_add, Matrix.add_mul, ← hspec]
      congr 1
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
    rw [hrw]
    exact hconj _ fun i => by have := (abs_le.mp (h i)).1; linarith only [this]

end Spectral

/-! ## The Schatten size of a doubled block -/

section Block

variable {d : ℕ}

/-- The Schatten trace of a symmetric doubled block is the sum of the `Q`-th
powers of the absolute eigenvalues of its flattening. -/
theorem schattenNorm_rpow_eq_sum_abs {H : BlockMat d} (hH : IsSymmetricBlockMat H) {Q : ℝ}
    (hQ : 0 < Q) :
    schattenNorm Q H ^ Q = ∑ i, |(isHermitian_toFullBlockMat hH).eigenvalues i| ^ Q := by
  rw [schattenNorm_rpow hH hQ,
    trace_cfc_rpow_mul_self_eq_sum_abs (isHermitian_toFullBlockMat hH) hQ]

/-- **The Schatten size dominates every eigenvalue in absolute value**: one term
of a sum of nonnegative terms is at most the whole. -/
theorem abs_eigenvalues_le_schattenNorm {H : BlockMat d} (hH : IsSymmetricBlockMat H) {Q : ℝ}
    (hQ : 0 < Q) (i : BlockCoord d) :
    |(isHermitian_toFullBlockMat hH).eigenvalues i| ≤ schattenNorm Q H := by
  have hterm : |(isHermitian_toFullBlockMat hH).eigenvalues i| ^ Q ≤ schattenNorm Q H ^ Q := by
    rw [schattenNorm_rpow_eq_sum_abs hH hQ]
    exact Finset.single_le_sum
      (f := fun j => |(isHermitian_toFullBlockMat hH).eigenvalues j| ^ Q)
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) Q) (Finset.mem_univ i)
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (zero_le_schattenNorm hH Q) hQ).mp hterm

/-- **A symmetric block is caught between `∓|H|_{S_Q}I`** in the Loewner
order. -/
theorem posSemidef_schattenNorm_smul_one_sub_add {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    {Q : ℝ} (hQ : 0 < Q) :
    (schattenNorm Q H • (1 : FullBlockMat d) - toFullBlockMat H).PosSemidef ∧
      (schattenNorm Q H • (1 : FullBlockMat d) + toFullBlockMat H).PosSemidef :=
  posSemidef_smul_one_sub_add_of_abs_eigenvalues_le (isHermitian_toFullBlockMat hH)
    fun i => abs_eigenvalues_le_schattenNorm hH hQ i

/-- **A symmetric block caught between `∓tI` has Schatten size at most
`(2d)^{1/Q}t`**: each of the `2d` absolute eigenvalues is at most `t`. -/
theorem schattenNorm_le_of_posSemidef {H : BlockMat d} (hH : IsSymmetricBlockMat H) {t Q : ℝ}
    (hQ : 0 < Q) (ht : 0 ≤ t)
    (hsub : (t • (1 : FullBlockMat d) - toFullBlockMat H).PosSemidef)
    (hadd : (t • (1 : FullBlockMat d) + toFullBlockMat H).PosSemidef) :
    schattenNorm Q H ≤ (2 * d : ℝ) ^ Q⁻¹ * t := by
  have hbound : schattenNorm Q H ^ Q ≤ (2 * d : ℝ) * t ^ Q := by
    rw [schattenNorm_rpow_eq_sum_abs hH hQ]
    calc ∑ i, |(isHermitian_toFullBlockMat hH).eigenvalues i| ^ Q
        ≤ ∑ _i : BlockCoord d, t ^ Q :=
          Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _)
            (abs_eigenvalues_le_of_posSemidef (isHermitian_toFullBlockMat hH) hsub hadd i) hQ.le
      _ = (Fintype.card (BlockCoord d) : ℝ) * t ^ Q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (2 * d : ℝ) * t ^ Q := by
          rw [Fintype.card_sum, Fintype.card_fin]
          push_cast
          ring
  refine (Real.rpow_le_rpow_iff (zero_le_schattenNorm hH Q) (by positivity) hQ).mp ?_
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) ht,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * d), inv_mul_cancel₀ (ne_of_gt hQ),
    Real.rpow_one]
  exact hbound

end Block

end

end Recurrence
end HighContrast
end HCPolySupport
