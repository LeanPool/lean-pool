/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixOverlap.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.BigOperators

/-! # Spectral-projector overlap algebra

The overlap convention is exactly `O j k = Tr (P k * (P j)ᴴ)`.
These results are unconditional finite-dimensional algebra; they do not assert
the Ginibre spectral pushforward or eigenvalue differentiability.

# Projector Gram matrices and overlap energy

Flatten the entries of each spectral projector into a column. The overlap matrix
is the Gram matrix of these columns, which proves positive semidefiniteness.
Its quadratic form is the Hilbert–Schmidt squared norm of the corresponding
projector combination. The real matrix gradient energy is computed from that
same combination, linking spectral derivatives to overlap weights.

The remaining identities track permutation of labels, rescaling of eigenvectors,
and rank-one projectors constructed from biorthogonal left and right eigenvectors.
For orthonormal eigenvectors the Gram matrix reduces to the identity. These are
finite matrix algebra results; simple-spectrum and analytic hypotheses enter
in the downstream modules that identify these projectors with eigenvalue derivatives.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace GinibrePoincare
noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- Columns consist of the entries of each spectral projector. -/
def matrixProjectorColumns (P : ι → Matrix n n ℂ) : Matrix (n × n) ι ℂ :=
  fun rc j => P j rc.1 rc.2

/-- The overlap Gram matrix, in the paper's index convention. -/
def matrixOverlap (P : ι → Matrix n n ℂ) : Matrix ι ι ℂ :=
  fun j k => Matrix.trace (P k * (P j)ᴴ)

omit [Fintype ι] in
theorem matrixOverlap_eq_gram (P : ι → Matrix n n ℂ) :
    matrixOverlap P = (matrixProjectorColumns P)ᴴ * matrixProjectorColumns P := by
  ext j k
  simp only [matrixOverlap, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, matrixProjectorColumns, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

/-- A Gram matrix is positive semidefinite, without finiteness of the column index. -/
private theorem gram_posSemidef {κ m : Type*} [Fintype m] (A : Matrix m κ ℂ) :
    (Aᴴ * A).PosSemidef := by
  refine ⟨isHermitian_conjTranspose_mul_self _, fun x => ?_⟩
  have key : (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * (Aᴴ * A) i j * xj) =
      ∑ k, star (∑ i ∈ x.support, A k i * x i) * (∑ j ∈ x.support, A k j * x j) := by
    simp only [Finsupp.sum, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul',
      Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key]
  exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _

omit [Fintype ι] in
/-- Hermitian positivity of the overlap matrix. -/
theorem matrixOverlap_posSemidef (P : ι → Matrix n n ℂ) :
    (matrixOverlap P).PosSemidef := by
  rw [matrixOverlap_eq_gram]
  exact gram_posSemidef _

omit [Fintype ι] in
theorem matrixOverlap_isHermitian (P : ι → Matrix n n ℂ) :
    (matrixOverlap P).IsHermitian := (matrixOverlap_posSemidef P).isHermitian

/-- Hilbert--Schmidt squared norm, represented without a choice of matrix norm. -/
def matrixHSNormSq (A : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (A * Aᴴ)).re

theorem matrixHSNormSq_eq_sum (A : Matrix n n ℂ) :
    matrixHSNormSq A = ∑ r, ∑ c, Complex.normSq (A r c) := by
  simp [matrixHSNormSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Complex.mul_conj, Complex.re_sum]

theorem matrixHSNormSq_nonneg (A : Matrix n n ℂ) : 0 ≤ matrixHSNormSq A := by
  rw [matrixHSNormSq_eq_sum]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Linear combination of spectral projectors. -/
def matrixProjectorCombination (P : ι → Matrix n n ℂ) (a : ι → ℂ) : Matrix n n ℂ :=
  ∑ j, a j • P j

/-- The overlap-weighted energy. -/
def matrixOverlapEnergy (P : ι → Matrix n n ℂ) (a : ι → ℂ) : ℝ :=
  (star a ⬝ᵥ (matrixOverlap P *ᵥ a)).re

theorem matrixOverlapEnergy_eq_HS (P : ι → Matrix n n ℂ) (a : ι → ℂ) :
    matrixOverlapEnergy P a = matrixHSNormSq (matrixProjectorCombination P a) := by
  unfold matrixOverlapEnergy
  rw [matrixOverlap_eq_gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  rw [matrixHSNormSq_eq_sum]
  simp only [dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Matrix.mulVec, dotProduct, matrixProjectorColumns, matrixProjectorCombination,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem matrixOverlapEnergy_nonneg (P : ι → Matrix n n ℂ) (a : ι → ℂ) :
    0 ≤ matrixOverlapEnergy P a := by
  rw [matrixOverlapEnergy_eq_HS]
  exact matrixHSNormSq_nonneg _

omit [Fintype n] in
/-- Reindexing the coefficients and projectors simultaneously changes nothing. -/
theorem matrixProjectorCombination_relabel (P : ι → Matrix n n ℂ) (a : ι → ℂ)
    (e : Equiv.Perm ι) :
    matrixProjectorCombination (P ∘ e) (a ∘ e) = matrixProjectorCombination P a := by
  exact Fintype.sum_equiv e _ (fun j => a j • P j) (fun _ => rfl)

theorem matrixOverlapEnergy_relabel (P : ι → Matrix n n ℂ) (a : ι → ℂ)
    (e : Equiv.Perm ι) :
    matrixOverlapEnergy (P ∘ e) (a ∘ e) = matrixOverlapEnergy P a := by
  rw [matrixOverlapEnergy_eq_HS, matrixOverlapEnergy_eq_HS,
    matrixProjectorCombination_relabel]

theorem matrixHSNormSq_conjTranspose (A : Matrix n n ℂ) :
    matrixHSNormSq Aᴴ = matrixHSNormSq A := by
  simp only [matrixHSNormSq, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_comm]

theorem matrixHSNormSq_two_smul (A : Matrix n n ℂ) :
    matrixHSNormSq ((2 : ℂ) • A) = 4 * matrixHSNormSq A := by
  rw [matrixHSNormSq_eq_sum, matrixHSNormSq_eq_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  norm_num

/-- The matrix representing the real Hilbert--Schmidt differential of a spectral observable. -/
def matrixLiftGradient (P : ι → Matrix n n ℂ) (a : ι → ℂ) : Matrix n n ℂ :=
  (2 : ℂ) • (matrixProjectorCombination P a)ᴴ

/-- Exact factor four in the paper's matrix-lift gradient identity. -/
theorem matrixLiftGradient_energy (P : ι → Matrix n n ℂ) (a : ι → ℂ) :
    matrixHSNormSq (matrixLiftGradient P a) = 4 * matrixOverlapEnergy P a := by
  rw [matrixLiftGradient, matrixHSNormSq_two_smul, matrixHSNormSq_conjTranspose,
    matrixOverlapEnergy_eq_HS]

/-- The real Hilbert--Schmidt pairing recovers the spectral differential formula. -/
theorem matrixLiftGradient_pairing (P : ι → Matrix n n ℂ) (a : ι → ℂ)
    (H : Matrix n n ℂ) :
    (Matrix.trace ((matrixLiftGradient P a)ᴴ * H)).re =
      2 * (∑ j, a j * Matrix.trace (P j * H)).re := by
  simp [matrixLiftGradient, Matrix.conjTranspose_smul, matrixProjectorCombination,
    Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]

/-- The rank-one spectral projector `r ℓ*`. -/
def matrixRankOneProjector (r l : n → ℂ) : Matrix n n ℂ :=
  fun i j => r i * star (l j)

omit [Fintype n] in
/-- The normalization change `r ↦ c r`, `ℓ ↦ conjugate(c⁻¹) ℓ`
leaves the spectral projector unchanged. -/
theorem matrixRankOneProjector_rescale (r l : n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    matrixRankOneProjector (c • r) (star (c⁻¹) • l) = matrixRankOneProjector r l := by
  ext i j
  simp only [matrixRankOneProjector, Pi.smul_apply, smul_eq_mul, star_mul, star_star]
  field_simp

omit [Fintype ι] in
theorem matrixOverlap_rescale (r l : ι → n → ℂ) (c : ι → ℂ)
    (hc : ∀ j, c j ≠ 0) :
    matrixOverlap (fun j => matrixRankOneProjector (c j • r j) (star ((c j)⁻¹) • l j)) =
      matrixOverlap (fun j => matrixRankOneProjector (r j) (l j)) := by
  congr 1
  funext j
  exact matrixRankOneProjector_rescale _ _ _ (hc j)

theorem matrixRankOneProjector_mul (r l r' l' : n → ℂ) :
    matrixRankOneProjector r l * matrixRankOneProjector r' l' =
      (star l ⬝ᵥ r') • matrixRankOneProjector r l' := by
  ext i j
  simp only [Matrix.mul_apply, matrixRankOneProjector, Matrix.smul_apply,
    smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype ι] in
/-- Biorthogonal right and left eigenvectors produce mutually orthogonal
idempotent spectral projectors. -/
theorem matrixRankOneProjector_biorthogonal [DecidableEq ι]
    (r l : ι → n → ℂ)
    (h : ∀ j k, star (l j) ⬝ᵥ r k = if j = k then 1 else 0) (j k : ι) :
    matrixRankOneProjector (r j) (l j) * matrixRankOneProjector (r k) (l k) =
      if j = k then matrixRankOneProjector (r j) (l j) else 0 := by
  rw [matrixRankOneProjector_mul, h]
  split_ifs with hjk
  · subst k; simp
  · simp

theorem matrixRankOneProjector_trace (r l : n → ℂ) :
    Matrix.trace (matrixRankOneProjector r l) = star l ⬝ᵥ r := by
  simp [Matrix.trace, Matrix.diag, matrixRankOneProjector, dotProduct, mul_comm]

/-- The spectral perturbation linear functional has the trace form used
in the paper. This is an algebraic identity for every matrix direction. -/
theorem matrixRankOneProjector_trace_mul (r l : n → ℂ) (H : Matrix n n ℂ) :
    Matrix.trace (matrixRankOneProjector r l * H) = star l ⬝ᵥ (H *ᵥ r) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixRankOneProjector,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype n] in
theorem matrixRankOneProjector_conjTranspose (r l : n → ℂ) :
    (matrixRankOneProjector r l)ᴴ = matrixRankOneProjector l r := by
  ext i j
  simp [Matrix.conjTranspose_apply, matrixRankOneProjector, mul_comm]

omit [Fintype ι] in
theorem matrixOverlap_rankOne_entry (r l : ι → n → ℂ) (j k : ι) :
    matrixOverlap (fun i => matrixRankOneProjector (r i) (l i)) j k =
      (star (l k) ⬝ᵥ l j) * (star (r j) ⬝ᵥ r k) := by
  simp only [matrixOverlap, matrixRankOneProjector_conjTranspose,
    matrixRankOneProjector_mul, Matrix.trace_smul, smul_eq_mul,
    matrixRankOneProjector_trace]

omit [Fintype ι] in
/-- For orthonormal eigenvectors of a normal matrix the overlap matrix is
the identity, explaining the absence of overlap weights in that case. -/
theorem matrixOverlap_orthonormal [DecidableEq ι] (r : ι → n → ℂ)
    (h : ∀ j k, star (r j) ⬝ᵥ r k = if j = k then 1 else 0) :
    matrixOverlap (fun j => matrixRankOneProjector (r j) (r j)) = 1 := by
  ext j k
  rw [matrixOverlap_rankOne_entry, h, h]
  simp only [Matrix.one_apply]
  split_ifs <;> simp_all

theorem matrixOverlapEnergy_orthonormal [DecidableEq ι] (r : ι → n → ℂ)
    (h : ∀ j k, star (r j) ⬝ᵥ r k = if j = k then 1 else 0) (a : ι → ℂ) :
    matrixOverlapEnergy (fun j => matrixRankOneProjector (r j) (r j)) a =
      ∑ j, Complex.normSq (a j) := by
  simp only [matrixOverlapEnergy, matrixOverlap_orthonormal r h, Matrix.one_mulVec,
    dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.re_sum, Complex.ofReal_re]

/-! Public matrix algebra is audited here; no analytic hypothesis is used. -/

end
end GinibrePoincare
