/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Positive semidefinite Gram matrices with a Kronecker weight

`F (A ⊗ A) Fᵀ` is positive semidefinite for positive semidefinite `A`; written out, this is the
four-index Gram matrix used for the third-derivative term of Letwin's Lemma 2.4.

Quadratic floors and the Sylvester estimate: `matrixEntries A` is the Euclidean (Frobenius) view of
the
entries; `QuadraticFloor S a` is `a‖v‖² ≤ ⟪v, S v⟫`; a positive definite matrix has a positive
floor, a floor
is stable under Frobenius-small perturbations, and for floors `a`, `b` and symmetric `T` the
identity
`S(S−T) + (S−T)T = S² − T²` (no commutation) gives `‖S − T‖_F ≤ ‖S² − T²‖_F / (a + b)`. Used for the
local
Lipschitz property of the principal inverse square root (`Analysis/Operator/InverseSqrt.lean`).

Inverse-quadratic Young inequality (`inverse_quadratic_young`): for a positive definite real matrix
`H` over any finite
index type (the empty one included), `2 (v ⬝ᵥ w) ≤ v ⬝ᵥ H⁻¹ v + w ⬝ᵥ H w`, from the nonnegative
quadratic form of
`w − H⁻¹ v`; no commutation or identity restriction. Support for Letwin, arXiv:2607.24164v1, Lemma
A.6.

Trace pairings of positive semidefinite matrices (`sum_entry_mul_nonneg`, `trace_mul_nonneg`): for
real positive
semidefinite `A`, `C` over any finite index type (the empty one included), `Σ_ij A_ij C_ij ≥ 0`
(through the Kronecker
product) and `tr(AC) ≥ 0`; the product itself is not claimed positive semidefinite. Trace-weighted
Gram matrices
(`traceGram_posSemidef`): for positive semidefinite `B` and symmetric `T a`, the matrix `(tr(B T_a B
T_b))_{ab}` is positive
semidefinite. Supports for Letwin, arXiv:2607.24164v1, (2.10).

Determinant floor (`posSemidef_sub_scalar_of_det_lower`): in positive dimension `n`, a positive
semidefinite `A` with
`A ≤ K·Id` and `δ ≤ det A` (`K, δ > 0`) satisfies `A ≥ (δ / K^(n-1))·Id`, since every eigenvalue
lies in `[0, K]` and their
product is at least `δ`. Finite matrix step for compact-local ellipticity of the regular-class
moment potential.
Reciprocal bounds (`inverse_posSemidef_bounds`): `α·Id ≤ A ≤ β·Id` for positive definite `A` gives
`β⁻¹·Id ≤ A⁻¹ ≤ α⁻¹·Id`.
Quadratic Young (`posSemidef_quadratic_young`): `2 xᵀAy ≤ ε xᵀAx + ε⁻¹ yᵀAy` for positive
semidefinite `A`, `ε > 0`.
-/

@[expose] public section

noncomputable section
open scoped MatrixOrder Kronecker

namespace FunctionalInequalities.Analysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/--
**Weighted Gram matrix**: for a positive semidefinite `A` and any family of matrices `T_i`, the
matrix
`G_{ij} = Σ_{a,b,c,d} A_{ac} A_{bd} (T_i)_{ab} (T_j)_{cd} = (F (A ⊗ A) Fᵀ)_{ij}` is positive
semidefinite. -/
theorem posSemidef_weightedGram [Finite κ] (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (T : κ → Matrix ι ι ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d, A a c * A b d * T i a b * T j c d).PosSemidef := by
  let F : Matrix κ (ι × ι) ℝ := fun i ab => T i ab.1 ab.2
  have h := (hA.kronecker hA).mul_mul_conjTranspose_same F
  have heq :
    F * (A ⊗ₖ A) * F.conjTranspose =
      Matrix.of (fun i j => ∑ a, ∑ b, ∑ c, ∑ d, A a c * A b d * T i a b * T j c d) := by
    rw [Matrix.mul_assoc]
    ext i j
    change
      (∑ ab : ι × ι,
          T i ab.1 ab.2 * (∑ cd : ι × ι, (A ab.1 cd.1 * A ab.2 cd.2) * T j cd.1 cd.2)) =
        _
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  exact heq ▸ h

section Frobenius

open Matrix Finset
open scoped RealInnerProductSpace

/-- Euclidean view of the matrix entries; its norm is the Frobenius norm. -/
def matrixEntries (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem matrixEntries_norm_sq (A : Matrix ι ι ℝ) :
    ‖matrixEntries A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_prod_type _

theorem matrixEntries_inner (A B : Matrix ι ι ℝ) :
    ⟪matrixEntries A, matrixEntries B⟫ = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [matrixEntries, PiLp.toLp_apply, Real.inner_apply]
  exact Fintype.sum_prod_type _

section MatrixEntries

omit [Fintype ι]
theorem matrixEntries_sub (A B : Matrix ι ι ℝ) :
    matrixEntries (A - B) = matrixEntries A - matrixEntries B := by
  ext ij
  rfl

theorem continuous_matrixEntries :
    Continuous (matrixEntries : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (PiLp.continuous_toLp 2 (fun _ : ι × ι => ℝ)).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end MatrixEntries

end Frobenius

section Floor

open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

/-- A quadratic lower floor `a ‖v‖² ≤ ⟪v, A v⟫` in coordinates. -/
def QuadraticFloor (A : Matrix ι ι ℝ) (a : ℝ) : Prop :=
  ∀ v : ι → ℝ, a * (∑ i, (v i) ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)

variable [DecidableEq ι]

/-- A Loewner scalar lower bound gives a quadratic floor. -/
theorem quadraticFloor_of_algebraMap_le {S : Matrix ι ι ℝ} {a : ℝ}
    (h : algebraMap ℝ (Matrix ι ι ℝ) a ≤ S) : QuadraticFloor S a := by
  have hp : (S - algebraMap ℝ (Matrix ι ι ℝ) a).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  intro v
  have hv := hp.dotProduct_mulVec_nonneg v
  rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, dotProduct_sub,
    smul_mulVec, one_mulVec, dotProduct_smul] at hv
  simp only [star_trivial, smul_eq_mul] at hv
  have he : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by simp only [dotProduct, pow_two]
  rw [he] at hv
  linarith

omit [DecidableEq ι] in
/-- A positive definite matrix has a positive quadratic floor (the empty index type gives floor `1`
without any spectrum argument). -/
theorem exists_quadraticFloor_of_posDef {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ a : ℝ, 0 < a ∧ QuadraticFloor S a := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    obtain ⟨a, ha, hle⟩ :=
      (CFC.exists_pos_algebraMap_le_iff S hS.isStrictlyPositive.isSelfAdjoint).mpr
        (fun x hx => hS.isStrictlyPositive.spectrum_pos hx)
    exact ⟨a, ha, quadraticFloor_of_algebraMap_le hle⟩
  · have : IsEmpty ι := not_nonempty_iff.mp h
    refine ⟨1, by norm_num, ?_⟩
    intro v
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, le_refl]

private def outer (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j

section RankOneBounds

omit [DecidableEq ι]
private theorem outer_norm (v : ι → ℝ) : ‖matrixEntries (outer v)‖ = ∑ i, (v i) ^ 2 := by
  have he : ‖matrixEntries (outer v)‖ ^ 2 = (∑ i, (v i) ^ 2) ^ 2 := by
    rw [matrixEntries_norm_sq]
    simp only [outer, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  nlinarith [norm_nonneg (matrixEntries (outer v))]

private theorem outer_inner (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    ⟪matrixEntries D, matrixEntries (outer v)⟫ = v ⬝ᵥ (D *ᵥ v) := by
  rw [matrixEntries_inner]
  simp only [outer, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The quadratic form is controlled by the Frobenius norm. -/
theorem abs_dotProduct_mulVec_le (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (D *ᵥ v)| ≤ ‖matrixEntries D‖ * (∑ i, (v i) ^ 2) := by
  rw [← outer_inner, ← outer_norm]
  simpa only [Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (matrixEntries D) (matrixEntries (outer v))

/-- A floor persists, halved, under a Frobenius perturbation of size at most `a / 2`. -/
theorem quadraticFloor_of_close {S S0 : Matrix ι ι ℝ} {a : ℝ} (hfloor : QuadraticFloor S0 a)
    (hclose : ‖matrixEntries (S - S0)‖ ≤ a / 2) : QuadraticFloor S (a / 2) := by
  intro v
  have hbase := hfloor v
  have hdiff := abs_dotProduct_mulVec_le (S - S0) v
  have hq : v ⬝ᵥ ((S - S0) *ᵥ v) = v ⬝ᵥ (S *ᵥ v) - v ⬝ᵥ (S0 *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub]
  rw [hq] at hdiff
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hclose hp
  have hneg := neg_abs_le (v ⬝ᵥ S *ᵥ v - v ⬝ᵥ S0 *ᵥ v)
  nlinarith [hdiff, hmul, hneg]

end RankOneBounds

end Floor

section Sylvester

open Matrix Finset
open scoped RealInnerProductSpace

variable [DecidableEq ι]

section SylvesterCoercivity

omit [DecidableEq ι]
private theorem left_floor (S D : Matrix ι ι ℝ) {a : ℝ} (hS : QuadraticFloor S a) :
    a * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (S * D) i j := by
  calc
    a * (∑ i, ∑ j, (D i j) ^ 2) = ∑ j, a * (∑ i, (D i j) ^ 2) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j, ∑ i, D i j * (S * D) i j := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [QuadraticFloor, dotProduct, mulVec, Matrix.mul_apply] using hS (fun i => D i j)
    _ = ∑ i, ∑ j, D i j * (S * D) i j := Finset.sum_comm

private theorem right_floor (T D : Matrix ι ι ℝ) {b : ℝ} (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    b * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (D * T) i j := by
  have he (i j : ι) : (D * T) i j = (T *ᵥ (fun k => D i k)) j := by
    simp only [Matrix.mul_apply, mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hSym k j]
    ring
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  simp_rw [he]
  exact hT (fun j => D i j)

/--
**Sylvester coercivity**: `(a + b)‖D‖_F² ≤ ⟪D, SD + DT⟫_F` for floors `a`, `b` and symmetric `T`; no
commutation assumption. -/
theorem sylvester_coercivity (S T D : Matrix ι ι ℝ) {a b : ℝ} (hS : QuadraticFloor S a)
    (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries D‖ ^ 2 ≤ ⟪matrixEntries D, matrixEntries (S * D + D * T)⟫ := by
  rw [matrixEntries_norm_sq, matrixEntries_inner]
  have hl := left_floor S D hS
  have hr := right_floor T D hT hSym
  calc
    (a + b) * (∑ i, ∑ j, (D i j) ^ 2) =
        a * (∑ i, ∑ j, (D i j) ^ 2) + b * (∑ i, ∑ j, (D i j) ^ 2) := by
      ring
    _ ≤ (∑ i, ∑ j, D i j * (S * D) i j) + (∑ i, ∑ j, D i j * (D * T) i j) := add_le_add hl hr
    _ = ∑ i, ∑ j, D i j * (S * D + D * T) i j := by
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

end SylvesterCoercivity

omit [DecidableEq ι] in
/-- **Root difference bound**: `(a + b)‖S − T‖_F ≤ ‖S² − T²‖_F` from the identity
`S(S − T) + (S − T)T = S² − T²`, which holds without commutation. -/
theorem root_difference_bound (S T : Matrix ι ι ℝ) {a b : ℝ}
    (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ := by
  classical
  have hid : S * (S - T) + (S - T) * T = S * S - T * T := by noncomm_ring
  have hlo := sylvester_coercivity S T (S - T) hS hT hSym
  rw [hid] at hlo
  have hupper : ⟪matrixEntries (S - T), matrixEntries (S * S - T * T)⟫ ≤
      ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
    have hc : |⟪matrixEntries (S - T), matrixEntries (S * S - T * T)⟫| ≤
        ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
        (matrixEntries (S - T)) (matrixEntries (S * S - T * T))
    exact (le_abs_self _).trans hc
  by_cases hz : ‖matrixEntries (S - T)‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg _
  have hd : 0 < ‖matrixEntries (S - T)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have h := hlo.trans hupper
  have h' : ‖matrixEntries (S - T)‖ * ((a + b) * ‖matrixEntries (S - T)‖) ≤
      ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
    nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hd).mp h'

omit [DecidableEq ι] in
theorem root_difference_le_div (S T : Matrix ι ι ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hS : QuadraticFloor S a) (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ / (a + b) := by
  classical
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  simpa only [mul_comm] using root_difference_bound S T hS hT hSym

end Sylvester

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section InverseYoung

open scoped BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The inverse-quadratic Young inequality for a finite real positive-definite matrix. -/
theorem inverse_quadratic_young
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) ≤ v ⬝ᵥ (H⁻¹ *ᵥ v) + w ⬝ᵥ (H *ᵥ w) := by
  classical
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hmul : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hcancel : H *ᵥ (H⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hmul]
    simp
  have hsymm : H.IsSymm := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have htranspose : Hᵀ = H := hsymm
  have hcross₁ : w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) = v ⬝ᵥ w := by
    rw [hcancel]
    exact dotProduct_comm _ _
  have hcross₂ : (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ w := by
    calc
      (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) =
          (H⁻¹ *ᵥ v) ⬝ᵥ (Hᵀ *ᵥ w) := by rw [htranspose]
      _ = w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) :=
        Matrix.dotProduct_transpose_mulVec H (H⁻¹ *ᵥ v) w
      _ = v ⬝ᵥ w := hcross₁
  have hlast : (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v)) =
      v ⬝ᵥ (H⁻¹ *ᵥ v) := by
    rw [hcancel]
    exact dotProduct_comm _ _
  have hquad :
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) =
        w ⬝ᵥ (H *ᵥ w) - 2 * (v ⬝ᵥ w) + v ⬝ᵥ (H⁻¹ *ᵥ v) := by
    calc
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) =
          (w ⬝ᵥ (H *ᵥ w) - w ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v))) -
            ((H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ w) -
              (H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (H⁻¹ *ᵥ v))) := by
        simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
        ring
      _ = w ⬝ᵥ (H *ᵥ w) - 2 * (v ⬝ᵥ w) + v ⬝ᵥ (H⁻¹ *ᵥ v) := by
        rw [hcross₁, hcross₂, hlast]
        ring
  have hnonneg : 0 ≤
      (w - H⁻¹ *ᵥ v) ⬝ᵥ (H *ᵥ (w - H⁻¹ *ᵥ v)) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg (w - H⁻¹ *ᵥ v)
  nlinarith [hquad, hnonneg]

end InverseYoung

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section TraceGram

open scoped BigOperators Kronecker
open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Frobenius pairing of two real PSD matrices, proved using their Kronecker product.
No nonempty-index assumption is needed. -/
theorem sum_entry_mul_nonneg {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * C i j := by
  classical
  have h := (hA.kronecker hC).dotProduct_mulVec_nonneg
    (fun p : ι × ι => if p.1 = p.2 then (1 : ℝ) else 0)
  change 0 ≤ ∑ p : ι × ι,
    (if p.1 = p.2 then (1 : ℝ) else 0) *
      (∑ q : ι × ι, (A p.1 q.1 * C p.2 q.2) *
        (if q.1 = q.2 then (1 : ℝ) else 0)) at h
  simpa [Fintype.sum_prod_type, mul_ite, ite_mul] using h

/-- The trace of a product of real PSD matrices is nonnegative; the product itself
is not asserted to be PSD. -/
theorem trace_mul_nonneg {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ (A * C).trace := by
  classical
  have hs (i j : ι) : C j i = C i j := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hC.isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  calc
    0 ≤ ∑ i, ∑ j, A i j * C i j := sum_entry_mul_nonneg hA hC
    _ = (A * C).trace := by
      change (∑ i, ∑ j, A i j * C i j) =
        ∑ i, ∑ j, A i j * C j i
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs i j]

/-- The matrix indexed by derivative directions with entries `tr(B Tᵤ B Tᵥ)`
is a genuine PSD weighted Gram matrix. -/
theorem traceGram_posSemidef {ι κ : Type*} [Fintype ι] [Finite κ]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ a, (T a).IsSymm) :
    (Matrix.of fun a b => (B * T a * B * T b).trace).PosSemidef := by
  classical
  have hb (i j : ι) : B i j = B j i := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M j i) hB.isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have ht (a : κ) (i j : ι) : T a j i = T a i j :=
    congrFun (congrFun (hT a) i) j
  have he (u v : κ) :
      (B * T u * B * T v).trace =
        ∑ p, ∑ q, ∑ r, ∑ s,
          B p r * B q s * T u p q * T v r s := by
    calc
      _ = ∑ r, ∑ s, ∑ q, ∑ p,
          B r p * T u p q * B q s * T v s r := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Finset.sum_mul]
      _ = ∑ r, ∑ p, ∑ q, ∑ s,
          B r p * T u p q * B q s * T v s r := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          (∑ s, ∑ q, ∑ p,
              B r p * T u p q * B q s * T v s r) =
              ∑ s, ∑ p, ∑ q,
                B r p * T u p q * B q s * T v s r := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_comm]
          _ = ∑ p, ∑ s, ∑ q,
              B r p * T u p q * B q s * T v s r := by
            rw [Finset.sum_comm]
          _ = ∑ p, ∑ q, ∑ s,
              B r p * T u p q * B q s * T v s r := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_comm]
      _ = ∑ p, ∑ q, ∑ r, ∑ s,
          B r p * T u p q * B q s * T v s r := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        rw [hb r p, ht v r s]
        ring
  have hmat :
      (Matrix.of fun u v => (B * T u * B * T v).trace) =
        (Matrix.of fun u v => ∑ p, ∑ q, ∑ r, ∑ s,
          B p r * B q s * T u p q * T v r s) := by
    ext u v
    exact he u v
  rw [hmat]
  exact posSemidef_weightedGram B hB T

end TraceGram

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section TraceForcingDensity

open Matrix

/-- For positive semidefinite `B`, `H`, `R`, `W` and symmetric `Tᵢ`, the pointwise trace density
`2 tr(B H B (-H + H W H + G_R)) + 2 ∑ R_{ij} tr(B Tᵢ B Tⱼ) + 2 tr(B H B H)` is nonnegative,
where `G_R` is the trace Gram matrix `tr(R Tᵢ R Tⱼ)`. -/
theorem trace_forcing_add_twice_energy_nonneg {n : ℕ}
    (B H R W : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (hH : H.PosSemidef) (hR : R.PosSemidef) (hW : W.PosSemidef)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i : Fin n, (T i).IsSymm) :
    0 ≤ (2 * (B * H * B * (-H + H * W * H +
        (Matrix.of fun i j => (R * T i * R * T j).trace))).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace) +
      2 * (B * H * B * H).trace := by
  classical
  have hC : (B * H * B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hH.mul_mul_conjTranspose_same B
  have hM : (H * W * H).PosSemidef := by
    simpa only [hH.isHermitian.eq] using hW.mul_mul_conjTranspose_same H
  have hG := traceGram_posSemidef R hR T hT
  have h1 := trace_mul_nonneg hC hM
  have h2 := trace_mul_nonneg hC hG
  have h3 := sum_entry_mul_nonneg hR (traceGram_posSemidef B hB T hT)
  have he :
      (B * H * B * (-H + H * W * H +
        (Matrix.of fun i j => (R * T i * R * T j).trace))).trace =
      -(B * H * B * H).trace + (B * H * B * (H * W * H)).trace +
        (B * H * B * (Matrix.of fun i j => (R * T i * R * T j).trace)).trace := by
    simp only [mul_add, mul_neg, Matrix.trace_add, Matrix.trace_neg]
  rw [he]
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R i j * (B * T i * B * T j).trace at h3
  linarith

end TraceForcingDensity

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section DeterminantFloor

open Matrix

/-- A determinant lower bound and a common scalar upper bound give an explicit
positive lower bound for a real positive-semidefinite matrix. This is the finite
matrix step for local uniform ellipticity of moment-map Monge-Ampere equations. -/
theorem posSemidef_sub_scalar_of_det_lower {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hupper : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) (hdet : δ ≤ A.det) :
    (A - (δ / K ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
    cases n with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hn)
  | succ
    m =>
    have hApos : A.PosDef := hA.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hδ hdet))
    let U := hA.isHermitian.eigenvectorUnitary
    let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) U
    let a := hA.isHermitian.eigenvalues
    have hspec : A = e (diagonal a) := by
      simpa only [e, U, a, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
        hA.isHermitian.spectral_theorem
    have hpres (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : (e B).PosSemidef ↔ B.PosSemidef := by
      dsimp only [e]
      rw [Unitary.conjStarAlgAut_apply]
      exact Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe
    have hupper_diag :
      (K • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - diagonal a).PosSemidef := by
      apply (hpres _).mp
      rw [map_sub, map_smul, map_one, ← hspec]
      exact hupper
    have ha_nonneg (i : Fin (m + 1)) : 0 ≤ a i := (hApos.eigenvalues_pos i).le
    have ha_le (i : Fin (m + 1)) : a i ≤ K := by
      have hi : 0 ≤ (K • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) - diagonal a) i i :=
        hupper_diag.diag_nonneg
      simpa using hi
    have hdet_prod : δ ≤ ∏ i, a i := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues] at hdet
      simpa only [a, RCLike.ofReal_real_eq_id, id_eq] using hdet
    have hlower (i : Fin (m + 1)) : δ / K ^ ((m + 1) - 1) ≤ a i := by
      have hrest : (∏ j ∈ Finset.univ.erase i, a j) ≤ K ^ ((m + 1) - 1) := by
        calc
          (∏ j ∈ Finset.univ.erase i, a j) ≤ ∏ _j ∈ Finset.univ.erase i, K :=
            Finset.prod_le_prod₀ (fun j _ => ha_nonneg j) (fun j _ => ha_le j)
          _ = K ^ ((m + 1) - 1) := by simp
      apply (div_le_iff₀ (pow_pos hK ((m + 1) - 1))).mpr
      calc
        δ ≤ ∏ j, a j := hdet_prod
        _ = a i * ∏ j ∈ Finset.univ.erase i, a j :=
          (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm
        _ ≤ a i * K ^ ((m + 1) - 1) := mul_le_mul_of_nonneg_left hrest (ha_nonneg i)
    have hdiag :
      (diagonal a -
          (δ / K ^ ((m + 1) - 1)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).PosSemidef := by
      have heq :
        diagonal a - (δ / K ^ ((m + 1) - 1)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
          diagonal (fun i => a i - δ / K ^ ((m + 1) - 1)) := by
        ext i j
        by_cases hij : i = j
        · subst j; simp
        · simp [hij]
      rw [heq]
      exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hlower i))
    have hout := (hpres _).mpr hdiag
    rw [map_sub, map_smul, map_one, ← hspec] at hout
    exact hout

end DeterminantFloor

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section InverseBounds

open Matrix

/--
**Reciprocal matrix bounds**: a real positive definite `A` with `α·Id ≤ A ≤ β·Id` (`α, β > 0`)
satisfies
`β⁻¹·Id ≤ A⁻¹ ≤ α⁻¹·Id`; every dimension, zero included. -/
theorem inverse_posSemidef_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hlower : (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hupper : (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    (A⁻¹ - β⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (α⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - A⁻¹).PosSemidef := by
  classical
  let R := A⁻¹
  have hR : R.PosDef := hA.inv
  have hRA : R * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAR : A * R = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hrstar : Rᴴ = R := hR.isHermitian.eq
  have hLo : (R - α • (R * R)).PosSemidef := by
    have h := hlower.mul_mul_conjTranspose_same R
    simpa only [hrstar, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, hRA] using h
  have hUp : (β • (R * R) - R).PosSemidef := by
    have h := hupper.mul_mul_conjTranspose_same R
    simpa only [hrstar, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, hAR, Matrix.mul_assoc] using h
  let U := hR.isHermitian.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U
  let a := hR.isHermitian.eigenvalues
  have hspec : R = e (diagonal a) := by
    simpa only [e, U, a, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hR.isHermitian.spectral_theorem
  have hpres (B : Matrix (Fin n) (Fin n) ℝ) : (e B).PosSemidef ↔ B.PosSemidef := by
    dsimp only [e]
    rw [Unitary.conjStarAlgAut_apply]
    exact Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe
  have hDLo : (diagonal a - α • (diagonal a * diagonal a)).PosSemidef := by
    apply (hpres _).mp
    rw [map_sub, map_smul, map_mul, ← hspec]
    exact hLo
  have hDUp : (β • (diagonal a * diagonal a) - diagonal a).PosSemidef := by
    apply (hpres _).mp
    rw [map_sub, map_smul, map_mul, ← hspec]
    exact hUp
  have ha (i : Fin n) : β⁻¹ ≤ a i ∧ a i ≤ α⁻¹ := by
    have hpos : 0 < a i := hR.eigenvalues_pos i
    have hlo : 0 ≤ a i - α * (a i * a i) := by simpa using hDLo.diag_nonneg (i := i)
    have hup : 0 ≤ β * (a i * a i) - a i := by simpa using hDUp.diag_nonneg (i := i)
    constructor
    · apply (inv_le_iff_one_le_mul₀ hβ).2
      nlinarith
    · have hm : a i * α ≤ 1 := by nlinarith
      simpa only [one_div] using (le_div_iff₀ hα).2 hm
  constructor
  · have hd : (diagonal a - β⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
      convert Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i).1) using 1
      ext i j
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
    have h := (hpres _).mpr hd
    simpa only [map_sub, map_smul, map_one, ← hspec, R] using h
  · have hd : (α⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - diagonal a).PosSemidef := by
      convert Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i).2) using 1
      ext i j
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
    have h := (hpres _).mpr hd
    simpa only [map_sub, map_smul, map_one, ← hspec, R] using h

end InverseBounds

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section QuadraticYoung

open Matrix

/--
**Young inequality for a positive semidefinite quadratic form**: `2 xᵀAy ≤ ε xᵀAx + ε⁻¹ yᵀAy` for
real positive
semidefinite `A` over any finite index type (the empty one included), any vectors and `ε > 0`; `A`
may be singular. -/
theorem posSemidef_quadratic_young {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (x y : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * dotProduct x (A.mulVec y) ≤
      ε * dotProduct x (A.mulVec x) + ε⁻¹ * dotProduct y (A.mulVec y) := by
  classical
  have htranspose : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hsym : dotProduct y (A.mulVec x) = dotProduct x (A.mulVec y) := by
    calc
      dotProduct y (A.mulVec x) = dotProduct y (Aᵀ.mulVec x) := by rw [htranspose]
      _ = dotProduct x (A.mulVec y) := Matrix.dotProduct_transpose_mulVec A y x
  have hpos := hA.dotProduct_mulVec_nonneg (ε • x - y)
  simp only [star_trivial] at hpos
  have hquad :
    dotProduct (ε • x - y) (A.mulVec (ε • x - y)) =
      ε ^ 2 * dotProduct x (A.mulVec x) - 2 * ε * dotProduct x (A.mulVec y) +
        dotProduct y (A.mulVec y) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hsym]
    ring
  rw [hquad] at hpos
  apply (mul_le_mul_iff_right₀ hε).mp
  calc
    ε * (2 * dotProduct x (A.mulVec y)) ≤
        ε ^ 2 * dotProduct x (A.mulVec x) + dotProduct y (A.mulVec y) := by
      linarith
    _ = ε * (ε * dotProduct x (A.mulVec x) + ε⁻¹ * dotProduct y (A.mulVec y)) := by
      field_simp [hε.ne']

/--
**Pointwise weighted Young inequality for real-power energy tests**: for real positive semidefinite
`A`, `s > 0`,
`p > 0` and real `χ`, `2 χ s^(-p) aᵀAb ≤ (p/2) χ² s^(-p-1) aᵀAa + (2/p) s^(1-p) bᵀAb`. Local algebra
for a Caccioppoli
estimate; not itself a PDE energy inequality. -/
theorem rpow_cutoff_quadratic_young {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (a b : ι → ℝ) {s p : ℝ} (hs : 0 < s) (hp : 0 < p) (χ : ℝ) :
    2 * χ * s ^ (-p) * dotProduct a (A.mulVec b) ≤
      (p / 2) * χ ^ 2 * s ^ (-p - 1) * dotProduct a (A.mulVec a) +
        (2 / p) * s ^ (1 - p) * dotProduct b (A.mulVec b) := by
  have h := posSemidef_quadratic_young A hA (χ • a) (s • b) (by positivity : 0 < p / 2)
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
  have hs1 : s ^ (-p - 1) * s = s ^ (-p) := by
    calc
      s ^ (-p - 1) * s = s ^ (-p - 1) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((-p - 1) + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ (-p) := by congr 1; ring
  have hs2 : s ^ (-p - 1) * s ^ (2 : ℕ) = s ^ (1 - p) := by
    calc
      s ^ (-p - 1) * s ^ (2 : ℕ) = s ^ (-p - 1) * s ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = s ^ ((-p - 1) + 2) := (Real.rpow_add hs _ _).symm
      _ = s ^ (1 - p) := by congr 1; ring
  have hi : (p / 2)⁻¹ = 2 / p := by field_simp
  have h' := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hs.le (-p - 1))
  calc
    2 * χ * s ^ (-p) * dotProduct a (A.mulVec b) =
        s ^ (-p - 1) * (2 * (s * (χ * dotProduct a (A.mulVec b)))) := by
      rw [← hs1]; ring
    _ ≤
        s ^ (-p - 1) *
          ((p / 2) * (χ * (χ * dotProduct a (A.mulVec a))) +
            (p / 2)⁻¹ * (s * (s * dotProduct b (A.mulVec b)))) :=
      h'
    _ =
        (p / 2) * χ ^ 2 * s ^ (-p - 1) * dotProduct a (A.mulVec a) +
          (2 / p) * s ^ (1 - p) * dotProduct b (A.mulVec b) := by
      rw [hi, ← hs2]; ring

end QuadraticYoung

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section PositiveCongruence
open Matrix
open scoped MatrixOrder
/--
**Positive definite matrices are congruent.** Two positive definite real matrices of the same
nonzero size
satisfy `A = S B Sᵀ` for an invertible real `S` (`S = A^{1/2} B^{-1/2}` by the continuous functional
calculus).
This is congruence, not similarity: the change of variables of Gilbarg–Trudinger (2001), proof of
Lemma 17.13,
Eq. (17.55). -/
theorem exists_invertible_congruence_of_posDef {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, IsUnit S ∧ A = S * B * Matrix.transpose S := by
  classical
    cases n with
  | zero => omega
  | succ m =>
    let X := CFC.sqrt A
    let Y := CFC.sqrt B
    have hXX : X * X = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
    have hYY : Y * Y = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
    have hUX : IsUnit X := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).2 hA.isUnit
    have hUY : IsUnit Y := (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).2 hB.isUnit
    have hXt : Xᵀ = X := (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg A).posSemidef.1).eq
    have hYt : Yᵀ = Y := (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg B).posSemidef.1).eq
    have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
    have hYL : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y ((Matrix.isUnit_iff_isUnit_det Y).mp hUY)
    have hYR : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y ((Matrix.isUnit_iff_isUnit_det Y).mp hUY)
    refine ⟨X * Y⁻¹, hUX.mul (Matrix.isUnit_nonsing_inv_iff.mpr hUY), ?_⟩
    symm
    rw [Matrix.transpose_mul, hYit, hXt, ← hYY]
    calc
      _ = X * (Y⁻¹ * Y) * (Y * Y⁻¹) * X := by simp only [Matrix.mul_assoc]
      _ = X * X := by rw [hYL, hYR]; simp only [mul_one]
      _ = A := hXX
end PositiveCongruence

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

open Set Filter
open scoped Topology

/-- A real symmetric matrix is PSD when every positive scalar identity shift
is PSD. The empty index type is included. -/
theorem posSemidef_of_positive_shifts {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (hu : ∀ t : ℝ, 0 < t → (B + t • 1).PosSemidef) : B.PosSemidef := by
  have hc : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hB, ?_⟩
  intro v
  have hv : Continuous (fun t : ℝ => star v ⬝ᵥ (B + t • 1).mulVec v) :=
    continuous_const.dotProduct (hc.matrix_mulVec continuous_const)
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ star v ⬝ᵥ (B + t • 1).mulVec v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hu t ht).dotProduct_mulVec_nonneg v
  simpa using ge_of_tendsto
    (hv.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hh

section AxisFrames
open Matrix Module
open scoped RealInnerProductSpace

/--
Positive definiteness generates an orthogonal coordinate basis while fixing a chosen axis. -/
theorem exists_orthogonal_basis_fixing_axis {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (k : Fin n) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ),
      b k = Pi.single k 1 ∧ ∀ i j, i ≠ j → (H *ᵥ b j) ⬝ᵥ b i = 0 := by
  classical
  let ng := H.toNormedAddCommGroup hH
  let _ : SeminormedAddCommGroup (Fin n → ℝ) := ng.toSeminormedAddCommGroup
  let _ : NormedAddCommGroup (Fin n → ℝ) := ng
  let _ : InnerProductSpace ℝ (Fin n → ℝ) := H.toInnerProductSpace hH.posSemidef
  let v : Fin n → ℝ := Pi.single k 1
  let a := Real.sqrt (H k k)
  have ha : 0 < a := Real.sqrt_pos.mpr hH.diag_pos
  have hasq : a ^ 2 = H k k := Real.sq_sqrt hH.diag_pos.le
  let w := a⁻¹ • v
  have hw : inner ℝ w w = 1 := by
    change (H *ᵥ w) ⬝ᵥ star w = 1
    simp only [w, v, star_trivial, smul_dotProduct, dotProduct_smul, mulVec_smul]
    simp only [mulVec_single, mul_one, dotProduct_single]
    simp only [Pi.smul_apply, op_smul_eq_smul, smul_eq_mul, Matrix.col]
    field_simp [ha.ne']
    exact hasq.symm
  have ho : Orthonormal ℝ (({ k } : Set (Fin n)).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j :=
      Subtype.ext
        ((Set.mem_singleton_iff.mp i.property).trans (Set.mem_singleton_iff.mp j.property).symm)
    simpa only [Set.domRestrict_apply, ite_eq_left hij] using hw
  obtain ⟨B, hB⟩ :=
    ho.exists_orthonormalBasis_extension_of_card_eq
      (by simp : Module.finrank ℝ (Fin n → ℝ) = Fintype.card (Fin n))
  let s : Fin n → ℝˣ := fun i =>
    Units.mk0 (if i = k then a else 1) (by
      split_ifs
      · exact ha.ne'
      · exact one_ne_zero)
  let b := B.toBasis.unitsSMul s
  refine ⟨b, ?_, ?_⟩
  · dsimp [b]
    rw [Basis.unitsSMul_apply]
    change (s k : ℝ) • B k = v
    rw [hB k (by simp)]
    simp only [s, Units.val_mk0]
    change a • (a⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · intro i j hij
    have hb : inner ℝ (b i) (b j) = 0 := by
      dsimp only [b]
      rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply]
      simp only [Units.smul_def, inner_smul_left, inner_smul_right]
      change (s j : ℝ) * ((starRingEnd ℝ) (s i : ℝ) * inner ℝ (B i) (B j)) = 0
      rw [B.orthonormal.inner_eq_zero hij]
      simp
    change (H *ᵥ b j) ⬝ᵥ star (b i) = 0 at hb
    simpa using hb

/-- The generated basis gives an invertible diagonalizing matrix fixing the chosen axis. -/
theorem exists_diagonal_frame_fixing_axis {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (k : Fin n) :
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      IsUnit A ∧
        (A *ᵥ Pi.single k 1) = Pi.single k 1 ∧
          (∀ i, 0 < d i) ∧ Aᵀ * H * A = Matrix.diagonal d := by
  classical
  obtain ⟨b, hbk, horth⟩ := exists_orthogonal_basis_fixing_axis H hH k
  let e := Pi.basisFun ℝ (Fin n)
  let A := e.toMatrix b
  have hA (i j) : A i j = b j i := rfl
  have hu : IsUnit A := by
    let _ : Invertible A := e.invertibleToMatrix b
    exact isUnit_of_invertible A
  have hentry (i j) : (Aᵀ * H * A) i j = (H *ᵥ b j) ⬝ᵥ b i := by
    rw [Matrix.mul_assoc]
    change (∑ l, A l i * (∑ m, H l m * A m j)) = ∑ l, (∑ m, H l m * b j m) * b i l
    simp_rw [hA]
    apply Finset.sum_congr rfl
    intro l _
    exact mul_comm _ _
  refine ⟨A, fun i => (H *ᵥ b i) ⬝ᵥ b i, hu, ?_, ?_, ?_⟩
  · ext i
    rw [Matrix.mulVec_single_one]
    change A i k = (Pi.single k (1 : ℝ) : Fin n → ℝ) i
    rw [hA, hbk]
  · intro i
    have hi := hH.dotProduct_mulVec_pos (b.ne_zero i)
    simpa only [star_trivial, dotProduct_comm] using hi
  · ext i j
    rw [hentry]
    by_cases hij : i = j
    · subst j; simp
    · rw [horth i j hij]
      simp [Matrix.diagonal, hij]

end AxisFrames

/-! ## Symmetric parts of real quadratic coefficients

CNS1984 (5.1) controls quadratic forms rather than the raw skew part. The
symmetric part is PSD, preserves Hermitian trace pairings and has the stated
ELEMENTWISE norm ceiling. Empty finite indices are included.
-/
section SymmetricCoefficients
open scoped Matrix.Norms.Elementwise

/--
Reindexing a double sum against the transpose; shared by the quadratic-form and trace identities. -/
private lemma sum_transpose_mul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (g : ι → ι → ℝ) :
    ∑ i, ∑ j, A.transpose i j * g i j = ∑ i, ∑ j, A i j * g j i := by
  rw [Finset.sum_comm]
  simp only [Matrix.transpose_apply]

/-- The coordinate quadratic form is `v ⬝ᵥ B v`; shared by positivity and the norm ceiling. -/
private lemma quadratic_eq_dotProduct {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (v : ι → ℝ) :
    ∑ i, ∑ j, B i j * v i * v j = dotProduct v (B.mulVec v) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem posSemidef_symmetricPart_of_quadratic_nonneg {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    ((1 / 2 : ℝ) • (A + A.transpose)).PosSemidef ∧
      (∀ v : ι → ℝ,
          (∑ i, ∑ j, ((1 / 2 : ℝ) • (A + A.transpose)) i j * v i * v j) =
            ∑ i, ∑ j, A i j * v i * v j) ∧
        (∀ (H : Matrix ι ι ℝ),
          H.IsHermitian →
            Matrix.trace (((1 / 2 : ℝ) • (A + A.transpose)) * H) = Matrix.trace (A * H)) := by
  classical
  have hquad :
    ∀ v : ι → ℝ,
      (∑ i, ∑ j, ((1 / 2 : ℝ) • (A + A.transpose)) i j * v i * v j) =
        ∑ i, ∑ j, A i j * v i * v j := by
    intro v
    have h : ∑ i, ∑ j, A.transpose i j * (v i * v j) = ∑ i, ∑ j, A i j * (v j * v i) :=
      sum_transpose_mul A fun i j => v i * v j
    have e :
      ∀ i j,
        ((1 / 2 : ℝ) • (A + A.transpose)) i j * v i * v j =
          (1 / 2) * (A i j * v i * v j) + (1 / 2) * (A.transpose i j * (v i * v j)) := by
      intro i j
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    have e2 : ∑ i, ∑ j, A i j * (v j * v i) = ∑ i, ∑ j, A i j * v i * v j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h, e2]
    ring
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_, hquad, fun H hH => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply]
    ring
  · have hv : star v = v := star_trivial v
    rw [hv, ← quadratic_eq_dotProduct, hquad]
    exact hA v
  · have hHs : ∀ i j, H j i = H i j := fun i j => by simpa using hH.apply i j
    have htr : ∀ B : Matrix ι ι ℝ, Matrix.trace (B * H) = ∑ i, ∑ j, B i j * H j i := fun B => by
      simp [Matrix.trace, Matrix.mul_apply]
    have h : ∑ i, ∑ j, A.transpose i j * H j i = ∑ i, ∑ j, A i j * H i j :=
      sum_transpose_mul A fun i j => H j i
    have e :
      ∀ i j,
        ((1 / 2 : ℝ) • (A + A.transpose)) i j * H j i =
          (1 / 2) * (A i j * H j i) + (1 / 2) * (A.transpose i j * H j i) := by
      intro i j
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    have e2 : ∑ i, ∑ j, A i j * H i j = ∑ i, ∑ j, A i j * H j i :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hHs]
    rw [htr, htr]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h, e2]
    ring

theorem norm_symmetricPart_le_of_quadratic_le {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) {M : ℝ} (hM : 0 ≤ M) (hA : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, A i j * v i * v j)
    (hcap : ∀ v : ι → ℝ, (∑ i, ∑ j, A i j * v i * v j) ≤ M * ∑ i, (v i) ^ 2) :
    ‖((1 / 2 : ℝ) • (A + A.transpose))‖ ≤ M := by
  classical
  obtain ⟨hS, hquad, -⟩ := posSemidef_symmetricPart_of_quadratic_nonneg A hA
  set S : Matrix ι ι ℝ := (1 / 2 : ℝ) • (A + A.transpose) with hSdef
  have hent : ∀ a b : ι, dotProduct (Pi.single a 1) (S.mulVec (Pi.single b 1)) = S a b :=
    fun a b => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  -- diagonal ceiling from the quadratic ceiling at `eᵢ`
  have hdiag : ∀ i : ι, S i i ≤ M := fun i => by
    rw [← hent, ← quadratic_eq_dotProduct, hquad]
    calc
      _ ≤ M * ∑ k, (Pi.single i (1 : ℝ) k) ^ 2 := hcap _
      _ = M := by simp [Pi.single_apply]
  rw [Matrix.norm_le_iff hM]
  intro i
    j
  -- canonical PSD Young inequality at `ε = 1` on `eᵢ` and `±eⱼ`
  have hp := posSemidef_quadratic_young S hS (Pi.single i 1) (Pi.single j 1) one_pos
  have hm := posSemidef_quadratic_young S hS (Pi.single i 1) (-Pi.single j 1) one_pos
  simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at hm
  rw [hent, hent, hent, inv_one, one_mul, one_mul] at hp hm
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hdiag i, hdiag j]

end SymmetricCoefficients

end FunctionalInequalities.Analysis
