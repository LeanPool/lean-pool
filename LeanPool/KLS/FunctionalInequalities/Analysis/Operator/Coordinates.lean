/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.RingInverseDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Orthonormal coordinates of operators

Entries `⟪b i, M (b j)⟫` of a continuous linear operator in an orthonormal basis: products, triple
products, entries of derivatives, and the coordinate form of the inverse derivative; and the full
matrix
`operatorMatrix b T = LinearMap.toMatrixOrthonormal b T` with its inverse `operatorOfMatrix`,
positivity,
unit and inverse transfer (identified with the entries by `operatorMatrix_apply_eq_operatorEntry`),
and the
continuous linear charts `operatorOfMatrixL`/`operatorMatrixL` between Euclidean matrix entries and
operators
(finite-dimensional norm comparison; no identification of the Frobenius and operator norms).
-/

@[expose] public section

noncomputable section
open scoped RealInnerProductSpace MatrixOrder

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `(i, j)` entry `⟪b i, M (b j)⟫` of an operator in an orthonormal basis. -/
def operatorEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (M : E →L[ℝ] E) (i j : Fin m) : ℝ :=
  ⟪b i, M (b j)⟫

/-- Entries of a product are the matrix product of entries. -/
theorem operatorEntry_mul {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (M N : E →L[ℝ] E)
    (i j : Fin m) :
    operatorEntry b (M * N) i j = ∑ k, operatorEntry b M i k * operatorEntry b N k j := by
  change ⟪b i, M (N (b j))⟫ = _
  conv_lhs => rw [← b.sum_repr' (N (b j))]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, operatorEntry]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

theorem operatorEntry_mul_three {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (M N P : E →L[ℝ] E)
    (i j : Fin m) :
    operatorEntry b (M * N * P) i j =
      ∑ a, ∑ c, operatorEntry b M i a * operatorEntry b N a c * operatorEntry b P c j := by
  rw [operatorEntry_mul]
  simp_rw [operatorEntry_mul, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The entry of a derivative is the derivative of the entry. -/
theorem operatorEntry_fderiv_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {H : E → (E →L[ℝ] E)} {x : E} (hH : DifferentiableAt ℝ H x) (i j : Fin m) (v : E) :
    fderiv ℝ (fun y => operatorEntry b (H y) i j) x v = operatorEntry b (fderiv ℝ H x v) i j := by
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ E (b j))
  have hd := L.hasFDerivAt.comp x hH.hasFDerivAt
  change fderiv ℝ (L ∘ H) x v = L (fderiv ℝ H x v)
  rw [hd.fderiv]
  rfl

section Inverse

variable [CompleteSpace E]

/--
Derivative of an entry of `H⁻¹` in coordinates: `−Σ_{a,c} (H⁻¹)_{ia} (DH[v])_{ac} (H⁻¹)_{cj}`. -/
theorem operatorEntry_ringInverse_fderiv_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {H : E → (E →L[ℝ] E)} {x : E} (hH : DifferentiableAt ℝ H x) (hunit : IsUnit (H x))
    (i j : Fin m) (v : E) :
    fderiv ℝ (fun y => operatorEntry b (Ring.inverse (H y)) i j) x v =
      -(∑ a,
          ∑ c,
            operatorEntry b (Ring.inverse (H x)) i a * operatorEntry b (fderiv ℝ H x v) a c *
              operatorEntry b (Ring.inverse (H x)) c j) := by
  rw [operatorEntry_fderiv_apply b (hH.inverse hunit), fderiv_ringInverse_comp_apply hH hunit]
  simp only [operatorEntry, neg_apply, inner_neg_right]
  change -operatorEntry b (Ring.inverse (H x) * fderiv ℝ H x v * Ring.inverse (H x)) i j = _
  rw [operatorEntry_mul_three]
  rfl

end Inverse

section OperatorMatrix

open Matrix

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The matrix of an operator in an orthonormal basis (`LinearMap.toMatrixOrthonormal`); its `(i, j)`
entry is
`operatorEntry b T i j` (`operatorMatrix_apply_eq_operatorEntry`). -/
def operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) : Matrix ι ι ℝ :=
  LinearMap.toMatrixOrthonormal b T.toLinearMap

/-- The operator with a given matrix in an orthonormal basis (inverse of `operatorMatrix`). -/
def operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) : E →L[ℝ] E :=
  ((LinearMap.toMatrixOrthonormal b).symm M).toContinuousLinearMap

@[simp] theorem operatorMatrix_operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorMatrix b (operatorOfMatrix b M) = M := by
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M

@[simp] theorem operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)

theorem operatorMatrix_injective (b : OrthonormalBasis ι ℝ E) :
    Function.Injective (operatorMatrix b) := by
  intro S T h
  have := congrArg (operatorOfMatrix b) h
  simpa only [operatorOfMatrix_operatorMatrix] using this

@[simp] theorem operatorMatrix_mul (b : OrthonormalBasis ι ℝ E) (S T : E →L[ℝ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T := by
  exact map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap

@[simp] theorem operatorMatrix_one (b : OrthonormalBasis ι ℝ E) :
    operatorMatrix b (1 : E →L[ℝ] E) = 1 := by
  exact map_one (LinearMap.toMatrixOrthonormal b)

/--
The matrix is positive semidefinite iff the operator is positive (Mathlib
`posSemidef_toMatrix_iff`). -/
theorem operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b

theorem operatorOfMatrix_isPositive (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) : (operatorOfMatrix b M).IsPositive := by
  apply (operatorMatrix_posSemidef_iff b _).mp
  simpa only [operatorMatrix_operatorOfMatrix] using hM

/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]

theorem operatorMatrix_isUnit_iff (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsUnit (operatorMatrix b A) ↔ IsUnit A := by
  exact (LinearMap.isUnit_toMatrix_iff b.toBasis).trans
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.symm

/-- The quadratic form in coordinates. -/
theorem inner_eq_dotProduct_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (v : E) :
    ⟪v, T v⟫ = star (fun i => b.repr v i) ⬝ᵥ
      (operatorMatrix b T *ᵥ (fun i => b.repr v i)) := by
  have hm := T.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis v
  have he (x : E) : (fun i => b.toBasis.repr x i) = (fun i => b.repr x i) :=
    funext (b.coe_toBasis_repr_apply x)
  change operatorMatrix b T *ᵥ (fun i => b.toBasis.repr v i) =
    (fun i => b.toBasis.repr (T v) i) at hm
  rw [he, he] at hm
  rw [hm, ← b.repr.inner_map_map v (T v)]
  change (fun i => b.repr (T v) i) ⬝ᵥ star (fun i => b.repr v i) = _
  exact dotProduct_comm _ _

omit [DecidableEq ι] in
/-- A positive unit is strictly positive (converse of `isUnit_of_inner_self_pos`). -/
theorem inner_self_pos_of_isPositive_of_isUnit (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (hpos : T.IsPositive) (hunit : IsUnit T)
    {v : E} (hv : v ≠ 0) : 0 < ⟪T v, v⟫ := by
  classical
  have hp := ((operatorMatrix_posSemidef_iff b T).mpr hpos).posDef_iff_isUnit.mpr
    ((operatorMatrix_isUnit_iff b T).mpr hunit)
  have hx : (fun i => b.repr v i) ≠ 0 := by
    intro hh
    apply hv
    apply b.repr.injective
    apply PiLp.ext
    intro i
    have := congrFun hh i
    simpa using this
  rw [real_inner_comm, inner_eq_dotProduct_operatorMatrix b T v]
  exact hp.dotProduct_mulVec_pos hx

/-- Identification of the two coordinate objects: the matrix entry is `operatorEntry`. -/
theorem operatorMatrix_apply_eq_operatorEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    (T : E →L[ℝ] E) (i j : Fin m) : operatorMatrix b T i j = operatorEntry b T i j := by
  rw [operatorMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- `matrixEntries` as a real-linear map, used to build `operatorMatrixL`. -/
def matrixEntriesLinear : Matrix ι ι ℝ →ₗ[ℝ] EuclideanSpace ℝ (ι × ι) where
  toFun := matrixEntries
  map_add' A B := by ext ij; rfl
  map_smul' a A := by ext ij; rfl

/-- The inverse of `matrixEntriesLinear`, used to build `operatorOfMatrixL`. -/
def matrixOfEntriesLinear : EuclideanSpace ℝ (ι × ι) →ₗ[ℝ] Matrix ι ι ℝ where
  toFun z i j := z (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The operator with given Euclidean matrix entries, as a continuous linear map (finite-dimensional
continuity gives a norm comparison between Frobenius entries and the operator norm; no isometry is
asserted). -/
def operatorOfMatrixL (b : OrthonormalBasis ι ℝ E) :
    EuclideanSpace ℝ (ι × ι) →L[ℝ] (E →L[ℝ] E) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((LinearMap.toMatrixOrthonormal b).symm.toAlgEquiv.toLinearMap.comp
      matrixOfEntriesLinear)).toContinuousLinearMap

@[simp] theorem operatorOfMatrixL_matrixEntries (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorOfMatrixL b (matrixEntries M) = operatorOfMatrix b M := rfl

/-- The Euclidean matrix entries of an operator, as a continuous linear map. -/
def operatorMatrixL (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →L[ℝ] EuclideanSpace ℝ (ι × ι) :=
  (matrixEntriesLinear.comp ((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
    LinearMap.toContinuousLinearMap.symm.toLinearMap)).toContinuousLinearMap

@[simp] theorem operatorMatrixL_apply (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorMatrixL b T = matrixEntries (operatorMatrix b T) := rfl

end OperatorMatrix

section EuclideanCoordinates

/--
Coordinates of an operator image in the standard basis: `(T v) j = Σ_r P j r v_r`, `P` the matrix of
`T`. -/
theorem euclidean_clm_apply_eq_sum_operatorMatrix {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (j : Fin n) :
    (T v) j = ∑ r : Fin n, operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T j r * v r := by
  simp only [operatorMatrix_apply_eq_operatorEntry, operatorEntry]
  have hc :
    ∀ w : EuclideanSpace ℝ (Fin n), ∀ k, ⟪EuclideanSpace.basisFun (Fin n) ℝ k, w⟫ = w k := by
    intro w k
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  have hs : ∀ w : EuclideanSpace ℝ (Fin n), ∀ k, ⟪EuclideanSpace.single k 1, w⟫ = w k := by
    intro w k
    simpa [EuclideanSpace.basisFun_apply] using hc w k
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [map_sum, map_smul, hs, mul_comm]

/-- For self-adjoint `T`, pairing `T e_i` against `v` reads off the `i`-th coordinate of `T v`. -/
theorem euclidean_inner_selfAdjoint_basisFun {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hT : IsSelfAdjoint T)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ⟪T (EuclideanSpace.basisFun (Fin n) ℝ i), v⟫ = (T v) i := by
    calc
      ⟪T (EuclideanSpace.basisFun (Fin n) ℝ i), v⟫ =
          ⟪EuclideanSpace.basisFun (Fin n) ℝ i, T v⟫ := hT.isSymmetric _ _
      _ = (T v) i := by
        simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/--
Entry algebra of a symmetric sandwich: `Σ_s Σ_t P j s (v_s v_t w) P t k = (Σ_s P j s v_s)(Σ_t P k t
v_t) w`. -/
theorem sum_sum_mul_mul_mul_mul_eq_of_symm {n : ℕ} (P : Fin n → Fin n → ℝ)
    (hP : ∀ r s, P r s = P s r) (v : Fin n → ℝ) (w : ℝ) (j k : Fin n) :
    ∑ s : Fin n, ∑ t : Fin n, P j s * (v s * v t * w) * P t k =
      (∑ s : Fin n, P j s * v s) * (∑ t : Fin n, P k t * v t) * w := by
  symm
  calc
    (∑ s : Fin n, P j s * v s) * (∑ t : Fin n, P k t * v t) * w =
        ((∑ s : Fin n, P j s * v s) * (∑ t : Fin n, P k t * v t)) * w :=
      rfl
    _ = (∑ s : Fin n, P j s * v s * (∑ t : Fin n, P k t * v t)) * w := by rw [Finset.sum_mul]
    _ = ∑ s : Fin n, (P j s * v s * (∑ t : Fin n, P k t * v t)) * w := by rw [Finset.sum_mul]
    _ = ∑ s : Fin n, ∑ t : Fin n, (P j s * v s * (P k t * v t)) * w := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ s : Fin n, ∑ t : Fin n, P j s * (v s * v t * w) * P t k := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      rw [hP t k]
      ring

end EuclideanCoordinates

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Probability.Stein
/-- A real square matrix representing a Stein kernel in coordinates. -/
abbrev KernelMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

end FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis
open Filter Topology
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An operator represented by a bilinear form is bounded by the form's norm. -/
theorem opNorm_le_of_inner_eq
    {A : E →L[ℝ] E}
    {κ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    (h : ∀ u v : E, ⟪A u, v⟫ = κ ![u, v]) : ‖A‖ ≤ ‖κ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  have h1 : ‖A u‖ * ‖A u‖ ≤ (‖κ‖ * ‖u‖) * ‖A u‖ := by
    calc
      ‖A u‖ * ‖A u‖ = ⟪A u, A u⟫ := (real_inner_self_eq_norm_mul_norm _).symm
      _ = κ ![u, A u] := h u (A u)
      _ ≤ ‖κ ![u, A u]‖ := le_abs_self _
      _ ≤ ‖κ‖ * ∏ i, ‖(![u, A u] : Fin 2 → E) i‖ := κ.le_opNorm _
      _ = (‖κ‖ * ‖u‖) * ‖A u‖ := by
        rw [Fin.prod_univ_two]
        simp [mul_assoc]
  rcases (norm_nonneg (A u)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right h1 h0


end FunctionalInequalities.Analysis
