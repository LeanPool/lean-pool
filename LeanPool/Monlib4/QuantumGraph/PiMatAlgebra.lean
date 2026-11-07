/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Classes

public import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Submodule
public import LeanPool.Monlib4.LinearAlgebra.Matrix.IncludeBlock
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Pi
public import LeanPool.Monlib4.LinearAlgebra.TensorProduct.FiniteDimensional
import LeanPool.Monlib4.Preq.Finset

/-!
# Matrix and Euclidean calculation lemmas

Tensor-product, rank-one, and unitary coordinate calculations used by the quantum-graph
construction. Keeping this algebra layer separate lets it compile before the graph proofs.
-/

@[expose] public section

variable {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [Π i, Fintype (p i)] [Π i, DecidableEq (p i)]

open scoped MatrixOrder ComplexOrder TensorProduct Matrix InnerProductSpace Kronecker
open Kronecker

theorem kroneckerTMulLinearEquiv_map_lid_tmul
    {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (x : Matrix m m R) (y : Matrix n n R) :
    ((kroneckerTMulLinearEquiv m m n n R R R R) (x ⊗ₜ[R] y)).map
      ⇑(Algebra.TensorProduct.lid R R) = x ⊗ₖ y := by
  exact kroneckerLinearEquiv_tmul x y

theorem StarAlgEquiv.lTensor_toLinearMap {R A B C : Type*}
  [RCLike R] [Ring A] [Ring B] [Ring C] [Algebra R A]
  [Algebra R B] [Algebra R C] [StarAddMonoid A] [StarAddMonoid B]
  [StarAddMonoid C] [StarModule R A] [StarModule R B]
  [StarModule R C] (f : A ≃⋆ₐ[R] B) :
  (StarAlgEquiv.lTensor C f).toLinearMap = LinearMap.lTensor C f.toLinearMap :=
rfl

theorem EuclideanSpace.prod_exists_finset {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  ∃ S : Finset ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m),
    x = ∑ s ∈ S, euclideanSpaceTensor' (R := ℂ) (s.1 ⊗ₜ[ℂ] s.2) := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ((euclideanSpaceTensor' (R:=ℂ)).symm x)
  refine ⟨S, ?_⟩
  simpa only [map_sum, LinearIsometryEquiv.apply_symm_apply] using
    congrArg (euclideanSpaceTensor' (R := ℂ)) hS

@[simp]
theorem Matrix.ite_kronecker {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  (if P then x₁ else 0) ⊗ₖ x₂ = if P then x₁ ⊗ₖ x₂ else 0 := by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]

@[simp]
theorem Matrix.dite_kronecker {α n m p q : Type*} [MulZeroClass α]
  (P : Prop) [Decidable P]
  (x₁ : P → Matrix n m α) (x₂ : Matrix p q α) :
  (dite P (fun p => x₁ p) (fun _ => 0)) ⊗ₖ x₂ = dite P (fun p => x₁ p ⊗ₖ x₂) (fun _ => 0) := by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]

@[simp]
theorem Matrix.kronecker_ite {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  x₁ ⊗ₖ (if P then x₂ else 0) = if P then x₁ ⊗ₖ x₂ else 0 := by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]

@[simp]
theorem Matrix.kronecker_dite {α n m p q : Type*} [MulZeroClass α]
  (x₁ : Matrix n m α) (P : Prop) [Decidable P] (x₂ : P → Matrix p q α) :
  x₁ ⊗ₖ (dite P (fun p => x₂ p) (fun _ => 0)) = dite P (fun p => x₁ ⊗ₖ x₂ p) (fun _ => 0) := by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]

theorem Matrix.vecMulVec_kronecker_vecMulVec {α n m p q : Type*} [CommSemiring α]
    (x : n → α) (y : m → α) (z : p → α) (w : q → α) :
  (vecMulVec x y) ⊗ₖ (vecMulVec z w) =
    vecMulVec (reshape (vecMulVec x z)) (reshape (vecMulVec y w)) := by
  ext
  simp only [kroneckerMap_apply, vecMulVec_apply, reshape_apply]
  exact mul_mul_mul_comm _ _ _ _

@[simp]
theorem Matrix.vecMulVec_toEuclideanLin {n m : Type*} [Fintype n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  toEuclideanLin (vecMulVec x y) = rankOne ℂ x (star y) := by
  classical
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change vecMulVec x y = toEuclideanLin.symm (InnerProductSpace.rankOne ℂ x (star y))
  rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp only [vecMulVec_apply, PiLp.star_apply, Pi.star_apply, star_star]

open Matrix in
theorem EuclideanSpaceTensor_apply_eq_reshape_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y) = reshape (vecMulVec x y) := by
  ext1
  simp only [euclideanSpaceTensor'_apply, reshape_apply, vecMulVec_apply]

theorem Matrix.vecMulVec_conj {α n m : Type*} [CommSemiring α] [StarMul α] (x : n → α) (y : m → α) :
  (vecMulVec x y)ᴴᵀ = vecMulVec (star x) (star y) := by
  ext
  simp only [conj_apply, vecMulVec_apply, Pi.star_apply, star_mul']

theorem rankOne_euclideanSpaceTensor_eq_toEuclideanLin_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x y : EuclideanSpace ℂ n) (z w : EuclideanSpace ℂ m) :
  rankOne ℂ (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z))
    (euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w)) =
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    (Matrix.vecMulVec
      (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
      (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))))) := by
  let xz : EuclideanSpace ℂ (n × m) := euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z)
  let yw : EuclideanSpace ℂ (n × m) := euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w)
  have hxz : xz.ofLp = Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp) :=
    EuclideanSpaceTensor_apply_eq_reshape_vecMulVec x z
  have hyw : yw.ofLp = Matrix.reshape (Matrix.vecMulVec y.ofLp w.ofLp) :=
    EuclideanSpaceTensor_apply_eq_reshape_vecMulVec y w
  have hsyw :
      (star yw).ofLp = Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp)) := by
    change star yw.ofLp = Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))
    rw [hyw]
    ext a
    simp [Matrix.reshape_apply, Matrix.vecMulVec_apply]
  calc
    rankOne ℂ (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z))
        (euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w))
        = rankOne ℂ xz yw := rfl
    _ = rankOne ℂ xz (star (star yw)) := by rw [star_star]
    _ = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.vecMulVec xz (star yw))) :=
      congrArg LinearMap.toContinuousLinearMap
        (Matrix.vecMulVec_toEuclideanLin xz (star yw)).symm
    _ = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (Matrix.vecMulVec
          (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
          (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))))) := by
      rw [show Matrix.vecMulVec xz (star yw) = Matrix.vecMulVec
          (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
          (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))) by
        rw [← hxz, ← hsyw]
        rfl]

theorem Matrix.includeBlock_apply_block {R k : Type*} [CommSemiring R] [DecidableEq k]
    {s : k → Type*} {i : k} (x : Matrix (s i) (s i) R) (j : k) :
    (Matrix.includeBlock x : PiMat R k s) j =
      dite (i = j) (fun h => Eq.mp (by rw [h]) x) fun _ => 0 := by
  rw [Matrix.includeBlock_apply]

theorem EuclideanSpace.sum_apply {n : Type*} {𝕜 : Type*} [RCLike 𝕜]
  {ι : Type*} (s : Finset ι)
  (x : ι → EuclideanSpace 𝕜 n) (j : n) :
  (∑ i ∈ s, x i) j = ∑ i ∈ s, (x i j) := by
  simp [WithLp.ofLp_sum, Finset.sum_apply]

theorem Module.Basis.tensorProduct_repr_tmul_apply' {R M N ι κ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (b : Module.Basis ι R M) (c : Module.Basis κ R N) (m : M) (n : N) (i : ι × κ) :
  ((b.tensorProduct c).repr (m ⊗ₜ[R] n)) i = (c.repr n) i.2 * (b.repr m) i.1 := by
  simpa [smul_eq_mul, mul_comm] using
    Module.Basis.tensorProduct_repr_tmul_apply b c m n i.1 i.2

theorem StarAlgEquiv.piCongrRight_symm {R ι : Type*} {A₁ A₂ : ι → Type*}
  [(i : ι) → Add (A₁ i)] [(i : ι) → Add (A₂ i)] [(i : ι) → Mul (A₁ i)] [(i : ι) → Mul (A₂ i)]
  [(i : ι) → Star (A₁ i)] [(i : ι) → Star (A₂ i)] [(i : ι) → SMul R (A₁ i)] [(i : ι) →
    SMul R (A₂ i)]
  (e : (i : ι) → A₁ i ≃⋆ₐ[R] A₂ i) :
  (StarAlgEquiv.piCongrRight e).symm = StarAlgEquiv.piCongrRight (fun i => (e i).symm) :=
rfl

theorem Matrix.kronecker_mulVec_euclideanSpaceTensor' {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n n ℂ) (B : Matrix m m ℂ) (x : EuclideanSpace ℂ n)
  (y : EuclideanSpace ℂ m) :
  (A ⊗ₖ B) *ᵥ ((WithLp.equiv 2 _) (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)))
    = WithLp.equiv 2 _ (euclideanSpaceTensor' (R := ℂ)
      ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ (WithLp.toLp 2 (B *ᵥ y.ofLp)))) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply, WithLp.equiv]
  calc
    ∑ x_1 : n × m,
    A a.1 x_1.1 * B a.2 x_1.2 * (Equiv.refl (WithLp 2 (n × m →
      ℂ))) (euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y)) x_1
      = ∑ x_1, A a.1 x_1.1 * B a.2 x_1.2 * ((euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)) x_1) := rfl
    _ = ∑ x_1 : n × m, A a.1 x_1.1 * B a.2 x_1.2 * (x x_1.1 * y x_1.2) := by
      simp only [euclideanSpaceTensor'_apply]
    _ = (euclideanSpaceTensor' (R := ℂ)
        ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ[ℂ] (WithLp.toLp 2 (B *ᵥ y.ofLp)))) a := ?_
    _ = (Equiv.refl (WithLp 2 (n × m → ℂ))) (euclideanSpaceTensor' (R := ℂ)
        ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ[ℂ] (WithLp.toLp 2 (B *ᵥ y.ofLp)))) a := rfl
  rw [euclideanSpaceTensor'_apply]
  simp_rw [mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Finset.sum_product_univ, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem StarAlgEquiv.piCongrRight_apply_includeBlock {ι : Type*}
  {p : ι → Type*} [∀ i, Fintype (p i)] [DecidableEq ι]
  (f : Π i, Matrix (p i) (p i) ℂ ≃⋆ₐ[ℂ] Matrix (p i) (p i) ℂ)
  (i : ι) (x : Matrix (p i) (p i) ℂ) :
  (StarAlgEquiv.piCongrRight (fun a => f a)) (Matrix.includeBlock x)
    = Matrix.includeBlock ((f i) x) := by
  ext
  simp only [piCongrRight_apply, Matrix.includeBlock_apply]
  aesop

theorem Matrix.innerAutStarAlg_apply_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x y) = vecMulVec (U *ᵥ x) (Uᴴᵀ *ᵥ y) := by
  simp only [innerAutStarAlg_apply, Unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose]
  rw [← Matrix.mulVec_transpose]
  rfl

theorem Matrix.innerAutStarAlg_apply_vecMulVec_star {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x (star y))
    = vecMulVec (U *ᵥ x) (star (U *ᵥ y)) := by
  simp only [innerAutStarAlg_apply, Unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose, star_mulVec]

theorem Matrix.innerAutStarAlg_apply_star_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec (star x) y)
    = (vecMulVec (Uᴴᵀ *ᵥ x) (star (Uᴴᵀ *ᵥ y)))ᴴᵀ := by
  rw [innerAutStarAlg_apply_vecMulVec, vecMulVec_conj, star_star, star_mulVec, ← vecMul_transpose,
    conj_conjTranspose]

theorem Matrix.PosSemidef.eq_iff_sq_eq_sq {n : Type*} [Fintype n]
  [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) {B : Matrix n n ℂ}
  (hB : B.PosSemidef) :
    A ^ 2 = B ^ 2 ↔ A = B := by
  let : Algebra ℝ ℂ := RCLike.toNormedAlgebra.toAlgebra
  have : NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    ContinuousFunctionalCalculus.toNonUnital
  have : NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
    Matrix.instNonnegSpectrumClass (n := n) (𝕜 := ℂ)
  simpa [pow_two] using (CFC.mul_self_eq_mul_self_iff A B hA.nonneg hB.nonneg)

theorem unitary.mul_inj {A : Type*} [Monoid A] [StarMul A] (U : ↥(unitary A)) (x y : A) :
  ↑U * x = ↑U * y ↔ x = y := by
  rw [← Unitary.val_toUnits_apply]
  exact (Units.mul_right_inj (Unitary.toUnits U))

theorem orthogonalProjection'_bot {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] :
  orthogonalProjection' (⊥ : Submodule 𝕜 E) = 0 :=
by simp

omit [Fintype ι] [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)] in
lemma LinearMap.proj_apply_includeBlock
  (i j : ι) (x : Matrix (p j) (p j) ℂ) :
  LinearMap.proj (R := ℂ) i (Matrix.includeBlock (i := j) x) =
    if h : j = i then by rw [← h]; exact x else 0 :=
by simp [Matrix.includeBlock_apply]

theorem Matrix.trace_eq_linearMap_trace
  {n : Type*} [Fintype n] [DecidableEq n]
  (y : Matrix n n ℂ) :
  Matrix.trace y = LinearMap.trace ℂ (EuclideanSpace ℂ n)
    (Matrix.toEuclideanLin y) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ n)]
  simp only [Matrix.toLpLin_eq_toLin, LinearMap.toMatrix_toLin]

lemma Submodule.finrank_eq_iff_eq_top {K V : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {S : Submodule K V} :
  Module.finrank K ↥S = Module.finrank K V ↔ S = ⊤ := by
  refine ⟨Submodule.eq_top_of_finrank_eq, ?_⟩
  rintro rfl
  simp only [finrank_top]
