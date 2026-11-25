/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedMongeAmpere

/-!
# Congruence of the mixed coefficient

The permutation-sum mixed coefficient is multilinear in its matrix slots, its
value on rank-one inputs `uᵢ wᵢᵀ` is `det U · det W`, and consequently
`C(A H₁ B, …, A Hₙ B) = det A · det B · C(H₁, …, Hₙ)` for arbitrary square
matrices `A` and `B`. With `A = Jᵀ` and `B = JBar` this is the transformation
law of mixed Monge–Ampère densities under a holomorphic change of variables.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

open FirstPass FirstPass.MixedMongeAmpere Matrix

variable {n : ℕ}

/-- A unitary matrix with a prescribed unit first column. -/
theorem exists_unitary_col_zero {m : ℕ} (y : Fin (m + 1) → ℂ) (hy : star y ⬝ᵥ y = 1) :
    ∃ W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ i, W i 0 = y i := by
  classical
  set v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 y with hvdef
  have hv : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ => v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only [ite_true]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change y ⬝ᵥ star y = 1
    rw [dotProduct_comm]
    exact hy
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := fun _ => v) (s := {0})
  set s := EuclideanSpace.basisFun (Fin (m + 1)) ℂ
  refine ⟨s.toBasis.toMatrix b, s.toMatrix_orthonormalBasis_conjTranspose_mul_self b,
    s.toMatrix_orthonormalBasis_self_mul_conjTranspose b, fun i => ?_⟩
  rw [Module.Basis.toMatrix_apply, hb 0 rfl]
  simp [s, hvdef]

/-- The diagonal unit matrix `E_k = diag(e_k)`. -/
noncomputable def unitDiag (k : Fin n) : Matrix (Fin n) (Fin n) ℂ := diagonal (Pi.single k 1)

/-- Row extraction as a linear map. -/
def matrixRowLinear (j : Fin n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun A := A j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The mixed coefficient as a multilinear map of its slots. -/
def mixedCoefficientML : MultilinearMap (RingHom.id ℂ)
      (fun _ : Fin n ↦ Matrix (Fin n) (Fin n) ℂ) ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    (Matrix.detRowAlternating.toMultilinearMap.compLinearMap
      (fun j ↦ matrixRowLinear j)).domDomCongr σ

@[simp] theorem mixedCoefficientML_apply (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficientML H = mixedCoefficient H := by
  classical
  simp [mixedCoefficientML, mixedCoefficient, matrixRowLinear, Matrix.det]
  rfl

/-- Scaling each slot multiplies the mixed coefficient by the product of the scalars. -/
theorem mixedCoefficient_smul_family (c : Fin n → ℂ) (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun i => c i • H i) = (∏ i, c i) * mixedCoefficient H := by
  simpa only [mixedCoefficientML_apply, RingHom.id_apply, smul_eq_mul] using
    (mixedCoefficientML (n := n)).map_smul_univ c H

/-- **Rank-one inputs.** -/
theorem mixedCoefficient_vecMulVec' (u w : Fin n → Fin n → ℂ) :
    mixedCoefficient (fun i ↦ vecMulVec (u i) (w i)) =
      (Matrix.of fun i j ↦ u i j).det * (Matrix.of fun i j ↦ w i j).det := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ u i j
  set W : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ w i j
  have hterm (σ : Equiv.Perm (Fin n)) :
      Matrix.det (fun j k ↦ vecMulVec (u (σ j)) (w (σ j)) j k) =
        (∏ j, U (σ j) j) * ((σ.sign : ℂ) * W.det) := by
    have h1 : (fun j k ↦ vecMulVec (u (σ j)) (w (σ j)) j k) =
        Matrix.of fun j k ↦ U (σ j) j * W.submatrix σ id j k := by
      ext j k; simp [vecMulVec_apply, U, W]
    rw [h1, det_mul_column, det_permute]
  rw [mixedCoefficient]
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  rw [det_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp [Units.smul_def, mul_comm, U]

/-- **Congruence.** -/
theorem mixedCoefficient_mul_mul (A B : Matrix (Fin n) (Fin n) ℂ)
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    mixedCoefficient (fun i ↦ A * H i * B) = A.det * B.det * mixedCoefficient H := by
  classical
  have hdec (M : Matrix (Fin n) (Fin n) ℂ) :
      M = ∑ a, vecMulVec (Pi.single a 1) (M a) := by
    ext j k
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  have hL : (fun i ↦ A * H i * B) = fun i ↦ ∑ a, vecMulVec (A *ᵥ Pi.single a 1) (H i a ᵥ* B) := by
    funext i
    conv_lhs => rw [hdec (H i)]
    rw [Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [mul_vecMulVec, vecMulVec_mul]
  have hR : H = fun i ↦ ∑ a, vecMulVec (Pi.single a (1 : ℂ)) (H i a) := funext fun i ↦ hdec (H i)
  rw [← mixedCoefficientML_apply, hL, MultilinearMap.map_sum]
  conv_rhs => rw [← mixedCoefficientML_apply, hR, MultilinearMap.map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simp only [mixedCoefficientML_apply, mixedCoefficient_vecMulVec']
  have h1 : (Matrix.of fun i j ↦ (A *ᵥ Pi.single (r i) (1 : ℂ)) j) =
      (A * Matrix.of fun j i ↦ (Pi.single (r i) (1 : ℂ) : Fin n → ℂ) j)ᵀ := by
    ext i j
    simp [mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply]
  have h2 : (Matrix.of fun i j ↦ (H i (r i) ᵥ* B) j) = (Matrix.of fun i j ↦ H i (r i) j) * B := by
    ext i j
    simp [vecMul, dotProduct, Matrix.mul_apply]
  have h3 : (Matrix.of fun j i ↦ (Pi.single (r i) (1 : ℂ) : Fin n → ℂ) j) =
      (Matrix.of fun i j ↦ (Pi.single (r i) (1 : ℂ) : Fin n → ℂ) j)ᵀ := by
    ext i j; rfl
  rw [h1, h2, det_transpose, det_mul, det_mul, h3, det_transpose]
  ring

end SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
