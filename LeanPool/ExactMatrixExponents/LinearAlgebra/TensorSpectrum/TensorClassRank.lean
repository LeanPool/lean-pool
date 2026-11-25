/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.SpectralBooks.Tensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClass
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching

/-!
# Actual finite tensor rank

The natural tensor is the diagonal coefficient tensor. Its local restrictions
are exactly the tensors admitting the corresponding number of rank-one terms.
Every finite coefficient tensor has such a decomposition, obtained by expanding
its individual coefficients. Exact rank is therefore a genuine minimum.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum

variable {K : Type*} [CommSemiring K]
namespace CoefficientTensor

/-- The diagonal tensor with `n` independent scalar products. -/
def natTensor (n : ℕ) : Tensor K (Fin n) (Fin n) (Fin n) :=
  Tensor.diagonal (K := K) (Fin n)

theorem restrict_natTensor {X Y Z : Type*} (n : ℕ)
    (a : X → Fin n → K) (b : Y → Fin n → K) (c : Z → Fin n → K) :
    Tensor.restrict a b c (natTensor n) =
      fun x y z => ∑ i, a x i * b y i * c z i := by
  classical
  funext x y z
  simp [Tensor.restrict, natTensor, Tensor.diagonal, mul_ite, ite_and]

theorem rankAtMost_natTensor (n : ℕ) : Tensor.RankAtMost (natTensor (K := K) n) n := by
  simpa only [natTensor, Fintype.card_fin] using Tensor.diagonal_rankAtMost (K := K) (Fin n)

/-- This equivalence exposes all three local matrices of the restriction. -/
theorem rankAtMost_iff_natTensor_restricts {X Y Z : Type*}
    (T : Tensor K X Y Z) (n : ℕ) :
    Tensor.RankAtMost T n ↔ Restricts (natTensor n) T := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨fun x i => a i x, fun y i => b i y, fun z i => c i z, ?_⟩
    simpa only [restrict_natTensor, Tensor.rankOne] using h
  · intro h
    exact h.rankAtMost (rankAtMost_natTensor n)

/-- The diagonal tensor on a sum of dimensions separates into its two blocks
under the actual standard bijection of finite coordinate sets. -/
theorem natTensor_add_pullback (r s : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))
      finSumFinEquiv finSumFinEquiv (natTensor (K := K) (r + s)) =
      blockSum (natTensor r) (natTensor (K := K) s) := by
  funext x y z
  simp only [Tensor.pullback, natTensor, Tensor.diagonal, Equiv.apply_eq_iff_eq]
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp [blockSum, Tensor.diagonal]

theorem natTensor_add_restricts (r s : ℕ) :
    Restricts (natTensor (K := K) (r + s)) (blockSum (natTensor r) (natTensor (K := K) s)) := by
  have h := Restricts.pullback (natTensor (K := K) (r + s))
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) finSumFinEquiv finSumFinEquiv
  rwa [natTensor_add_pullback] at h

theorem rankAtMost_blockSum {X Y Z U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : Tensor.RankAtMost T r) (hS : Tensor.RankAtMost S s) :
    Tensor.RankAtMost (blockSum T S) (r + s) := by
  apply (rankAtMost_iff_natTensor_restricts (blockSum T S) (r + s)).mpr
  exact (natTensor_add_restricts r s).trans
    (((rankAtMost_iff_natTensor_restricts T r).mp hT).blockSum
      ((rankAtMost_iff_natTensor_restricts S s).mp hS))

variable {X Y Z U V W : Type*}

section Coordinates

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Selecting the first coordinates realizes the usual comparison of diagonal
tensors by actual local coefficient matrices. -/
theorem natTensor_restricts_of_le {r s : ℕ} (h : r ≤ s) :
    Restricts (natTensor (K := K) s) (natTensor r) := by
  have hp := Restricts.pullback (natTensor (K := K) s)
    (Fin.castLE h) (Fin.castLE h) (Fin.castLE h)
  have heq : Tensor.pullback (Fin.castLE h) (Fin.castLE h) (Fin.castLE h)
      (natTensor (K := K) s) = natTensor r := by
    funext x y z
    simp [Tensor.pullback, natTensor, Tensor.diagonal, Fin.ext_iff]
  rwa [heq] at hp

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rankAtMost_mono {T : Tensor K X Y Z} {r s : ℕ}
    (hT : Tensor.RankAtMost T r) (hrs : r ≤ s) : Tensor.RankAtMost T s := by
  apply (rankAtMost_iff_natTensor_restricts T s).mpr
  exact (natTensor_restricts_of_le hrs).trans
    ((rankAtMost_iff_natTensor_restricts T r).mp hT)

theorem unit_restricts_natTensor_one {T : Tensor K X Y Z} (hT : ∃ x y z, T x y z = 1) :
    Restricts T (natTensor 1) := by
  classical
  obtain ⟨x, y, z, hxyz⟩ := hT
  refine ⟨fun _ i => if i = x then 1 else 0,
    fun _ j => if j = y then 1 else 0,
    fun _ k => if k = z then 1 else 0, ?_⟩
  funext i j k
  have hij : i = j := Subsingleton.elim _ _
  have hik : i = k := Subsingleton.elim _ _
  subst j
  subst k
  simp [Tensor.restrict, natTensor, Tensor.diagonal, ite_mul, mul_ite, hxyz]

end Coordinates

section Rank

variable [Finite X] [Finite Y]

/-- The least size of an actual rank-one decomposition. -/
noncomputable def rank (T : Tensor K X Y Z) : ℕ := SpectralBooks.tensorRank T

theorem rank_spec (T : Tensor K X Y Z) : Tensor.RankAtMost T (rank T) :=
  SpectralBooks.rankAtMost_tensorRank T

theorem rank_le_iff (T : Tensor K X Y Z) (n : ℕ) :
    rank T ≤ n ↔ Tensor.RankAtMost T n :=
  ⟨rankAtMost_mono (rank_spec T), SpectralBooks.tensorRank_le_of_rankAtMost⟩

end Rank

theorem rank_mono [Fintype X] [Fintype Y] [Fintype Z] [Finite U] [Finite V]
    {T : Tensor K X Y Z} {S : Tensor K U V W} (h : Restricts T S) :
    rank S ≤ rank T :=
  (rank_le_iff S _).mpr (h.rankAtMost (rank_spec T))

theorem rank_product_le [Finite X] [Finite Y] [Finite U] [Finite V]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    rank (Tensor.product T S) ≤ rank T * rank S :=
  (rank_le_iff _ _).mpr ((rank_spec T).product (rank_spec S))

theorem rank_blockSum_le [Finite X] [Finite Y] [Finite U] [Finite V]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    rank (blockSum T S) ≤ rank T + rank S :=
  (rank_le_iff _ _).mpr (rankAtMost_blockSum (rank_spec T) (rank_spec S))

theorem rank_eq_zero_iff [Finite X] [Finite Y] (T : Tensor K X Y Z) : rank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr := rank_spec T
    rw [h] at hr
    rcases hr with ⟨a, b, c, heq⟩
    funext x y z
    simpa using congrFun (congrFun (congrFun heq x) y) z
  · rintro rfl
    exact Nat.eq_zero_of_le_zero
      ((rank_le_iff (0 : Tensor K X Y Z) 0).mpr Tensor.rankAtMost_zero)

end CoefficientTensor

namespace TensorRep

/-- Uses `CoefficientTensor.rank T.coeff` as the representation. -/
noncomputable def rank (T : (TensorRep K)) : ℕ := CoefficientTensor.rank T.coeff

theorem Restricts.rank_le {A B : (TensorRep K)} (h : Restricts A B) : rank B ≤ rank A :=
  CoefficientTensor.rank_mono h

theorem Equivalent.rank_eq {A B : (TensorRep K)} (h : Equivalent A B) : rank A = rank B :=
  Nat.le_antisymm (Restricts.rank_le h.2) (Restricts.rank_le h.1)

end TensorRep

namespace TensorClass

theorem ofTensor_natTensor_add (r s : ℕ) :
    ofTensor (CoefficientTensor.natTensor (K := K) (r + s)) =
      ofTensor (Tensor.blockSum
        (CoefficientTensor.natTensor r) (CoefficientTensor.natTensor s)) := by
  have h := ofTensor_pullback_equiv (CoefficientTensor.natTensor (K := K) (r + s))
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) finSumFinEquiv finSumFinEquiv
  rw [CoefficientTensor.natTensor_add_pullback] at h
  exact h.symm

theorem ofTensor_natTensor_one :
    ofTensor (CoefficientTensor.natTensor 1) =
      ofTensor (fun (_ _ _ : PUnit) => (1 : K)) := by
  let e : PUnit ≃ Fin 1 := Equiv.ofUnique _ _
  have h := ofTensor_pullback_equiv (CoefficientTensor.natTensor (K := K) 1) e e e
  have heq : Tensor.pullback e e e (CoefficientTensor.natTensor 1) =
      fun (_ _ _ : PUnit) => (1 : K) := by
    funext x y z
    have hxy : x = y := Subsingleton.elim _ _
    have hxz : x = z := Subsingleton.elim _ _
    subst y
    subst z
    simp [Tensor.pullback, CoefficientTensor.natTensor, Tensor.diagonal]
  rw [heq] at h
  exact h.symm

theorem ofTensor_natTensor_zero :
    ofTensor (CoefficientTensor.natTensor 0) =
      ofTensor (0 : Tensor K Empty Empty Empty) := by
  apply ofTensor_eq
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x
    exact Empty.elim x
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x
    exact Fin.elim0 x

/-- Exact rank is invariant under mutual local restriction. -/
noncomputable def rank : (TensorClass K) → ℕ :=
  Quotient.lift TensorRep.rank (fun _ _ h => TensorRep.Equivalent.rank_eq h)

@[simp] theorem rank_ofRep (T : (TensorRep K)) : rank (ofRep T) = T.rank := rfl

theorem rank_mono {A B : (TensorClass K)} (h : A ≤ B) : rank A ≤ rank B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      exact TensorRep.Restricts.rank_le h

theorem rank_ofTensor {X Y Z : Type*} (T : Tensor K X Y Z) [Fintype X] [Fintype Y] [Fintype Z] :
    rank (ofTensor T) = CoefficientTensor.rank T := by
  apply Nat.le_antisymm
  · exact CoefficientTensor.rank_mono (TensorRep.restricts_ofTensor T)
  · exact CoefficientTensor.rank_mono (TensorRep.ofTensor_restricts T)

end TensorClass
end MatrixMultiplicationAllFields.TensorSpectrum
