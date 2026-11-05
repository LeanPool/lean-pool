/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/RankExponent.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed; docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatMul
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation


open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Finite X] [Finite Y] [Finite Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype Z := Fintype.ofFinite Z
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite coefficient tensor over `K`. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

variable (K) in
/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (n : ℕ) : ℕ := exactRank (Tensor.matMul K n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Tensor.matMul K n n n) (exactMatrixRank K n) :=
  exactRank_spec _

/-- The ordinary scalar multiplication algorithm uses `n³` simple tensors. -/
theorem matrixMultiplication_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Tensor.matMul K n n n) (n ^ 3) := by
  classical
  let a : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p x => if x = (p.1, p.2.1) then 1 else 0
  let b : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p y => if y = (p.2.1, p.2.2) then 1 else 0
  let c : Fin n × Fin n × Fin n → Fin n × Fin n → K :=
    fun p z => if z = (p.2.2, p.1) then 1 else 0
  have heq : Tensor.matMul K n n n =
      fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Tensor.matMul,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite]
    split_ifs <;> simp_all
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne a b c using 1
  simp [Fintype.card_prod, pow_succ, Nat.mul_assoc]

theorem exactMatrixRank_upper (n : ℕ) : exactMatrixRank K n ≤ n ^ 3 :=
  exactRank_le (matrixMultiplication_rankAtMost_cubic n)

/-- An identity minor of the output flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Tensor.matMul K n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have hminor : ∀ i k : Fin n × Fin n,
      Tensor.matMul K n n n (i.2, j) (j, i.1) k =
        if i = k then 1 else 0 := by
    intro i k
    simp [Tensor.matMul, Prod.ext_iff, eq_comm]
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j))
    (fun i : Fin n × Fin n => (j, i.1)) id hminor
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank K n :=
  matrixMultiplication_rank_lower hn (exactMatrixRank_spec n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < exactMatrixRank K n :=
  lt_of_lt_of_le (pow_pos hn 2) (exactMatrixRank_lower hn)

@[simp] theorem exactMatrixRank_zero : exactMatrixRank K 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using exactMatrixRank_upper 0)

@[simp] theorem exactMatrixRank_one : exactMatrixRank K 1 = 1 := by
  apply le_antisymm
  · simpa using exactMatrixRank_upper 1
  · simpa using exactMatrixRank_lower (n := 1) zero_lt_one

variable (K) in
/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank K n)}

variable (K) in
/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent : ℝ := sInf (exactRankExponentSet K)

theorem exactRankExponentSet_nonempty : (exactRankExponentSet K).Nonempty :=
  ⟨Real.logb 2 (exactMatrixRank K 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank K n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank K n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactMatrixRank_logb_upper {n : ℕ} (hn : 2 ≤ n) :
    Real.logb n (exactMatrixRank K n) ≤ 3 := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank K n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.logb_le_iff_le_rpow hn1 hr).mpr
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast exactMatrixRank_upper n

theorem exactRankExponentSet_bddBelow : BddBelow (exactRankExponentSet K) := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact exactMatrixRank_logb_lower hn

theorem exactRankExponent_lower : 2 ≤ exactRankExponent K :=
  le_csInf exactRankExponentSet_nonempty (by
    rintro τ ⟨n, hn, rfl⟩
    exact exactMatrixRank_logb_lower hn)

theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    exactRankExponent K ≤ Real.logb n (exactMatrixRank K n) :=
  csInf_le exactRankExponentSet_bddBelow ⟨n, hn, rfl⟩

theorem exactRankExponent_upper : exactRankExponent K ≤ 3 :=
  (exactRankExponent_le_logb (n := 2) le_rfl).trans
    (exactMatrixRank_logb_upper (n := 2) le_rfl)

/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ exactRankExponent K ≤ exactMatrixRank K n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank K n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp (exactRankExponent_le_logb hn)

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent K ≤ exactMatrixRank K n := by
  by_cases hn2 : 2 ≤ n
  · exact exactMatrixRank_rpow_lower hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent K < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank K n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank K n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ

/-- Finite decompositions approximate the exact-rank exponent with any positive slack. -/
theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Tensor.matMul K n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ (exactRankExponent K + ε) := by
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (K := K) (lt_add_of_pos_right _ hε)
  exact ⟨n, exactMatrixRank K n, hn, exactMatrixRank_spec n, hR.le⟩

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
