/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.OneSlice

/-! # Integer slices as uniform averages over actual Boolean vertices -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators

/-- The subset indicator, elaborated in the concrete finite-set type. -/
noncomputable def booleanVertexIndicator {n : ℕ} (S T : Finset (Fin n)) : ℝ :=
  if S ⊆ T then 1 else 0

/-- Evaluate a square-free monomial at the vertex whose one-coordinates form `T`. -/
noncomputable def booleanVertexMonoid {n : ℕ} (T : Finset (Fin n)) :
    BooleanMonomial n →* ℝ where
  toFun S := booleanVertexIndicator S T
  map_one' := by
    change (if (∅ : Finset (Fin n)) ⊆ T then (1 : ℝ) else 0) = 1
    simp
  map_mul' S U := by
    classical
    let s : Finset (Fin n) := S
    let u : Finset (Fin n) := U
    change (if s ∪ u ⊆ T then (1 : ℝ) else 0) =
      (if s ⊆ T then 1 else 0) * (if u ⊆ T then 1 else 0)
    by_cases hs : s ⊆ T <;> by_cases hu : u ⊆ T <;> simp [Finset.union_subset_iff, hs, hu]

/-- Evaluation at an arbitrary Boolean vertex. -/
noncomputable def booleanVertexEval {n : ℕ} (T : Finset (Fin n)) :
    BooleanPolynomial n →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ ℝ (BooleanMonomial n) (booleanVertexMonoid T)

theorem booleanVertexEval_monomial {n : ℕ} (T S : Finset (Fin n)) (a : ℝ) :
    booleanVertexEval T (booleanMonomial S a) = if S ⊆ T then a else 0 := by
  classical
  rw [booleanVertexEval, booleanMonomial, MonoidAlgebra.lift_single]
  change a * (if S ⊆ T then 1 else 0) = _
  split_ifs <;> simp

/-- The uniform average over all vertices of Hamming weight `k`. -/
noncomputable def integerSliceAverage (n k : ℕ) : BooleanPolynomial n →ₗ[ℝ] ℝ :=
  (n.choose k : ℝ)⁻¹ •
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (booleanVertexEval T).toLinearMap

/-- Counting subsets containing a fixed set gives the falling-factorial slice moment. -/
theorem choose_ratio_eq_sliceMoment {n k r : ℕ} (hkn : k ≤ n) (hrn : r ≤ n) (hrk : r ≤ k) :
    ((n - r).choose (k - r) : ℝ) / (n.choose k : ℝ) = sliceMoment n (k : ℝ) r := by
  have hn : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  have hr : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hrn).ne'
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  have hc : (n.choose k : ℝ) * (k.choose r : ℝ) =
      (n.choose r : ℝ) * ((n - r).choose (k - r) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) hrk)
  rw [sliceMoment, falling_natCast, falling_natCast,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [mul_div_mul_left _ _ hf]
  field_simp
  simpa only [mul_comm] using hc.symm

/-- The uniform integer-slice average has the prescribed monomial moments. -/
theorem integerSliceAverage_monomial {n k : ℕ} (hkn : k ≤ n)
    (S : Finset (Fin n)) (a : ℝ) :
    integerSliceAverage n k (booleanMonomial S a) = a * sliceMoment n (k : ℝ) S.card := by
  classical
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  simp only [integerSliceAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, booleanVertexEval_monomial, smul_eq_mul]
  by_cases hSk : S.card ≤ k
  · have hc := Finset.card_filter_powersetCard_subset S (Finset.univ : Finset (Fin n)) k
      (Finset.subset_univ _) hSk
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [hc]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← choose_ratio_eq_sliceMoment hkn hSn hSk]
    ring
  · have hz (T : Finset (Fin n)) (hT : T ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
        ¬ S ⊆ T := by
      intro hST
      have hcard := Finset.card_le_card hST
      have hTk := (Finset.mem_powersetCard.mp hT).2
      omega
    rw [Finset.sum_eq_zero (by intro T hT; simp [hz T hT]), mul_zero]
    have hf : falling (k : ℝ) S.card = 0 := by
      rw [falling_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero]
    simp [sliceMoment, hf]

/-- At every integer slice the interpolated functional is the actual uniform vertex average. -/
theorem sliceFunctional_integer_average {n k : ℕ} (hkn : k ≤ n) (f : BooleanPolynomial n) :
    sliceFunctional n (k : ℝ) f = integerSliceAverage n k f := by
  classical
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [sliceFunctional_monomial, integerSliceAverage_monomial hkn]

/-- Every integer slice is positive on squares of arbitrary degree. -/
theorem sliceFunctional_integer_square_nonneg {n k : ℕ} (hkn : k ≤ n)
    (f : BooleanPolynomial n) : 0 ≤ sliceFunctional n (k : ℝ) (f ^ 2) := by
  classical
  rw [sliceFunctional_integer_average hkn]
  simp only [integerSliceAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, map_pow, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun T _ ↦ sq_nonneg _))

end NoncommutativeAMGM
