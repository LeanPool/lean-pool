/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import LeanPool.CCDN.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Bounded integral linear forms dual to independent integer rows.
A nonzero minor and its cofactors give the separation required in CCDN
Lemma 5.4, with the bound s! T^s for s+1 independent equations. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma integer_adjugate_entry_abs_le {s : ℕ}
    (M : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) (T : ℕ)
    (hM : ∀ i j, |M i j| ≤ (T : ℤ)) (i j : Fin (s + 1)) :
    |M.adjugate i j| ≤ (s.factorial : ℤ) * (T : ℤ) ^ s := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul]
  have hh := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := M.submatrix j.succAbove i.succAbove)
    (fun a b => hM (j.succAbove a) (i.succAbove b))
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh

/-- A full independent family admits simultaneous bounded integral dual
forms. -/
theorem exists_bounded_integer_dual_rows {s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin r) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (T : ℕ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) :
    ∃ D : ℤ, D ≠ 0 ∧
      |D| ≤ ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1) ∧
      ∃ b : Fin (s + 1) → Fin r → ℤ,
      (∀ i ℓ, ∑ j, A ℓ j * b i j = if ℓ = i then D else 0) ∧
      (∀ i j, |b i j| ≤ (s.factorial : ℤ) * (T : ℤ) ^ s) := by
  classical
  let AQ : Matrix (Fin (s + 1)) (Fin r) ℚ := Matrix.of (fun i j => (A i j : ℚ))
  obtain ⟨c, hc, hminor⟩ := Matrix.exists_det_submatrix_ne_zero_of_linearIndependent_row AQ hli
  let M := A.submatrix id c
  have hmap : (Int.castRingHom ℚ).mapMatrix M = AQ.submatrix id c := by
    ext i j
    rfl
  have hdet : M.det ≠ 0 := by
    intro hz
    have hh := congrArg (Int.castRingHom ℚ) hz
    rw [RingHom.map_det, hmap, map_zero] at hh
    exact hminor hh
  have hdetbound : |M.det| ≤ ((s + 1).factorial : ℤ) * (T : ℤ) ^ (s + 1) := by
    have hh := Matrix.det_le (abv := AbsoluteValue.abs) (A := M)
      (fun i j => hA i (c j))
    simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hh
  let b : Fin (s + 1) → Fin r → ℤ :=
    fun i j => ∑ k, if c k = j then M.adjugate k i else 0
  have hbimage (i k : Fin (s + 1)) : b i (c k) = M.adjugate k i := by
    simp only [b, hc.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hboutside (i : Fin (s + 1)) (j : Fin r) (hj : ¬∃ k, c k = j) :
      b i j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (fun he => hj ⟨k, he⟩)
  refine ⟨M.det, hdet, hdetbound, b, ?_, ?_⟩
  · intro i ℓ
    have hrow : (∑ j, A ℓ j * b i j) = ∑ k, M ℓ k * M.adjugate k i := by
      simp only [b, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        M, Matrix.submatrix_apply, id_eq]
    rw [hrow]
    have hh := congrArg (fun Q : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ => Q ℓ i)
      (Matrix.mul_adjugate M)
    simpa only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero] using hh
  · intro i j
    by_cases hj : ∃ k, c k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [hbimage]
      exact integer_adjugate_entry_abs_le M T (fun a b => hA a (c b)) k i
    · rw [hboutside i j hj, abs_zero]
      positivity

/-- A valid factorial cofactor bound for the separation conclusion of CCDN
Lemma 5.4. The different numerical constant printed in that lemma is refuted
in `CCDNPaper/Counterexample/RowSeparatorConstant.lean`. -/
theorem exists_bounded_row_separator {s r : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin r) ℤ)
    (hli : LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)))
    (T : ℕ) (hA : ∀ i j, |A i j| ≤ (T : ℤ)) (i : Fin (s + 1)) :
    ∃ b : Fin r → ℤ,
      (∑ j, A i j * b j) ≠ 0 ∧
      (∀ ℓ, ℓ ≠ i → ∑ j, A ℓ j * b j = 0) ∧
      (∀ j, |b j| ≤ (s.factorial : ℤ) * (T : ℤ) ^ s) := by
  obtain ⟨D, hD, _, b, hb, hbound⟩ := exists_bounded_integer_dual_rows A hli T hA
  refine ⟨b i, ?_, ?_, hbound i⟩
  · simpa only [hb, ite_true] using hD
  · intro ℓ hℓ
    simp only [hb, ite_eq_right hℓ]

end
end CCDN
