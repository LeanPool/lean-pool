/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
public import Mathlib.Basic.Real.Basic

/-!
# Polynomial families, level expansions, and disjoint digit alphabets
-/

@[expose] public section

open Finset Polynomial
open scoped BigOperators

namespace Autoconvolutions.Construction

/-- The polynomial whose coefficients will be the step heights. -/
noncomputable def family (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) (n K : ℕ) :
    Polynomial ℝ :=
  ∑ i ∈ range (K + 1), U ^ (n - i) * V ^ (n + i) * P i

/-- The part of level s supported on the higher base - D digits. -/
noncomputable def level (U V : Polynomial ℝ) (n s : ℕ) : Polynomial ℝ :=
  U ^ (2 * n - s) * V ^ (2 * n + s)

/-- The truncated coefficient convolution at level s. -/
noncomputable def block (P : ℕ → Polynomial ℝ) (K s : ℕ) : Polynomial ℝ :=
  ∑ ij ∈ (antidiagonal s).filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K), P ij.1 * P ij.2

/-- Group the ordered pairs in the square by the sum of their two levels.
All subtractions are in ℕ. The bound K ≤ n is what makes the power identity valid. -/
theorem family_sq (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ} (hK : K ≤ n) :
    family P U V n K ^ 2 = ∑ s ∈ range (2 * K + 1), level U V n s * block P K s := by
  classical
  let I := range (K + 1)
  let t (i : ℕ) := U ^ (n - i) * V ^ (n + i) * P i
  let S := I ×ˢ I
  have hmap : ∀ ij ∈ S, ij.1 + ij.2 ∈ range (2 * K + 1) := by
    intro ⟨i,j⟩ hij
    simp only [S, I, mem_product, mem_range] at hij ⊢
    omega
  have hfiber (s : ℕ) :
      S.filter (fun ij => ij.1 + ij.2 = s) =
        (antidiagonal s).filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K) := by
    ext ⟨i,j⟩
    simp only [S, I, mem_filter, mem_product, mem_range, mem_antidiagonal]
    omega
  change (∑ i ∈ I, t i) ^ 2 = _
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product' I I (fun i j => t i * t j)]
  change ∑ ij ∈ S, t ij.1 * t ij.2 = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro s _
  rw [hfiber, block, Finset.mul_sum]
  apply sum_congr rfl
  intro ⟨i,j⟩ hij
  simp only [mem_filter, mem_antidiagonal] at hij
  have hU : (n - i) + (n - j) = 2 * n - s := by omega
  have hV : (n + i) + (n + j) = 2 * n + s := by omega
  dsimp [t, level]
  rw [← hU, ← hV, pow_add, pow_add]
  ring

/-- Geometric weights from the relative sizes of the two digit alphabets. -/
theorem weight_eq (r b : ℝ) (hr : r ≠ 0) {m i : ℕ} (hi : i ≤ m) :
    r ^ (m - i) * b ^ (m + i) = (r * b) ^ m * (b / r) ^ i := by
  rw [div_pow, mul_pow, pow_add]
  field_simp
  have hpow : r ^ (m - i) * r ^ i = r ^ m := by rw [← pow_add, Nat.sub_add_cancel hi]
  linear_combination b ^ m * b ^ i * hpow

theorem eval_family_one (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) {n K : ℕ}
    (hK : K ≤ n) (hP : ∀ i, (P i).eval 1 = 1) (hU : U.eval 1 ≠ 0) :
    (family P U V n K).eval 1 =
      (U.eval 1 * V.eval 1) ^ n * ∑ i ∈ range (K + 1), (V.eval 1 / U.eval 1) ^ i := by
  classical
  simp only [family, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    hP, mul_one, Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  apply weight_eq _ _ hU
  exact Nat.le_trans (Nat.le_of_lt_succ (mem_range.mp hi)) hK

/-- Coefficientwise nonnegativity is preserved under multiplication. -/
theorem mul_nonneg_coeff {U V : Polynomial ℝ}
    (hU : ∀ k, 0 ≤ U.coeff k) (hV : ∀ k, 0 ≤ V.coeff k) (k : ℕ) :
    0 ≤ (U * V).coeff k := by
  rw [coeff_mul]
  exact sum_nonneg fun ij _ => mul_nonneg (hU ij.1) (hV ij.2)

theorem pow_nonneg_coeff {U : Polynomial ℝ} (hU : ∀ k, 0 ≤ U.coeff k) (n k : ℕ) :
    0 ≤ (U ^ n).coeff k := by
  induction n generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split <;> simp
  | succ n ih => rw [pow_succ]; exact mul_nonneg_coeff ih hU k

theorem family_nonneg_coeff (P : ℕ → Polynomial ℝ) {U V : Polynomial ℝ}
    (hP : ∀ i k, 0 ≤ (P i).coeff k) (hU : ∀ k, 0 ≤ U.coeff k)
    (hV : ∀ k, 0 ≤ V.coeff k) (n K k : ℕ) : 0 ≤ (family P U V n K).coeff k := by
  rw [family, finsetSum_coeff]
  apply sum_nonneg
  intro i _
  exact mul_nonneg_coeff (mul_nonneg_coeff (pow_nonneg_coeff hU _) (pow_nonneg_coeff hV _)) (hP i) k

/-- Zero - based higher - digit indices for the paper's positions 1,3,...,2r - 1.
The units digit has its own role in the construction. -/
def oddAlphabet (r : ℕ) : Finset (Fin (2 * r)) :=
  univ.map (⟨fun i : Fin r => ⟨2 * i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩ : Fin r ↪ Fin (2 * r))

/-- Zero - based indices for the even powers 2,4,...,2b. -/
def evenAlphabet (r b : ℕ) (hb : b ≤ r) : Finset (Fin (2 * r)) :=
  univ.map (⟨fun i : Fin b => ⟨2 * i.val + 1, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩ : Fin b ↪ Fin (2 * r))

@[simp] theorem card_oddAlphabet (r : ℕ) : (oddAlphabet r).card = r := by simp [oddAlphabet]

@[simp] theorem card_evenAlphabet (r b : ℕ) (hb : b ≤ r) : (evenAlphabet r b hb).card = b := by
  simp [evenAlphabet]

theorem disjoint_alphabets (r b : ℕ) (hb : b ≤ r) :
    Disjoint (oddAlphabet r) (evenAlphabet r b hb) := by
  apply Finset.disjoint_left.mpr
  intro a ha ha'
  obtain ⟨i, _, hi⟩ := mem_map.mp ha
  obtain ⟨j, _, hj⟩ := mem_map.mp ha'
  have := congrArg Fin.val (hi.trans hj.symm)
  dsimp at this
  omega

end Autoconvolutions.Construction
