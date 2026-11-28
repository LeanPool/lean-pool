/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Poly
public import LeanPool.ReadL1.Projection
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# From coordinates back to polynomials

Śliwa's basis polynomials `fᵢ` (`ReadL1.fPoly`) give the inverse of `ReadL1.toCoord`: a
finitely supported sequence `g` goes to `∑ gᵢ fᵢ` (`ReadL1.fromCoord`), with
`toCoord (fromCoord g) = g` (`ReadL1.toCoord_fromCoord`) and `fromCoord (xⁱ) = xⁱ`
(`ReadL1.fromCoord_xPow`).

Two support facts about the coordinates of `xⁱ`, used in Lemma 5:

* they vanish above `i` (`ReadL1.xPow_apply_eq_zero`), so `Fₙ` is spanned by `f₀, …, fₙ`;
* for `vₙ₋₁ < j ≤ (n - 1)aₙ` they vanish on `(vₙ₋₂, vₙ₋₁]` (`ReadL1.xPow_apply_gap`): the
  recursion on an `I` block steps down by `aₙ` and jumps from `Iₙ,₁` straight below `vₙ₋₂`.
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/- ### The basis polynomials -/

/-- Śliwa's basis polynomial `fᵢ`. -/
noncomputable def fPoly (d : ℕ → ℕ) (i : ℕ) : ℂ[X] :=
  if i = 0 then 1 else
    match (block d i).kind with
    | .J => C (weight (seqA d (block d i).n) (block d i).r i : ℂ) * X ^ i
    | .I => C (seqA d ((block d i).n - (block d i).r) : ℂ) *
        (X ^ i - X ^ (i - seqA d (block d i).n))
    | .L => C (weight (seqB d (block d i).n) (block d i).r i : ℂ) * X ^ i
    | .K => X ^ i - C (seqB d (block d i).n : ℂ) * X ^ (i - seqB d (block d i).n)

lemma fPoly_zero : fPoly d 0 = 1 := by simp [fPoly]

lemma fPoly_of_J (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .J) :
    fPoly d i = C (weight (seqA d B.n) B.r i : ℂ) * X ^ i := by
  have hi := Block.one_le_of_mem h hB
  rw [fPoly, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma fPoly_of_I (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .I) :
    fPoly d i = C (seqA d (B.n - B.r) : ℂ) * (X ^ i - X ^ (i - seqA d B.n)) := by
  have hi := Block.one_le_of_mem h hB
  rw [fPoly, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma fPoly_of_L (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .L) :
    fPoly d i = C (weight (seqB d B.n) B.r i : ℂ) * X ^ i := by
  have hi := Block.one_le_of_mem h hB
  rw [fPoly, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma fPoly_of_K (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .K) :
    fPoly d i = X ^ i - C (seqB d B.n : ℂ) * X ^ (i - seqB d B.n) := by
  have hi := Block.one_le_of_mem h hB
  rw [fPoly, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma toCoord_C_mul (c : ℂ) (p : ℂ[X]) : toCoord d (C c * p) = c • toCoord d p := by
  rw [← smul_eq_C_mul, map_smul]

/-- **The coordinates of `fᵢ` are `δᵢ`.** -/
lemma toCoord_fPoly (h : PartitionHyp d) (i : ℕ) : toCoord d (fPoly d i) = single i 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [fPoly_zero, ← pow_zero X, toCoord_X_pow]; simp [xPow]
  have hB := block_mem h hi
  rcases hbl : block d i with ⟨n, r, k⟩
  rw [hbl] at hB
  cases k with
  | J => rw [fPoly_of_J h hB rfl, toCoord_C_mul, toCoord_X_pow, ← single_eq_of_J h hB rfl]
  | I => rw [fPoly_of_I h hB rfl, toCoord_C_mul, map_sub, toCoord_X_pow, toCoord_X_pow,
      ← single_eq_of_I h hB rfl]
  | L => rw [fPoly_of_L h hB rfl, toCoord_C_mul, toCoord_X_pow, ← single_eq_of_L h hB rfl]
  | K => rw [fPoly_of_K h hB rfl, map_sub, toCoord_C_mul, toCoord_X_pow, toCoord_X_pow,
      ← single_eq_of_K h hB rfl]

lemma natDegree_fPoly_le (h : PartitionHyp d) (i : ℕ) : (fPoly d i).natDegree ≤ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [fPoly_zero, natDegree_one]
  have hB := block_mem h hi
  rcases hbl : block d i with ⟨n, r, k⟩
  rw [hbl] at hB
  have hXs : ∀ j, (X ^ i - X ^ (i - j) : ℂ[X]).natDegree ≤ i := fun j ↦
    (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le _)
      ((natDegree_X_pow_le _).trans (Nat.sub_le _ _)))
  cases k with
  | J => rw [fPoly_of_J h hB rfl]; exact natDegree_C_mul_X_pow_le _ _
  | I => rw [fPoly_of_I h hB rfl]; exact (natDegree_C_mul_le _ _).trans (hXs _)
  | L => rw [fPoly_of_L h hB rfl]; exact natDegree_C_mul_X_pow_le _ _
  | K =>
    rw [fPoly_of_K h hB rfl]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le _)
      ((natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)))

/- ### The inverse map -/

/-- A finitely supported sequence of coordinates, as a polynomial: `g ↦ ∑ gᵢ fᵢ`. -/
noncomputable def fromCoord (d : ℕ → ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ[X] := linearCombination ℂ (fPoly d)

lemma fromCoord_single (i : ℕ) (c : ℂ) : fromCoord d (single i c) = c • fPoly d i := by
  simp [fromCoord]

lemma toCoord_fromCoord (h : PartitionHyp d) (g : ℕ →₀ ℂ) : toCoord d (fromCoord d g) = g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g k hg hk => rw [map_add, map_add, hg, hk]
  | single i c => rw [fromCoord_single, map_smul, toCoord_fPoly h, smul_single, smul_eq_mul,
      mul_one]

/-- `xⁱ`, written in coordinates and read back, is `xⁱ`. -/
lemma fromCoord_xPow (h : PartitionHyp d) (i : ℕ) : fromCoord d (xPow d i) = X ^ i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [xPow, fromCoord_single, fPoly_zero]
  have hB := block_mem h hi
  rcases hbl : block d i with ⟨n, r, k⟩
  rw [hbl] at hB
  have ha : 1 ≤ seqA d n := h.one_le_a n
  have hb : 0 < seqB d n := lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b n)
  cases k with
  | J =>
    rw [xPow_of_J h hB rfl, map_smul, fromCoord_single, one_smul, fPoly_of_J h hB rfl,
      smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (weight_ne_zero _ _ _), C_1, one_mul]
  | I =>
    have ha' : (seqA d (n - r) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h.one_le_a _))
    rw [xPow_of_I h hB rfl, map_add, map_smul, fromCoord_single, one_smul, fPoly_of_I h hB rfl,
      ih (i - seqA d n) (by omega), smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha', C_1,
      one_mul,
      sub_add_cancel]
  | L =>
    rw [xPow_of_L h hB rfl, map_smul, fromCoord_single, one_smul, fPoly_of_L h hB rfl,
      smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (weight_ne_zero _ _ _), C_1, one_mul]
  | K =>
    rw [xPow_of_K h hB rfl, map_add, map_smul, fromCoord_single, one_smul, fPoly_of_K h hB rfl,
      ih (i - seqB d n) (by omega), smul_eq_C_mul, sub_add_cancel]

lemma natDegree_fromCoord_le (h : PartitionHyp d) {g : ℕ →₀ ℂ} {N : ℕ}
    (hg : ∀ j ∈ g.support, j ≤ N) : (fromCoord d g).natDegree ≤ N := by
  rw [fromCoord, linearCombination_apply, Finsupp.sum]
  exact natDegree_sum_le_of_forall_le _ _ fun j hj ↦
    (natDegree_smul_le _ _).trans ((natDegree_fPoly_le h j).trans (hg j hj))

/- ### Where the coordinates of `xⁱ` vanish -/

/-- **The coordinates of `xⁱ` vanish above `i`.** -/
lemma xPow_apply_eq_zero (h : PartitionHyp d) {i j : ℕ} (hij : i < j) : xPow d i j = 0 := by
  induction i using Nat.strong_induction_on generalizing j with
  | _ i ih =>
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [xPow, show (0 : ℕ) ≠ j by omega]
  have hB := block_mem h hi
  rcases hbl : block d i with ⟨n, r, k⟩
  rw [hbl] at hB
  have ha : 1 ≤ seqA d n := h.one_le_a n
  have hb : 0 < seqB d n := lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b n)
  cases k with
  | J => simp [xPow_of_J h hB rfl, show i ≠ j by omega]
  | I =>
    rw [xPow_of_I h hB rfl]
    simp [show i ≠ j by omega, ih _ (show i - seqA d n < i by omega)
      (show i - seqA d n < j by omega)]
  | L => simp [xPow_of_L h hB rfl, show i ≠ j by omega]
  | K =>
    rw [xPow_of_K h hB rfl]
    simp [show i ≠ j by omega, ih _ (show i - seqB d n < i by omega)
      (show i - seqB d n < j by omega)]

/-- **The gap**: for `vₙ₋₁ < j ≤ (n - 1)aₙ`, the coordinates of `xʲ` vanish on `(vₙ₋₂, vₙ₋₁]`. -/
lemma xPow_apply_gap (h : PartitionHyp d) {n : ℕ} (hn : 2 ≤ n) {i : ℕ}
    (hi1 : seqV d (n - 2) < i) (hi2 : i ≤ seqV d (n - 1)) :
    ∀ j, seqV d (n - 1) < j → j ≤ (n - 1) * seqA d n → xPow d j i = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hj2
  have hvn : (n - 1) * seqA d n ≤ seqV d n := by
    unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hlev := block_level h (m := n - 1) (i := j) (by omega) hj1
    (by rw [show n - 1 + 1 = n by omega]; omega)
  have hB := block_mem h (i := j) (by omega)
  rcases hbl : block d j with ⟨n', r, k⟩
  rw [hbl] at hB hlev
  dsimp only at hlev
  rw [show n' = n by omega] at hB
  have ha : 1 ≤ seqA d n := h.one_le_a n
  have hab := h.a_lt_b n
  have hn1 : (n - 1) * seqA d n = (n - 2) * seqA d n + seqA d n := by
    rw [show n - 1 = n - 2 + 1 by omega, add_one_mul]
  cases k with
  | J => simp [xPow_of_J h hB rfl, show j ≠ i by omega]
  | I =>
    obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
    dsimp only at hr1 hrn hlo hhi
    rw [xPow_of_I h hB rfl]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
      ite_eq_right (show ¬ j = i by omega), smul_zero, zero_add]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : (r' + 1) * seqA d n = r' * seqA d n + seqA d n := add_one_mul _ _
    rcases Nat.eq_zero_or_pos r' with rfl | hr'0
    · -- `j ∈ Iₙ,₁`: `j - aₙ ≤ vₙ₋₂ < i`.
      rw [show n - (0 + 1) - 1 = n - 2 by omega] at hhi
      exact xPow_apply_eq_zero h (by omega)
    · -- `j ∈ Iₙ,ᵣ` with `r ≥ 2`: `j - aₙ` is still in `(vₙ₋₁, (n - 1)aₙ]`.
      have hva := h.v_lt_a n (n - 1) (by omega)
      have hle : seqA d n ≤ r' * seqA d n := Nat.le_mul_of_pos_left _ hr'0
      exact ih _ (by omega) (by omega) (by omega)
  | L =>
    obtain ⟨-, -, hlo, -⟩ := hB
    dsimp only at hlo
    omega
  | K =>
    obtain ⟨hr1, -, hlo, -⟩ := hB
    dsimp only at hr1 hlo
    have : seqA d n + seqB d n ≤ r * (seqA d n + seqB d n) := Nat.le_mul_of_pos_left _ hr1
    omega

end ReadL1
