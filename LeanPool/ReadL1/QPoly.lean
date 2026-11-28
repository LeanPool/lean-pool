/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Coord
public import LeanPool.ReadL1.Lemma4
public import LeanPool.ReadL1.Lemma6
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# `Qₘ e` as a polynomial

Śliwa treats `Qₘ e` as a polynomial of degree at most `(m - 1)aₘ` and takes its coefficient
norm. Here: `Qₘ fₗ` as a polynomial (`ReadL1.qPolyBasis`); its `j`-th coefficient, extended to ℓ¹
as the functional `e ↦ ∑ₗ eₗ (Qₘ fₗ)ⱼ` (`ReadL1.qCoeffCLM`); and the polynomial with those
coefficients (`ReadL1.qPoly`), whose coordinates are `Qₘ e` (`ReadL1.toL1_toCoord_qPoly`).
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

lemma norm_coeff_le_pnorm (p : ℂ[X]) (j : ℕ) : ‖p.coeff j‖ ≤ pnorm p := by
  simpa using sum_norm_coeff_le_pnorm p {j}

/- ### `Qₘ fₗ` as a polynomial -/

/-- The polynomial `Qₘ fₗ`. -/
noncomputable def qPolyBasis (d : ℕ → ℕ) (m l : ℕ) : ℂ[X] := fromCoord d (qImage d m l)

lemma qPolyBasis_of_le {m l : ℕ} (hl : l ≤ (m - 1) * seqA d m) : qPolyBasis d m l = fPoly d l := by
  rw [qPolyBasis, qImage, ite_eq_left hl, fromCoord_single, one_smul]

lemma qPolyBasis_of_gt (h : PartitionHyp d) {m l : ℕ} (hl : (m - 1) * seqA d m < l) :
    qPolyBasis d m l =
      if (block d l).kind = .I ∧ (block d l).r + m = (block d l).n then
        -(seqA d m : ℂ) • X ^ (l - ((block d l).n - m) * seqA d (block d l).n)
      else 0 := by
  rw [qPolyBasis, qImage, ite_eq_right (by omega)]
  split_ifs
  · rw [map_smul, fromCoord_xPow h]
  · rw [map_zero]

/-- On `Iₙ,ₙ₋ₘ` the exponent `l - (n - m)aₙ` is at most `vₘ₋₁`. -/
lemma exponent_le_of_I (h : PartitionHyp d) {m l : ℕ} (hk : (block d l).kind = .I)
    (hr : (block d l).r + m = (block d l).n) (hl : 1 ≤ l) :
    l - ((block d l).n - m) * seqA d (block d l).n ≤ seqV d (m - 1) := by
  have hB := block_mem h hl
  rcases hbl : block d l with ⟨n, r, k⟩
  rw [hbl] at hB hk hr
  dsimp only at hk hr ⊢
  subst hk
  obtain ⟨hr1, hrn, hlo, hhi⟩ := hB
  dsimp only at hr1 hrn hlo hhi
  rw [show n - m = r by omega]
  rw [show n - r - 1 = m - 1 by omega] at hhi
  omega

lemma natDegree_qPolyBasis_le (h : PartitionHyp d) {m : ℕ} (hm : 2 ≤ m) (l : ℕ) :
    (qPolyBasis d m l).natDegree ≤ (m - 1) * seqA d m := by
  rcases le_or_gt l ((m - 1) * seqA d m) with hl | hl
  · rw [qPolyBasis_of_le hl]; exact (natDegree_fPoly_le h l).trans hl
  · rw [qPolyBasis_of_gt h hl]
    split_ifs with hc
    · refine (natDegree_smul_le _ _).trans ((natDegree_X_pow_le _).trans ?_)
      have := exponent_le_of_I h hc.1 hc.2 (by omega)
      have hva := h.v_lt_a m (m - 1) (by omega)
      have : seqA d m ≤ (m - 1) * seqA d m := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · simp

/-- A bound for all `|Qₘ fₗ|`: the finitely many `|fₗ|` with `l ≤ (m - 1)aₘ`, plus `aₘ`. -/
noncomputable def qBound (d : ℕ → ℕ) (m : ℕ) : ℝ :=
  ∑ l ∈ Finset.range ((m - 1) * seqA d m + 1), pnorm (fPoly d l) + seqA d m

lemma pnorm_qPolyBasis_le (h : PartitionHyp d) (m l : ℕ) :
    pnorm (qPolyBasis d m l) ≤ qBound d m := by
  have hsum : 0 ≤ ∑ l ∈ Finset.range ((m - 1) * seqA d m + 1), pnorm (fPoly d l) :=
    Finset.sum_nonneg fun _ _ ↦ pnorm_nonneg _
  have ha : (0 : ℝ) ≤ seqA d m := Nat.cast_nonneg _
  rcases le_or_gt l ((m - 1) * seqA d m) with hl | hl
  · rw [qPolyBasis_of_le hl, qBound]
    have := Finset.single_le_sum (fun l _ ↦ pnorm_nonneg (fPoly d l))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
    linarith
  · rw [qPolyBasis_of_gt h hl, qBound]
    split_ifs
    · rw [smul_eq_C_mul, pnorm_C_mul, pnorm_X_pow, mul_one, norm_neg, Complex.norm_natCast]
      linarith
    · rw [pnorm_zero]; linarith

/- ### The coefficients of `Qₘ e` -/

/-- The `j`-th coefficient of `Qₘ e`, as a functional on ℓ¹: `e ↦ ∑ₗ eₗ (Qₘ fₗ)ⱼ`. -/
noncomputable def qCoeffCLM (h : PartitionHyp d) (m j : ℕ) : L1 →L[ℂ] ℂ :=
  l1Lift (fun l ↦ (qPolyBasis d m l).coeff j) (qBound d m)
    (fun l ↦ (norm_coeff_le_pnorm _ _).trans (pnorm_qPolyBasis_le h m l))

lemma qCoeffCLM_apply (h : PartitionHyp d) (m j : ℕ) (e : L1) :
    qCoeffCLM h m j e = ∑' l, e l * (qPolyBasis d m l).coeff j := by
  rw [qCoeffCLM, l1Lift_apply]; rfl

lemma qCoeffCLM_single (h : PartitionHyp d) (m j l : ℕ) :
    qCoeffCLM h m j (δ l) = (qPolyBasis d m l).coeff j :=
  l1Lift_single _ _ _ l

/-- Above degree `(m - 1)aₘ` every coefficient vanishes. -/
lemma qCoeffCLM_eq_zero (h : PartitionHyp d) {m : ℕ} (hm : 2 ≤ m) {j : ℕ}
    (hj : (m - 1) * seqA d m < j) (e : L1) : qCoeffCLM h m j e = 0 := by
  rw [qCoeffCLM_apply]
  convert tsum_zero with l
  rw [coeff_eq_zero_of_natDegree_lt ((natDegree_qPolyBasis_le h hm l).trans_lt hj), mul_zero]

/-- **`Qₘ e` as a polynomial.** -/
noncomputable def qPoly (h : PartitionHyp d) (m : ℕ) (e : L1) : ℂ[X] :=
  ∑ j ∈ Finset.range ((m - 1) * seqA d m + 1), C (qCoeffCLM h m j e) * X ^ j

lemma coeff_qPoly (h : PartitionHyp d) {m : ℕ} (hm : 2 ≤ m) (e : L1) (j : ℕ) :
    (qPoly h m e).coeff j = qCoeffCLM h m j e := by
  rw [qPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hj
  · rfl
  · rw [qCoeffCLM_eq_zero h hm (by simp at hj; omega)]

lemma natDegree_qPoly_le (h : PartitionHyp d) (m : ℕ) (e : L1) :
    (qPoly h m e).natDegree ≤ (m - 1) * seqA d m := by
  rw [qPoly]
  exact natDegree_sum_le_of_forall_le _ _ fun j hj ↦
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

/-- **The coordinates of the polynomial `Qₘ e` are `Qₘ e`.** Both sides are continuous and
linear in `e`, and they agree on each `δₗ`. -/
theorem toL1_toCoord_qPoly (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) (e : L1) :
    toL1 (toCoord d (qPoly h.toPartitionHyp m e)) = readQ h hm e := by
  have hP := h.toPartitionHyp
  set N := (m - 1) * seqA d m
  let A : L1 →L[ℂ] L1 := ∑ j ∈ Finset.range (N + 1),
    (qCoeffCLM hP m j).smulRight (toL1 (xPow d j))
  have hA : ∀ e, toL1 (toCoord d (qPoly hP m e)) = A e := fun e ↦ by
    simp only [qPoly, map_sum, toCoord_C_mul, toCoord_X_pow, map_smul, A,
      _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  rw [hA]
  congr 1
  refine lp.ext_continuousLinearMap ENNReal.one_ne_top fun l ↦ ?_
  refine ContinuousLinearMap.ext_ring ?_
  change A (δ l) = readQ h hm (δ l)
  rw [readQ_single, ← toCoord_fromCoord hP (qImage d m l), ← qPolyBasis,
    as_sum_range' (qPolyBasis d m l) (N + 1)
      (Nat.lt_succ_of_le (natDegree_qPolyBasis_le hP hm l))]
  simp only [A, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, qCoeffCLM_single, map_sum, ← C_mul_X_pow_eq_monomial,
    toCoord_C_mul, toCoord_X_pow, map_smul]

end ReadL1
