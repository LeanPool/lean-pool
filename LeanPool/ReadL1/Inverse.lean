/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.PolyNorm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SplitIfs

/-!
# Exact inverses of a polynomial, up to a given degree

The construction inside Śliwa's Lemma 6 (p. 639): if `y₀ ≠ 0`, put `qᵢ = 0` for `i < m`,
`qₘ = y₀⁻¹` and `q_{m+t} = -y₀⁻¹ ∑_{j=1}^{t} yⱼ q_{m+t-j}`. Then `q y` agrees with `xᵐ` in every
degree up to any `n ≥ m` (`ReadL1.ptrunc_invPoly_mul`), and `|q_{m+t}| ≤ (M/|y₀|)ᵗ / |y₀|` when
`|y| ≤ M` (`ReadL1.norm_invCoeff_le`).
-/

@[expose] public section

namespace ReadL1

open Polynomial

/-- The coefficients `qᵢ` of the inverse of `y` from degree `m`. -/
noncomputable def invCoeff (y : ℂ[X]) (m : ℕ) : ℕ → ℂ
  | i =>
    if _h1 : i < m then 0
    else if _h2 : i = m then (y.coeff 0)⁻¹
    else -(y.coeff 0)⁻¹ * ∑ j ∈ (Finset.Icc 1 (i - m)).attach,
      y.coeff j.1 * invCoeff y m (i - j.1)
  termination_by i => i
  decreasing_by
    have := (Finset.mem_Icc.1 j.2).1
    omega

lemma invCoeff_of_lt {y : ℂ[X]} {m i : ℕ} (hi : i < m) : invCoeff y m i = 0 := by
  rw [invCoeff, dite_eq_left hi]

lemma invCoeff_self (y : ℂ[X]) (m : ℕ) : invCoeff y m m = (y.coeff 0)⁻¹ := by
  rw [invCoeff, dite_eq_right (lt_irrefl m), dite_eq_left rfl]

lemma invCoeff_of_gt {y : ℂ[X]} {m i : ℕ} (hi : m < i) :
    invCoeff y m i = -(y.coeff 0)⁻¹ *
      ∑ j ∈ Finset.Icc 1 (i - m), y.coeff j * invCoeff y m (i - j) := by
  rw [invCoeff, dite_eq_right (by omega), dite_eq_right (by omega)]
  congr 1
  exact Finset.sum_attach (Finset.Icc 1 (i - m)) fun j ↦ y.coeff j * invCoeff y m (i - j)

/-- **The convolution identity**: `∑_{a ≤ l} qₐ y_{l - a}` is `1` at `l = m` and `0` elsewhere. -/
lemma sum_invCoeff_mul {y : ℂ[X]} (hy : y.coeff 0 ≠ 0) (m l : ℕ) :
    ∑ a ∈ Finset.range (l + 1), invCoeff y m a * y.coeff (l - a) = if l = m then 1 else 0 := by
  rcases lt_trichotomy l m with hlt | rfl | hgt
  · rw [ite_eq_right hlt.ne]
    exact Finset.sum_eq_zero fun a ha ↦ by
      rw [invCoeff_of_lt (by have := Finset.mem_range.1 ha; omega), zero_mul]
  · rw [ite_eq_left rfl, Finset.sum_range_succ, Finset.sum_eq_zero fun a ha ↦ by
      rw [invCoeff_of_lt (Finset.mem_range.1 ha), zero_mul], zero_add, Nat.sub_self,
      invCoeff_self, inv_mul_cancel₀ hy]
  · rw [ite_eq_right hgt.ne', Finset.sum_range_succ, Nat.sub_self, invCoeff_of_gt hgt]
    -- `∑_{a < l} qₐ y_{l-a}` is the sum in the definition of `q_l`: drop `a < m`, then `a ↦ l - a`.
    have h1 : ∑ a ∈ Finset.range l, invCoeff y m a * y.coeff (l - a) =
        ∑ a ∈ Finset.Ico m l, invCoeff y m a * y.coeff (l - a) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) hgt.le,
        Finset.sum_eq_zero fun a ha ↦ by
          rw [invCoeff_of_lt (Finset.mem_Ico.1 ha).2, zero_mul], zero_add]
    have h2 : ∑ a ∈ Finset.Ico m l, invCoeff y m a * y.coeff (l - a) =
        ∑ j ∈ Finset.Icc 1 (l - m), y.coeff j * invCoeff y m (l - j) := by
      refine Finset.sum_nbij' (fun a ↦ l - a) (fun j ↦ l - j) (fun a ha ↦ ?_) (fun j hj ↦ ?_)
        (fun a ha ↦ ?_) (fun j hj ↦ ?_) (fun a ha ↦ ?_)
      · simp only [Finset.mem_Ico, Finset.mem_Icc] at ha ⊢; omega
      · simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
      · simp only [Finset.mem_Ico] at ha; omega
      · simp only [Finset.mem_Icc] at hj; omega
      · simp only [Finset.mem_Ico] at ha
        rw [show l - (l - a) = a by omega, mul_comm]
    rw [h1, h2]
    field_simp
    ring

/-- The inverse polynomial `q = ∑_{i ≤ n} qᵢ xⁱ`. -/
noncomputable def invPoly (y : ℂ[X]) (m n : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range (n + 1), monomial i (invCoeff y m i)

lemma coeff_invPoly (y : ℂ[X]) (m n i : ℕ) :
    (invPoly y m n).coeff i = if i ≤ n then invCoeff y m i else 0 := by
  classical
  rw [invPoly, finsetSum_coeff]
  simp [coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']

lemma natDegree_invPoly_le (y : ℂ[X]) (m n : ℕ) : (invPoly y m n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_invPoly, ite_eq_right (by exact_mod_cast not_le.2 hi)]

/-- **`Pₙ (q y) = xᵐ`** for `m ≤ n`, when `y₀ ≠ 0`. -/
lemma ptrunc_invPoly_mul {y : ℂ[X]} (hy : y.coeff 0 ≠ 0) {m n : ℕ} (hmn : m ≤ n) :
    ptrunc n (invPoly y m n * y) = X ^ m := by
  ext l
  rw [coeff_ptrunc, coeff_X_pow]
  split_ifs with hl hlm hlm
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_invPoly]
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [ite_eq_left (by have := Finset.mem_range.1 ha; omega)], sum_invCoeff_mul hy m l,
        ite_eq_left hlm]
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_invPoly]
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [ite_eq_left (by have := Finset.mem_range.1 ha; omega)], sum_invCoeff_mul hy m l,
        ite_eq_right hlm]
  · omega
  · rfl

/-- Any finite part of `|y|` is at most `|y|`. -/
lemma sum_norm_coeff_le_pnorm (y : ℂ[X]) (s : Finset ℕ) :
    ∑ j ∈ s, ‖y.coeff j‖ ≤ pnorm y := by
  classical
  rw [pnorm_eq_sum_of_subset y (Finset.subset_union_right (s₁ := s))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ ↦ norm_nonneg _

/-- **`|q_{m+t}| ≤ (M/|y₀|)ᵗ / |y₀|`** when `|y| ≤ M`. -/
lemma norm_invCoeff_le {y : ℂ[X]} {M : ℝ} (hy0 : 0 < ‖y.coeff 0‖) (hM : pnorm y ≤ M) (m t : ℕ) :
    ‖invCoeff y m (m + t)‖ ≤ (M / ‖y.coeff 0‖) ^ t / ‖y.coeff 0‖ := by
  have hy0M : ‖y.coeff 0‖ ≤ M := (sum_norm_coeff_le_pnorm y {0}).trans hM |>.trans_eq' (by simp)
  have hr : 1 ≤ M / ‖y.coeff 0‖ := (one_le_div hy0).2 hy0M
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [add_zero, invCoeff_self, norm_inv, pow_zero, one_div]
  · rw [invCoeff_of_gt (by omega), norm_mul, norm_neg, norm_inv, show m + t - m = t by omega]
    have hsum : ‖∑ j ∈ Finset.Icc 1 t, y.coeff j * invCoeff y m (m + t - j)‖ ≤
        (M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖ * M := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ Finset.Icc 1 t, ‖y.coeff j * invCoeff y m (m + t - j)‖
          ≤ ∑ j ∈ Finset.Icc 1 t, ‖y.coeff j‖ * ((M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖) := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            simp only [Finset.mem_Icc] at hj
            rw [norm_mul, show m + t - j = m + (t - j) by omega]
            gcongr
            refine (ih (t - j) (by omega)).trans ?_
            gcongr
            omega
        _ = (∑ j ∈ Finset.Icc 1 t, ‖y.coeff j‖) * ((M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖) := by
            rw [Finset.sum_mul]
        _ ≤ M * ((M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖) := by
            gcongr; exact (sum_norm_coeff_le_pnorm y _).trans hM
        _ = (M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖ * M := by ring
    calc ‖y.coeff 0‖⁻¹ * ‖∑ j ∈ Finset.Icc 1 t, y.coeff j * invCoeff y m (m + t - j)‖
        ≤ ‖y.coeff 0‖⁻¹ * ((M / ‖y.coeff 0‖) ^ (t - 1) / ‖y.coeff 0‖ * M) := by gcongr
      _ = (M / ‖y.coeff 0‖) ^ (t - 1 + 1) / ‖y.coeff 0‖ := by
          rw [pow_succ]; field_simp
      _ = (M / ‖y.coeff 0‖) ^ t / ‖y.coeff 0‖ := by rw [Nat.sub_add_cancel ht]

/-- `|q| ≤ (n - m + 1) (M/|y₀|)^{n-m} / |y₀|`. -/
lemma pnorm_invPoly_le {y : ℂ[X]} {M : ℝ} (hy0 : 0 < ‖y.coeff 0‖) (hM : pnorm y ≤ M)
    {m n : ℕ} (hmn : m ≤ n) :
    pnorm (invPoly y m n) ≤ (n - m + 1 : ℕ) * ((M / ‖y.coeff 0‖) ^ (n - m) / ‖y.coeff 0‖) := by
  have hy0M : ‖y.coeff 0‖ ≤ M := (sum_norm_coeff_le_pnorm y {0}).trans hM |>.trans_eq' (by simp)
  have hr : 1 ≤ M / ‖y.coeff 0‖ := (one_le_div hy0).2 hy0M
  refine (pnorm_sum_le _ _).trans ?_
  simp only [pnorm_monomial]
  -- Only `i = m + t` with `t ≤ n - m` contribute.
  rw [show Finset.range (n + 1) = Finset.range m ∪ (Finset.range (n - m + 1)).map
      ⟨(m + ·), add_right_injective m⟩ by
    ext i; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hi; by_cases him : i < m
      · exact Or.inl him
      · exact Or.inr ⟨i - m, by omega, by omega⟩
    · rintro (hi | ⟨t, ht, rfl⟩) <;> omega]
  rw [Finset.sum_union (Finset.disjoint_left.2 fun i h1 h2 ↦ by
    simp only [Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨t, -, rfl⟩ := h2; omega), Finset.sum_map,
    Finset.sum_eq_zero fun i hi ↦ by rw [invCoeff_of_lt (Finset.mem_range.1 hi), norm_zero],
    zero_add]
  calc ∑ t ∈ Finset.range (n - m + 1), ‖invCoeff y m (m + t)‖
      ≤ ∑ t ∈ Finset.range (n - m + 1), (M / ‖y.coeff 0‖) ^ (n - m) / ‖y.coeff 0‖ := by
        refine Finset.sum_le_sum fun t ht ↦ (norm_invCoeff_le hy0 hM m t).trans ?_
        gcongr
        exact Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    _ = (n - m + 1 : ℕ) * ((M / ‖y.coeff 0‖) ^ (n - m) / ‖y.coeff 0‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ReadL1
