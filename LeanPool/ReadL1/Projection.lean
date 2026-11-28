/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma1
public import LeanPool.ReadL1.Operator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SplitIfs

/-!
# Powers of the operator, and Śliwa's projection `Qₘ`

Lemma 4 compares `Tˢ` with `Tˢ Qₘ`. This file prepares it:

* `Tᵏ` sends `xⁱ` to `xⁱ⁺ᵏ` (`ReadL1.T₀_pow_xPow`), and `‖Tᵏ g‖ ≤ αᵏ ‖g‖`
  (`ReadL1.nrm_T₀_pow_le`), from `‖T‖ ≤ α`;
* each basis vector `fᵢ = δᵢ` written through powers of `x` (`ReadL1.single_eq_of_J` and friends),
  so that `Tˢ fᵢ` is a combination of shifted powers;
* **`Qₘ`** (Śliwa p. 632): `Qₘ fᵢ = fᵢ` for `i ≤ (m - 1)aₘ`, `Qₘ fᵢ = -aₘ x^{i - (n - m)aₙ}` for
  `i ∈ Iₙ,ₙ₋ₘ` with `n > m`, and `0` otherwise (`ReadL1.qImage`), with
  `‖Qₘ fᵢ‖ ≤ √Aₘ` (`ReadL1.nrm_qImage_le`).
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/- ### Powers of the operator -/

/-- `Tᵏ xⁱ = xⁱ⁺ᵏ`. -/
lemma T₀_pow_xPow (h : PartitionHyp d) (k i : ℕ) : (T₀ d ^ k) (xPow d i) = xPow d (i + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, T₀_xPow h, add_assoc]

/-- The operator on ℓ¹ and on finite sequences agree, power by power. -/
lemma readOp_pow_toL1 (h : GrowthHyp d) (k : ℕ) (g : ℕ →₀ ℂ) :
    (readOp h ^ k) (toL1 g) = toL1 ((T₀ d ^ k) g) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, readOp_toL1, pow_succ',
      mul_apply_eq_comp]

/-- **`‖Tᵏ g‖ ≤ αᵏ ‖g‖`.** -/
lemma nrm_T₀_pow_le (h : GrowthHyp d) (k : ℕ) (g : ℕ →₀ ℂ) :
    nrm ((T₀ d ^ k) g) ≤ alpha ^ k * nrm g := by
  rw [← norm_toL1, ← norm_toL1, ← readOp_pow_toL1 h]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
    exact ((readOp h).le_opNorm _).trans
      (mul_le_mul (norm_readOp_le h) ih (norm_nonneg _) (by norm_num [alpha]))

/- ### Basis vectors through powers of `x` -/

lemma single_eq_of_J (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .J) : single i (1 : ℂ) = (weight (seqA d B.n) B.r i : ℂ) • xPow d i := by
  rw [xPow_of_J h hB hk, smul_smul, mul_inv_cancel₀ (weight_ne_zero _ _ _), one_smul]

lemma single_eq_of_L (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .L) : single i (1 : ℂ) = (weight (seqB d B.n) B.r i : ℂ) • xPow d i := by
  rw [xPow_of_L h hB hk, smul_smul, mul_inv_cancel₀ (weight_ne_zero _ _ _), one_smul]

lemma single_eq_of_I (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .I) : single i (1 : ℂ) =
      (seqA d (B.n - B.r) : ℂ) • (xPow d i - xPow d (i - seqA d B.n)) := by
  have ha' : (seqA d (B.n - B.r) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h.one_le_a _))
  rw [xPow_of_I h hB hk, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ha', one_smul]

lemma single_eq_of_K (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .K) : single i (1 : ℂ) =
      xPow d i - (seqB d B.n : ℂ) • xPow d (i - seqB d B.n) := by
  rw [xPow_of_K h hB hk, add_sub_cancel_right]

/- ### The projection `Qₘ` -/

/-- `Qₘ fᵢ` in coordinates. -/
noncomputable def qImage (d : ℕ → ℕ) (m i : ℕ) : ℕ →₀ ℂ :=
  if i ≤ (m - 1) * seqA d m then single i 1
  else if (block d i).kind = .I ∧ (block d i).r + m = (block d i).n then
    -(seqA d m : ℂ) • xPow d (i - ((block d i).n - m) * seqA d (block d i).n)
  else 0

/-- **`‖Qₘ fᵢ‖ ≤ √Aₘ = α^{√aₘ/2}`** for `m ≥ 2`: on `Iₙ,ₙ₋ₘ` the power has exponent at most
`vₘ₋₁`, so Lemma 1 (a) bounds it by `Bₘ₋₁`, and `aₘ Bₘ₋₁ ≤ √Aₘ`. -/
lemma nrm_qImage_le (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) (i : ℕ) :
    nrm (qImage d m i) ≤ alpha ^ (Real.sqrt (seqA d m) / 2) := by
  have hone : (1 : ℝ) ≤ alpha ^ (Real.sqrt (seqA d m) / 2) :=
    one_le_alpha_rpow (by positivity)
  unfold qImage
  split_ifs with h1 h2
  · rw [nrm_single, norm_one]; exact hone
  · obtain ⟨hk, hr⟩ := h2
    have hi : 1 ≤ i := by omega
    have hB := block_mem h.toPartitionHyp hi
    rcases hbl : block d i with ⟨n, r, k⟩
    rw [hbl] at hB hk hr
    dsimp only at hk hr ⊢
    subst hk
    obtain ⟨hr1, hrn, hlo, hhi⟩ := hB
    dsimp only at hr1 hrn hlo hhi
    -- `i - (n - m)aₙ = i - r aₙ ≤ vₙ₋ᵣ₋₁ = vₘ₋₁`.
    have hrm : n - m = r := by omega
    have hidx : i - (n - m) * seqA d n ≤ seqV d (m - 1) := by
      rw [hrm]; rw [show n - r - 1 = m - 1 by omega] at hhi; omega
    have hcap := (nrm_xPow_le_cap h (m - 1) (by omega)).2 _ hidx
    rw [nrm_smul, norm_neg, Complex.norm_natCast]
    calc (seqA d m : ℝ) * nrm (xPow d (i - (n - m) * seqA d n))
        ≤ seqA d m * capB d (m - 1) := by gcongr
      _ ≤ alpha ^ (Real.sqrt (seqA d m) / 2) := h.q_bound m hm
  · rw [nrm_zero]; linarith

end ReadL1
