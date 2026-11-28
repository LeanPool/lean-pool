/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 2: the operator is bounded

Śliwa (pp. 630–632) shows `‖T fᵢ‖ ≤ α` for every `i`, by four cases (the block of `i`), each split
in two: `i` inside its block, where `T fᵢ` is a multiple of `fᵢ₊₁`, and `i` at the right end of its
block, where `x fᵢ` crosses into the next block. The boundary subcases are where the growth facts
are used, and give the sharper bounds of his Remark 3 (p. 632), which Lemma 4 needs later.

In coordinates `fᵢ = δᵢ` and `T fᵢ = shiftImage i`, so the statement is
`nrm (shiftImage d i) ≤ α`.
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-! ### `T fᵢ` block by block -/

lemma shiftImage_of_J (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .J) : shiftImage d i = (weight (seqA d B.n) B.r i : ℂ) • xPow d (i + 1) := by
  have hi := Block.one_le_of_mem h hB
  rw [shiftImage, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma shiftImage_of_L (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .L) : shiftImage d i = (weight (seqB d B.n) B.r i : ℂ) • xPow d (i + 1) := by
  have hi := Block.one_le_of_mem h hB
  rw [shiftImage, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma shiftImage_of_I (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .I) : shiftImage d i =
      (seqA d (B.n - B.r) : ℂ) • (xPow d (i + 1) - xPow d (i + 1 - seqA d B.n)) := by
  have hi := Block.one_le_of_mem h hB
  rw [shiftImage, ite_eq_right (by omega), block_eq h hB]; simp [hk]

lemma shiftImage_of_K (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .K) : shiftImage d i =
      xPow d (i + 1) - (seqB d B.n : ℂ) • xPow d (i + 1 - seqB d B.n) := by
  have hi := Block.one_le_of_mem h hB
  rw [shiftImage, ite_eq_right (by omega), block_eq h hB]; simp [hk]

/-! ### Inside a block -/

/-- **Case 1.1°:** inside `Jₙ,ᵣ`, `T fᵢ = α^{1/√aₙ} fᵢ₊₁`. -/
lemma nrm_shiftImage_J_inner (h : PartitionHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .J⟩ : Block).Mem d i) (hi : i + 1 < r * seqA d n) :
    nrm (shiftImage d i) ≤ alpha := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hB' : (⟨n, r, .J⟩ : Block).Mem d (i + 1) := ⟨hr1, hrn, by dsimp; omega, hi⟩
  have ha : 0 < seqA d n := h.one_le_a n
  rw [shiftImage_of_J h hB rfl, nrm_smul, nrm_xPow_of_J h hB' rfl]
  dsimp only
  rw [Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le,
    weight_eq_mul_succ ha, mul_assoc, mul_inv_cancel₀ (weight_pos _ _ _).ne', mul_one]
  -- `α^{1/√aₙ} ≤ α` as `aₙ ≥ 1`.
  calc alpha ^ (1 / Real.sqrt (seqA d n)) ≤ alpha ^ (1 : ℝ) := by
        refine alpha_rpow_le ?_
        rw [div_le_one (Real.sqrt_pos.2 (by exact_mod_cast ha))]
        exact Real.one_le_sqrt.2 (by exact_mod_cast ha)
    _ = alpha := Real.rpow_one _

/-- **Case 3.1°:** inside `Lₙ,ᵣ`, `T fᵢ = α^{1/√bₙ} fᵢ₊₁`. -/
lemma nrm_shiftImage_L_inner (h : GrowthHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .L⟩ : Block).Mem d i) (hi : i + 1 < r * (seqA d n + seqB d n)) :
    nrm (shiftImage d i) ≤ alpha := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hB' : (⟨n, r, .L⟩ : Block).Mem d (i + 1) := ⟨hr1, hrn, by dsimp; omega, hi⟩
  have hb : 0 < seqB d n := by have := h.two_le_b n; omega
  rw [shiftImage_of_L h.toPartitionHyp hB rfl, nrm_smul,
    nrm_xPow_of_L h.toPartitionHyp hB' rfl]
  dsimp only
  rw [Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le,
    weight_eq_mul_succ hb, mul_assoc, mul_inv_cancel₀ (weight_pos _ _ _).ne', mul_one]
  calc alpha ^ (1 / Real.sqrt (seqB d n)) ≤ alpha ^ (1 : ℝ) := by
        refine alpha_rpow_le ?_
        rw [div_le_one (Real.sqrt_pos.2 (by exact_mod_cast hb))]
        exact Real.one_le_sqrt.2 (by exact_mod_cast hb)
    _ = alpha := Real.rpow_one _

/-- **Case 2.1°:** inside `Iₙ,ᵣ`, `T fᵢ = fᵢ₊₁`. -/
lemma shiftImage_I_inner (h : PartitionHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : i < r * seqA d n + seqV d (n - r - 1)) :
    shiftImage d i = single (i + 1) 1 := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hB' : (⟨n, r, .I⟩ : Block).Mem d (i + 1) := ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
  have ha' : (seqA d (n - r) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h.one_le_a _))
  rw [shiftImage_of_I h hB rfl, xPow_of_I h hB' rfl]
  dsimp only
  rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ha', one_smul]

/-- **Case 4.1°:** inside `Kₙ,ᵣ`, `T fᵢ = fᵢ₊₁`. -/
lemma shiftImage_K_inner (h : PartitionHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hi : i < (n - 1) * seqA d n + r * seqB d n) :
    shiftImage d i = single (i + 1) 1 := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hB' : (⟨n, r, .K⟩ : Block).Mem d (i + 1) := ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
  rw [shiftImage_of_K h hB rfl, xPow_of_K h hB' rfl]
  dsimp only
  rw [add_sub_cancel_right]

/-! ### Facts about powers of `α` used at the block boundaries -/

/-- `α^{-√c/4}` decreases as `c` grows. -/
lemma rpow_neg_sqrt_anti {c c' : ℝ} (hcc : c ≤ c') :
    alpha ^ (-(Real.sqrt c' / 4)) ≤ alpha ^ (-(Real.sqrt c / 4)) :=
  alpha_rpow_le (neg_le_neg (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hcc) (by norm_num)))

/-- Śliwa's `α c² < α^{√c/4}`, rearranged: `c² α^{-√c/4} < 1/α`. -/
lemma sq_mul_rpow_lt {c : ℝ} (hc : alpha * c ^ 2 < alpha ^ (Real.sqrt c / 4)) :
    c ^ 2 * alpha ^ (-(Real.sqrt c / 4)) < 1 / alpha := by
  have hp : 0 < alpha ^ (Real.sqrt c / 4) := Real.rpow_pos_of_pos alpha_pos _
  rw [Real.rpow_neg alpha_pos.le, ← div_eq_mul_inv, div_lt_div_iff₀ hp alpha_pos]
  linarith

/-- `α^{1 - √c/2} = α (α^{-√c/4})²`. -/
lemma rpow_one_sub_half (c : ℝ) :
    alpha ^ (1 - Real.sqrt c / 2) = alpha * (alpha ^ (-(Real.sqrt c / 4)) *
      alpha ^ (-(Real.sqrt c / 4))) := by
  rw [show 1 - Real.sqrt c / 2 = 1 + (-(Real.sqrt c / 4)) + (-(Real.sqrt c / 4)) by ring,
    Real.rpow_add alpha_pos, Real.rpow_add alpha_pos, Real.rpow_one, mul_assoc]

/-- The weight at an index past `r c - 1` is at most `α^{1 - √c/2}`. -/
lemma weight_le_of_ge {c r i : ℕ} (hc : 1 ≤ c) (hi : (r : ℝ) * c ≤ i + 1) :
    weight c r i ≤ alpha ^ (1 - Real.sqrt c / 2) := by
  have hs : 1 ≤ Real.sqrt c := Real.one_le_sqrt.2 (by exact_mod_cast hc)
  refine alpha_rpow_le ?_
  rw [sqrt_four_mul, div_le_iff₀ (by positivity)]
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  nlinarith only [hi, hs, hsq]

/-- On a `J` or `L` block, at its last index `i = r c - 1` the weight is at most `α^{1 - √c/2}`. -/
lemma weight_last_le {c r i : ℕ} (hc : 1 ≤ c) (hi : (i : ℝ) + 1 = r * c) :
    weight c r i ≤ alpha ^ (1 - Real.sqrt c / 2) :=
  weight_le_of_ge hc hi.ge

/-- `‖x^{r aₙ}‖ ≤ 2`: `r aₙ` is the first point of `Iₙ,ᵣ`, and Lemma 1 (b) compares `x^{r aₙ}`
with `x⁰`. -/
lemma nrm_xPow_mul_a_le (h : GrowthHyp d) {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r < n) :
    nrm (xPow d (r * seqA d n)) ≤ 2 := by
  have hB : (⟨n, r, .I⟩ : Block).Mem d (r * seqA d n) :=
    ⟨hr1, hrn, le_rfl, by dsimp; omega⟩
  have h1 := nrm_xPow_sub_of_I h hB
  rw [Nat.sub_self, show xPow d 0 = single 0 1 by rw [xPow]] at h1
  have ha : (2 : ℝ) ≤ seqA d (n - r) := by
    have := h.a_big (n - r) (by omega); exact_mod_cast (show 2 ≤ seqA d (n - r) by omega)
  have h2 : 2 / (seqA d (n - r) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact ha
  calc nrm (xPow d (r * seqA d n))
      = nrm ((xPow d (r * seqA d n) - single 0 1) + single 0 1) := by rw [sub_add_cancel]
    _ ≤ nrm (xPow d (r * seqA d n) - single 0 1) + nrm (single 0 1) := nrm_add_le _ _
    _ ≤ 2 / seqA d (n - r) + 1 := by rw [nrm_single, norm_one]; linarith
    _ ≤ 2 := by linarith

/-! ### At the end of a block -/

/-- **Case 1.2° (Remark 3):** at the last index of `Jₙ,ᵣ`, `‖T fᵢ‖ ≤ 1/aₙ`. -/
lemma nrm_shiftImage_J_last (h : GrowthHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .J⟩ : Block).Mem d i) (hi : i + 1 = r * seqA d n) :
    nrm (shiftImage d i) ≤ 1 / seqA d n := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha1 : 1 ≤ seqA d n := h.one_le_a n
  have ha : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha1
  rw [shiftImage_of_J h.toPartitionHyp hB rfl, nrm_smul, hi]
  dsimp only
  rw [Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le]
  have hw := weight_last_le (c := seqA d n) (r := r) (i := i) ha1 (by exact_mod_cast hi)
  rw [rpow_one_sub_half] at hw
  have hx := nrm_xPow_mul_a_le h hr1 hrn
  have hx0 := nrm_nonneg (xPow d (r * seqA d n))
  have hsmall := sq_mul_rpow_lt (h.rpow_a n (by omega))
  set s := alpha ^ (-(Real.sqrt (seqA d n) / 4)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos alpha_pos _
  -- `‖T fᵢ‖ ≤ 2 α s²`, and `aₙ² s < 1/α` makes `2 α s² aₙ ≤ 1`.
  have hα : alpha = 8 := rfl
  have hαs : 0 ≤ alpha * (s * s) := by rw [hα]; positivity
  rw [hα] at hsmall
  rw [le_div_iff₀ (by linarith)]
  have ha4 : (seqA d n : ℝ) ≤ (seqA d n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (seqA d n : ℝ) ^ 3 := one_le_pow₀ ha
    nlinarith
  have hsq : ((seqA d n : ℝ) ^ 2 * s) ^ 2 < (1 / 8) ^ 2 := by
    have : 0 ≤ (seqA d n : ℝ) ^ 2 * s := by positivity
    exact pow_lt_pow_left₀ hsmall this (by norm_num)
  calc weight (seqA d n) r i * nrm (xPow d (r * seqA d n)) * seqA d n
      ≤ (alpha * (s * s)) * 2 * seqA d n := by gcongr
    _ = (8 * (s * s)) * 2 * seqA d n := by rw [hα]
    _ ≤ 16 * ((seqA d n : ℝ) ^ 4 * (s * s)) := by nlinarith
    _ = 16 * (((seqA d n : ℝ) ^ 2 * s) ^ 2) := by ring
    _ ≤ 1 := by nlinarith

/-- On a `J` block, `‖xᵐ‖ ≤ α^{-√aₙ/4}` once the exponent's numerator is at least `aₙ / 2`. -/
lemma nrm_xPow_J_le (h : PartitionHyp d) {N R m : ℕ} (hB : (⟨N, R, .J⟩ : Block).Mem d m)
    (hE : (seqA d N : ℝ) / 2 ≤ (2 * (R : ℝ) - 1) * seqA d N - 2 * m) :
    nrm (xPow d m) ≤ alpha ^ (-(Real.sqrt (seqA d N) / 4)) := by
  rw [nrm_xPow_of_J h hB rfl]
  exact inv_weight_le (h.one_le_a N) hE

/-- On an `L` block, `‖xᵐ‖ ≤ α^{-√bₙ/4}` once the exponent's numerator is at least `bₙ / 2`. -/
lemma nrm_xPow_L_le (h : GrowthHyp d) {N R m : ℕ} (hB : (⟨N, R, .L⟩ : Block).Mem d m)
    (hE : (seqB d N : ℝ) / 2 ≤ (2 * (R : ℝ) - 1) * seqB d N - 2 * m) :
    nrm (xPow d m) ≤ alpha ^ (-(Real.sqrt (seqB d N) / 4)) := by
  rw [nrm_xPow_of_L h.toPartitionHyp hB rfl]
  exact inv_weight_le (lt_of_lt_of_le two_pos (h.two_le_b N)) hE

/-- **Case 4.2°:** at the last index of `Kₙ,ᵣ`, `‖T fᵢ‖ ≤ 1`. Here
`T fᵢ = xⁱ⁺¹ - bₙ xʲ` with `j = i + 1 - bₙ` in `Lₙ,ᵣ`, and `i + 1` in `Lₙ,ᵣ₊₁` (or, for
`r = n - 1`, in `Jₙ₊₁,₁`); both powers have norm at most `α^{-√bₙ/4}`. -/
lemma nrm_shiftImage_K_last (h : GrowthHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hi : i = (n - 1) * seqA d n + r * seqB d n) :
    nrm (shiftImage d i) ≤ 1 := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha := h.one_le_a n
  have hb2 := h.two_le_b n
  have hab := h.a_small n (by omega)
  -- Linear facts for `omega`.
  have e1 : (r - 1) * seqB d n + seqB d n = r * seqB d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  have e2 : (n - 1) * seqA d n + seqA d n = n * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have e3 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
  have e4 : r * (seqA d n + seqB d n) = r * seqA d n + r * seqB d n := by ring
  have e5 : seqA d n ≤ r * seqA d n := Nat.le_mul_of_pos_left _ hr1
  set j := i + 1 - seqB d n with hj
  have hjv : j = (n - 1) * seqA d n + (r - 1) * seqB d n + 1 := by omega
  -- `j ∈ Lₙ,ᵣ`, with numerator `bₙ - 2(n - 1)aₙ - 2 ≥ bₙ / 2`.
  have hjL : (⟨n, r, .L⟩ : Block).Mem d j := ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
  have hnumR : (2 * ((n : ℝ) - 1)) * seqA d n + 2 ≤ seqB d n / 2 := by
    have : (8 * (n * seqA d n) : ℝ) < seqB d n := by exact_mod_cast (e3 ▸ hab)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have ha1 : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha
    nlinarith
  have hjb : nrm (xPow d j) ≤ alpha ^ (-(Real.sqrt (seqB d n) / 4)) := by
    refine nrm_xPow_L_le h hjL ?_
    rw [hjv]; push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub hr1]; push_cast
    nlinarith
  -- `i + 1`: in `Lₙ,ᵣ₊₁` if `r < n - 1`, in `Jₙ₊₁,₁` if `r = n - 1`.
  have hib : nrm (xPow d (i + 1)) ≤ alpha ^ (-(Real.sqrt (seqB d n) / 4)) := by
    rcases Nat.lt_or_ge r (n - 1) with hr | hr
    · have e6 : (r + 1) * (seqA d n + seqB d n) = r * seqA d n + seqA d n + r * seqB d n +
          seqB d n := by ring
      have hL : (⟨n, r + 1, .L⟩ : Block).Mem d (i + 1) := by
        refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · simp only [Nat.add_sub_cancel]; omega
        · omega
      refine nrm_xPow_L_le h hL ?_
      rw [hi]; push_cast
      rw [Nat.cast_sub (by omega)]; push_cast
      nlinarith
    · have hrn1 : r = n - 1 := by omega
      have hvn : seqV d n = (n - 1) * seqA d n + r * seqB d n := by
        rw [seqV, hrn1]; ring
      have hv := h.v_small (n + 1) n (by omega)
      have hJ : (⟨n + 1, 1, .J⟩ : Block).Mem d (i + 1) :=
        ⟨le_rfl, by dsimp; omega, by dsimp; simp only [zero_mul, zero_add]; omega,
          by dsimp; omega⟩
      refine (nrm_xPow_J_le h.toPartitionHyp hJ ?_).trans ?_
      · have : (8 * (seqV d n + 1) : ℝ) < seqA d (n + 1) := by exact_mod_cast hv
        rw [hi, ← hvn]; push_cast; nlinarith
      · refine rpow_neg_sqrt_anti ?_
        have := h.b_small n (by omega)
        have : seqB d n ≤ seqA d (n + 1) := by nlinarith
        exact_mod_cast this
  -- Total: `‖xⁱ⁺¹‖ + bₙ ‖xʲ‖ ≤ (1 + bₙ) s ≤ 2 bₙ s ≤ 1`, as `bₙ² s < 1/8`.
  have hsmall := sq_mul_rpow_lt (h.rpow_b n (by omega))
  set sb := alpha ^ (-(Real.sqrt (seqB d n) / 4))
  have hsb0 : 0 < sb := Real.rpow_pos_of_pos alpha_pos _
  have hb1 : (1 : ℝ) ≤ seqB d n := by exact_mod_cast (show 1 ≤ seqB d n by omega)
  rw [shiftImage_of_K h.toPartitionHyp hB rfl]
  dsimp only
  calc nrm (xPow d (i + 1) - (seqB d n : ℂ) • xPow d j)
      ≤ nrm (xPow d (i + 1)) + nrm ((seqB d n : ℂ) • xPow d j) := nrm_sub_le _ _
    _ = nrm (xPow d (i + 1)) + seqB d n * nrm (xPow d j) := by
        rw [nrm_smul, Complex.norm_natCast]
    _ ≤ sb + seqB d n * sb := by gcongr
    _ ≤ 1 := by
        have hα : alpha = 8 := rfl
        rw [hα] at hsmall
        nlinarith

/-- `a` is monotone from index `1`. -/
lemma seqA_mono (h : GrowthHyp d) {m m' : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') :
    seqA d m ≤ seqA d m' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmm
  have := pow_two_mul_le_seqA h hm j
  have : seqA d m ≤ 2 ^ j * seqA d m := Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- `aₖ₊₁ ≥ 8aₖ²`: from `k² aₖ² < bₖ` and `8k bₖ < aₖ₊₁`. -/
lemma eight_sq_le_seqA_succ (h : GrowthHyp d) {k : ℕ} (hk : 1 ≤ k) :
    8 * seqA d k ^ 2 ≤ seqA d (k + 1) := by
  have h1 := h.a_sq k hk
  have h2 := h.b_small k hk
  have : seqA d k ^ 2 ≤ k ^ 2 * seqA d k ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
  have : seqB d k ≤ k * seqB d k := Nat.le_mul_of_pos_left _ hk
  nlinarith

/-- **Case 2.2° (Remark 3):** at the last index of `Iₙ,ᵣ`, `‖T fᵢ‖ ≤ 1/aₙ₋ᵣ`. Here
`T fᵢ = aₙ₋ᵣ (xⁱ⁺¹ - xʲ)` with `j = i + 1 - aₙ`; both powers are tiny, and `aₙ₋ᵣ₊₁ ≥ 8aₙ₋ᵣ²`. -/
lemma nrm_shiftImage_I_last (h : GrowthHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : i = r * seqA d n + seqV d (n - r - 1)) :
    nrm (shiftImage d i) ≤ 1 / seqA d (n - r) := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hP := h.toPartitionHyp
  have ha := h.one_le_a n
  have hab := h.a_small n (by omega)
  have hvs := h.v_small n (n - r - 1) (by omega)
  have e3 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
  have e2 : (n - 1) * seqA d n + seqA d n = n * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have ersucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  set a' := seqA d (n - r) with ha'
  have ha'1 : 1 ≤ n - r := by omega
  have ha'n : a' ≤ seqA d n := seqA_mono h ha'1 (by omega)
  set s' := alpha ^ (-(Real.sqrt a' / 4)) with hs'
  -- (A) `‖xⁱ⁺¹‖ ≤ s'`.
  have hA : nrm (xPow d (i + 1)) ≤ s' := by
    rcases Nat.lt_or_ge r (n - 1) with hr | hr
    · -- `i + 1 ∈ Jₙ,ᵣ₊₁`.
      have hJ : (⟨n, r + 1, .J⟩ : Block).Mem d (i + 1) := by
        refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · simp only [Nat.add_sub_cancel, show n - (r + 1) = n - r - 1 by omega]; omega
        · rw [Nat.add_mul, one_mul]; omega
      refine (nrm_xPow_J_le hP hJ ?_).trans (rpow_neg_sqrt_anti (by exact_mod_cast ha'n))
      have : (8 * (seqV d (n - r - 1) + 1) : ℝ) < seqA d n := by exact_mod_cast hvs
      rw [hi]; push_cast; nlinarith
    · -- `r = n - 1`: `i + 1 = (n - 1)aₙ + 1 ∈ Lₙ,₁`.
      have hrn1 : r = n - 1 := by omega
      have hv0 : seqV d (n - r - 1) = 0 := by rw [show n - r - 1 = 0 by omega, seqV_zero]
      have hL : (⟨n, 1, .L⟩ : Block).Mem d (i + 1) := by
        refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · simp only [Nat.sub_self, zero_mul, add_zero]; rw [hi, hv0, hrn1]; omega
        · rw [one_mul, hi, hv0, hrn1]; omega
      refine (nrm_xPow_L_le h hL ?_).trans (rpow_neg_sqrt_anti ?_)
      · have : (8 * (n * seqA d n) : ℝ) < seqB d n := by exact_mod_cast (e3 ▸ hab)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have ha1 : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha
        rw [hi, hv0, hrn1]; push_cast
        rw [Nat.cast_sub (by omega)]; push_cast
        nlinarith
      · have : a' ≤ seqB d n := by
          have : seqA d n ≤ n * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
          omega
        exact_mod_cast this
  -- (B) `‖xʲ‖ ≤ 2/aₙ₋ᵣ₊₁ + s'`, `j = i + 1 - aₙ = (r - 1)aₙ + vₙ₋ᵣ₋₁ + 1`.
  set j := i + 1 - seqA d n with hj
  have hjv : j = (r - 1) * seqA d n + seqV d (n - r - 1) + 1 := by omega
  have hB2 : nrm (xPow d j) ≤ 2 / seqA d (n - r + 1) + s' := by
    have h2pos : (0 : ℝ) ≤ 2 / seqA d (n - r + 1) := by positivity
    suffices hJ : nrm (xPow d j) ≤ s' ∨
        nrm (xPow d j) ≤ 2 / seqA d (n - r + 1) + s' by
      rcases hJ with hJ | hJ <;> linarith
    rcases Nat.lt_or_ge 1 r with hr1' | hr1'
    · rcases Nat.lt_or_ge r (n - 1) with hr | hr
      · -- `1 < r < n - 1`: `j ∈ Iₙ,ᵣ₋₁`, and Lemma 1 (b) brings it down to `vₙ₋ᵣ₋₁ + 1`.
        right
        have hvlt : seqV d (n - r - 1) < seqV d (n - r) := by
          have := seqV_lt_succ hP (n := n - r - 1) (by omega)
          rwa [show n - r - 1 + 1 = n - r by omega] at this
        have hI : (⟨n, r - 1, .I⟩ : Block).Mem d j := by
          refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · rw [hjv]; omega
          · rw [hjv, show n - (r - 1) - 1 = n - r by omega]; omega
        have h1b := nrm_xPow_sub_of_I h hI
        rw [show n - (r - 1) = n - r + 1 by omega] at h1b
        have hbot : j - (r - 1) * seqA d n = seqV d (n - r - 1) + 1 := by omega
        rw [hbot] at h1b
        have hv2 := h.v_small (n - r) (n - r - 1) (by omega)
        have hJ : (⟨n - r, 1, .J⟩ : Block).Mem d (seqV d (n - r - 1) + 1) := by
          refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · simp only [Nat.sub_self, zero_mul, zero_add]
            omega
          · rw [one_mul]; omega
        have hlow : nrm (xPow d (seqV d (n - r - 1) + 1)) ≤ s' := by
          refine nrm_xPow_J_le hP hJ ?_
          have : (8 * (seqV d (n - r - 1) + 1) : ℝ) < seqA d (n - r) := by exact_mod_cast hv2
          push_cast; nlinarith
        calc nrm (xPow d j)
            = nrm ((xPow d j - xPow d (seqV d (n - r - 1) + 1)) +
                xPow d (seqV d (n - r - 1) + 1)) := by rw [sub_add_cancel]
          _ ≤ nrm (xPow d j - xPow d (seqV d (n - r - 1) + 1)) +
                nrm (xPow d (seqV d (n - r - 1) + 1)) := nrm_add_le _ _
          _ ≤ 2 / seqA d (n - r + 1) + s' := add_le_add h1b hlow
      · -- `r = n - 1 > 1`: `j = (n - 2)aₙ + 1 ∈ Jₙ,ₙ₋₁`.
        left
        have hrn1 : r = n - 1 := by omega
        have hv0 : seqV d (n - r - 1) = 0 := by rw [show n - r - 1 = 0 by omega, seqV_zero]
        have ha4 := h.a_big n (by omega)
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have hjk : j = k * seqA d (k + 2) + 1 := by
          rw [hjv, hv0, hrn1]; simp
        have hJ : (⟨k + 2, k + 1, .J⟩ : Block).Mem d j := by
          refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · simp only [show k + 2 - (k + 1) = 1 by omega, show k + 1 - 1 = k by omega, seqV_one]
            omega
          · have : k * seqA d (k + 2) + seqA d (k + 2) = (k + 1) * seqA d (k + 2) := by ring
            omega
        refine (nrm_xPow_J_le hP hJ ?_).trans (rpow_neg_sqrt_anti (by exact_mod_cast ha'n))
        rw [hjk]; push_cast
        have : (4096 : ℝ) ≤ seqA d (k + 2) := by exact_mod_cast ha4
        nlinarith
    · -- `r = 1`: `j = vₙ₋₂ + 1`.
      left
      have hr1e : r = 1 := by omega
      rcases Nat.lt_or_ge 2 n with hn | hn
      · -- `n > 2`: `j ∈ Jₙ₋₁,₁`, and `aₙ₋₁ = aₙ₋ᵣ`.
        have hv2 := h.v_small (n - 1) (n - 2) (by omega)
        have hJ : (⟨n - 1, 1, .J⟩ : Block).Mem d j := by
          refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · rw [hjv, hr1e, show n - 1 - 1 = n - 2 by omega]; simp
          · rw [hjv, hr1e, one_mul, show n - 1 - 1 = n - 2 by omega]; simp; omega
        refine (nrm_xPow_J_le hP hJ ?_).trans (le_of_eq ?_)
        · have : (8 * (seqV d (n - 2) + 1) : ℝ) < seqA d (n - 1) := by exact_mod_cast hv2
          rw [hjv, hr1e, show n - 1 - 1 = n - 2 by omega]; push_cast; simp; nlinarith
        · rw [hs', ha', hr1e]
      · -- `n = 2`: `j = 1 ∈ J₂,₁`.
        have hn2 : n = 2 := by omega
        have hJ : (⟨2, 1, .J⟩ : Block).Mem d j := by
          refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · rw [hjv, hr1e, hn2]; simp [seqV_one, seqV_zero]
          · rw [hjv, hr1e, hn2]; simp [seqV_zero]; have := h.a_big 2 (by omega); omega
        have ha4 := h.a_big 2 (by omega)
        refine (nrm_xPow_J_le hP hJ ?_).trans (rpow_neg_sqrt_anti ?_)
        · rw [hjv, hr1e, hn2]; simp [seqV_zero]
          have : (4096 : ℝ) ≤ seqA d 2 := by exact_mod_cast ha4
          nlinarith
        · rw [ha', hr1e, hn2]; exact_mod_cast seqA_mono h (le_refl 1) (by norm_num)
  -- (C) `aₙ₋ᵣ (‖xⁱ⁺¹‖ + ‖xʲ‖) ≤ aₙ₋ᵣ (2s' + 2/aₙ₋ᵣ₊₁) ≤ 1/aₙ₋ᵣ`.
  have hsmall := sq_mul_rpow_lt (h.rpow_a (n - r) ha'1)
  rw [← hs', ← ha'] at hsmall
  have hs0 : 0 < s' := Real.rpow_pos_of_pos alpha_pos _
  have ha'R : (1 : ℝ) ≤ a' := by exact_mod_cast h.one_le_a (n - r)
  have h8 : 8 * (a' : ℝ) ^ 2 ≤ seqA d (n - r + 1) := by
    exact_mod_cast eight_sq_le_seqA_succ h ha'1
  have hnext : (0 : ℝ) < seqA d (n - r + 1) := by exact_mod_cast h.one_le_a _
  rw [shiftImage_of_I hP hB rfl]
  dsimp only
  rw [nrm_smul, Complex.norm_natCast, le_div_iff₀ (by linarith)]
  have hdiff := nrm_sub_le (xPow d (i + 1)) (xPow d j)
  have hα : alpha = 8 := rfl
  rw [hα] at hsmall
  have hfrac : (a' : ℝ) ^ 2 * (2 / seqA d (n - r + 1)) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hnext (by norm_num)]; nlinarith
  calc (a' : ℝ) * nrm (xPow d (i + 1) - xPow d j) * a'
      ≤ (a' : ℝ) * (s' + (2 / seqA d (n - r + 1) + s')) * a' := by gcongr; linarith
    _ = 2 * ((a' : ℝ) ^ 2 * s') + (a' : ℝ) ^ 2 * (2 / seqA d (n - r + 1)) := by ring
    _ ≤ 1 := by linarith


/-- **Case 3.2° (Remark 3):** at the last index of `Lₙ,ᵣ`, `‖T fᵢ‖ ≤ 1/bₙ`. Here
`i + 1 = r(aₙ + bₙ)` starts `Kₙ,ᵣ`, so Lemma 1 (b) and `‖x^{r aₙ}‖ ≤ 2` give `‖xⁱ⁺¹‖ ≤ 3bₙʳ`,
against a weight of at most `α^{1 - √bₙ/2}`; Śliwa's `bₙ^{4n} < α^{√bₙ/4}` finishes. -/
lemma nrm_shiftImage_L_last (h : GrowthHyp d) {n r i : ℕ}
    (hB : (⟨n, r, .L⟩ : Block).Mem d i) (hi : i + 1 = r * (seqA d n + seqB d n)) :
    nrm (shiftImage d i) ≤ 1 / seqB d n := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hP := h.toPartitionHyp
  have hb2 := h.two_le_b n
  have hbR : (2 : ℝ) ≤ seqB d n := by exact_mod_cast hb2
  -- `‖xⁱ⁺¹‖ ≤ 3 bₙʳ`.
  have hK : (⟨n, r, .K⟩ : Block).Mem d (i + 1) := by
    refine ⟨hr1, hrn, ?_, ?_⟩ <;> dsimp only <;> rw [hi]
    have : r * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have h1b := nrm_xPow_sub_of_K h hK
  have hdown : i + 1 - r * seqB d n = r * seqA d n := by rw [hi]; ring_nf; omega
  rw [hdown] at h1b
  have hra := nrm_xPow_mul_a_le h hr1 hrn
  have hx : nrm (xPow d (i + 1)) ≤ 3 * (seqB d n : ℝ) ^ r := by
    have hpow : 2 * (seqB d n : ℝ) ^ (r - 1) ≤ (seqB d n : ℝ) ^ r := by
      have hsplit : (seqB d n : ℝ) ^ r = (seqB d n : ℝ) ^ (r - 1) * seqB d n := by
        rw [← pow_succ, Nat.sub_add_cancel hr1]
      rw [hsplit]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ seqB d n by linarith) (r - 1)]
    calc nrm (xPow d (i + 1))
        = nrm ((xPow d (i + 1) - (seqB d n : ℂ) ^ r • xPow d (r * seqA d n)) +
            (seqB d n : ℂ) ^ r • xPow d (r * seqA d n)) := by rw [sub_add_cancel]
      _ ≤ nrm (xPow d (i + 1) - (seqB d n : ℂ) ^ r • xPow d (r * seqA d n)) +
            nrm ((seqB d n : ℂ) ^ r • xPow d (r * seqA d n)) := nrm_add_le _ _
      _ ≤ 2 * (seqB d n : ℝ) ^ (r - 1) + (seqB d n : ℝ) ^ r * 2 := by
          rw [nrm_smul, norm_pow, Complex.norm_natCast]
          gcongr
      _ ≤ 3 * (seqB d n : ℝ) ^ r := by linarith
  -- The weight is at most `α^{1 - √bₙ/2} = α s²`, and `bₙ^{4n} s < 1`.
  have hw := weight_le_of_ge (c := seqB d n) (r := r) (i := i) (by omega)
    (by have : (r : ℝ) * seqB d n ≤ r * (seqA d n + seqB d n) := by
          have : (0 : ℝ) ≤ r * seqA d n := by positivity
          nlinarith
        exact_mod_cast (show ((r * seqB d n : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) by
          push_cast; rw [show ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, hi];
          push_cast; nlinarith [show (0 : ℝ) ≤ r * seqA d n by positivity]))
  rw [rpow_one_sub_half] at hw
  set s := alpha ^ (-(Real.sqrt (seqB d n) / 4)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos alpha_pos _
  have hpb := h.pow_b n (by omega)
  have hbs : (seqB d n : ℝ) ^ (4 * n) * s < 1 := by
    have hp : 0 < alpha ^ (Real.sqrt (seqB d n) / 4) := Real.rpow_pos_of_pos alpha_pos _
    rw [hs, Real.rpow_neg alpha_pos.le, ← div_eq_mul_inv, div_lt_one hp]; exact hpb
  -- `24 bₙ^{r+1} ≤ bₙ^{8n}`, as `8n - (r + 1) ≥ 5` and `bₙ ≥ 2`.
  have h24 : 24 * (seqB d n : ℝ) ^ (r + 1) ≤ (seqB d n : ℝ) ^ (8 * n) := by
    have hsplit : (seqB d n : ℝ) ^ (8 * n) =
        (seqB d n : ℝ) ^ (r + 1) * (seqB d n : ℝ) ^ (8 * n - (r + 1)) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have h32 : (32 : ℝ) ≤ (seqB d n : ℝ) ^ (8 * n - (r + 1)) := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (8 * n - (r + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ (seqB d n : ℝ) ^ (8 * n - (r + 1)) := pow_le_pow_left₀ (by norm_num) hbR _
    rw [hsplit]
    have : (0 : ℝ) ≤ (seqB d n : ℝ) ^ (r + 1) := by positivity
    nlinarith
  rw [shiftImage_of_L hP hB rfl]
  dsimp only
  rw [nrm_smul, Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le,
    le_div_iff₀ (by linarith)]
  have hα : alpha = 8 := rfl
  have hx0 := nrm_nonneg (xPow d (i + 1))
  have hαs : 0 ≤ alpha * (s * s) := by rw [hα]; positivity
  have hsq : ((seqB d n : ℝ) ^ (4 * n) * s) ^ 2 < 1 := by
    have : 0 ≤ (seqB d n : ℝ) ^ (4 * n) * s := by positivity
    nlinarith
  calc weight (seqB d n) r i * nrm (xPow d (i + 1)) * seqB d n
      ≤ (alpha * (s * s)) * (3 * (seqB d n : ℝ) ^ r) * seqB d n := by gcongr
    _ = (s * s) * (24 * (seqB d n : ℝ) ^ (r + 1)) := by rw [hα, pow_succ]; ring
    _ ≤ (s * s) * (seqB d n : ℝ) ^ (8 * n) := by gcongr
    _ = ((seqB d n : ℝ) ^ (4 * n) * s) ^ 2 := by
        rw [show 8 * n = 4 * n + 4 * n by ring, pow_add]; ring
    _ ≤ 1 := hsq.le

/-- **`i = 0`:** `T f₀ = x = α^{-(a₂ - 2)/√(4a₂)} f₁`, of norm at most `1`. -/
lemma nrm_shiftImage_zero (h : GrowthHyp d) : nrm (shiftImage d 0) ≤ 1 := by
  have hP := h.toPartitionHyp
  have ha := h.a_big 2 (by norm_num)
  have hJ : (⟨2, 1, .J⟩ : Block).Mem d 1 := by
    refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
    · simp [seqV_one]
    · omega
  rw [shiftImage, ite_eq_left rfl]
  refine (nrm_xPow_J_le hP hJ ?_).trans ?_
  · have : (4096 : ℝ) ≤ seqA d 2 := by exact_mod_cast ha
    push_cast; nlinarith
  · calc alpha ^ (-(Real.sqrt (seqA d 2) / 4)) ≤ alpha ^ (0 : ℝ) :=
          alpha_rpow_le (by have := Real.sqrt_nonneg (seqA d 2 : ℝ); linarith)
      _ = 1 := Real.rpow_zero _

/-- **Śliwa's Lemma 2: `‖T fᵢ‖ ≤ α` for every `i`.** -/
theorem nrm_shiftImage_le (h : GrowthHyp d) (i : ℕ) : nrm (shiftImage d i) ≤ alpha := by
  have hP := h.toPartitionHyp
  have h1α : (1 : ℝ) ≤ alpha := one_le_alpha
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · linarith [nrm_shiftImage_zero h]
  have hB := block_mem hP hi
  rcases hbl : block d i with ⟨n, r, k⟩
  rw [hbl] at hB
  -- A bound `≤ 1/c` with `c ≥ 1` is at most `α`.
  have inv_le : ∀ c : ℕ, 1 ≤ c → (1 : ℝ) / c ≤ alpha := fun c hc ↦ by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    exact (div_le_one (by linarith)).2 this |>.trans h1α
  obtain ⟨hr1, hrn, hk⟩ := id hB
  dsimp only at hr1 hrn hk
  cases k with
  | J =>
    obtain ⟨hlo, hhi⟩ := hk
    rcases Nat.lt_or_ge (i + 1) (r * seqA d n) with hin | hin
    · exact nrm_shiftImage_J_inner hP hB hin
    · exact (nrm_shiftImage_J_last h hB (by omega)).trans (inv_le _ (h.one_le_a n))
  | I =>
    obtain ⟨hlo, hhi⟩ := hk
    rcases Nat.lt_or_ge i (r * seqA d n + seqV d (n - r - 1)) with hin | hin
    · rw [shiftImage_I_inner hP hB hin, nrm_single, norm_one]; exact h1α
    · exact (nrm_shiftImage_I_last h hB (by omega)).trans (inv_le _ (h.one_le_a _))
  | L =>
    obtain ⟨hlo, hhi⟩ := hk
    rcases Nat.lt_or_ge (i + 1) (r * (seqA d n + seqB d n)) with hin | hin
    · exact nrm_shiftImage_L_inner h hB hin
    · exact (nrm_shiftImage_L_last h hB (by omega)).trans
        (inv_le _ (by have := h.two_le_b n; omega))
  | K =>
    obtain ⟨hlo, hhi⟩ := hk
    rcases Nat.lt_or_ge i ((n - 1) * seqA d n + r * seqB d n) with hin | hin
    · rw [shiftImage_K_inner hP hB hin, nrm_single, norm_one]; exact h1α
    · exact (nrm_shiftImage_K_last h hB (by omega)).trans h1α

end ReadL1
