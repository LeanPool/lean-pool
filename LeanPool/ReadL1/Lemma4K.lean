/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma4L
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 4, Case 4 (`K` blocks)

For `i ∈ Kₙ,ᵣ` above `(m - 1)aₘ` (so `n ≥ m`), `Qₘ fᵢ = 0` and `Tˢ fᵢ = xʲ - bₙ x^{j - bₙ}` with
`j = i + s` (Śliwa p. 635). Either `j` stays in a `K` block and `Tˢ fᵢ = fⱼ` (4.1°, 4.3°), or
`‖xʲ‖ ≤ 1` and `‖x^{j - bₙ}‖ ≤ 1/bₙ`, so `‖Tˢ fᵢ‖ ≤ 2` (4.2°, 4.4°).
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

private theorem nrm_K_difference_le {n j : ℕ} (hb : 0 < seqB d n)
    (hOne : nrm (xPow d j) ≤ 1) (hInv : nrm (xPow d (j - seqB d n)) ≤ 1 / seqB d n) :
    nrm (xPow d j - (seqB d n : ℂ) • xPow d (j - seqB d n)) ≤ alpha := by
  have hbReal : (0 : ℝ) < seqB d n := by exact_mod_cast hb
  have hDifference := nrm_sub_le (xPow d j) ((seqB d n : ℂ) • xPow d (j - seqB d n))
  rw [nrm_smul, Complex.norm_natCast] at hDifference
  have hProduct := mul_le_mul_of_nonneg_left hInv hbReal.le
  rw [mul_one_div_cancel hbReal.ne'] at hProduct
  exact hDifference.trans ((add_le_add hOne hProduct).trans (by norm_num [alpha]))

private theorem nrm_K_difference_le_of_mem {n r j : ℕ} (h : PartitionHyp d)
    (hK : (⟨n, r, .K⟩ : Block).Mem d j) :
    nrm (xPow d j - (seqB d n : ℂ) • xPow d (j - seqB d n)) ≤ alpha := by
  rw [← single_eq_of_K h hK rfl, nrm_single, norm_one]
  exact one_le_alpha

private theorem nrm_K_eq_predecessor_le (h : GrowthHyp d) {m r j : ℕ}
    (hr1 : 1 ≤ r) (hrn : r < m)
    (hjLower : (m - 1) * seqA d m + (r + 1) * seqB d m < j)
    (hjUpper : j ≤ 2 * ((m - 1) * seqA d m) + (r + 1) * seqB d m)
    (hLength : 8 * ((m - 1) * seqA d m) ≤ seqB d m)
    (hjNext : 4 * j < seqA d (m + 1)) :
    nrm (xPow d (j - seqB d m)) ≤ 1 / seqB d m := by
  have hm : 1 ≤ m := by omega
  have hP := h.toPartitionHyp
  have hb2 := h.two_le_b m
  have hbR : (1 : ℝ) ≤ seqB d m := by exact_mod_cast (show 1 ≤ seqB d m by omega)
  have hbJ : seqB d m ≤ j := by
    have := Nat.le_mul_of_pos_left (seqB d m) (by omega : 0 < r + 1)
    omega
  have hrb : (r + 1) * seqB d m = r * seqB d m + seqB d m := by
    rw [Nat.add_mul, one_mul]
  rcases Nat.lt_or_ge (r + 1) m with hr | hr
  · have hL : (⟨m, r + 1, .L⟩ : Block).Mem d (j - seqB d m) := by
      refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
      · rw [Nat.add_sub_cancel]
        omega
      · rw [Nat.mul_add, hrb]
        omega
    refine (nrm_xPow_L_le h hL ?_).trans (rpow_neg_le_inv hbR (h.rpow_b m hm))
    have hjR : (j : ℝ) ≤ ((2 * ((m - 1) * seqA d m) + (r + 1) * seqB d m : ℕ) : ℝ) :=
      by exact_mod_cast hjUpper
    have hLenR : ((8 * ((m - 1) * seqA d m) : ℕ) : ℝ) ≤ seqB d m :=
      by exact_mod_cast hLength
    rw [Nat.cast_sub hbJ]
    push_cast at hjR hLenR ⊢
    linarith only [hjR, hLenR]
  · have hrEq : r + 1 = m := by omega
    have hv : seqV d m = (m - 1) * seqA d m + r * seqB d m := by
      unfold seqV
      rw [Nat.mul_add, show m - 1 = r by omega]
    have hJ : (⟨m + 1, 1, .J⟩ : Block).Mem d (j - seqB d m) := by
      refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
      · simp only [Nat.sub_self, zero_mul, zero_add, Nat.add_sub_cancel]
        omega
      · rw [one_mul]
        omega
    have haR : (1 : ℝ) ≤ seqA d (m + 1) := by exact_mod_cast h.one_le_a (m + 1)
    have hbA : seqB d m ≤ seqA d (m + 1) := by
      have hSmall := h.b_small m hm
      have := Nat.le_mul_of_pos_left (seqB d m) (by omega : 0 < m)
      omega
    refine ((nrm_xPow_J_le hP hJ ?_).trans
      (rpow_neg_le_inv haR (h.rpow_a (m + 1) (by omega)))).trans ?_
    · have hjR : (4 * j : ℝ) < seqA d (m + 1) := by exact_mod_cast hjNext
      rw [Nat.cast_sub hbJ]
      push_cast
      linarith only [hjR, hbR]
    · gcongr

/-- Lemma 4, Case 4 with `n = m`. -/
lemma lemma4_K_eq (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i)
    (hmn : m = n) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hq : qImage d m i = 0 := qImage_eq_zero hi (by rw [block_eq hP hB]; simp)
  have hnm : m ≤ n := le_level h (by omega) hB hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hb2 := h.two_le_b n
  have hb0 : 0 < seqB d n := by omega
  have hbR : (2 : ℝ) ≤ seqB d n := by exact_mod_cast hb2
  have ha := h.one_le_a n
  have hab := h.a_small n (by omega)
  have e3 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
  have hna : (n - 1) * seqA d n + seqA d n = n * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hrb : (r - 1) * seqB d n + seqB d n = r * seqB d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  have hrab : r * (seqA d n + seqB d n) = r * seqA d n + r * seqB d n := by ring
  have hran : r * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have hvn : seqV d n = (n - 1) * seqA d n + (n - 1) * seqB d n := by unfold seqV; ring
  have hrbn : r * seqB d n ≤ (n - 1) * seqB d n := Nat.mul_le_mul_right _ (by omega)
  have hiv : i ≤ seqV d n := by omega
  have hr1b : (r + 1) * seqB d n = r * seqB d n + seqB d n := by ring
  have hman : (n - 1) * seqA d n ≤ n * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have h4j := four_add_lt h (by omega) hs hnm hiv
  have h2b := hs.le_two_b h (by omega)
  have hs1 := hs.1
  have hs2 := hs.2
  rw [hq, sub_zero, single_eq_of_K hP hB rfl, map_sub, map_smul, T₀_pow_xPow hP,
    T₀_pow_xPow hP]
  dsimp only
  have hbi : seqB d n ≤ i := by
    have : seqB d n ≤ r * seqB d n := Nat.le_mul_of_pos_left _ hr1
    omega
  rw [show i - seqB d n + s = i + s - seqB d n by omega]
  set j := i + s with hj
  have two_bound := nrm_K_difference_le (d := d) (n := n) (j := j) hb0
  have one_bound := fun r' => nrm_K_difference_le_of_mem (n := n) (j := j) (r := r') hP
  -- `n = m`.
  subst hmn
  rcases le_or_gt j ((m - 1) * seqA d m + (r + 1) * seqB d m) with h41 | h42
  · -- 4.1°: `j ∈ Kₘ,ᵣ₊₁`.
    have hK : (⟨m, r + 1, .K⟩ : Block).Mem d j := by
      refine ⟨by dsimp; omega, ?_, ?_, h41⟩
      · dsimp only
        by_contra hc
        have : (m - 1) * seqA d m < (r + 1) * seqA d m := Nat.mul_lt_mul_of_pos_right
          (by omega) (by omega)
        have : (r + 1) * (seqA d m + seqB d m) ≤ j := by
          have : (r + 1) * (seqA d m + seqB d m) = r * seqA d m + r * seqB d m +
            seqA d m + seqB d m := by ring
          omega
        rw [Nat.add_mul] at h41; nlinarith
      · dsimp only
        have : (r + 1) * (seqA d m + seqB d m) = r * seqA d m + r * seqB d m +
          seqA d m + seqB d m := by ring
        omega
    exact one_bound _ hK
  · -- 4.2°.
    have h1 : nrm (xPow d j) ≤ 1 := by
      rcases Nat.lt_or_ge (r + 2) m with hr2 | hr2
      · have hL : (⟨m, r + 2, .L⟩ : Block).Mem d j := by
          refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · rw [show r + 2 - 1 = r + 1 by omega]; omega
          · have : (r + 2) * (seqA d m + seqB d m) =
                r * seqA d m + r * seqB d m + 2 * seqA d m + 2 * seqB d m := by ring
            omega
        refine nrm_xPow_L_le_one hP hL ?_
        have hjN : j ≤ 2 * ((m - 1) * seqA d m) + (r + 1) * seqB d m := by omega
        have hjb : (j : ℝ) ≤ ((2 * ((m - 1) * seqA d m) + (r + 1) * seqB d m : ℕ) : ℝ) := by
          exact_mod_cast hjN
        push_cast at hjb
        have h4N : 4 * ((m - 1) * seqA d m) ≤ seqB d m := by omega
        have h4 : ((4 * ((m - 1) * seqA d m) : ℕ) : ℝ) ≤ seqB d m := by exact_mod_cast h4N
        push_cast at h4
        push_cast; linarith
      · have hJ : (⟨m + 1, 1, .J⟩ : Block).Mem d j := by
          refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · simp only [Nat.sub_self, zero_mul, zero_add, Nat.add_sub_cancel]
            have : (m - 1) * seqB d m ≤ (r + 1) * seqB d m := Nat.mul_le_mul_right _ (by omega)
            omega
          · rw [one_mul]; omega
        refine nrm_xPow_J_le_one hP hJ ?_
        have : (4 * j : ℝ) < seqA d (m + 1) := by exact_mod_cast h4j
        push_cast; linarith
    have hjUpper : j ≤ 2 * ((m - 1) * seqA d m) + (r + 1) * seqB d m := by omega
    have hLength : 8 * ((m - 1) * seqA d m) ≤ seqB d m := by omega
    have h2 := nrm_K_eq_predecessor_le h hr1 hrn h42 hjUpper hLength h4j
    exact two_bound h1 h2

/-- Lemma 4, Case 4 with `n > m`. -/
lemma lemma4_K_gt (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i)
    (hmn : m < n) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hq : qImage d m i = 0 := qImage_eq_zero hi (by rw [block_eq hP hB]; simp)
  have hnm : m ≤ n := le_level h (by omega) hB hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hb2 := h.two_le_b n
  have hb0 : 0 < seqB d n := by omega
  have hbR : (2 : ℝ) ≤ seqB d n := by exact_mod_cast hb2
  have ha := h.one_le_a n
  have hab := h.a_small n (by omega)
  have e3 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
  have hna : (n - 1) * seqA d n + seqA d n = n * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hrb : (r - 1) * seqB d n + seqB d n = r * seqB d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  have hrab : r * (seqA d n + seqB d n) = r * seqA d n + r * seqB d n := by ring
  have hran : r * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have hvn : seqV d n = (n - 1) * seqA d n + (n - 1) * seqB d n := by unfold seqV; ring
  have hrbn : r * seqB d n ≤ (n - 1) * seqB d n := Nat.mul_le_mul_right _ (by omega)
  have hiv : i ≤ seqV d n := by omega
  have hr1b : (r + 1) * seqB d n = r * seqB d n + seqB d n := by ring
  have hman : (n - 1) * seqA d n ≤ n * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have h4j := four_add_lt h (by omega) hs hnm hiv
  have h2b := hs.le_two_b h (by omega)
  have hs1 := hs.1
  have hs2 := hs.2
  rw [hq, sub_zero, single_eq_of_K hP hB rfl, map_sub, map_smul, T₀_pow_xPow hP,
    T₀_pow_xPow hP]
  dsimp only
  have hbi : seqB d n ≤ i := by
    have : seqB d n ≤ r * seqB d n := Nat.le_mul_of_pos_left _ hr1
    omega
  rw [show i - seqB d n + s = i + s - seqB d n by omega]
  set j := i + s with hj
  have two_bound := nrm_K_difference_le (d := d) (n := n) (j := j) hb0
  have one_bound := fun r' => nrm_K_difference_le_of_mem (n := n) (j := j) (r := r') hP
  -- `α^{-√c/4} ≤ 1/c` for `c = bₙ` and `c = aₙ₊₁ ≥ bₙ`.
  have hrpb := rpow_neg_le_inv (show (1 : ℝ) ≤ seqB d n by linarith) (h.rpow_b n (by omega))
  have hbA : seqB d n ≤ seqA d (n + 1) := by
    have := h.b_small n (by omega)
    have : seqB d n ≤ n * seqB d n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hrpa := rpow_neg_le_inv (show (1 : ℝ) ≤ seqA d (n + 1) by
    exact_mod_cast h.one_le_a (n + 1)) (h.rpow_a (n + 1) (by omega))
  have hAinv : 1 / (seqA d (n + 1) : ℝ) ≤ 1 / seqB d n := by
    gcongr
  -- `n > m`.
  have hsa := hs.le_sqrt_a h (by omega) hmn
  have hsmall : 8 * s ≤ seqA d n := eight_mul_le_seqA h hm hs hmn
  rcases le_or_gt j ((n - 1) * seqA d n + r * seqB d n) with h43 | h44
  · -- 4.3°: `j ∈ Kₙ,ᵣ`.
    exact one_bound r ⟨hr1, hrn, by dsimp; omega, h43⟩
  · -- 4.4°.
    have h1 : nrm (xPow d j) ≤ 1 := by
      rcases Nat.lt_or_ge (r + 1) n with hr' | hr'
      · have hL : (⟨n, r + 1, .L⟩ : Block).Mem d j := by
          refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · rw [Nat.add_sub_cancel]; omega
          · have : (r + 1) * (seqA d n + seqB d n) =
                r * seqA d n + r * seqB d n + seqA d n + seqB d n := by ring
            omega
        refine nrm_xPow_L_le_one hP hL ?_
        have hjb : (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * seqA d n + r * seqB d n + s := by
          have : j ≤ (n - 1) * seqA d n + r * seqB d n + s := by omega
          exact_mod_cast this
        have h4N : 2 * ((n - 1) * seqA d n) + 2 * s ≤ seqB d n := by omega
        have h4 : ((2 * ((n - 1) * seqA d n) + 2 * s : ℕ) : ℝ) ≤ seqB d n := by
          exact_mod_cast h4N
        push_cast at h4
        push_cast; linarith
      · have hJ : (⟨n + 1, 1, .J⟩ : Block).Mem d j := by
          refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
          · simp only [Nat.sub_self, zero_mul, zero_add, Nat.add_sub_cancel]
            have : (n - 1) * seqB d n ≤ r * seqB d n := Nat.mul_le_mul_right _ (by omega)
            omega
          · rw [one_mul]; omega
        refine nrm_xPow_J_le_one hP hJ ?_
        have : (4 * j : ℝ) < seqA d (n + 1) := by exact_mod_cast h4j
        push_cast; linarith
    have h2 : nrm (xPow d (j - seqB d n)) ≤ 1 / seqB d n := by
      have hL : (⟨n, r, .L⟩ : Block).Mem d (j - seqB d n) := by
        refine ⟨hr1, hrn, ?_, ?_⟩ <;> dsimp only
        · omega
        · omega
      refine (nrm_xPow_L_le h hL ?_).trans hrpb
      have hjb : (j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * seqA d n + r * seqB d n + s := by
        have : j ≤ (n - 1) * seqA d n + r * seqB d n + s := by omega
        exact_mod_cast this
      have h4N : 4 * ((n - 1) * seqA d n) + 4 * s ≤ seqB d n := by omega
      have h4 : ((4 * ((n - 1) * seqA d n) + 4 * s : ℕ) : ℝ) ≤ seqB d n := by
        exact_mod_cast h4N
      push_cast at h4
      rw [Nat.cast_sub (by omega)]
      linarith
    exact two_bound h1 h2

/-- **Lemma 4, Case 4.** -/
lemma lemma4_K (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hnm : m ≤ n := le_level h (by omega) hB hi
  rcases Nat.eq_or_lt_of_le hnm with hmn | hmn
  · exact lemma4_K_eq h hm hs hB hi hmn
  · exact lemma4_K_gt h hm hs hB hi hmn

end ReadL1
