/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma4J
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Abel

/-!
# Śliwa's Lemma 4, Case 2 (`I` blocks)

For `i ∈ Iₙ,ᵣ` above `(m - 1)aₘ` (so `n > m`), `Tˢ fᵢ = aₙ₋ᵣ (xⁱ⁺ˢ - x^{i + s - aₙ})`
(Śliwa pp. 633–634):

* **2.1°** `r = n - m`: here `Qₘ fᵢ = -aₘ xʲ` with `i = r aₙ + j`, and
  `Tˢ (fᵢ - Qₘ fᵢ) = aₘ (xⁱ⁺ˢ - (x^{i + s - aₙ} - x^{j + s}))`; `xⁱ⁺ˢ` is tiny and Lemma 1 (b)
  makes the bracket at most `2/aₘ₊₁`;
* **2.2° (a)** `r > n - m`: both powers are tiny;
* **2.2° (b)** `r < n - m`: either `Tˢ fᵢ = fᵢ₊ₛ`, or `Tˢ fᵢ = T^k (T f_p)` for the last index `p`
  of the block, and Remark 3 gives `‖T f_p‖ ≤ 1/aₙ₋ᵣ` with `aₙ₋ᵣ ≥ aₘ₊₁ ≥ αˢ`.
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- `α^{-√c/4} ≤ 1/c` (from `α c² < α^{√c/4}`). -/
lemma rpow_neg_le_inv {c : ℝ} (hc : 1 ≤ c) (hrp : alpha * c ^ 2 < alpha ^ (Real.sqrt c / 4)) :
    alpha ^ (-(Real.sqrt c / 4)) ≤ 1 / c := by
  have hs := sq_mul_rpow_lt hrp
  have hinv : 1 / alpha ≤ 1 := by rw [div_le_one alpha_pos]; exact one_le_alpha
  have hp : 0 ≤ alpha ^ (-(Real.sqrt c / 4)) := (Real.rpow_pos_of_pos alpha_pos _).le
  rw [le_div_iff₀ (by linarith)]
  have hcc : c ≤ c ^ 2 := by nlinarith
  calc alpha ^ (-(Real.sqrt c / 4)) * c ≤ alpha ^ (-(Real.sqrt c / 4)) * c ^ 2 :=
        mul_le_mul_of_nonneg_left hcc hp
    _ = c ^ 2 * alpha ^ (-(Real.sqrt c / 4)) := by ring
    _ ≤ 1 := by linarith

private lemma four_add_seqV_le (h : GrowthHyp d) {m s n k : ℕ}
    (hm : 2 < m) (hs : InK1 d m s) (hmn : m < n) (hkn : k < n) :
    4 * (seqV d k + s) ≤ seqA d n := by
  have hShift := eight_mul_le_seqA h hm hs hmn
  have hLevel := h.v_small n k hkn
  omega

/-- Lemma 4, Case 2.2° (b): `r < n - m`. -/
lemma lemma4_I_lt (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i)
    (hlt : r + m < n) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hnm : m < n := lt_level_of_JI h (by omega) hB (Or.inr rfl) hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha := h.one_le_a n
  have haR : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha
  have hsa := hs.le_sqrt_a h (by omega) hnm
  have hsmall := four_add_seqV_le h hm hs hnm (show n - r - 1 < n by omega)
  have hsmallR : (4 * (seqV d (n - r - 1) + s) : ℝ) ≤ seqA d n := by exact_mod_cast hsmall
  have hrpa := rpow_neg_le_inv haR (h.rpow_a n (by omega))
  have hαs := hs.alpha_pow_le h (by omega)
  have hone : (1 : ℝ) ≤ alpha := one_le_alpha
  -- 2.2° (b): `r < n - m`, `Qₘ fᵢ = 0`.
  have hq : qImage d m i = 0 :=
    qImage_eq_zero hi (by rw [block_eq hP hB]; simp; omega)
  rw [hq, sub_zero, single_eq_of_I hP hB rfl, map_smul, map_sub, T₀_pow_xPow hP,
    T₀_pow_xPow hP]
  dsimp only
  set V := seqV d (n - r - 1) with hV
  rcases le_or_gt (i + s) (r * seqA d n + V) with hin | hout
  · -- `i + s ∈ Iₙ,ᵣ`: `Tˢ fᵢ = fᵢ₊ₛ`.
    have hB' : (⟨n, r, .I⟩ : Block).Mem d (i + s) := ⟨hr1, hrn, by dsimp; omega, hin⟩
    rw [show i - seqA d n + s = i + s - seqA d n by
      have : seqA d n ≤ i := (Nat.le_mul_of_pos_left _ hr1).trans hlo; omega,
      ← single_eq_of_I hP hB' rfl, nrm_single, norm_one]
    exact hone
  · -- Through `T f_p`, `p = r aₙ + V`.
    set p := r * seqA d n + V with hp
    have hpB : (⟨n, r, .I⟩ : Block).Mem d p := ⟨hr1, hrn, by dsimp; omega, le_rfl⟩
    set k := i + s - (p + 1) with hk
    have hsI := shiftImage_of_I hP hpB rfl
    have hiden : (seqA d (n - r) : ℂ) • (xPow d (i + s) - xPow d (i - seqA d n + s)) =
        (T₀ d ^ k) (shiftImage d p) := by
      have hai : seqA d n ≤ i := (Nat.le_mul_of_pos_left _ hr1).trans hlo
      have hap : seqA d n ≤ p + 1 := by omega
      rw [hsI, map_smul, map_sub, T₀_pow_xPow hP, T₀_pow_xPow hP]
      dsimp only
      rw [show p + 1 + k = i + s by omega,
        show p + 1 - seqA d n + k = i - seqA d n + s by omega]
    rw [hiden]
    have hrem := nrm_shiftImage_I_last h hpB rfl
    have hTk := nrm_T₀_pow_le h k (shiftImage d p)
    have hnr : (seqA d (m + 1) : ℝ) ≤ seqA d (n - r) := by
      exact_mod_cast seqA_mono h (by omega) (by omega)
    have hnr0 : (0 : ℝ) < seqA d (n - r) := by exact_mod_cast h.one_le_a _
    have hks : k ≤ s := by omega
    calc nrm ((T₀ d ^ k) (shiftImage d p))
        ≤ alpha ^ k * (1 / seqA d (n - r)) :=
          hTk.trans (mul_le_mul_of_nonneg_left hrem (pow_nonneg alpha_pos.le _))
      _ ≤ alpha ^ s * (1 / seqA d (n - r)) := by
          gcongr
      _ ≤ seqA d (n - r) * (1 / seqA d (n - r)) := by gcongr; linarith
      _ = 1 := by field_simp
      _ ≤ alpha := hone

/-- Lemma 4, Case 2.1°: `r = n - m`. -/
lemma lemma4_I_eq (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i)
    (heq : r + m = n) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hnm : m < n := lt_level_of_JI h (by omega) hB (Or.inr rfl) hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha := h.one_le_a n
  have haR : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha
  have hsa := hs.le_sqrt_a h (by omega) hnm
  have hsmall := four_add_seqV_le h hm hs hnm (show n - r - 1 < n by omega)
  have hsmallR : (4 * (seqV d (n - r - 1) + s) : ℝ) ≤ seqA d n := by exact_mod_cast hsmall
  have hrpa := rpow_neg_le_inv haR (h.rpow_a n (by omega))
  have hαs := hs.alpha_pow_le h (by omega)
  have hone : (1 : ℝ) ≤ alpha := one_le_alpha
  -- 2.1°: `r = n - m`, `Qₘ fᵢ = -aₘ xʲ`, `j = i - r aₙ`.
  have hq : qImage d m i = -(seqA d m : ℂ) • xPow d (i - r * seqA d n) := by
    rw [qImage, ite_eq_right (by omega), block_eq hP hB, ite_eq_left ⟨rfl, heq⟩]
    dsimp only; rw [show n - m = r by omega]
  have hnrm : n - r = m := by omega
  set j := i - r * seqA d n with hj
  have hjV : j ≤ seqV d (m - 1) := by rw [show m - 1 = n - r - 1 by omega]; omega
  rw [hq, single_eq_of_I hP hB rfl]
  dsimp only
  rw [hnrm, neg_smul, sub_neg_eq_add, map_add, map_smul, map_smul,
    map_sub, T₀_pow_xPow hP, T₀_pow_xPow hP, T₀_pow_xPow hP, ← smul_add]
  rw [show i - seqA d n + s = i + s - seqA d n by
    have : seqA d n ≤ i := (Nat.le_mul_of_pos_left _ hr1).trans hlo; omega]
  -- `xⁱ⁺ˢ ∈ Jₙ,ᵣ₊₁`, tiny.
  have hJ : (⟨n, r + 1, .J⟩ : Block).Mem d (i + s) := by
    have hvm := h.v_small m (m - 1) (by omega)
    have hsv : seqV d (m - 1) < s := by have := hs.1; omega
    refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
    · rw [Nat.add_sub_cancel, show n - (r + 1) = n - r - 1 by omega,
        show n - r - 1 = m - 1 by omega]; omega
    · rw [Nat.add_mul, one_mul]
      rw [show m - 1 = n - r - 1 by omega] at hjV; omega
  have hxJ : nrm (xPow d (i + s)) ≤ 1 / seqA d n := by
    refine (nrm_xPow_J_le hP hJ ?_).trans hrpa
    have hij : i = r * seqA d n + j := by omega
    rw [hij]; push_cast
    have : (4 * (j + s) : ℝ) ≤ seqA d n := by
      have : 4 * (j + s) ≤ seqA d n := by
        rw [show m - 1 = n - r - 1 by omega] at hjV; omega
      exact_mod_cast this
    nlinarith
  -- `‖x^{i + s - aₙ} - x^{j + s}‖ ≤ 2/aₘ₊₁` (Lemma 1 (b) on `Iₙ,ᵣ₋₁`, or `0` if `r = 1`).
  have hdiff : nrm (xPow d (i + s - seqA d n) - xPow d (j + s)) ≤ 2 / seqA d (m + 1) := by
    rcases Nat.eq_or_lt_of_le hr1 with hr1' | hr1'
    · subst hr1'
      rw [show i + s - seqA d n = j + s by omega, sub_self, nrm_zero]
      positivity
    · have hI : (⟨n, r - 1, .I⟩ : Block).Mem d (i + s - seqA d n) := by
        have hvm : seqV d (m - 1) + s ≤ seqV d m := by
          have := hs.2
          have hvlt := h.v_small m (m - 1) (by omega)
          have hab : seqA d m ≤ seqB d m := by
            have := h.a_small m (by omega); nlinarith
          have hvm_eq : seqV d m = (m - 1) * seqA d m + (m - 1) * seqB d m := by
            unfold seqV; ring
          have e : (m - 1) * seqB d m = seqB d m + (m - 2) * seqB d m := by
            rw [show m - 1 = 1 + (m - 2) by omega]; ring
          have : seqA d m ≤ (m - 2) * seqB d m :=
            le_trans hab (Nat.le_mul_of_pos_left _ (by omega))
          omega
        have hrsucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
        refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · omega
        · rw [show n - (r - 1) - 1 = n - r by omega, hnrm]
          have hvv : seqV d (n - r - 1) = seqV d (m - 1) := by
            rw [show n - r - 1 = m - 1 by omega]
          omega
      have h1b := nrm_xPow_sub_of_I h hI
      rw [show n - (r - 1) = m + 1 by omega,
        show i + s - seqA d n - (r - 1) * seqA d n = j + s by
          have hrsucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
          omega] at h1b
      exact h1b
  -- Total: `aₘ (1/aₙ + 2/aₘ₊₁) ≤ 3aₘ/aₘ₊₁ ≤ 1`.
  have hm1 : (seqA d (m + 1) : ℝ) ≤ seqA d n := by
    exact_mod_cast seqA_mono h (by omega) (by omega)
  have h8 : 8 * (seqA d m : ℝ) ^ 2 ≤ seqA d (m + 1) := by
    exact_mod_cast eight_sq_le_seqA_succ h (by omega)
  have hamR : (1 : ℝ) ≤ seqA d m := by exact_mod_cast h.one_le_a m
  have hm10 : (0 : ℝ) < seqA d (m + 1) := by nlinarith
  rw [nrm_smul, Complex.norm_natCast]
  have hsub := nrm_sub_le (xPow d (i + s)) (xPow d (i + s - seqA d n) - xPow d (j + s))
  rw [show xPow d (i + s) - xPow d (i + s - seqA d n) + xPow d (j + s) =
    xPow d (i + s) - (xPow d (i + s - seqA d n) - xPow d (j + s)) by abel]
  have hinv : 1 / (seqA d n : ℝ) ≤ 1 / seqA d (m + 1) := by gcongr
  calc (seqA d m : ℝ) * nrm (xPow d (i + s) - (xPow d (i + s - seqA d n) - xPow d (j + s)))
      ≤ seqA d m * (1 / seqA d (m + 1) + 2 / seqA d (m + 1)) := by gcongr; linarith
    _ = 3 * seqA d m / seqA d (m + 1) := by ring
    _ ≤ 1 := by rw [div_le_one hm10]; nlinarith
    _ ≤ alpha := hone

/-- Lemma 4, Case 2.2° (a): `r > n - m`. -/
lemma lemma4_I_gt (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i)
    (hgt : n < r + m) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hnm : m < n := lt_level_of_JI h (by omega) hB (Or.inr rfl) hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha := h.one_le_a n
  have haR : (1 : ℝ) ≤ seqA d n := by exact_mod_cast ha
  have hsa := hs.le_sqrt_a h (by omega) hnm
  have hsmall := four_add_seqV_le h hm hs hnm (show n - r - 1 < n by omega)
  have hsmallR : (4 * (seqV d (n - r - 1) + s) : ℝ) ≤ seqA d n := by exact_mod_cast hsmall
  have hrpa := rpow_neg_le_inv haR (h.rpow_a n (by omega))
  have hαs := hs.alpha_pow_le h (by omega)
  have hone : (1 : ℝ) ≤ alpha := one_le_alpha
  -- 2.2° (a): `r > n - m`, `Qₘ fᵢ = 0`.
  have hq : qImage d m i = 0 :=
    qImage_eq_zero hi (by rw [block_eq hP hB]; simp; omega)
  rw [hq, sub_zero, single_eq_of_I hP hB rfl, map_smul, map_sub, T₀_pow_xPow hP,
    T₀_pow_xPow hP]
  dsimp only
  have hai : seqA d n ≤ i := (Nat.le_mul_of_pos_left _ hr1).trans hlo
  rw [show i - seqA d n + s = i + s - seqA d n by omega]
  have hv1 : seqV d (n - r) < s := by
    have hvm := seqV_mono hP (show n - r ≤ m - 1 by omega)
    have := h.v_small m (m - 1) (by omega)
    have := hs.1; omega
  have hrsucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  -- `x^{i + s - aₙ} ∈ Jₙ,ᵣ`.
  have hJ1 : (⟨n, r, .J⟩ : Block).Mem d (i + s - seqA d n) :=
    ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
  have hx1 : nrm (xPow d (i + s - seqA d n)) ≤ alpha ^ (-(Real.sqrt (seqA d n) / 4)) := by
    refine nrm_xPow_J_le hP hJ1 ?_
    have : ((i + s - seqA d n : ℕ) : ℝ) = i + s - seqA d n := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]
    have : (4 * (i + s) : ℝ) ≤ (4 * r + 1) * seqA d n := by
      have : 4 * (i + s) ≤ (4 * r + 1) * seqA d n := by
        have := Nat.mul_le_mul_left 4 hhi; nlinarith
      exact_mod_cast this
    nlinarith
  -- `xⁱ⁺ˢ` in `Jₙ,ᵣ₊₁` or `Lₙ,₁`.
  have hx2 : nrm (xPow d (i + s)) ≤ alpha ^ (-(Real.sqrt (seqA d n) / 4)) := by
    rcases Nat.lt_or_ge (r + 1) n with hr' | hr'
    · have hJ2 : (⟨n, r + 1, .J⟩ : Block).Mem d (i + s) := by
        refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · rw [Nat.add_sub_cancel, show n - (r + 1) = n - r - 1 by omega]
          have := seqV_mono hP (show n - r - 1 ≤ n - r by omega); omega
        · rw [Nat.add_mul, one_mul]; omega
      refine nrm_xPow_J_le hP hJ2 ?_
      push_cast
      have : (4 * (i + s) : ℝ) ≤ (4 * r + 1) * seqA d n := by
        have : 4 * (i + s) ≤ (4 * r + 1) * seqA d n := by nlinarith
        exact_mod_cast this
      nlinarith
    · have hrn1 : r + 1 = n := by omega
      have hv0 : seqV d (n - r - 1) = 0 := by rw [show n - r - 1 = 0 by omega, seqV_zero]
      -- Linear facts: `i ≤ r aₙ`, `r aₙ + aₙ = n aₙ`, `8n aₙ < bₙ`, `4s ≤ aₙ`.
      have hab := h.a_small n (by omega)
      have e3 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
      have er : r * seqA d n + seqA d n = n * seqA d n := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, hrn1]
      rw [hv0] at hsmall hhi
      have h4b : 4 * (i + s) ≤ seqB d n := by omega
      have hL : (⟨n, 1, .L⟩ : Block).Mem d (i + s) := by
        refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
        · rw [Nat.sub_self, zero_mul, add_zero, show n - 1 = r by omega]; omega
        · rw [one_mul]; omega
      refine (nrm_xPow_L_le h hL ?_).trans (rpow_neg_sqrt_anti ?_)
      · push_cast
        have : (4 * (i + s) : ℝ) ≤ seqB d n := by exact_mod_cast h4b
        linarith
      · have : seqA d n ≤ seqB d n := by omega
        exact_mod_cast this
  -- Total: `aₙ₋ᵣ (2α^{-√aₙ/4}) ≤ 2aₙ/aₙ ... ≤ 1`.
  have hnr : (seqA d (n - r) : ℝ) ≤ seqA d n := by
    exact_mod_cast seqA_mono h (by omega) (by omega)
  have hsm := sq_mul_rpow_lt (h.rpow_a n (by omega))
  obtain ⟨sa, hsa⟩ : ∃ x, x = alpha ^ (-(Real.sqrt (seqA d n) / 4)) := ⟨_, rfl⟩
  rw [← hsa] at hx1 hx2 hsm
  have hsa0 : 0 < sa := hsa ▸ Real.rpow_pos_of_pos alpha_pos _
  have hinv : 1 / alpha ≤ 1 / 2 := by
    rw [div_le_div_iff₀ alpha_pos (by norm_num)]; norm_num [alpha]
  have haa : (seqA d n : ℝ) * sa ≤ (seqA d n : ℝ) ^ 2 * sa :=
    mul_le_mul_of_nonneg_right (le_self_pow₀ haR (by norm_num)) hsa0.le
  rw [nrm_smul, Complex.norm_natCast]
  have hsub := nrm_sub_le (xPow d (i + s)) (xPow d (i + s - seqA d n))
  have hsum : nrm (xPow d (i + s) - xPow d (i + s - seqA d n)) ≤ sa + sa :=
    hsub.trans (add_le_add hx2 hx1)
  calc (seqA d (n - r) : ℝ) * nrm (xPow d (i + s) - xPow d (i + s - seqA d n))
      ≤ seqA d n * (sa + sa) :=
        mul_le_mul hnr hsum (nrm_nonneg _) (by positivity)
    _ = 2 * ((seqA d n : ℝ) * sa) := by ring
    _ ≤ 1 := by linarith only [haa, hsm, hinv]
    _ ≤ alpha := hone

/-- **Lemma 4, Case 2.** -/
lemma lemma4_I (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .I⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  rcases Nat.lt_trichotomy (r + m) n with hlt | heq | hgt
  · exact lemma4_I_lt h hm hs hB hi hlt
  · exact lemma4_I_eq h hm hs hB hi heq
  · exact lemma4_I_gt h hm hs hB hi hgt

end ReadL1
