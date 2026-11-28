/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma4I
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 4, Case 3 (`L` blocks)

For `i ∈ Lₙ,ᵣ` above `(m - 1)aₘ` (so `n ≥ m`), `Qₘ fᵢ = 0` and `Tˢ fᵢ = cᵢ xʲ` with `j = i + s`
(Śliwa p. 634). With `n = m`: `j` lies in `Jₙ₊₁,₁` (3.1°), `Lₙ,ᵣ₊₁`, `Kₙ,ᵣ₊₁` or `Lₙ,ᵣ₊₂` (3.2°).
With `n > m`: `j` is still in `Lₙ,ᵣ` (3.3°), or `Tˢ fᵢ` passes through `T f_{r(aₙ + bₙ) - 1}`, which
Remark 3 bounds by `1/bₙ` (3.4°).
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/- ### Weights and small powers -/

/-- The ratio of two weights of the same `c` is a power of `α`. -/
lemma weight_mul_inv_weight (c r i r' j : ℕ) :
    weight c r i * (weight c r' j)⁻¹ =
      alpha ^ ((((2 * (r : ℝ) - 1) * c - 2 * i) - ((2 * (r' : ℝ) - 1) * c - 2 * j)) /
        Real.sqrt (4 * c)) := by
  rw [weight, weight, ← Real.rpow_neg alpha_pos.le, ← Real.rpow_add alpha_pos]
  congr 1; ring

/-- A weight is at most `α^{√c/2}` when its numerator is at most `c`. -/
lemma weight_le_half {c r i : ℕ} (hc : 0 < c) (hE : (2 * (r : ℝ) - 1) * c - 2 * i ≤ c) :
    weight c r i ≤ alpha ^ (Real.sqrt c / 2) := by
  refine alpha_rpow_le ?_
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  rw [sqrt_four_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- A weight is at most `α^{-√c/4}` when its numerator is at most `-c/2`. -/
lemma weight_le_neg {c r i : ℕ} (hc : 0 < c) (hE : (2 * (r : ℝ) - 1) * c - 2 * i ≤ -(c / 2)) :
    weight c r i ≤ alpha ^ (-(Real.sqrt c / 4)) := by
  refine alpha_rpow_le ?_
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  rw [sqrt_four_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- `‖xʲ‖ ≤ 1` on a `J` block whose numerator is nonnegative. -/
lemma nrm_xPow_J_le_one (h : PartitionHyp d) {N R j : ℕ} (hB : (⟨N, R, .J⟩ : Block).Mem d j)
    (hE : 0 ≤ (2 * (R : ℝ) - 1) * seqA d N - 2 * j) : nrm (xPow d j) ≤ 1 := by
  rw [nrm_xPow_of_J h hB rfl, inv_weight]
  calc _ ≤ alpha ^ (0 : ℝ) :=
        alpha_rpow_le (by have := div_nonneg hE (Real.sqrt_nonneg (4 * (seqA d N : ℝ)))
                          dsimp only at this ⊢; linarith)
    _ = 1 := Real.rpow_zero _

/-- `‖xʲ‖ ≤ 1` on an `L` block whose numerator is nonnegative. -/
lemma nrm_xPow_L_le_one (h : PartitionHyp d) {N R j : ℕ} (hB : (⟨N, R, .L⟩ : Block).Mem d j)
    (hE : 0 ≤ (2 * (R : ℝ) - 1) * seqB d N - 2 * j) : nrm (xPow d j) ≤ 1 := by
  rw [nrm_xPow_of_L h hB rfl, inv_weight]
  calc _ ≤ alpha ^ (0 : ℝ) :=
        alpha_rpow_le (by have := div_nonneg hE (Real.sqrt_nonneg (4 * (seqB d N : ℝ)))
                          dsimp only at this ⊢; linarith)
    _ = 1 := Real.rpow_zero _

/-- Above `(m - 1)aₘ`, every block has level at least `m`: lower levels end by `vₘ₋₁ < aₘ`. -/
lemma le_level (h : GrowthHyp d) {m i : ℕ} (hm : 2 ≤ m) {B : Block} (hB : B.Mem d i)
    (hi : (m - 1) * seqA d m < i) : m ≤ B.n := by
  have hP := h.toPartitionHyp
  have hhi := ((B.mem_level hP hB).2.1)
  by_contra hnm
  have hv := seqV_mono hP (show B.n ≤ m - 1 by omega)
  have hva := hP.v_lt_a m (m - 1) (by omega)
  have : seqA d m ≤ (m - 1) * seqA d m := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- `4j < aₙ₊₁` for `j = i + s` with `i ≤ vₙ`, `n ≥ m`. -/
lemma four_add_lt (h : GrowthHyp d) {m s n i : ℕ} (hm : 2 ≤ m) (hs : InK1 d m s) (hnm : m ≤ n)
    (hi : i ≤ seqV d n) : 4 * (i + s) < seqA d (n + 1) := by
  have h2b := hs.le_two_b h (by omega)
  have hv := h.v_small (n + 1) n (by omega)
  have hb := h.b_small n (by omega)
  have hbm : seqB d m ≤ seqB d n := by
    rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
    · exact le_rfl
    · have h1 := h.b_small m (by omega)
      have h2 := seqA_mono h (show 1 ≤ m + 1 by omega) (show m + 1 ≤ n by omega)
      have h3 := h.a_small n (by omega)
      have : seqA d n ≤ n * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
      have : seqB d m ≤ m * seqB d m := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
  -- `4i ≤ 4vₙ < aₙ₊₁/2` and `4s ≤ 8bₘ ≤ 8bₙ ≤ 4n bₙ < aₙ₊₁/2`.
  have e8 : 8 * n * seqB d n = 8 * (n * seqB d n) := by ring
  have hnb : 2 * seqB d n ≤ n * seqB d n := Nat.mul_le_mul_right _ (by omega)
  omega

/- ### The subcases of Case 3

Each states the bound on `cᵢ ‖xʲ‖` (`cᵢ` the weight of `i ∈ Lₙ,ᵣ`, `j = i + s`) from the facts it
uses, to keep every proof short. -/

/-- **3.1°** `n = m`, `j > vₘ`: `j ∈ Jₘ₊₁,₁` and `cᵢ ≤ α^{√bₘ/2}`, while `‖xʲ‖ ≤ α^{-√aₘ₊₁/4}` and
`2√bₘ ≤ √aₘ₊₁`. -/
lemma lemma4_L_31 (h : GrowthHyp d) {m r i j : ℕ} (hm : 2 < m)
    (hB : (⟨m, r, .L⟩ : Block).Mem d i) (hjv : seqV d m < j)
    (h4j : 4 * j < seqA d (m + 1)) :
    weight (seqB d m) r i * nrm (xPow d j) ≤ 1 := by
  have hP := h.toPartitionHyp
  obtain ⟨hr1, hrn, hlo, -⟩ := hB
  dsimp only at hr1 hrn hlo
  have hb0 : 0 < seqB d m := lt_of_lt_of_le two_pos (h.two_le_b m)
  have hJ : (⟨m + 1, 1, .J⟩ : Block).Mem d j := by
    refine ⟨le_rfl, by dsimp; omega, ?_, ?_⟩ <;> dsimp only
    · simp only [Nat.sub_self, zero_mul, zero_add, Nat.add_sub_cancel]; omega
    · rw [one_mul]; omega
  have hxj : nrm (xPow d j) ≤ alpha ^ (-(Real.sqrt (seqA d (m + 1)) / 4)) := by
    refine nrm_xPow_J_le hP hJ ?_
    have : (4 * j : ℝ) < seqA d (m + 1) := by exact_mod_cast h4j
    push_cast; linarith only [this]
  have hw : weight (seqB d m) r i ≤ alpha ^ (Real.sqrt (seqB d m) / 2) := by
    refine weight_le_half hb0 ?_
    have h1 : (r - 1) * seqB d m < i := by omega
    have h2 : (((r - 1 : ℕ) : ℝ)) * seqB d m < i := by exact_mod_cast h1
    rw [Nat.cast_sub hr1] at h2; push_cast at h2; linarith only [h2]
  have h4 : 2 * Real.sqrt (seqB d m) ≤ Real.sqrt (seqA d (m + 1)) := by
    have hbs := h.b_small m (by omega)
    have hmb : seqB d m ≤ m * seqB d m := Nat.le_mul_of_pos_left _ (by omega)
    have e8 : 8 * m * seqB d m = 8 * (m * seqB d m) := by ring
    have h4n : 4 * seqB d m ≤ seqA d (m + 1) := by omega
    have h4R : (4 * seqB d m : ℝ) ≤ seqA d (m + 1) := by exact_mod_cast h4n
    calc 2 * Real.sqrt (seqB d m) = Real.sqrt (4 * seqB d m) := by rw [sqrt_four_mul]
      _ ≤ Real.sqrt (seqA d (m + 1)) := Real.sqrt_le_sqrt h4R
  calc weight (seqB d m) r i * nrm (xPow d j)
      ≤ alpha ^ (Real.sqrt (seqB d m) / 2) * alpha ^ (-(Real.sqrt (seqA d (m + 1)) / 4)) :=
        mul_le_mul hw hxj (nrm_nonneg _) (Real.rpow_pos_of_pos alpha_pos _).le
    _ = alpha ^ (Real.sqrt (seqB d m) / 2 + -(Real.sqrt (seqA d (m + 1)) / 4)) :=
        (Real.rpow_add alpha_pos _ _).symm
    _ ≤ alpha ^ (0 : ℝ) := alpha_rpow_le (by linarith only [h4])
    _ = 1 := Real.rpow_zero _

/-- **3.2° (a)** `n = m`, `j ∈ Lₘ,ᵣ₊₁`: `cᵢ / cⱼ = α^{(s - bₘ)/√bₘ}` with `s - bₘ ≤ √bₘ`. -/
lemma lemma4_L_32a (h : GrowthHyp d) {m s r i : ℕ} (hm : 2 < m) (hs : InK1 d m s)
    (hL : (⟨m, r + 1, .L⟩ : Block).Mem d (i + s)) :
    weight (seqB d m) r i * nrm (xPow d (i + s)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hb0 : 0 < seqB d m := lt_of_lt_of_le two_pos (h.two_le_b m)
  rw [nrm_xPow_of_L hP hL rfl, weight_mul_inv_weight]
  dsimp only
  have hsb : (s : ℝ) - seqB d m ≤ Real.sqrt (seqB d m) := by
    have hsq := h.a_sq m (by omega)
    have hma : (m - 1) * seqA d m ≤ m * seqA d m := Nat.mul_le_mul_right _ (by omega)
    have hsq' : ((m - 1) * seqA d m) ^ 2 ≤ seqB d m :=
      le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_left hma 2) (by rw [mul_pow]; exact hsq))
    have h1 : (((m - 1) * seqA d m : ℕ) : ℝ) ≤ Real.sqrt (seqB d m) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast hsq')
    have h2 : (s : ℝ) ≤ (((m - 1) * seqA d m : ℕ) : ℝ) + seqB d m := by exact_mod_cast hs.2
    linarith only [h1, h2]
  calc alpha ^ (((2 * (r : ℝ) - 1) * seqB d m - 2 * i -
        ((2 * ((r + 1 : ℕ) : ℝ) - 1) * seqB d m - 2 * ((i + s : ℕ) : ℝ))) /
          Real.sqrt (4 * seqB d m))
      ≤ alpha ^ (1 : ℝ) := by
        refine alpha_rpow_le ?_
        rw [sqrt_four_mul, div_le_one (by positivity)]
        push_cast; linarith only [hsb]
    _ = alpha := Real.rpow_one _

/-- **3.2° (b)** `n = m`, `j ∈ Kₘ,ᵣ₊₁`: `‖xʲ‖ ≤ 3bₘᵐ` (Lemma 1, and `Aₘ ≤ bₘ`), while
`cᵢ ≤ α^{-√bₘ/4}` because `4i ≥ (4r - 1)bₘ`; Śliwa's `bₘ^{4m} < α^{√bₘ/4}` finishes. -/
lemma lemma4_L_32b (h : GrowthHyp d) {m s r i : ℕ} (hm : 2 < m) (hs : InK1 d m s) (hr1 : 1 ≤ r)
    (hK : (⟨m, r + 1, .K⟩ : Block).Mem d (i + s)) :
    weight (seqB d m) r i * nrm (xPow d (i + s)) ≤ 1 := by
  have hP := h.toPartitionHyp
  obtain ⟨-, hrm, hKlo, hKhi⟩ := id hK
  dsimp only at hrm hKlo hKhi
  have hb2 := h.two_le_b m
  have hb0 : 0 < seqB d m := by omega
  have hbR : (2 : ℝ) ≤ seqB d m := by exact_mod_cast hb2
  have hb1 : (1 : ℝ) ≤ seqB d m := by linarith only [hbR]
  -- `‖xʲ‖ ≤ 2bₘʳ + bₘ^{r+1} Aₘ ≤ 3bₘᵐ`.
  have h1b := nrm_xPow_K_le h hK
  have hdown : i + s - (r + 1) * seqB d m ≤ (m - 1) * seqA d m := by omega
  have hcap := (nrm_xPow_le_cap h m (by omega)).1 _ hdown
  have hAb := h.rpow_a_le_b m (by omega)
  unfold capA at hcap
  have hxj : nrm (xPow d (i + s)) ≤ 3 * (seqB d m : ℝ) ^ m := by
    have hp1 : (seqB d m : ℝ) ^ (r + 1 - 1) ≤ (seqB d m : ℝ) ^ m :=
      pow_le_pow_right₀ hb1 (by omega)
    have hp2 : (seqB d m : ℝ) ^ (r + 1) * seqB d m ≤ (seqB d m : ℝ) ^ m := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hb1 (by omega)
    have h3 : (seqB d m : ℝ) ^ (r + 1) * nrm (xPow d (i + s - (r + 1) * seqB d m)) ≤
        (seqB d m : ℝ) ^ (r + 1) * seqB d m :=
      mul_le_mul_of_nonneg_left (hcap.trans hAb) (by positivity)
    linarith only [h1b, hp1, hp2, h3]
  -- `cᵢ ≤ α^{-√bₘ/4}`.
  have hw : weight (seqB d m) r i ≤ alpha ^ (-(Real.sqrt (seqB d m) / 4)) := by
    refine weight_le_neg hb0 ?_
    have hab := h.a_small m (by omega)
    have h8 : 4 * ((m - 2 - r) * seqA d m) ≤ seqB d m := by
      have : (m - 2 - r) * seqA d m ≤ m * seqA d m := Nat.mul_le_mul_right _ (by omega)
      have e8 : 8 * m * seqA d m = 8 * (m * seqA d m) := by ring
      omega
    have hexp : (r + 1) * (seqA d m + seqB d m) =
        (r + 1) * seqA d m + r * seqB d m + seqB d m := by ring
    have hm2 : (m - 1) * seqA d m = (r + 1) * seqA d m + (m - 2 - r) * seqA d m := by
      rw [← Nat.add_mul]; congr 1; omega
    have h4r : (4 * r - 1) * seqB d m + seqB d m = 4 * (r * seqB d m) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, show 4 * r - 1 + 1 = 4 * r by omega]; ring
    have hs2 := hs.2
    have hi4 : (4 * r - 1) * seqB d m ≤ 4 * i := by omega
    have h4R : ((4 * r - 1 : ℕ) : ℝ) * seqB d m ≤ 4 * i := by exact_mod_cast hi4
    rw [Nat.cast_sub (by omega)] at h4R; push_cast at h4R; linarith only [h4R]
  have hpb := h.pow_b m (by omega)
  have hp : 0 < alpha ^ (Real.sqrt (seqB d m) / 4) := Real.rpow_pos_of_pos alpha_pos _
  have h3 : 3 * (seqB d m : ℝ) ^ m ≤ (seqB d m : ℝ) ^ (4 * m) := by
    have hsplit : (seqB d m : ℝ) ^ (4 * m) = (seqB d m : ℝ) ^ m * (seqB d m : ℝ) ^ (3 * m) := by
      rw [← pow_add]; ring_nf
    rw [hsplit]
    have h3' : (3 : ℝ) ≤ (seqB d m : ℝ) ^ (3 * m) :=
      le_trans (by norm_num) (le_trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show 2 ≤ 3 * m by omega)) (pow_le_pow_left₀ (by norm_num) hbR _))
    have hp0 : (0 : ℝ) ≤ (seqB d m : ℝ) ^ m := pow_nonneg (by linarith only [hbR]) m
    nlinarith only [h3', hp0]
  calc weight (seqB d m) r i * nrm (xPow d (i + s))
      ≤ alpha ^ (-(Real.sqrt (seqB d m) / 4)) * (3 * (seqB d m : ℝ) ^ m) :=
        mul_le_mul hw hxj (nrm_nonneg _) (Real.rpow_pos_of_pos alpha_pos _).le
    _ ≤ alpha ^ (-(Real.sqrt (seqB d m) / 4)) * (seqB d m : ℝ) ^ (4 * m) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_pos_of_pos alpha_pos _).le
    _ ≤ 1 := by rw [Real.rpow_neg alpha_pos.le, inv_mul_le_iff₀ hp, mul_one]; exact hpb.le

/-- **3.2° (c)** `n = m`, `j ∈ Lₘ,ᵣ₊₂`: `cᵢ / cⱼ = α^{(s - 2bₘ)/√bₘ} ≤ 1`. -/
lemma lemma4_L_32c (h : GrowthHyp d) {m s r i : ℕ} (hm : 2 < m) (hs : InK1 d m s)
    (hL : (⟨m, r + 2, .L⟩ : Block).Mem d (i + s)) :
    weight (seqB d m) r i * nrm (xPow d (i + s)) ≤ 1 := by
  have hP := h.toPartitionHyp
  have h2b := hs.le_two_b h (by omega)
  rw [nrm_xPow_of_L hP hL rfl, weight_mul_inv_weight]
  dsimp only
  calc alpha ^ (((2 * (r : ℝ) - 1) * seqB d m - 2 * i -
        ((2 * ((r + 2 : ℕ) : ℝ) - 1) * seqB d m - 2 * ((i + s : ℕ) : ℝ))) /
          Real.sqrt (4 * seqB d m))
      ≤ alpha ^ (0 : ℝ) := by
        refine alpha_rpow_le (div_nonpos_of_nonpos_of_nonneg ?_ (Real.sqrt_nonneg _))
        have : (s : ℝ) ≤ 2 * seqB d m := by exact_mod_cast h2b
        push_cast; linarith only [this]
    _ = 1 := Real.rpow_zero _

/-- **3.3°** `n > m`, `j ∈ Lₙ,ᵣ`: `cᵢ / cⱼ = α^{s/√bₙ} ≤ α`. -/
lemma lemma4_L_33 (h : GrowthHyp d) {m s n r i : ℕ} (hm : 2 < m) (hs : InK1 d m s)
    (hmn : m < n) (hL : (⟨n, r, .L⟩ : Block).Mem d (i + s)) :
    weight (seqB d n) r i * nrm (xPow d (i + s)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hb0 : 0 < seqB d n := lt_of_lt_of_le two_pos (h.two_le_b n)
  have hsa := hs.le_sqrt_a h (by omega) hmn
  have hab' : (seqA d n : ℝ) ≤ seqB d n := by
    have hab := h.a_small n (by omega)
    have : seqA d n ≤ n * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
    have e8 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
    have : seqA d n ≤ seqB d n := by omega
    exact_mod_cast this
  have hsb : (s : ℝ) ≤ Real.sqrt (seqB d n) := hsa.trans (Real.sqrt_le_sqrt hab')
  rw [nrm_xPow_of_L hP hL rfl, weight_mul_inv_weight]
  dsimp only
  calc alpha ^ (((2 * (r : ℝ) - 1) * seqB d n - 2 * i -
        ((2 * (r : ℝ) - 1) * seqB d n - 2 * ((i + s : ℕ) : ℝ))) / Real.sqrt (4 * seqB d n))
      ≤ alpha ^ (1 : ℝ) := by
        refine alpha_rpow_le ?_
        rw [sqrt_four_mul, div_le_one (by positivity)]
        push_cast; linarith only [hsb]
    _ = alpha := Real.rpow_one _

/-- **3.4°** `n > m`, `j ≥ r(aₙ + bₙ)`: through `T f_p` with `p = r(aₙ + bₙ) - 1`, Remark 3 gives
`‖T f_p‖ ≤ 1/bₙ`, and `αˢ ≤ aₘ₊₁ ≤ bₙ`. -/
lemma lemma4_L_34 (h : GrowthHyp d) {m s n r i : ℕ} (hm : 2 < m) (hs : InK1 d m s)
    (hmn : m < n) (hB : (⟨n, r, .L⟩ : Block).Mem d i)
    (h34 : r * (seqA d n + seqB d n) ≤ i + s) :
    weight (seqB d n) r i * nrm (xPow d (i + s)) ≤ 1 := by
  have hP := h.toPartitionHyp
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hb0 : 0 < seqB d n := lt_of_lt_of_le two_pos (h.two_le_b n)
  have hsqb : 0 < Real.sqrt (seqB d n) := Real.sqrt_pos.2 (by exact_mod_cast hb0)
  have hsa := hs.le_sqrt_a h (by omega) hmn
  have hab := h.a_small n (by omega)
  have hna : seqA d n ≤ n * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
  have e8 : 8 * n * seqA d n = 8 * (n * seqA d n) := by ring
  have hab' : (seqA d n : ℝ) ≤ seqB d n := by
    have : seqA d n ≤ seqB d n := by omega
    exact_mod_cast this
  have hsb : (s : ℝ) ≤ Real.sqrt (seqB d n) := hsa.trans (Real.sqrt_le_sqrt hab')
  set k := r * (seqA d n + seqB d n) with hk
  set p := k - 1 with hp
  have hpL : (⟨n, r, .L⟩ : Block).Mem d p := ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
  have hsL := shiftImage_of_L hP hpL rfl
  have hpow : xPow d (i + s) =
      (weight (seqB d n) r p : ℂ)⁻¹ • (T₀ d ^ (i + s - k)) (shiftImage d p) := by
    rw [hsL, map_smul, T₀_pow_xPow hP, smul_smul, inv_mul_cancel₀ (weight_ne_zero _ _ _),
      one_smul]
    congr 1; omega
  have hrem := nrm_shiftImage_L_last h hpL (by omega)
  have hTk := nrm_T₀_pow_le h (i + s - k) (shiftImage d p)
  have hpi : i ≤ p := by omega
  rw [hpow, nrm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le,
    weight_eq_mul_add hb0 r i (p - i), show i + (p - i) = p by omega, ← mul_assoc,
    mul_assoc _ _ (weight _ _ _)⁻¹, mul_inv_cancel₀ (weight_pos _ _ _).ne', mul_one]
  have hone : (1 : ℝ) ≤ alpha := one_le_alpha
  have hexp : alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqB d n)) ≤ alpha := by
    calc alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqB d n)) ≤ alpha ^ (1 : ℝ) := by
          refine alpha_rpow_le ((div_le_one hsqb).2 (le_trans ?_ hsb))
          exact_mod_cast (show p - i ≤ s by omega)
      _ = alpha := Real.rpow_one _
  have hαs : alpha * alpha ^ (i + s - k) ≤ alpha ^ s := by
    rw [← pow_succ']; exact pow_le_pow_right₀ hone (by omega)
  have hsA := hs.alpha_pow_le h (by omega)
  have hAb : (seqA d (m + 1) : ℝ) ≤ seqB d n := by
    have := seqA_mono h (show 1 ≤ m + 1 by omega) (show m + 1 ≤ n by omega)
    have : seqA d (m + 1) ≤ seqB d n := by omega
    exact_mod_cast this
  have hpow0 : 0 ≤ alpha ^ (i + s - k) := pow_nonneg alpha_pos.le _
  have hbpos : (0 : ℝ) < seqB d n := by exact_mod_cast hb0
  calc alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqB d n)) *
        nrm ((T₀ d ^ (i + s - k)) (shiftImage d p))
      ≤ alpha * (alpha ^ (i + s - k) * (1 / seqB d n)) :=
        mul_le_mul hexp (hTk.trans (mul_le_mul_of_nonneg_left hrem hpow0)) (nrm_nonneg _)
          (by norm_num [alpha])
    _ = (alpha * alpha ^ (i + s - k)) * (1 / seqB d n) := by ring
    _ ≤ alpha ^ s * (1 / seqB d n) := by gcongr
    _ ≤ seqB d n * (1 / seqB d n) := by gcongr; linarith only [hsA, hAb]
    _ = 1 := by field_simp

/-- **Lemma 4, Case 3** (`i ∈ Lₙ,ᵣ`). -/
lemma lemma4_L (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .L⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hq : qImage d m i = 0 := qImage_eq_zero hi (by rw [block_eq hP hB]; simp)
  have hnm : m ≤ n := le_level h (by omega) hB hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have hone : (1 : ℝ) ≤ alpha := one_le_alpha
  rw [hq, sub_zero, single_eq_of_L hP hB rfl, map_smul, T₀_pow_xPow hP, nrm_smul,
    Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le]
  dsimp only
  have hiv : i ≤ seqV d n := ((⟨n, r, .L⟩ : Block).mem_level hP hB).2.1
  have h4j := four_add_lt h (by omega) hs hnm hiv
  have hs1 := hs.1
  have hs2 := hs.2
  rcases Nat.eq_or_lt_of_le hnm with rfl | hmn
  · -- `n = m`.
    have hvn : seqV d m = (m - 1) * seqA d m + (m - 1) * seqB d m := by unfold seqV; ring
    have hrab : r * (seqA d m + seqB d m) = r * seqA d m + r * seqB d m := by ring
    have hrb : (r - 1) * seqB d m + seqB d m = r * seqB d m := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
    have hna : (m - 1) * seqA d m + seqA d m = m * seqA d m := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    rcases lt_or_ge (seqV d m) (i + s) with hjv | hjv
    · exact (lemma4_L_31 h hm hB hjv h4j).trans hone
    · have hjlo : m * seqA d m + r * seqB d m < i + s := by omega
      have hrm : r + 1 < m := by
        by_contra hc
        have : (m - 1) * seqB d m ≤ r * seqB d m := Nat.mul_le_mul_right _ (by omega)
        omega
      have hr1ab : (r + 1) * (seqA d m + seqB d m) =
          r * seqA d m + r * seqB d m + seqA d m + seqB d m := by ring
      rcases lt_or_ge (i + s) ((r + 1) * (seqA d m + seqB d m)) with ha' | ha'
      · refine lemma4_L_32a h hm hs ⟨by dsimp; omega, by dsimp; omega, ?_, ha'⟩
        dsimp only; rw [Nat.add_sub_cancel]; omega
      · rcases le_or_gt (i + s) ((m - 1) * seqA d m + (r + 1) * seqB d m) with hb' | hb'
        · exact (lemma4_L_32b h hm hs hr1
            ⟨by dsimp; omega, by dsimp; omega, ha', hb'⟩).trans hone
        · have hrm2 : r + 2 < m := by
            by_contra hc
            have : (m - 1) * seqB d m ≤ (r + 1) * seqB d m := Nat.mul_le_mul_right _ (by omega)
            omega
          refine (lemma4_L_32c h hm hs ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩).trans hone
          · dsimp only; rw [show r + 2 - 1 = r + 1 by omega]; omega
          · dsimp only
            have : (r + 2) * (seqA d m + seqB d m) =
                r * seqA d m + r * seqB d m + 2 * seqA d m + 2 * seqB d m := by ring
            have hab := h.a_small m (by omega)
            have hma : (m - 1) * seqA d m ≤ m * seqA d m := Nat.mul_le_mul_right _ (by omega)
            have e8 : 8 * m * seqA d m = 8 * (m * seqA d m) := by ring
            omega
  · -- `n > m`.
    rcases lt_or_ge (i + s) (r * (seqA d n + seqB d n)) with h33 | h34
    · exact lemma4_L_33 h hm hs hmn ⟨hr1, hrn, by dsimp; omega, h33⟩
    · exact (lemma4_L_34 h hm hs hmn hB h34).trans hone

end ReadL1
