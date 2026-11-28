/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Projection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 4, setup and Case 1 (`J` blocks)

Lemma 4 (Śliwa pp. 632–635): for `m > 2` and `s ∈ Kₘ,₁`, `‖Tˢ - Tˢ Qₘ‖ ≤ α`. It suffices to bound
`‖Tˢ (fᵢ - Qₘ fᵢ)‖` for each `i`. For `i ≤ (m - 1)aₘ` this is `0`. Otherwise `Qₘ fᵢ = 0` unless
`i ∈ Iₙ,ₙ₋ₘ`, and the four cases follow the block of `i`.

This file: the general facts every case uses (`s < 2bₘ`, `s` is small against `√aₙ` for `n > m`,
`αˢ ≤ aₘ₊₁`), when `Qₘ fᵢ = 0`, and **Case 1** (`i ∈ Jₙ,ᵣ`).
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- `s ∈ Kₘ,₁` means `aₘ + bₘ ≤ s ≤ (m - 1)aₘ + bₘ`. -/
def InK1 (d : ℕ → ℕ) (m s : ℕ) : Prop :=
  seqA d m + seqB d m ≤ s ∧ s ≤ (m - 1) * seqA d m + seqB d m

/-- `Qₘ fᵢ = 0` above `(m - 1)aₘ`, unless `i ∈ Iₙ,ₙ₋ₘ`. -/
lemma qImage_eq_zero {m i : ℕ} (hi : (m - 1) * seqA d m < i)
    (hk : ¬ ((block d i).kind = .I ∧ (block d i).r + m = (block d i).n)) : qImage d m i = 0 := by
  rw [qImage, ite_eq_right (by omega), ite_eq_right hk]

/-- Consecutive weights `k` apart differ by `α^{k/√c}`. -/
lemma weight_eq_mul_add {c : ℕ} (hc : 0 < c) (r i k : ℕ) :
    weight c r i = alpha ^ ((k : ℝ) / Real.sqrt c) * weight c r (i + k) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  rw [weight, weight, ← Real.rpow_add alpha_pos, sqrt_four_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- Above `(m - 1)aₘ`, a block has level `n > m` unless it is an `L` or `K` block of level `m`:
`J` and `I` blocks of level `n` end by `(n - 1)aₙ`. -/
lemma lt_level_of_JI (h : GrowthHyp d) {m i : ℕ} (hm : 1 ≤ m) {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .J ∨ B.kind = .I) (hi : (m - 1) * seqA d m < i) : m < B.n := by
  have hX := ((B.mem_level h.toPartitionHyp hB).2.2).2 hk
  by_contra hnm
  have h2 := Block.two_le_n hB
  have : (B.n - 1) * seqA d B.n ≤ (m - 1) * seqA d m :=
    Nat.mul_le_mul (by omega) (seqA_mono h (by omega) (by omega))
  omega

/-- `s ≤ 2bₘ`. -/
lemma InK1.le_two_b (h : GrowthHyp d) {m s : ℕ} (hm : 1 ≤ m) (hs : InK1 d m s) :
    s ≤ 2 * seqB d m := by
  have := h.a_small m hm
  have : (m - 1) * seqA d m ≤ m * seqA d m := Nat.mul_le_mul_right _ (by omega)
  have := hs.2
  nlinarith

/-- For `s ∈ Kₘ,₁` and `n > m`, the growth inequalities give `8s ≤ aₙ`. -/
lemma eight_mul_le_seqA (h : GrowthHyp d) {m s n : ℕ} (hm : 2 < m) (hs : InK1 d m s)
    (hmn : m < n) : 8 * s ≤ seqA d n := by
  have hmpos : 1 ≤ m := by omega
  have haPos : 0 < seqA d m := h.one_le_a m
  have hb8 : 8 ≤ seqB d m :=
    (Nat.le_mul_of_pos_right 8 (by omega : 0 < m)).trans
      ((Nat.le_mul_of_pos_right (8 * m) haPos).trans (h.a_small m hmpos).le)
  calc
    8 * s ≤ 8 * (2 * seqB d m) := Nat.mul_le_mul_left _ (hs.le_two_b h hmpos)
    _ = 16 * seqB d m := by rw [← Nat.mul_assoc]
    _ ≤ (4 * seqB d m) * seqB d m := Nat.mul_le_mul_right _ (by omega)
    _ = 4 * seqB d m ^ 2 := by rw [pow_two, Nat.mul_assoc]
    _ ≤ seqA d (m + 1) := (h.four_sq_b_lt_a m hmpos).le
    _ ≤ seqA d n := seqA_mono h (by omega) (by omega)

/-- For `n > m`, `s ≤ √aₙ`: `s ≤ 2bₘ` and `4bₘ² < aₘ₊₁ ≤ aₙ`. -/
lemma InK1.le_sqrt_a (h : GrowthHyp d) {m s n : ℕ} (hm : 1 ≤ m) (hs : InK1 d m s)
    (hnm : m < n) : (s : ℝ) ≤ Real.sqrt (seqA d n) := by
  have h2 := hs.le_two_b h hm
  have h4 := h.four_sq_b_lt_a m hm
  have hmono := seqA_mono h (show 1 ≤ m + 1 by omega) (show m + 1 ≤ n by omega)
  refine Real.le_sqrt_of_sq_le ?_
  have : s ^ 2 ≤ seqA d n := by nlinarith
  exact_mod_cast this

/-- `αˢ ≤ aₘ₊₁`: `s ≤ 2bₘ` and Śliwa's growth condition `aₘ₊₁ ≥ α^{2bₘ}`. -/
lemma InK1.alpha_pow_le (h : GrowthHyp d) {m s : ℕ} (hm : 1 ≤ m) (hs : InK1 d m s) :
    alpha ^ s ≤ seqA d (m + 1) :=
  (pow_le_pow_right₀ one_le_alpha (hs.le_two_b h hm)).trans (h.alpha_pow_two_b_le m hm)

/-- **Lemma 4, Case 1:** `i ∈ Jₙ,ᵣ` above `(m - 1)aₘ`. Then `Qₘ fᵢ = 0` and
`Tˢ fᵢ = cᵢ xⁱ⁺ˢ`. If `i + s` is still in `Jₙ,ᵣ` this is `α^{s/√aₙ} fᵢ₊ₛ` (1.1°). Otherwise it is
`(cᵢ / c_p) T^{i + s - r aₙ} (T f_p)` with `p = r aₙ - 1` the last index of the block, and Remark 3
gives `‖T f_p‖ ≤ 1/aₙ` (1.2°). -/
lemma lemma4_J (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) {n r i : ℕ}
    (hB : (⟨n, r, .J⟩ : Block).Mem d i) (hi : (m - 1) * seqA d m < i) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  have hq : qImage d m i = 0 := qImage_eq_zero hi (by rw [block_eq hP hB]; simp)
  have hnm : m < n := lt_level_of_JI h (by omega) hB (Or.inl rfl) hi
  obtain ⟨hr1, hrn, hlo, hhi⟩ := id hB
  dsimp only at hr1 hrn hlo hhi
  have ha : 0 < seqA d n := h.one_le_a n
  have hsa := hs.le_sqrt_a h (by omega) hnm
  have hsqa : 0 < Real.sqrt (seqA d n) := Real.sqrt_pos.2 (by exact_mod_cast ha)
  rw [hq, sub_zero, single_eq_of_J hP hB rfl, map_smul, T₀_pow_xPow hP, nrm_smul,
    Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le]
  dsimp only
  rcases lt_or_ge (i + s) (r * seqA d n) with h11 | h12
  · -- 1.1°: `i + s ∈ Jₙ,ᵣ`, and `cᵢ / cᵢ₊ₛ = α^{s/√aₙ} ≤ α`.
    have hB' : (⟨n, r, .J⟩ : Block).Mem d (i + s) := ⟨hr1, hrn, by dsimp; omega, h11⟩
    rw [nrm_xPow_of_J hP hB' rfl, weight_eq_mul_add ha r i s, mul_assoc,
      mul_inv_cancel₀ (weight_pos _ _ _).ne', mul_one]
    calc alpha ^ ((s : ℝ) / Real.sqrt (seqA d n)) ≤ alpha ^ (1 : ℝ) :=
          alpha_rpow_le ((div_le_one hsqa).2 hsa)
      _ = alpha := Real.rpow_one _
  · -- 1.2°: through `T f_p`, `p = r aₙ - 1`.
    set p := r * seqA d n - 1 with hp
    have hpB : (⟨n, r, .J⟩ : Block).Mem d p := ⟨hr1, hrn, by dsimp; omega, by dsimp; omega⟩
    have hpi : i ≤ p := by omega
    have hpow : xPow d (i + s) =
        (weight (seqA d n) r p : ℂ)⁻¹ • (T₀ d ^ (i + s - r * seqA d n)) (shiftImage d p) := by
      rw [shiftImage_of_J hP hpB rfl, map_smul, T₀_pow_xPow hP, smul_smul,
        inv_mul_cancel₀ (weight_ne_zero _ _ _), one_smul]
      congr 1; omega
    have hrem := nrm_shiftImage_J_last h hpB (by omega)
    have hTk := nrm_T₀_pow_le h (i + s - r * seqA d n) (shiftImage d p)
    rw [hpow, nrm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (weight_pos _ _ _).le,
      weight_eq_mul_add ha r i (p - i), show i + (p - i) = p by omega, ← mul_assoc,
      mul_assoc _ _ (weight _ _ _)⁻¹, mul_inv_cancel₀ (weight_pos _ _ _).ne', mul_one]
    -- `α^{(p - i)/√aₙ} ≤ α`, `α · α^{i + s - r aₙ} ≤ αˢ ≤ aₘ₊₁ ≤ aₙ`.
    have hexp : alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqA d n)) ≤ alpha := by
      calc alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqA d n)) ≤ alpha ^ (1 : ℝ) := by
            refine alpha_rpow_le ((div_le_one hsqa).2 (le_trans ?_ hsa))
            exact_mod_cast (show p - i ≤ s by omega)
        _ = alpha := Real.rpow_one _
    have hαs : alpha * alpha ^ (i + s - r * seqA d n) ≤ alpha ^ s := by
      rw [← pow_succ']; exact pow_le_pow_right₀ one_le_alpha (by omega)
    have hsA := hs.alpha_pow_le h (by omega)
    have hAn : (seqA d (m + 1) : ℝ) ≤ seqA d n := by
      exact_mod_cast seqA_mono h (by omega) (by omega)
    have haR : (0 : ℝ) < seqA d n := by exact_mod_cast ha
    have hx0 := nrm_nonneg (shiftImage d p)
    have hpow0 : 0 ≤ alpha ^ (i + s - r * seqA d n) := pow_nonneg alpha_pos.le _
    calc alpha ^ (((p - i : ℕ) : ℝ) / Real.sqrt (seqA d n)) *
          nrm ((T₀ d ^ (i + s - r * seqA d n)) (shiftImage d p))
        ≤ alpha * (alpha ^ (i + s - r * seqA d n) * (1 / seqA d n)) :=
          mul_le_mul hexp (hTk.trans (mul_le_mul_of_nonneg_left hrem hpow0)) (nrm_nonneg _)
            (by norm_num [alpha])
      _ ≤ alpha ^ s * (1 / seqA d n) := by rw [← mul_assoc]; gcongr
      _ ≤ seqA d n * (1 / seqA d n) := by gcongr; linarith
      _ = 1 := by field_simp
      _ ≤ alpha := one_le_alpha

end ReadL1
