/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 1 (a): the size of `xⁱ`

With `Aₘ = α^{√aₘ}` and `Bₘ = α^{√bₘ}`, Śliwa (pp. 629–630) shows for `m ≥ 2`

* `‖xⁱ‖ ≤ Aₘ` for `i ≤ (m - 1)aₘ`, and
* `‖xⁱ‖ ≤ Bₘ` for `i ≤ vₘ`,

by induction on `m`: going from `vₘ` up to `m aₘ₊₁` crosses the `J` and `I` blocks of level
`m + 1`, and from there up to `vₘ₊₁` the `L` and `K` blocks. On a `J` block `‖xⁱ‖` is at most
`α^{√c/2}` and on an `L` block at most `α^{√c}`; on an `I` block Lemma 1 (b) compares `xⁱ` with
a power at most `vₘ`; on a `K` block with a power at most `m aₘ₊₁`. (The statement holds for
`m = 1` too, where both ranges are `{0}`.)
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- `Aₘ = α^{√aₘ}`. -/
noncomputable def capA (d : ℕ → ℕ) (m : ℕ) : ℝ := alpha ^ Real.sqrt (seqA d m)

/-- `Bₘ = α^{√bₘ}`. -/
noncomputable def capB (d : ℕ → ℕ) (m : ℕ) : ℝ := alpha ^ Real.sqrt (seqB d m)

lemma one_le_alpha_rpow {x : ℝ} (hx : 0 ≤ x) : 1 ≤ alpha ^ x :=
  Real.one_le_rpow one_le_alpha hx

lemma one_le_capA (m : ℕ) : 1 ≤ capA d m := one_le_alpha_rpow (Real.sqrt_nonneg _)

lemma one_le_capB (m : ℕ) : 1 ≤ capB d m := one_le_alpha_rpow (Real.sqrt_nonneg _)

/-- If the numerator `N` of the weight exponent is at least `-c`, then `-N/√(4c) ≤ √c/2`. -/
lemma neg_exponent_le_half {c : ℕ} (hc : 0 < c) {N : ℝ} (hN : -(c : ℝ) ≤ N) :
    -(N / Real.sqrt (4 * c)) ≤ Real.sqrt c / 2 := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  rw [sqrt_four_mul]
  calc -(N / (2 * Real.sqrt c)) = -N / (2 * Real.sqrt c) := by ring
    _ ≤ c / (2 * Real.sqrt c) := by gcongr; linarith
    _ = Real.sqrt c / 2 := by
        rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith [hsq]

/-- If the numerator `N` of the weight exponent is at least `-2c`, then `-N/√(4c) ≤ √c`. -/
lemma neg_exponent_le_sqrt {c : ℕ} (hc : 0 < c) {N : ℝ} (hN : -(2 * c : ℝ) ≤ N) :
    -(N / Real.sqrt (4 * c)) ≤ Real.sqrt c := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  rw [sqrt_four_mul]
  calc -(N / (2 * Real.sqrt c)) = -N / (2 * Real.sqrt c) := by ring
    _ ≤ (2 * c) / (2 * Real.sqrt c) := by gcongr; linarith
    _ = Real.sqrt c := by
        rw [div_eq_iff (by positivity)]; nlinarith [hsq]

/-- On a `J` block, `‖xⁱ‖ ≤ α^{√aₙ/2}`: the exponent's numerator is at least `2 - aₙ`. -/
lemma nrm_xPow_J_le_half (h : PartitionHyp d) {n r i : ℕ} (hB : (⟨n, r, .J⟩ : Block).Mem d i) :
    nrm (xPow d i) ≤ alpha ^ (Real.sqrt (seqA d n) / 2) := by
  have hhi : i < r * seqA d n := hB.2.2.2
  have ha : 0 < seqA d n := h.one_le_a n
  rw [nrm_xPow_of_J h hB rfl, inv_weight]
  refine alpha_rpow_le (neg_exponent_le_half ha ?_)
  have hi : (i : ℝ) + 1 ≤ r * seqA d n := by exact_mod_cast hhi
  dsimp only
  nlinarith

/-- On an `L` block, `‖xⁱ‖ ≤ α^{√bₙ}`: the exponent's numerator is at least `-bₙ - 2r aₙ`, and
`2r aₙ < bₙ`. -/
lemma nrm_xPow_L_le_sqrt (h : GrowthHyp d) {n r i : ℕ} (hB : (⟨n, r, .L⟩ : Block).Mem d i) :
    nrm (xPow d i) ≤ alpha ^ Real.sqrt (seqB d n) := by
  have hhi : i < r * (seqA d n + seqB d n) := hB.2.2.2
  have hlo : (n - 1) * seqA d n + (r - 1) * seqB d n < i := hB.2.2.1
  have hr1 : 1 ≤ r := hB.1
  have hrn : r < n := hB.2.1
  have hb : 0 < seqB d n := lt_of_lt_of_le two_pos (h.two_le_b n)
  rw [nrm_xPow_of_L h.toPartitionHyp hB rfl, inv_weight]
  refine alpha_rpow_le (neg_exponent_le_sqrt hb ?_)
  dsimp only
  -- `i + 1 ≤ r aₙ + r bₙ` and `2r aₙ ≤ 2(n - 1)aₙ < bₙ`.
  have hi : (i : ℝ) + 1 ≤ r * seqA d n + r * seqB d n := by
    have : i + 1 ≤ r * seqA d n + r * seqB d n := by nlinarith
    exact_mod_cast this
  have hra : 2 * r * seqA d n < seqB d n := by
    have := h.a_small n (by omega)
    have : r * seqA d n ≤ n * seqA d n := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hraR : (2 * r * seqA d n : ℝ) < seqB d n := by exact_mod_cast hra
  nlinarith

/-- On an `I` block, `‖xⁱ‖ ≤ 2 + ‖x^{i - r aₙ}‖` (Lemma 1 (b)). -/
lemma nrm_xPow_I_le (h : GrowthHyp d) {n r i : ℕ} (hB : (⟨n, r, .I⟩ : Block).Mem d i) :
    nrm (xPow d i) ≤ 2 + nrm (xPow d (i - r * seqA d n)) := by
  have h1 := nrm_xPow_sub_of_I h hB
  have ha : (1 : ℝ) ≤ seqA d (n - r) := by exact_mod_cast h.one_le_a _
  have h2 : 2 / (seqA d (n - r) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc nrm (xPow d i)
      = nrm ((xPow d i - xPow d (i - r * seqA d n)) + xPow d (i - r * seqA d n)) := by
        rw [sub_add_cancel]
    _ ≤ nrm (xPow d i - xPow d (i - r * seqA d n)) + nrm (xPow d (i - r * seqA d n)) :=
        nrm_add_le _ _
    _ ≤ 2 + nrm (xPow d (i - r * seqA d n)) := by linarith

/-- On a `K` block, `‖xⁱ‖ ≤ 2bₙ^{r-1} + bₙʳ ‖x^{i - r bₙ}‖` (Lemma 1 (b)). -/
lemma nrm_xPow_K_le (h : GrowthHyp d) {n r i : ℕ} (hB : (⟨n, r, .K⟩ : Block).Mem d i) :
    nrm (xPow d i) ≤
      2 * (seqB d n : ℝ) ^ (r - 1) + (seqB d n : ℝ) ^ r * nrm (xPow d (i - r * seqB d n)) := by
  have h1 := nrm_xPow_sub_of_K h hB
  calc nrm (xPow d i)
      = nrm ((xPow d i - (seqB d n : ℂ) ^ r • xPow d (i - r * seqB d n)) +
          (seqB d n : ℂ) ^ r • xPow d (i - r * seqB d n)) := by rw [sub_add_cancel]
    _ ≤ nrm (xPow d i - (seqB d n : ℂ) ^ r • xPow d (i - r * seqB d n)) +
          nrm ((seqB d n : ℂ) ^ r • xPow d (i - r * seqB d n)) := nrm_add_le _ _
    _ ≤ 2 * (seqB d n : ℝ) ^ (r - 1) +
          (seqB d n : ℝ) ^ r * nrm (xPow d (i - r * seqB d n)) := by
        rw [nrm_smul, norm_pow, Complex.norm_natCast]; linarith

/-- An index in `(vₘ, vₘ₊₁]` lies in a block of level `m + 1`. -/
lemma block_level (h : PartitionHyp d) {m i : ℕ} (hm : 1 ≤ m) (hlo : seqV d m < i)
    (hhi : i ≤ seqV d (m + 1)) : (block d i).n = m + 1 := by
  have hB := block_mem h (i := i) (by omega)
  obtain ⟨hBlo, hBhi, -⟩ := (block d i).mem_level h hB
  exact level_unique h (Block.two_le_n hB) (by omega) ⟨hBlo, hBhi⟩
    ⟨by simpa using hlo, hhi⟩

/-- **Śliwa's Lemma 1 (a).** -/
theorem nrm_xPow_le_cap (h : GrowthHyp d) (m : ℕ) (hm : 1 ≤ m) :
    (∀ i ≤ (m - 1) * seqA d m, nrm (xPow d i) ≤ capA d m) ∧
      (∀ i ≤ seqV d m, nrm (xPow d i) ≤ capB d m) := by
  have hP := h.toPartitionHyp
  induction m, hm using Nat.le_induction with
  | base =>
    -- Both ranges are `{0}`, and `‖x⁰‖ = 1`.
    have h0 : nrm (xPow d 0) = 1 := by rw [xPow, nrm_single, norm_one]
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [show i = 0 by simpa using hi, h0]; exact one_le_capA 1
    · rw [show i = 0 by simpa [seqV_one] using hi, h0]; exact one_le_capB 1
  | succ m hm ih =>
    obtain ⟨-, ihB⟩ := ih
    -- Below `vₘ`, use `Bₘ ≤ Aₘ₊₁ ≤ Bₘ₊₁`.
    have hBA : capB d m ≤ capA d (m + 1) := by
      have := h.rpow_b_add_two_le m hm; unfold capB capA; linarith
    have hAB : capA d (m + 1) ≤ capB d (m + 1) := by
      refine alpha_rpow_le (Real.sqrt_le_sqrt ?_)
      have := h.a_small (m + 1) (by omega)
      have : seqA d (m + 1) ≤ seqB d (m + 1) := by nlinarith
      exact_mod_cast this
    -- The `X` side of level `m + 1`.
    have hA : ∀ i ≤ m * seqA d (m + 1), nrm (xPow d i) ≤ capA d (m + 1) := by
      intro i hi
      rcases le_or_gt i (seqV d m) with hv | hv
      · exact (ihB i hv).trans hBA
      have hvn : i ≤ seqV d (m + 1) := by
        have : m * seqA d (m + 1) ≤ seqV d (m + 1) := by
          unfold seqV; simp only [Nat.add_sub_cancel]; nlinarith
        omega
      have hn := block_level hP hm hv hvn
      have hB := block_mem hP (i := i) (by omega)
      have hside := ((block d i).mem_level hP hB).2.2
      rw [hn, Nat.add_sub_cancel] at hside
      rcases hbl : block d i with ⟨n, r, k⟩
      rw [hbl] at hB hn hside
      dsimp only at hn hside
      subst hn
      cases k with
      | J =>
        refine (nrm_xPow_J_le_half hP hB).trans (alpha_rpow_le ?_)
        have := Real.sqrt_nonneg (seqA d (m + 1) : ℝ); linarith
      | I =>
        -- `i - r aₘ₊₁ ≤ vₘ₊₁₋ᵣ₋₁ ≤ vₘ`.
        have hdown : i - r * seqA d (m + 1) ≤ seqV d m := by
          obtain ⟨hr1, hrn, hlo', hhi'⟩ := hB
          dsimp only at hr1 hrn hlo' hhi'
          have := seqV_mono hP (show m + 1 - r - 1 ≤ m by omega)
          omega
        refine (nrm_xPow_I_le h hB).trans ?_
        have := ihB _ hdown
        have := h.rpow_b_add_two_le m hm
        unfold capB at *; unfold capA; linarith
      | L => simp at hside; omega
      | K => simp at hside; omega
    refine ⟨fun i hi ↦ hA i (by simpa using hi), fun i hi ↦ ?_⟩
    rcases le_or_gt i (m * seqA d (m + 1)) with hX | hX
    · exact (hA i hX).trans hAB
    -- The `Y` side of level `m + 1`.
    have hvm : seqV d m < i := by
      have := hP.v_lt_a (m + 1) m (by omega)
      have : seqA d (m + 1) ≤ m * seqA d (m + 1) := Nat.le_mul_of_pos_left _ hm
      omega
    have hn := block_level hP hm hvm hi
    have hB := block_mem hP (i := i) (by omega)
    have hside := ((block d i).mem_level hP hB).2.2
    rw [hn, Nat.add_sub_cancel] at hside
    rcases hbl : block d i with ⟨n, r, k⟩
    rw [hbl] at hB hn hside
    dsimp only at hn hside
    subst hn
    cases k with
    | J => simp at hside; omega
    | I => simp at hside; omega
    | L =>
      exact nrm_xPow_L_le_sqrt h hB
    | K =>
      -- `i - r bₘ₊₁ ∈ [r aₘ₊₁, m aₘ₊₁]`, where `‖·‖ ≤ Aₘ₊₁`.
      obtain ⟨hr1, hrn, hlo', hhi'⟩ := id hB
      dsimp only at hr1 hrn hlo' hhi'
      have hdown : i - r * seqB d (m + 1) ≤ m * seqA d (m + 1) := by
        rw [Nat.add_sub_cancel] at hhi'; omega
      have hxA := hA _ hdown
      have hb : (1 : ℝ) ≤ seqB d (m + 1) := by
        exact_mod_cast (show 1 ≤ seqB d (m + 1) by have := h.two_le_b (m + 1); omega)
      have hbpow : (seqB d (m + 1) : ℝ) ^ (r - 1) ≤ (seqB d (m + 1) : ℝ) ^ (m + 1) :=
        pow_le_pow_right₀ hb (by omega)
      have hbpow' : (seqB d (m + 1) : ℝ) ^ r ≤ (seqB d (m + 1) : ℝ) ^ (m + 1) :=
        pow_le_pow_right₀ hb (by omega)
      have h3 := h.three_pow_rpow_a_le (m + 1) (by omega)
      have hA1 := one_le_capA (d := d) (m + 1)
      refine (nrm_xPow_K_le h hB).trans ?_
      unfold capB
      unfold capA at hxA hA1
      have hpos : (0 : ℝ) ≤ (seqB d (m + 1) : ℝ) ^ r := by positivity
      calc 2 * (seqB d (m + 1) : ℝ) ^ (r - 1) + (seqB d (m + 1) : ℝ) ^ r *
            nrm (xPow d (i - r * seqB d (m + 1)))
          ≤ 2 * (seqB d (m + 1) : ℝ) ^ (m + 1) * alpha ^ Real.sqrt (seqA d (m + 1)) +
              (seqB d (m + 1) : ℝ) ^ (m + 1) * alpha ^ Real.sqrt (seqA d (m + 1)) := by
            have h1 : (seqB d (m + 1) : ℝ) ^ (r - 1) ≤
                (seqB d (m + 1) : ℝ) ^ (m + 1) * alpha ^ Real.sqrt (seqA d (m + 1)) :=
              hbpow.trans (le_mul_of_one_le_right (by positivity) hA1)
            have h2 : (seqB d (m + 1) : ℝ) ^ r * nrm (xPow d (i - r * seqB d (m + 1))) ≤
                (seqB d (m + 1) : ℝ) ^ (m + 1) * alpha ^ Real.sqrt (seqA d (m + 1)) :=
              mul_le_mul hbpow' hxA (nrm_nonneg _) (by positivity)
            linarith
        _ = 3 * (seqB d (m + 1) : ℝ) ^ (m + 1) * alpha ^ Real.sqrt (seqA d (m + 1)) := by ring
        _ ≤ alpha ^ Real.sqrt (seqB d (m + 1)) := h3

end ReadL1
