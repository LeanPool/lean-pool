/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedThresholds
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitCarriers
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDelayExponentUniform
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEstimates

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSplitWitnessCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split witness is a power of the telescope base

The enlarged-witness cap: at the normalized gauge
the minimal growth power is capped (`K^{n+2} ≤ 2K³`), and the burn-split
witness `burnSplitThreshold·K^{n+2}` — hence its growth bar, and hence
every crude-moment logarithm of the enlarged source — is bounded by a
pre-law power of the telescope base `2 + Π·K`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- **The minimal growth power at the normalized gauge.** -/
theorem exists_minimal_two_pow {K : ℝ} (hK : 1 < K) :
    ∃ n : ℕ, 2 ≤ K ^ n ∧ K ^ (n + 2) ≤ 2 * K ^ 3 := by
  have hK0 : (0 : ℝ) < K := lt_trans one_pos hK
  refine ⟨⌈Real.logb K 2⌉₊, ?_, ?_⟩
  · have hlog : Real.logb K 2 ≤ (⌈Real.logb K 2⌉₊ : ℝ) := Nat.le_ceil _
    have h := Real.rpow_le_rpow_of_exponent_le hK.le hlog
    rw [Real.rpow_logb hK0 hK.ne' (by norm_num)] at h
    calc (2 : ℝ) ≤ K ^ ((⌈Real.logb K 2⌉₊ : ℕ) : ℝ) := h
      _ = K ^ (⌈Real.logb K 2⌉₊ : ℕ) := Real.rpow_natCast K _
  · have hup : (⌈Real.logb K 2⌉₊ : ℝ) ≤ Real.logb K 2 + 1 := by
      have hl0 : 0 ≤ Real.logb K 2 :=
        Real.logb_nonneg hK (by norm_num)
      have := Nat.ceil_lt_add_one hl0
      linarith only [this]
    have hpow : K ^ (⌈Real.logb K 2⌉₊ : ℕ) ≤ 2 * K := by
      have h1 : K ^ ((⌈Real.logb K 2⌉₊ : ℕ) : ℝ) ≤
          K ^ (Real.logb K 2 + 1) :=
        Real.rpow_le_rpow_of_exponent_le hK.le hup
      have h2 : K ^ (Real.logb K 2 + 1) = 2 * K := by
        rw [Real.rpow_add hK0, Real.rpow_logb hK0 hK.ne' (by norm_num),
          Real.rpow_one]
      rw [← Real.rpow_natCast K ⌈Real.logb K 2⌉₊]
      linarith only [h1, h2.le, h2.ge]
    calc K ^ (⌈Real.logb K 2⌉₊ + 2) =
        K ^ (⌈Real.logb K 2⌉₊ : ℕ) * K ^ 2 := by ring
      _ ≤ 2 * K * K ^ 2 :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 2 * K ^ 3 := by ring

/-- **The crude moment constant is a growth-bar power.** -/
theorem crude_le_growth_pow (N : ℕ) {gK : ℝ} (h2 : 2 ≤ gK) :
    1 + 2 * (N : ℝ) * (1 + Real.log gK) *
        gK ^ IndependentSums.natTriangular N ≤
      (4 * (N : ℝ) + 1) * gK ^ (IndependentSums.natTriangular N + 1) := by
  have hgK0 : (0 : ℝ) < gK := by linarith only [h2]
  have hlog : Real.log gK ≤ gK - 1 := Real.log_le_sub_one_of_pos hgK0
  have hone : 1 + Real.log gK ≤ gK := by linarith only [hlog]
  have hpow0 : (0 : ℝ) ≤ gK ^ IndependentSums.natTriangular N :=
    pow_nonneg (by linarith only [h2]) _
  have hpow1 : (1 : ℝ) ≤ gK ^ (IndependentSums.natTriangular N + 1) :=
    one_le_pow₀ (by linarith only [h2])
  have hstep : 2 * (N : ℝ) * (1 + Real.log gK) *
      gK ^ IndependentSums.natTriangular N ≤
      2 * (N : ℝ) * gK ^ (IndependentSums.natTriangular N + 1) := by
    have h1 : 2 * (N : ℝ) * (1 + Real.log gK) *
        gK ^ IndependentSums.natTriangular N ≤
        2 * (N : ℝ) * gK * gK ^ IndependentSums.natTriangular N := by
      refine mul_le_mul_of_nonneg_right ?_ hpow0
      have hN0 : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hone hN0
    calc 2 * (N : ℝ) * (1 + Real.log gK) *
        gK ^ IndependentSums.natTriangular N ≤
        2 * (N : ℝ) * gK * gK ^ IndependentSums.natTriangular N := h1
      _ = 2 * (N : ℝ) * gK ^ (IndependentSums.natTriangular N + 1) := by
        ring
  have hN0 : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
  nlinarith only [hstep, hpow1, hN0]

/-- The nonnegative-max split for ternary powers. -/
theorem three_zpow_max_le_mul {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (3 : ℝ) ^ (max a b) ≤ (3 : ℝ) ^ a * (3 : ℝ) ^ b := by
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ a := one_le_zpow₀ (by norm_num) ha
  have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ b := one_le_zpow₀ (by norm_num) hb
  rcases max_cases a b with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    nlinarith only [h2, zpow_pos (by norm_num : (0:ℝ) < 3) a]
  · rw [hm]
    nlinarith only [h1, zpow_pos (by norm_num : (0:ℝ) < 3) b]

/-- The ceiling collapse at a nonnegative exponent. -/
theorem three_zpow_intCeil_le (y : ℝ) :
    (3 : ℝ) ^ (⌈y⌉ : ℤ) ≤ 3 * (3 : ℝ) ^ y := by
  have hceil : ((⌈y⌉ : ℤ) : ℝ) ≤ y + 1 := (Int.ceil_lt_add_one y).le
  have h1 : (3 : ℝ) ^ (⌈y⌉ : ℤ) = (3 : ℝ) ^ ((⌈y⌉ : ℤ) : ℝ) := by
    rw [Real.rpow_intCast]
  rw [h1]
  have h2 : (3 : ℝ) ^ ((⌈y⌉ : ℤ) : ℝ) ≤ (3 : ℝ) ^ (y + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
  have h3 : (3 : ℝ) ^ (y + 1) = 3 * (3 : ℝ) ^ y := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 3), Real.rpow_one]
    ring
  linarith only [h2, h3.le, h3.ge]

/-- The logb-power collapse: `3^{c·log₃ x} = x^c`. -/
theorem three_rpow_mul_logb {x : ℝ} (hx : 0 < x) (c : ℝ) :
    (3 : ℝ) ^ (c * Real.logb 3 x) = x ^ c := by
  rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    Real.rpow_logb (by norm_num) (by norm_num) hx]

private theorem source_burn_power_bound
    (d : ℕ) (K : ℝ) (hgK2 : (2 : ℝ) ≤ growthBar K)
    (hgK0 : (0 : ℝ) < growthBar K)
    {lgK : ℝ} (hlgKdef : lgK = Real.logb 3 (growthBar K))
    (hlgK0 : 0 ≤ lgK) :
    (3 : ℝ) ^ (sourceBurn d 1 K) ≤
      (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 * growthBar K ^ (4 * d + 8) := by
  classical
  have hmm : momentMultiplier 1 (growthBar K) ≤ 3 * growthBar K ^ 2 := by
    rw [momentMultiplier]
    have hlog : Real.log (growthBar K) ≤ growthBar K - 1 :=
      Real.log_le_sub_one_of_pos hgK0
    have hceil1 : (⌈(1 : ℝ) * (1 + 1) / 2⌉ : ℤ) = 1 := by norm_num
    rw [hceil1, inv_one, Real.rpow_one]
    have h1 : growthBar K ^ (1 : ℤ) = growthBar K := zpow_one _
    rw [h1]
    nlinarith only [hlog, hgK2]
  have hsb : (3 : ℝ) ^ (sourceBurn d 1 K) ≤
      (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 * growthBar K ^ (4 * d + 8) := by
    rw [sourceBurn, ← hlgKdef]
    have hc2 : (0 : ℤ) ≤ ⌈2 * lgK⌉ := by
      refine Int.ceil_nonneg ?_
      linarith only [hlgK0]
    have hc3arg : 0 ≤ 2 + 4 * ((d : ℝ) + 1) * lgK +
        Real.logb 3 (momentMultiplier 1 (growthBar K)) := by
      have hmm1 : (1 : ℝ) ≤ momentMultiplier 1 (growthBar K) := by
        rw [momentMultiplier]
        have hceil1 : (⌈(1 : ℝ) * (1 + 1) / 2⌉ : ℤ) = 1 := by norm_num
        rw [hceil1, inv_one, Real.rpow_one, zpow_one]
        have hlog0 : 0 ≤ Real.log (growthBar K) :=
          Real.log_nonneg (by linarith only [hgK2])
        nlinarith only [hgK2, hlog0]
      have hlmm0 : 0 ≤ Real.logb 3 (momentMultiplier 1 (growthBar K)) :=
        Real.logb_nonneg (by norm_num) hmm1
      have hd0 : (0 : ℝ) ≤ 4 * ((d : ℝ) + 1) * lgK := by positivity
      linarith only [hlmm0, hd0]
    have hc3 : (0 : ℤ) ≤ ⌈2 + 4 * ((d : ℝ) + 1) * lgK +
        Real.logb 3 (momentMultiplier 1 (growthBar K))⌉ :=
      Int.ceil_nonneg hc3arg
    have hkz : (0 : ℤ) ≤ ((kZero d : ℕ) : ℤ) := Int.natCast_nonneg _
    have hsplit1 := three_zpow_max_le_mul (a := ⌈2 * lgK⌉)
      (b := ⌈2 + 4 * ((d : ℝ) + 1) * lgK +
        Real.logb 3 (momentMultiplier 1 (growthBar K))⌉) hc2 hc3
    have hsplit2 := three_zpow_max_le_mul (a := ((kZero d : ℕ) : ℤ))
      (b := max ⌈2 * lgK⌉ ⌈2 + 4 * ((d : ℝ) + 1) * lgK +
        Real.logb 3 (momentMultiplier 1 (growthBar K))⌉) hkz
      (le_max_of_le_left hc2)
    have hA : (3 : ℝ) ^ (⌈2 * lgK⌉ : ℤ) ≤ 3 * growthBar K ^ (2 : ℕ) := by
      refine le_trans (three_zpow_intCeil_le _) ?_
      rw [hlgKdef, three_rpow_mul_logb hgK0]
      have hconv : growthBar K ^ (2 : ℝ) = growthBar K ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast (growthBar K) 2]
        norm_num
      rw [hconv]
    have hB : (3 : ℝ) ^ (⌈2 + 4 * ((d : ℝ) + 1) * lgK +
        Real.logb 3 (momentMultiplier 1 (growthBar K))⌉ : ℤ) ≤
        27 * growthBar K ^ (4 * d + 4) *
          (3 * growthBar K ^ 2) := by
      refine le_trans (three_zpow_intCeil_le _) ?_
      have hexp : (3 : ℝ) ^ (2 + 4 * ((d : ℝ) + 1) * lgK +
          Real.logb 3 (momentMultiplier 1 (growthBar K))) =
          9 * (3 : ℝ) ^ (4 * ((d : ℝ) + 1) * lgK) *
            momentMultiplier 1 (growthBar K) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 3),
          Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        have hmm0 : (0 : ℝ) < momentMultiplier 1 (growthBar K) := by
          rw [momentMultiplier]
          have hceil1 : (⌈(1 : ℝ) * (1 + 1) / 2⌉ : ℤ) = 1 := by norm_num
          rw [hceil1, inv_one, Real.rpow_one, zpow_one]
          have hlog0 : 0 ≤ Real.log (growthBar K) :=
            Real.log_nonneg (by linarith only [hgK2])
          nlinarith only [hgK2, hlog0]
        rw [hlgKdef, Real.rpow_logb (by norm_num) (by norm_num) hmm0]
        norm_num
      rw [hexp]
      have hpow : (3 : ℝ) ^ (4 * ((d : ℝ) + 1) * lgK) =
          growthBar K ^ (4 * ((d : ℝ) + 1)) := by
        rw [hlgKdef]
        exact three_rpow_mul_logb hgK0 _
      rw [hpow]
      have hpowc : growthBar K ^ (4 * ((d : ℝ) + 1)) =
          growthBar K ^ ((4 * d + 4 : ℕ) : ℝ) := by
        congr 1
        push_cast
        ring
      rw [hpowc, Real.rpow_natCast]
      calc 3 * (9 * growthBar K ^ (4 * d + 4) *
            momentMultiplier 1 (growthBar K)) =
          27 * growthBar K ^ (4 * d + 4) *
            momentMultiplier 1 (growthBar K) := by ring
        _ ≤ 27 * growthBar K ^ (4 * d + 4) * (3 * growthBar K ^ 2) := by
            refine mul_le_mul_of_nonneg_left hmm ?_
            positivity
    refine le_trans hsplit2 ?_
    have hstep := mul_le_mul hA hB (by positivity) (by positivity)
    calc (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) *
          (3 : ℝ) ^ (max ⌈2 * lgK⌉ ⌈2 + 4 * ((d : ℝ) + 1) * lgK +
            Real.logb 3 (momentMultiplier 1 (growthBar K))⌉) ≤
        (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) *
          ((3 : ℝ) ^ (⌈2 * lgK⌉ : ℤ) *
            (3 : ℝ) ^ (⌈2 + 4 * ((d : ℝ) + 1) * lgK +
              Real.logb 3 (momentMultiplier 1 (growthBar K))⌉ : ℤ)) := by
          refine mul_le_mul_of_nonneg_left hsplit1 ?_
          positivity
      _ ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) *
          (3 * growthBar K ^ (2 : ℕ) *
            (27 * growthBar K ^ (4 * d + 4) * (3 * growthBar K ^ 2))) := by
          refine mul_le_mul_of_nonneg_left hstep ?_
          positivity
      _ = (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 *
          growthBar K ^ (4 * d + 8) := by
          rw [show 4 * d + 8 = 2 + (4 * d + 4) + 2 from by omega]
          ring
  exact hsb

private theorem burn_quotient_ceiling_power_bound
    (d : ℕ) (hd : 2 ≤ d) (D : ℕ) (K : ℝ)
    (hgK0 : (0 : ℝ) < growthBar K)
    {lgK : ℝ} (hlgKdef : lgK = Real.logb 3 (growthBar K))
    (hlgK0 : 0 ≤ lgK) :
    (3 : ℝ) ^ (⌈((d : ℝ) * (2 * (D : ℝ)) +
      16 * ((d : ℝ) + 1) ^ 2 * lgK) / (4 * (d : ℝ) + 3)⌉ : ℤ) ≤
      3 * ((3 : ℝ) ^ (D : ℕ) * growthBar K ^ (5 * d + 5)) := by
  classical
  have hq : ((d : ℝ) * (2 * (D : ℝ)) +
      16 * ((d : ℝ) + 1) ^ 2 * lgK) / (4 * (d : ℝ) + 3) ≤
      (D : ℝ) + 5 * ((d : ℝ) + 1) * lgK := by
    have hden : (0 : ℝ) < 4 * (d : ℝ) + 3 := by positivity
    rw [div_le_iff₀ hden]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith only [hd1]
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (d : ℝ) * (D : ℝ) := mul_nonneg hd0 hD0
    have h2 : (0 : ℝ) ≤ ((d : ℝ) + 1) * lgK :=
      mul_nonneg (by linarith only [hd0]) hlgK0
    have h3 : (0 : ℝ) ≤ (d : ℝ) * (((d : ℝ) + 1) * lgK) :=
      mul_nonneg hd0 h2
    nlinarith only [hd1, h1, h2, h3, hD0, hlgK0]
  have hqceil : (3 : ℝ) ^ (⌈((d : ℝ) * (2 * (D : ℝ)) +
      16 * ((d : ℝ) + 1) ^ 2 * lgK) / (4 * (d : ℝ) + 3)⌉ : ℤ) ≤
      3 * ((3 : ℝ) ^ (D : ℕ) * growthBar K ^ (5 * d + 5)) := by
    have harg0 : 0 ≤ ((d : ℝ) * (2 * (D : ℝ)) +
        16 * ((d : ℝ) + 1) ^ 2 * lgK) / (4 * (d : ℝ) + 3) := by
      have hden : (0 : ℝ) < 4 * (d : ℝ) + 3 := by positivity
      refine div_nonneg ?_ hden.le
      have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ (d : ℝ) * (2 * (D : ℝ)) := by positivity
      have h2 : (0 : ℝ) ≤ 16 * ((d : ℝ) + 1) ^ 2 * lgK := by positivity
      linarith only [h1, h2]
    refine le_trans (three_zpow_intCeil_le _) ?_
    have hmono : (3 : ℝ) ^ (((d : ℝ) * (2 * (D : ℝ)) +
        16 * ((d : ℝ) + 1) ^ 2 * lgK) / (4 * (d : ℝ) + 3)) ≤
        (3 : ℝ) ^ ((D : ℝ) + 5 * ((d : ℝ) + 1) * lgK) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
    have hsplit : (3 : ℝ) ^ ((D : ℝ) + 5 * ((d : ℝ) + 1) * lgK) =
        (3 : ℝ) ^ (D : ℕ) * growthBar K ^ (5 * d + 5) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 1
      · rw [Real.rpow_natCast]
      · rw [hlgKdef, three_rpow_mul_logb hgK0]
        rw [show (5 * ((d : ℝ) + 1)) = ((5 * d + 5 : ℕ) : ℝ) from by
          push_cast; ring]
        rw [Real.rpow_natCast]
    refine le_trans (mul_le_mul_of_nonneg_left hmono (by norm_num)) ?_
    rw [hsplit]
  exact hqceil

private theorem burn_split_threshold_power_bound
    (d : ℕ) (K : ℝ) (D : ℕ) (jS : ℤ)
    (hgKpow : ∀ a b : ℕ, a ≤ b → growthBar K ^ a ≤ growthBar K ^ b)
    (hD31 : (1 : ℝ) ≤ (3 : ℝ) ^ D)
    (hjS : (3 : ℝ) ^ jS ≤
      ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 * growthBar K ^ (4 * d + 8)) *
        (3 * ((3 : ℝ) ^ D * growthBar K ^ (5 * d + 5)))) :
    burnSplitThreshold d K jS (jS + ((2 * D : ℕ) : ℤ)) ≤
      ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
        ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13) := by
  classical
  have hthr : burnSplitThreshold d K jS (jS + ((2 * D : ℕ) : ℤ)) ≤
      ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
        ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13) := by
    rw [burnSplitThreshold]
    have hMjS : jS + ((2 * D : ℕ) : ℤ) - jS + 1 = ((2 * D : ℕ) : ℤ) + 1 := by
      ring
    have h2D : (3 : ℝ) ^ (jS + ((2 * D : ℕ) : ℤ)) =
        (3 : ℝ) ^ jS * ((3 : ℝ) ^ (D : ℕ)) ^ (2 : ℕ) := by
      rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
      congr 1
      rw [show ((2 * D : ℕ) : ℤ) = (2 * D : ℕ) from rfl]
      rw [zpow_natCast]
      ring
    have hterm1 : (3 : ℝ) ^ (jS + ((2 * D : ℕ) : ℤ)) ≤
        ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729) *
          ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13) := by
      rw [h2D]
      have hstep := mul_le_mul_of_nonneg_right hjS
        (by positivity : (0:ℝ) ≤ ((3 : ℝ) ^ (D : ℕ)) ^ (2 : ℕ))
      refine le_trans hstep (le_of_eq ?_)
      rw [show 9 * d + 13 = (4 * d + 8) + (5 * d + 5) from by omega]
      rw [pow_add]
      ring
    have hterm2 : growthBar K ^ (4 * (d + 1)) *
        (3 : ℝ) ^ (jS + ((2 * D : ℕ) : ℤ) - jS + 1) ≤
        3 * ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
          growthBar K ^ (9 * d + 13) := by
      rw [hMjS]
      have hz : (3 : ℝ) ^ (((2 * D : ℕ) : ℤ) + 1) =
          3 * ((3 : ℝ) ^ (D : ℕ)) ^ (2 : ℕ) := by
        rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_natCast, zpow_one]
        ring
      rw [hz]
      have hgle : growthBar K ^ (4 * (d + 1)) ≤
          growthBar K ^ (9 * d + 13) :=
        hgKpow _ _ (by omega)
      have hDle : ((3 : ℝ) ^ (D : ℕ)) ^ (2 : ℕ) ≤
          ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) :=
        pow_le_pow_right₀ hD31 (by omega)
      calc growthBar K ^ (4 * (d + 1)) *
            (3 * ((3 : ℝ) ^ (D : ℕ)) ^ (2 : ℕ)) ≤
          growthBar K ^ (9 * d + 13) *
            (3 * ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ)) := by
            refine mul_le_mul hgle ?_ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hDle (by norm_num)
        _ = 3 * ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
            growthBar K ^ (9 * d + 13) := by ring
    refine max_le (le_trans hterm1 ?_) (le_trans hterm2 ?_)
    · have h1 : (0 : ℝ) ≤ ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
          growthBar K ^ (9 * d + 13) := by positivity
      nlinarith only [h1]
    · have h1 : (0 : ℝ) ≤ ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
          growthBar K ^ (9 * d + 13) := by positivity
      have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 := by
        positivity
      nlinarith only [h1, h2]
  exact hthr

/-- **The burn-split witness exponent.** -/
theorem exists_burnSplit_witness_exponent (d : ℕ) (hd : 2 ≤ d)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ cW : ℝ, 0 ≤ cW ∧
      ∀ K Pi : ℝ, 1 < K → 1 ≤ Pi →
        ∀ n : ℕ, K ^ (n + 2) ≤ 2 * K ^ 3 →
        burnSplitThreshold d K
            (burnSplitAnchor d 1 K (burnSplitDepth d Cd g Pi))
            (burnSplitAnchor d 1 K (burnSplitDepth d Cd g Pi) +
              ((2 * burnSplitDepth d Cd g Pi : ℕ) : ℤ)) *
          K * K ^ (n + 1) ≤ Real.rpow (2 + Pi * K) cW := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hzeta : (1 : ℝ) ≤ zetaG g := by
    have hlt : (3 : ℝ) ^ (-(1 - g)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith only [hg.2])
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [zetaG]
    rw [le_inv_comm₀ (by norm_num) (by linarith only [hlt, hpos])]
    linarith only [hpos]
  have hsd1 : (1 : ℝ) ≤ Real.sqrt d := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt h1
  set CW : ℝ := (100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d with hCWdef
  have hCW1 : (1 : ℝ) ≤ CW := by
    rw [hCWdef]
    have hcz : (1 : ℝ) ≤ Cd * zetaG g := by
      nlinarith only [hCd1, hzeta,
        mul_nonneg (sub_nonneg.mpr hCd1) (sub_nonneg.mpr hzeta)]
    have hczs : (1 : ℝ) ≤ Cd * zetaG g * Real.sqrt d := by
      nlinarith only [hcz, hsd1,
        mul_nonneg (sub_nonneg.mpr hcz) (sub_nonneg.mpr hsd1)]
    nlinarith only [hczs]
  obtain ⟨c1, hc10, hc1⟩ := exists_rpow_ge_uniform
    (2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) * (3 * CW) ^ (3 : ℕ))
  refine ⟨c1 + (9 * (d : ℝ) + 19), by positivity, ?_⟩
  intro K Pi hK hPi n hn
  set D : ℕ := burnSplitDepth d Cd g Pi with hDdef
  set jS : ℤ := burnSplitAnchor d 1 K D with hjSdef
  set base : ℝ := 2 + Pi * K with hbasedef
  have hK1 : (1 : ℝ) ≤ K := hK.le
  have hbase3 : (3 : ℝ) ≤ base := by
    rw [hbasedef]
    have h := mul_le_mul hPi hK.le (by norm_num) (by linarith only [hPi])
    linarith only [h]
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase3]
  have hgK2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hgK0 : (0 : ℝ) < growthBar K := by linarith only [hgK2]
  have hgKb : growthBar K ≤ base := by
    rw [hbasedef, growthBar]
    have hPK : K ≤ Pi * K := by
      nlinarith only [hPi, hK]
    refine max_le (by linarith only [hPK, hK]) (by linarith only [hPK])
  have hPib : Pi ≤ base := by
    rw [hbasedef]; nlinarith only [hPi, hK]
  set lgK : ℝ := Real.logb 3 (growthBar K) with hlgKdef
  have hlgK0 : 0 ≤ lgK := by
    rw [hlgKdef]
    exact Real.logb_nonneg (by norm_num) (by linarith only [hgK2])
  -- S1: the depth power
  have hD3 : (3 : ℝ) ^ (D : ℕ) ≤ 3 * (CW * Pi) := by
    have heq : (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d =
        CW * Pi := by
      rw [hCWdef]; ring
    have harg : (1 : ℝ) ≤ CW * Pi := by nlinarith only [hCW1, hPi]
    have h := three_pow_ceil_logb_le (x := CW * Pi)
      (by linarith only [harg])
    rw [max_eq_right harg] at h
    rw [hDdef, burnSplitDepth, canonicalGridEnlargement, heq]
    exact h
  have hD31 : (1 : ℝ) ≤ (3 : ℝ) ^ (D : ℕ) := one_le_pow₀ (by norm_num)
  -- S3a: the source burn
  have hsb := source_burn_power_bound d K hgK2 hgK0 hlgKdef hlgK0
  -- S3b: the quotient ceiling
  have hqceil := burn_quotient_ceiling_power_bound d hd D K hgK0 hlgKdef hlgK0
  -- S5: the anchor power
  have hjSnn : (0 : ℤ) ≤ jS := by
    rw [hjSdef, burnSplitAnchor]
    refine le_trans ?_ (le_max_left _ _)
    rw [sourceBurn]
    exact le_max_of_le_left (Int.natCast_nonneg _)
  have hjS : (3 : ℝ) ^ jS ≤
      ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 * growthBar K ^ (4 * d + 8)) *
        (3 * ((3 : ℝ) ^ (D : ℕ) * growthBar K ^ (5 * d + 5))) := by
    rw [hjSdef, burnSplitAnchor]
    have hsbnn : (0 : ℤ) ≤ sourceBurn d 1 K := by
      rw [sourceBurn]
      exact le_max_of_le_left (Int.natCast_nonneg _)
    have hcnn : (0 : ℤ) ≤ ⌈((d : ℝ) * (2 * (D : ℝ)) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3)⌉ := by
      refine Int.ceil_nonneg ?_
      have hden : (0 : ℝ) < 4 * (d : ℝ) + 3 := by positivity
      refine div_nonneg ?_ hden.le
      have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ (d : ℝ) * (2 * (D : ℝ)) := by positivity
      have h2 : (0 : ℝ) ≤ 16 * ((d : ℝ) + 1) ^ 2 *
          Real.logb 3 (growthBar K) := by
        rw [← hlgKdef]
        positivity
      linarith only [h1, h2]
    refine le_trans (three_zpow_max_le_mul hsbnn hcnn) ?_
    rw [← hlgKdef]
    exact mul_le_mul hsb hqceil (by positivity) (by positivity)
  -- S4/S6: the threshold and the witness value
  have hgKpow : ∀ a b : ℕ, a ≤ b →
      growthBar K ^ a ≤ growthBar K ^ b := fun a b hab =>
    pow_le_pow_right₀ (by linarith only [hgK2]) hab
  have hthr := burn_split_threshold_power_bound d K D jS hgKpow hD31 hjS
  -- the final assembly
  have hval : burnSplitThreshold d K jS (jS + ((2 * D : ℕ) : ℤ)) *
      K * K ^ (n + 1) ≤
      2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) * (3 * CW) ^ (3 : ℕ) *
        base ^ (9 * d + 19) := by
    have hKn : K * K ^ (n + 1) = K ^ (n + 2) := by ring
    have hthr0 : 0 ≤ burnSplitThreshold d K jS (jS + ((2 * D : ℕ) : ℤ)) := by
      rw [burnSplitThreshold]
      refine le_max_of_le_left ?_
      positivity
    have hKp0 : (0 : ℝ) ≤ K ^ (n + 2) := by positivity
    have hstep1 : burnSplitThreshold d K jS (jS + ((2 * D : ℕ) : ℤ)) *
        K * K ^ (n + 1) ≤
        (((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
          ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13)) *
          (2 * K ^ 3) := by
      rw [mul_assoc, hKn]
      exact mul_le_mul hthr hn hKp0 (by positivity)
    refine le_trans hstep1 ?_
    have hD3' : ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) ≤ (3 * (CW * Pi)) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hD3 3
    have hPi3 : (3 * (CW * Pi)) ^ (3 : ℕ) = (3 * CW) ^ (3 : ℕ) *
        Pi ^ (3 : ℕ) := by ring
    have hgKb' : growthBar K ^ (9 * d + 13) ≤ base ^ (9 * d + 13) :=
      pow_le_pow_left₀ (by linarith only [hgK2]) hgKb _
    have hKb : K ^ 3 ≤ base ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hK1]) (by
        rw [hbasedef]; nlinarith only [hPi, hK]) 3
    have hPib' : Pi ^ (3 : ℕ) ≤ base ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by linarith only [hPi]) hPib 3
    have hchain : (((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
        ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13)) *
        (2 * K ^ 3) ≤
        2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
          (3 * CW) ^ (3 : ℕ) *
          (base ^ (3 : ℕ) * base ^ (9 * d + 13) * base ^ 3) := by
      have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 243 + 3 := by
        positivity
      have hCW0 : (0 : ℝ) ≤ 3 * CW := by linarith only [hCW1]
      have hb1 := mul_le_mul hD3' hgKb' (by positivity) (by positivity)
      rw [hPi3] at hb1
      have hb2 := mul_le_mul_of_nonneg_left hPib'
        (by positivity : (0:ℝ) ≤ (3 * CW) ^ (3 : ℕ))
      have hb3 : ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
          growthBar K ^ (9 * d + 13) ≤
          (3 * CW) ^ (3 : ℕ) * base ^ (3 : ℕ) * base ^ (9 * d + 13) := by
        calc ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
            growthBar K ^ (9 * d + 13) ≤
            (3 * CW) ^ (3 : ℕ) * Pi ^ (3 : ℕ) * base ^ (9 * d + 13) := hb1
          _ ≤ (3 * CW) ^ (3 : ℕ) * base ^ (3 : ℕ) * base ^ (9 * d + 13) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact hb2
      calc (((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
          ((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) * growthBar K ^ (9 * d + 13)) *
          (2 * K ^ 3) =
          2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
            (((3 : ℝ) ^ (D : ℕ)) ^ (3 : ℕ) *
              growthBar K ^ (9 * d + 13)) * K ^ 3 := by ring
        _ ≤ 2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
            ((3 * CW) ^ (3 : ℕ) * base ^ (3 : ℕ) * base ^ (9 * d + 13)) *
            base ^ 3 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hb3 (by
              positivity)) hKb (by positivity) (by positivity)
        _ = 2 * ((3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * 729 + 3) *
            (3 * CW) ^ (3 : ℕ) *
            (base ^ (3 : ℕ) * base ^ (9 * d + 13) * base ^ 3) := by ring
    refine le_trans hchain (le_of_eq ?_)
    have hbp : base ^ (3 : ℕ) * base ^ (9 * d + 13) * base ^ 3 =
        base ^ (9 * d + 19) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hbp]
  refine le_trans hval ?_
  have hcap := hc1 base hbase3
  have hpow0 : (0 : ℝ) ≤ base ^ (9 * d + 19) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hcap hpow0
  refine le_trans hstep (le_of_eq ?_)
  show base ^ c1 * base ^ (9 * d + 19) = base ^ (c1 + (9 * (d : ℝ) + 19))
  rw [show base ^ (9 * d + 19) = base ^ (((9 * d + 19 : ℕ) : ℝ)) from
    (Real.rpow_natCast base _).symm, ← Real.rpow_add hbase0]
  congr 1
  push_cast
  ring

end

end HCPolySupport.HighContrast.Quenched
