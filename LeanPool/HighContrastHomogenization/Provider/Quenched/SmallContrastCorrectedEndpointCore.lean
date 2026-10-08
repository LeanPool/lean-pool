/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepFamilyAtIsotropySplit
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitWitnessCap
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedCadenceDesign
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedSourcePricing
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitRateCheck
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastNormalizedGauge
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastThresholdPolynomial
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewUnitRange
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDesignConstantBounds
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedSourceCap
import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapFiniteBandTransfer

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedEndpointCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
open HCPolySupport.HighContrast.Quenched HCPolySupport.HighContrast HCPolySupport MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
noncomputable section

private theorem ceil_le_split_tail (s c t : ℤ) (G : ℕ) (hc : c ≤ max 1 c) (ht : 1 ≤ t) : c ≤ (s
  + max 1 c + t) + (G : ℤ) - s := by
  omega

private theorem le_three_zpow_ceil_logb {x : ℝ} (hx : 0 < x) : x ≤ (3 : ℝ) ^ (⌈Real.logb 3 x⌉ :
  ℤ) := by
  have hceil : Real.logb 3 x ≤ ((⌈Real.logb 3 x⌉ : ℤ) : ℝ) := Int.le_ceil _
  calc
    x = (3 : ℝ) ^ Real.logb 3 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ (3 : ℝ) ^ ((⌈Real.logb 3 x⌉ : ℤ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      hceil
    _ = (3 : ℝ) ^ (⌈Real.logb 3 x⌉ : ℤ) := Real.rpow_intCast 3 _

private theorem sourceMomentTwo_le_isotropySplit_tail {d : ℕ} (K Cd g : ℝ) (m : Mat d) (G : ℕ)
  (s : ℤ) : sourceMomentTwo K ≤ (3 : ℝ) ^ (isotropySplit K (1 / 8 / 2) Cd g m G s + (G : ℤ) - s)
  := by
  have hx1 : (1 : ℝ) ≤ sourceMomentTwo K := one_le_sourceMomentTwo K
  have hx0 : (0 : ℝ) < sourceMomentTwo K / (1 / 8 / 2) := div_pos (lt_of_lt_of_le one_pos hx1)
    (by norm_num)
  have hceil := le_three_zpow_ceil_logb hx0
  have ht := one_le_tiltGap Cd g (1 / 8 / 2) m G
  have hc := le_max_right (1 : ℤ)
    ⌈Real.logb 3 (sourceMomentTwo K / (1 / 8 / 2))⌉
  have hle : (⌈Real.logb 3 (sourceMomentTwo K / (1 / 8 / 2))⌉ : ℤ) ≤ isotropySplit K (1 / 8 / 2)
    Cd g m G s + (G : ℤ) - s := by
    rw [isotropySplit, euclideanEntryThreshold]
    exact ceil_le_split_tail s _ _ G hc ht
  have hmono := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hle
  have hdiv : sourceMomentTwo K ≤ sourceMomentTwo K / (1 / 8 / 2) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 8 / 2)]
    nlinarith only [hx1]
  exact hdiv.trans (hceil.trans hmono)

private theorem one_le_thirteen_mul_pow_four {x : ℝ} (hx : 2 ≤ x) : (1 : ℝ) ≤ 13 * x ^ 4 := by
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by nlinarith only [hx]
  nlinarith only [hx2, sq_nonneg (x ^ 2)]

private theorem exists_three_pow_sandwich {x : ℝ} (hx : 1 ≤ x) : ∃ n : ℕ, x ≤ (3 : ℝ) ^ n ∧ (3 :
  ℝ) ^ n ≤ 3 * x := by
  refine ⟨⌈Real.logb 3 x⌉₊, ?_, ?_⟩
  · have hceil : Real.logb 3 x ≤ (⌈Real.logb 3 x⌉₊ : ℝ) := Nat.le_ceil _
    calc
      x = (3 : ℝ) ^ Real.logb 3 x := (Real.rpow_logb (by norm_num) (by norm_num)
          (lt_of_lt_of_le one_pos hx)).symm
      _ ≤ (3 : ℝ) ^ (⌈Real.logb 3 x⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = (3 : ℝ) ^ (⌈Real.logb 3 x⌉₊ : ℕ) := Real.rpow_natCast 3 _
  · have h := three_pow_ceil_logb_le
      (x := x) (lt_of_lt_of_le one_pos hx)
    rw [max_eq_right hx] at h
    exact h

private theorem exists_deep_kill_generation (H D : ℕ) : ∃ n : ℕ, H ≤ n ∧ (10 * (3 : ℝ) ^ (2 * D
  + H) : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ))) ∧ (3 : ℝ) ^ n ≤ 8100 * 3 ^ (3 *
  H) * (3 : ℝ) ^ (4 * D) := by
  have hx1 : (1 : ℝ) ≤ 10 * (3 : ℝ) ^ (2 * D + H) := by
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * D + H) := one_le_pow₀ (by norm_num)
    linarith only [h1]
  set y : ℝ := Real.logb 3 (10 * (3 : ℝ) ^ (2 * D + H)) with hydef
  have hy0 : 0 ≤ y := by
    rw [hydef]
    exact Real.logb_nonneg (by norm_num) hx1
  refine ⟨H + 2 * (⌈y⌉₊ + 1), by omega, ?_, ?_⟩
  · have hceil : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (1 / 2 : ℝ) * (((H + 2 * (⌈y⌉₊ + 1) : ℕ) : ℝ) + 1 - (H : ℝ)) = (⌈y⌉₊ : ℝ) + 3 /
      2 := by
      push_cast
      ring
    rw [hcast]
    calc
      (10 * (3 : ℝ) ^ (2 * D + H) : ℝ) = (3 : ℝ) ^ y := by
        rw [hydef]
        exact (Real.rpow_logb (by norm_num) (by norm_num)
          (lt_of_lt_of_le one_pos hx1)).symm
      _ ≤ (3 : ℝ) ^ ((⌈y⌉₊ : ℝ) + 3 / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith only [hceil])
  · have hceil : ((3 : ℝ) ^ (⌈y⌉₊ : ℕ)) ≤ 3 * (3 : ℝ) ^ y := by
      have h1 : ((⌈y⌉₊ : ℕ) : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
      calc
        ((3 : ℝ) ^ (⌈y⌉₊ : ℕ)) =
            (3 : ℝ) ^ ((⌈y⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast 3 _).symm
        _ ≤ (3 : ℝ) ^ (y + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = 3 * (3 : ℝ) ^ y := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
          ring
    have hyval : (3 : ℝ) ^ y = 10 * (3 : ℝ) ^ (2 * D + H) := by
      rw [hydef]
      exact Real.rpow_logb (by norm_num) (by norm_num)
        (lt_of_lt_of_le one_pos hx1)
    have hsq : ((3 : ℝ) ^ (⌈y⌉₊ : ℕ)) ^ 2 ≤ (3 * (10 * (3 : ℝ) ^ (2 * D + H))) ^ 2 := by
      rw [hyval] at hceil
      exact pow_le_pow_left₀ (by positivity) hceil 2
    have hexp : (3 : ℝ) ^ (H + 2 * (⌈y⌉₊ + 1) : ℕ) = (3 : ℝ) ^ H * 9 * ((3 : ℝ) ^ (⌈y⌉₊ : ℕ)) ^
      2 := by
      rw [show H + 2 * (⌈y⌉₊ + 1) = H + ⌈y⌉₊ * 2 + 2 by ring,
        pow_add, pow_add, ← pow_mul]
      norm_num
      ring
    rw [hexp]
    have hpowsplit : ((3 : ℝ) ^ (2 * D + H)) ^ 2 = (3 : ℝ) ^ (4 * D) * ((3 : ℝ) ^ H) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    have h3H : ((3 : ℝ) ^ H) ^ 2 * (3 : ℝ) ^ H = (3 : ℝ) ^ (3 * H) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    nlinarith only [hsq, hpowsplit, h3H,
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) H,
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (4 * D)]

private theorem exists_rate_generation {r rate : ℝ} (hr : 1 ≤ r) (hrate : 0 < rate) : ∃ n : ℕ, r
  ≤ (3 : ℝ) ^ (rate * (n : ℝ)) ∧ (3 : ℝ) ^ n ≤ 3 * r ^ rate⁻¹ := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  set z : ℝ := Real.logb 3 r with hzdef
  have hz0 : 0 ≤ z := by rw [hzdef]; exact Real.logb_nonneg (by norm_num) hr
  have hzval : (3 : ℝ) ^ z = r := by
    rw [hzdef]
    exact Real.rpow_logb (by norm_num) (by norm_num) hr0
  refine ⟨⌈z / rate⌉₊, ?_, ?_⟩
  · have hceil : z / rate ≤ (⌈z / rate⌉₊ : ℝ) := Nat.le_ceil _
    have hmul : z ≤ rate * (⌈z / rate⌉₊ : ℝ) := by
      rw [div_le_iff₀ hrate] at hceil
      linarith only [hceil]
    calc
      r = (3 : ℝ) ^ z := hzval.symm
      _ ≤ (3 : ℝ) ^ (rate * (⌈z / rate⌉₊ : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        hmul
  · have hdiv0 : 0 ≤ z / rate := div_nonneg hz0 hrate.le
    have hceil : ((⌈z / rate⌉₊ : ℕ) : ℝ) ≤ z / rate + 1 := (Nat.ceil_lt_add_one hdiv0).le
    calc
      (3 : ℝ) ^ (⌈z / rate⌉₊ : ℕ) =
          (3 : ℝ) ^ ((⌈z / rate⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast 3 _).symm
      _ ≤ (3 : ℝ) ^ (z / rate + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = 3 * (3 : ℝ) ^ (z / rate) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
        ring
      _ = 3 * r ^ rate⁻¹ := by
        rw [div_eq_mul_inv, Real.rpow_mul (by norm_num), hzval]

private theorem exists_generation_max (H nB nE nF : ℕ) : ∃ n : ℕ, H + 1 ≤ n ∧ nB ≤ n ∧ nE ≤ n ∧
  nF ≤ n ∧ n ≤ (H + 1) + nB + nE + nF := by
  exact ⟨max (max (H + 1) nB) (max nE nF), by omega, by omega,
    by omega, by omega, by omega⟩

private theorem three_rpow_neg_half_le_three_fifths : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 5 := by
  have hsqrt3 : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hy0 : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hy53 : (5 / 3 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) := by
    nlinarith only [hsqrt3, hy0]
  rw [Real.rpow_neg (by norm_num)]
  have hinv := mul_inv_cancel₀ hy0.ne'
  have h5 := mul_le_mul_of_nonneg_right hy53 (inv_nonneg.mpr hy0.le)
  rw [hinv] at h5
  have hcast : ((3 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ = ((3 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by norm_num
  rw [hcast] at h5 ⊢
  linarith only [h5]

private theorem geom_inverse_le_five_halves {g : ℝ} (hg : g < 1) : (1 - (3 : ℝ) ^ (-(3 / 2 -
  g)))⁻¹ ≤ 5 / 2 := by
  have hle : (3 : ℝ) ^ (-(3 / 2 - g)) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hg])
  have hden : (2 / 5 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(3 / 2 - g)) := by
    linarith only [hle, three_rpow_neg_half_le_three_fifths]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 / 5) hden
  rw [one_div, one_div] at h
  calc
    (1 - (3 : ℝ) ^ (-(3 / 2 - g)))⁻¹ ≤ ((2 : ℝ) / 5)⁻¹ := h
    _ = 5 / 2 := by norm_num

private theorem deepKill_mono (H D n₀ n : ℕ) (hn : n₀ ≤ n) (hkill : (10 * (3 : ℝ) ^ (2 * D + H)
  : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n₀ : ℝ) + 1 - (H : ℝ)))) : (10 * (3 : ℝ) ^ (2 * D + H) : ℝ)
  ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ))) := by
  refine hkill.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have hnr : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith only [hnr]

private theorem generation_index_bounds (lAl sKw split : ℤ) (N₀ ns H nsB G : ℕ) (hlN : lAl ≤ (N₀
  : ℤ)) (hKw : sKw + 2 ≤ split) (hN : (N₀ : ℤ) = split) (hB : nsB ≤ ns) : lAl ≤ (N₀ : ℤ) + ((ns
  - H : ℕ) : ℤ) ∧ (∀ n : ℕ, ns ≤ n → lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) ∧ (∀ n : ℕ,
  ns ≤ n → sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) ∧ (∀ n : ℕ, ns ≤ n → split ≤ (N₀ : ℤ)
  + (n : ℤ) - ((n - ns : ℕ) : ℤ)) ∧ (∀ n : ℕ, ns ≤ n → (nsB : ℤ) ≤ ((N₀ : ℤ) + (n : ℤ) - ((n -
  ns : ℕ) : ℤ)) + ((G + 1 : ℕ) : ℤ) - 1 - sKw) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro n hn <;> omega

private theorem zero_le_euclideanEntryThreshold_of_nonneg (K c : ℝ) (s : ℤ) (hs : 0 ≤ s) : 0 ≤
  euclideanEntryThreshold K c s := by
  rw [euclideanEntryThreshold]
  omega

private theorem split_le_nat_add (split : ℤ) (N₀ : ℕ) (hN : (N₀ : ℤ) = split) : ∀ n : ℕ, split ≤
  (N₀ : ℤ) + (n : ℤ) := by
  intro n
  rw [← hN]
  exact Int.le_add_of_nonneg_right (Int.natCast_nonneg n)

private theorem le_of_le_add_two {a b c : ℤ} (hab : a ≤ b) (hbc : b + 2 ≤ c) : a ≤ c := by omega

private theorem exists_nat_eq_with_lower (l s : ℤ) (hl : 0 ≤ l) (hls : l ≤ s) : ∃ N : ℕ, (N : ℤ)
  = s ∧ l ≤ (N : ℤ) := by
  have hs : 0 ≤ s := hl.trans hls
  refine ⟨s.toNat, Int.toNat_of_nonneg hs, ?_⟩
  rw [Int.toNat_of_nonneg hs]
  exact hls

private theorem pred_depth_accounts (D G c : ℕ) (hD : 1 ≤ D) (hG : G = D - 1) (hc : c + 1 ≤ D) :
  G + 1 = D ∧ c ≤ G := by
  omega

private theorem three_pow_mono {m n : ℕ} (h : m ≤ n) : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
  pow_le_pow_right₀ (by norm_num) h

private theorem three_pow_reindex {x : ℝ} {G D : ℕ} (hGD : G + 1 = D) (h : x ≤ (3 : ℝ) ^ D) : x
  ≤ (3 : ℝ) ^ (G + 1) := by
  rwa [hGD]

private theorem vsumSourceConstant_mono_delta {d : ℕ} {Csub Msc delta delta' : ℝ} (hdelta :
  delta ≤ delta') : vsumSourceConstant d Csub Msc delta ≤ vsumSourceConstant d Csub Msc delta' := by
  have hdeep : deepSlotConstant d Csub Msc delta ≤ deepSlotConstant d Csub Msc delta' := by
    rw [deepSlotConstant, deepSlotConstant]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_left hdelta (slotBaseCoefficient_nonneg d)) _
  rw [vsumSourceConstant, vsumSourceConstant]
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right hdeep _) (zero_le_one.trans halfGeom_one_le)

private theorem one_le_mul_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith only [ha, hb, mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

private theorem growth_row_bound_of_generation {K : ℝ} {nB : ℕ} {e : ℤ} (hK : (2 : ℝ) ≤
  growthBar K) (hB : 13 * growthBar K ^ 4 ≤ (3 : ℝ) ^ nB) (he : (nB : ℤ) ≤ e) : 1 + 2 * ((2 + 1
  : ℕ) : ℝ) * (1 + Real.log (growthBar K)) * growthBar K ^ IndependentSums.natTriangular (2 + 1)
  ≤ (3 : ℝ) ^ (((1 : ℕ) : ℝ) * (e : ℝ)) := by
  have hcrude := crude_le_growth_pow (2 + 1) hK
  have hT3 : IndependentSums.natTriangular (2 + 1) + 1 = 4 := by rfl
  have h13 : (4 * ((2 + 1 : ℕ) : ℝ) + 1) * growthBar K ^ (IndependentSums.natTriangular (2 + 1)
    + 1) = 13 * growthBar K ^ 4 := by
    rw [hT3]
    norm_num
  have heR : ((nB : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (e : ℝ) := by
    rw [Nat.cast_one, one_mul]
    exact_mod_cast he
  calc
    1 + 2 * ((2 + 1 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (2 + 1) ≤
        (4 * ((2 + 1 : ℕ) : ℝ) + 1) *
          growthBar K ^ (IndependentSums.natTriangular (2 + 1) + 1) := hcrude
    _ = 13 * growthBar K ^ 4 := h13
    _ ≤ (3 : ℝ) ^ (nB : ℕ) := hB
    _ = (3 : ℝ) ^ ((nB : ℕ) : ℝ) := (Real.rpow_natCast 3 _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) heR

private theorem cubic_smallness_mono {A Abar delta : ℝ} (hA : 1 ≤ A) (hAle : A ≤ Abar) (hdelta :
  0 < delta) (hcap : (128 * Abar ^ 2) ^ 3 * delta ≤ 1 / 3) : (128 * A ^ 2) ^ 3 * delta ≤ 1 / 3 := by
  have hsq : A ^ 2 ≤ Abar ^ 2 := by
    nlinarith only [hAle, hA]
  have hmul : 128 * A ^ 2 ≤ 128 * Abar ^ 2 := by
    linarith only [hsq]
  have hmul0 : (0 : ℝ) ≤ 128 * A ^ 2 := by positivity
  have hcube := pow_le_pow_left₀ hmul0 hmul 3
  nlinarith only [hcube, hcap, hdelta,
    pow_nonneg (by positivity : (0 : ℝ) ≤ 128 * A ^ 2) 3]

private theorem twenty_four_mul_le_three_rpow_rate_ceil {A Abar alpha : ℝ} {cA : ℕ} (hAle : A ≤
  Abar) (hAbar : 1 ≤ Abar) (halpha : 0 < alpha) (hcA : cA = ⌈Real.logb 3 (24 * Abar) / alpha⌉₊)
  : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)) := by
  have h24 : (0 : ℝ) < 24 * Abar := by linarith only [hAbar]
  have hlogb : Real.logb 3 (24 * Abar) / alpha ≤ (cA : ℝ) := by
    rw [hcA]
    exact Nat.le_ceil _
  have hexp : Real.logb 3 (24 * Abar) ≤ alpha * (cA : ℝ) := by
    rw [div_le_iff₀ halpha] at hlogb
    linarith only [hlogb]
  calc
    24 * A ≤ 24 * Abar := by linarith only [hAle]
    _ = (3 : ℝ) ^ Real.logb 3 (24 * Abar) := (Real.rpow_logb (by norm_num) (by norm_num) h24).symm
    _ ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

private theorem terminal_delay_mono {base Centry Cpref rateLo rateHi Cdelay : ℝ} (hbase : 3 ≤
  base) (hCpref : 0 ≤ Cpref) (hrateLo : 0 < rateLo) (hrates : rateLo ≤ rateHi) (hCdelay : Cdelay
  = Centry + (1 + Cpref / (rateLo / 2))) : Real.rpow base (Centry + (1 + Cpref / (rateHi / 2)))
  ≤ Real.rpow base Cdelay := by
  refine Real.rpow_le_rpow_of_exponent_le (by linarith only [hbase]) ?_
  rw [hCdelay]
  have hden : rateLo / 2 ≤ rateHi / 2 := by linarith only [hrates]
  have hinv : (rateHi / 2)⁻¹ ≤ (rateLo / 2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < rateLo / 2) hden
  have hquot : Cpref / (rateHi / 2) ≤ Cpref / (rateLo / 2) := mul_le_mul_of_nonneg_left hinv hCpref
  exact add_le_add_right (add_le_add_right hquot 1) Centry

private theorem terminal_decay_mono {rateLo rateHi : ℝ} (hrates : rateLo ≤ rateHi) (j : ℕ) :
  Real.rpow (3 : ℝ) (-(rateHi / 2) * (j : ℝ)) ≤ Real.rpow (3 : ℝ) (-(rateLo / 2) * (j : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith only [hrates, hj]

private theorem corrected_source_pricing_endpoint_branch (d : ℕ) (hd : 2 ≤ d) {Cpre Mabs L Csub
  Msc delta conv K R g beta2 : ℝ} {ns N₀ Gacc : ℕ} {sKw : ℤ} (hCpre : 0 ≤ Cpre) (hMabs : 0 ≤
  Mabs) (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta) (hconv : 0 ≤ conv) (hR : 1 ≤ R)
  (hg1 : g < 1) (hbetaHalf : beta2 ≤ 1 / 2) (hbetaAlpha : beta2 ≤ contrastAlpha g) (hoffset : 0
  ≤ (N₀ : ℤ) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw) : ∀ n m : ℕ, ns ≤ m → m ≤ n → 3 * weakCoefficient
  d Cpre * weakSourceGroupSummed Mabs L (contrastRho g) (slotVsumSharp d Csub Msc delta (n - min
  n m)) (conv * slotSourceSeq d Csub Msc delta (n - min n m) 0) (Real.sqrt 2 * Real.sqrt (L + 1)
  * Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K (((N₀ : ℤ) + (n : ℤ)) + ((Gacc
  + 1 : ℕ) : ℤ) - 1 - sKw)) (R / 2) R + Real.sqrt 2 * (3 : ℝ) ^ (-((1 - contrastRho g) / 2) *
  ((n - ns : ℕ) : ℝ)) * Real.sqrt (L + 1)) ^ 2 ≤ 1 * (3 : ℝ) ^ (-(1 * (m : ℝ))) + (1 + 6 *
  weakCoefficient d Cpre * weakSourceGroupSummed Mabs L (contrastRho g) (vsumSourceConstant d
  Csub Msc delta) (conv * vsumSourceConstant d Csub Msc delta) 0 ^ 2) * (3 : ℝ) ^ (-(1 * ((n - m
  : ℕ) : ℝ))) + (1 + 6 * weakCoefficient d Cpre * weakSourceGroupSummed Mabs L (contrastRho g) 0
  0 (badSourceLegConstantAtLevel L K R) ^ 2 * (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) * (3 : ℝ) ^ (-(2
  * beta2 * (n : ℝ))) := by
  intro n m hm hmn
  let Delta : ℤ := ((N₀ : ℤ) + (n : ℤ)) +
    ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw
  have hDelta0 : 0 ≤ Delta := by
    dsimp only [Delta]
    omega
  have hsub : ((n - ns : ℕ) : ℝ) ≤ (Delta : ℝ) := by
    exact_mod_cast (show ((n - ns : ℕ) : ℤ) ≤ Delta by
      dsimp only [Delta]
      omega)
  have hrate : beta2 * ((n - ns : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (Delta : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_right hbetaHalf (Nat.cast_nonneg (n - ns))
    linarith only [hstep, hsub]
  exact corrected_source_pricing_min
    (d := d) (Cpre := Cpre) (Mabs := Mabs) (L := L) (Csub := Csub)
    (Msc := Msc) (delta := delta) (conv := conv) (K := K) (R := R)
    (g := g) (beta2 := beta2) (ns := ns) (n := n) (m := m)
    (Delta := Delta) hd hCpre hMabs hCsub hMsc hdelta hconv hR hg1
    hbetaAlpha hm hmn hDelta0 hrate

private theorem euclidean_entry_threshold_power_cap {K base cW : ℝ} {s : ℤ} (hK2 : (2 : ℝ) ≤
  growthBar K) (hgrowth : growthBar K ≤ 2 * Real.rpow base cW) (hrpow : 1 ≤ Real.rpow base cW)
  (hm2 : 1 ≤ sourceMomentTwo K) : (3 : ℝ) ^ euclideanEntryThreshold K (1 / 8 / 2) s ≤ (3 : ℝ) ^
  s * (3 * (16 * (9 * (4 * Real.rpow base cW ^ 2)))) := by
  have hT2 : IndependentSums.natTriangular 2 + 1 = 2 := by rfl
  have hm2cap : sourceMomentTwo K ≤ 9 * growthBar K ^ 2 := by
    have hcrude := crude_le_growth_pow 2 hK2
    have h92 : (4 * ((2 : ℕ) : ℝ) + 1) * growthBar K ^ (IndependentSums.natTriangular 2 + 1) = 9
      * growthBar K ^ 2 := by
      rw [hT2]
      norm_num
    rw [sourceMomentTwo]
    linarith only [hcrude, h92.le, h92.ge]
  have hbrpow0 : (0 : ℝ) < Real.rpow base cW := by
    linarith only [hrpow]
  have hgrowthSq : growthBar K ^ 2 ≤ 4 * Real.rpow base cW ^ 2 := by
    have h1 : growthBar K ^ 2 ≤ (2 * Real.rpow base cW) ^ 2 := by
      exact pow_le_pow_left₀ (by linarith only [hK2]) hgrowth 2
    nlinarith only [h1]
  refine le_trans (three_zpow_euclideanEntryThreshold_le
    (by norm_num : (0 : ℝ) < 1 / 8 / 2) s) ?_
  have hz0 : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) _
  refine mul_le_mul_of_nonneg_left ?_ hz0.le
  have harg : sourceMomentTwo K / (1 / 8 / 2) = 16 * sourceMomentTwo K := by ring
  rw [harg]
  have h16 : 16 * sourceMomentTwo K ≤ 16 * (9 * (4 * Real.rpow base cW ^ 2)) := by
    have hcap := le_trans hm2cap (by
      linarith only [hgrowthSq] :
        9 * growthBar K ^ 2 ≤ 9 * (4 * Real.rpow base cW ^ 2))
    linarith only [hcap]
  have hmax : max 1 (16 * sourceMomentTwo K) ≤ 16 * (9 * (4 * Real.rpow base cW ^ 2)) := by
    refine max_le ?_ h16
    have h1 : (1 : ℝ) ≤ 16 * sourceMomentTwo K := by
      linarith only [hm2]
    linarith only [h1, h16]
  linarith only [hmax]

private theorem sqrt_nat_one_le {d : ℕ} (hd : 2 ≤ d) : (1 : ℝ) ≤ Real.sqrt d := by
  rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ d))

private theorem burn_split_depth_power_cap (d : ℕ) (hd : 2 ≤ d) {E : BlockMat d} {Cd g base C5 :
  ℝ} {D : ℕ} (hD : D = burnSplitDepth d Cd g (aspectRatio E)) (hCd : 1 ≤ Cd) (haspect : 1 ≤
  aspectRatio E) (hzeta : 1 ≤ zetaG g) (haspectBase : aspectRatio E ≤ base) (hC5 : C5 = 3 *
  ((100 / 99) * Cd * zetaG g * Real.sqrt d)) : (3 : ℝ) ^ D ≤ C5 * base := by
  have h := three_pow_ceil_logb_le
    (x := (100 / 99 : ℝ) * (Cd * aspectRatio E * zetaG g) * Real.sqrt d)
    (by
      have hsqrt : (1 : ℝ) ≤ Real.sqrt d := sqrt_nat_one_le hd
      have hprod : (1 : ℝ) ≤ Cd * aspectRatio E * zetaG g := by
        calc
          (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ Cd * aspectRatio E * zetaG g := by
            refine mul_le_mul (mul_le_mul hCd haspect zero_le_one
              (by linarith only [hCd])) hzeta zero_le_one ?_
            have hca := mul_le_mul hCd haspect zero_le_one
              (by linarith only [hCd])
            linarith only [hca]
      have hpos : (0 : ℝ) < (100 / 99 : ℝ) * (Cd * aspectRatio E * zetaG g) := by
        linarith only [hprod]
      positivity)
  have hmax : max 1 ((100 / 99 : ℝ) * (Cd * aspectRatio E * zetaG g) * Real.sqrt d) = (100 / 99
    : ℝ) * (Cd * aspectRatio E * zetaG g) * Real.sqrt d := by
    refine max_eq_right ?_
    have hsqrt : (1 : ℝ) ≤ Real.sqrt d := sqrt_nat_one_le hd
    have hprod : (1 : ℝ) ≤ Cd * aspectRatio E * zetaG g := by
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ Cd * aspectRatio E * zetaG g := by
          refine mul_le_mul (mul_le_mul hCd haspect zero_le_one
            (by linarith only [hCd])) hzeta zero_le_one ?_
          have hca := mul_le_mul hCd haspect zero_le_one
            (by linarith only [hCd])
          linarith only [hca]
    nlinarith only [hsqrt, hprod]
  rw [hmax] at h
  have heq : (3 : ℝ) ^ D ≤ 3 * ((100 / 99 : ℝ) * (Cd * aspectRatio E * zetaG g) * Real.sqrt d) := by
    rw [hD, burnSplitDepth, canonicalGridEnlargement]
    exact h
  refine le_trans heq ?_
  rw [hC5]
  have hs0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hz0 : (0 : ℝ) ≤ zetaG g := by linarith only [hzeta]
  have hC0 : (0 : ℝ) ≤ 3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d) := mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (by linarith only [hCd] : 0 ≤ Cd)) hz0) hs0)
  have hstep := mul_le_mul_of_nonneg_left haspectBase hC0
  have hleft : 3 * ((100 / 99 : ℝ) * (Cd * aspectRatio E * zetaG g) * Real.sqrt d) = (3 * ((100
    / 99 : ℝ) * Cd * zetaG g * Real.sqrt d)) * aspectRatio E := by ring
  have hright : 3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d) * base = (3 * ((100 / 99 : ℝ)
    * Cd * zetaG g * Real.sqrt d)) * base := by ring
  linarith only [hstep, hleft.le, hleft.ge, hright.le, hright.ge]

private theorem tilt_gap_power_cap {d : ℕ} [NeZero d] {Cd g base C5 CdvZ iexp : ℝ} {m : Mat d}
  {G D : ℕ} (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) (hm : m.PosDef) (hCd : 1 ≤ Cd) (hzeta : 1
  ≤ zetaG g) (hecc : witnessEccentricity m ≤ base) (hbase : 3 ≤ base) (hC5 : C5 = 3 * ((100 /
  99) * Cd * zetaG g * Real.sqrt d)) (hCdvZ : CdvZ = Cd * zetaG g) (hG : G + 1 = D) (hDcap : (3
  : ℝ) ^ D ≤ C5 * base) (hiexp : iexp = (1 - g)⁻¹) (hiexp0 : 0 < iexp) : (3 : ℝ) ^ tiltGap Cd g
  (1 / 8 / 2) m (G + 1) ≤ 3 * ((32 * CdvZ * C5) ^ iexp * base ^ (2 * iexp)) := by
  have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd]
  have hzeta0 : (0 : ℝ) ≤ zetaG g := by linarith only [hzeta]
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hbCpos : (0 : ℝ) < boundaryConst Cd g m := Transport.zero_lt_boundaryConst (by linarith
    only [hCd]) hg.2 hm
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hC5_3 : (3 : ℝ) ≤ C5 := by
    rw [hC5]
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := sqrt_nat_one_le hd
    have hA : (1 : ℝ) ≤ 100 / 99 * Cd := by nlinarith only [hCd]
    have hB : (1 : ℝ) ≤ 100 / 99 * Cd * zetaG g := by
      nlinarith only [hA, hzeta]
    have hC : (1 : ℝ) ≤ 100 / 99 * Cd * zetaG g * Real.sqrt d := by
      nlinarith only [hB, hsqrt1]
    linarith only [hC]
  have hCdvZ1 : (1 : ℝ) ≤ CdvZ := by
    rw [hCdvZ]
    nlinarith only [hCd, hzeta]
  have hbCle : boundaryConst Cd g m ≤ CdvZ * base := by
    rw [boundaryConst, hCdvZ]
    have hCz0 : (0 : ℝ) ≤ Cd * zetaG g := mul_nonneg hCd0 hzeta0
    calc
      Cd * witnessEccentricity m * zetaG g =
          (Cd * zetaG g) * witnessEccentricity m := by ring
      _ ≤ (Cd * zetaG g) * base := mul_le_mul_of_nonneg_left hecc hCz0
      _ = Cd * zetaG g * base := by ring
  have h3gG : (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) ≤ C5 * base := by
    have h1 : (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) ≤ (3 : ℝ) ^ ((G + 1 : ℕ) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h0 : (0 : ℝ) ≤ ((G + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith only [h0, hg.1, hg.2]
    have h2 : (3 : ℝ) ^ ((G + 1 : ℕ) : ℝ) = (3 : ℝ) ^ (G + 1 : ℕ) := Real.rpow_natCast 3 _
    rw [h2] at h1
    refine h1.trans ?_
    rw [hG]
    exact hDcap
  have hbb0 : (0 : ℝ) ≤ CdvZ * base := mul_nonneg (by linarith only [hCdvZ1]) hbase0.le
  have hargle : 2 * boundaryConst Cd g m * (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) / (1 / 8 / 2) ≤ 32
    * CdvZ * C5 * (base * base) := by
    have hmul := mul_le_mul hbCle h3gG (by positivity) hbb0
    have hEq : 2 * boundaryConst Cd g m * (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) / (1 / 8 / 2) = 32 *
      (boundaryConst Cd g m * (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ))) := by ring
    rw [hEq]
    have hEq2 : (CdvZ * base) * (C5 * base) = CdvZ * C5 * (base * base) := by ring
    rw [hEq2] at hmul
    nlinarith only [hmul, hbb0, hbase0, hCdvZ1, hC5_3]
  refine le_trans (three_zpow_tiltGap_le hg (by norm_num) hbCpos (G + 1)) ?_
  have harg0 : (0 : ℝ) ≤ 2 * boundaryConst Cd g m * (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) / (1 / 8 /
    2) := by
    have hp : (0 : ℝ) < (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hpow := Real.rpow_le_rpow harg0 hargle hiexp0.le
  have h32c : (0 : ℝ) ≤ 32 * CdvZ * C5 := by
    nlinarith only [hCdvZ1, hC5_3]
  have hbbnn : (0 : ℝ) ≤ base * base := mul_nonneg hbase0.le hbase0.le
  have hsplitp : (32 * CdvZ * C5 * (base * base)) ^ iexp = (32 * CdvZ * C5) ^ iexp * (base *
    base) ^ iexp := Real.mul_rpow h32c hbbnn
  have hbb2 : (base * base) ^ iexp = base ^ (2 * iexp) := by
    have h1 : base * base = base ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h1, ← Real.rpow_mul hbase0.le]
  have hmaxb : max 1 ((2 * boundaryConst Cd g m * (3 : ℝ) ^ (g * ((G + 1 : ℕ) : ℝ)) / (1 / 8 /
    2)) ^ (1 - g)⁻¹) ≤ (32 * CdvZ * C5) ^ iexp * base ^ (2 * iexp) := by
    rw [← hiexp]
    refine max_le ?_ ?_
    · have ha : (1 : ℝ) ≤ (32 * CdvZ * C5) ^ iexp := Real.one_le_rpow (by nlinarith only
      [hCdvZ1, hC5_3]) hiexp0.le
      have hb : (1 : ℝ) ≤ base ^ (2 * iexp) := Real.one_le_rpow (by linarith only [hbase])
          (by linarith only [hiexp0.le])
      nlinarith only [ha, hb]
    · rw [← hbb2, ← hsplitp]
      exact hpow
  linarith only [hmaxb]

private theorem isotropy_split_power_cap {d : ℕ} {K Cd g base cW cburn CdvZ C5 iexp C6 c6 : ℝ}
  {m : Mat d} {G : ℕ} {s l split : ℤ} (hsplit : split = isotropySplit K (1 / 8 / 2) Cd g m (G +
  1) s) (hentry : (3 : ℝ) ^ euclideanEntryThreshold K (1 / 8 / 2) s ≤ (3 : ℝ) ^ s * (3 * (16 *
  (9 * (4 * Real.rpow base cW ^ 2))))) (htilt : (3 : ℝ) ^ tiltGap Cd g (1 / 8 / 2) m (G + 1) ≤ 3
  * ((32 * CdvZ * C5) ^ iexp * base ^ (2 * iexp))) (hsCap : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ l * (3 *
  growthBar K)) (hlCap : (3 : ℝ) ^ l ≤ base ^ (((2 : ℝ) + cW) * cburn)) (hgrowth : growthBar K ≤
  2 * base ^ cW) (hK2 : (2 : ℝ) ≤ growthBar K) (hbase : 0 < base) (hC6 : C6 = 31104 * ((32 *
  CdvZ * C5) ^ iexp)) (hc6 : c6 = (2 + cW) * cburn + 3 * cW + 2 * iexp) : (3 : ℝ) ^ split ≤ C6 *
  base ^ c6 := by
  have hentry' : (3 : ℝ) ^ euclideanEntryThreshold K (1 / 8 / 2) s ≤ (3 : ℝ) ^ s * (3 * (16 * (9
    * (4 * (base ^ cW * base ^ cW))))) := by
    refine hentry.trans (le_of_eq ?_)
    rw [pow_two]
    rfl
  have hpowpos : ∀ y : ℝ, (0 : ℝ) < base ^ y := fun y =>
    Real.rpow_pos_of_pos hbase y
  have hsR : (3 : ℝ) ^ s ≤ base ^ (((2 : ℝ) + cW) * cburn) * (3 * (2 * base ^ cW)) := by
    refine hsCap.trans ?_
    have hz1 : (0 : ℝ) < (3 : ℝ) ^ l := zpow_pos (by norm_num) _
    refine mul_le_mul hlCap ?_ ?_ (hpowpos _).le
    · linarith only [hgrowth]
    · linarith only [hK2]
  have hzsplit : (3 : ℝ) ^ split = (3 : ℝ) ^ euclideanEntryThreshold K (1 / 8 / 2) s * (3 : ℝ) ^
    tiltGap Cd g (1 / 8 / 2) m (G + 1) := by
    rw [hsplit, isotropySplit, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hzsplit]
  have hz2 : (0 : ℝ) < (3 : ℝ) ^ tiltGap Cd g (1 / 8 / 2) m (G + 1) := zpow_pos (by norm_num) _
  have hstepA : (3 : ℝ) ^ euclideanEntryThreshold K (1 / 8 / 2) s ≤ (base ^ (((2 : ℝ) + cW) *
    cburn) * (3 * (2 * base ^ cW))) * (3 * (16 * (9 * (4 * (base ^ cW * base ^ cW))))) := by
    refine hentry'.trans ?_
    refine mul_le_mul_of_nonneg_right hsR ?_
    positivity
  have hstepB := mul_le_mul hstepA htilt hz2.le (by positivity)
  refine hstepB.trans (le_of_eq ?_)
  have hmerge : base ^ (((2 : ℝ) + cW) * cburn) * (base ^ cW * (base ^ cW * (base ^ cW * base ^
    (2 * iexp)))) = base ^ c6 := by
    rw [← Real.rpow_add hbase, ← Real.rpow_add hbase,
      ← Real.rpow_add hbase, ← Real.rpow_add hbase]
    congr 1
    rw [hc6]
    ring
  rw [hC6, ← hmerge]
  ring

private theorem corrected_endpoint_prefactor_cap {d : ℕ} {P : Measure (CoeffSpace d)} {lAl : ℤ}
  {E : BlockMat d} {N₀ ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ} {base Cns C7 cns ct2 C cC
  Cpref : ℝ} (hbase : (3 : ℝ) ≤ base) (hfloor0 : 0 ≤ hatExcess P (roundedGrid lAl
  (canonicalMetric E)) N₀ 0) (hfloor : hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0 ≤
  1 / 9) (hrate0 : 0 ≤ linRate A alpha b0 bA b2 cA S0) (hrate4 : linRate A alpha b0 bA b2 cA S0
  ≤ 1 / 4) (hCns : 1 ≤ Cns) (hC7 : 1 ≤ C7) (hcns : 0 ≤ cns) (hct2 : 0 ≤ ct2) (hstart : (3 : ℝ) ^
  ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤ Cns ^ (2 : ℕ) * C7 * Real.rpow base (2
  * cns + ct2)) (hC : C = 36 * Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹) (hCcap : C ≤ Real.rpow base cC)
  (hCpref : Cpref = cC + (cns / 2 + ct2 / 4)) : 9 / 2 * ((1 + hatExcess P (roundedGrid lAl
  (canonicalMetric E)) N₀ 0) * (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 * ((linR ns cA A alpha
  b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) * (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) +
  1) ≤ Real.rpow base Cpref := by
  refine corrected_cadence_prefactor_of_uniform_cap
    (C := C) (c := cns / 2 + ct2 / 4) (cC := cC) hbase ?_ hCcap hCpref
  rw [hC]
  exact corrected_cadence_raw_prefactor_cap hbase hfloor0 hfloor hrate0
    hrate4 hCns hC7 hcns hct2 hstart

private theorem source_coefficient_mono_sq {w X Y : ℝ} (hw : 0 ≤ w) (hX : 0 ≤ X) (hXY : X ≤ Y) :
  1 + 6 * w * X ^ 2 ≤ 1 + 6 * w * Y ^ 2 := by
  have hsq := pow_le_pow_left₀ hX hXY 2
  nlinarith only [hsq, hw]

private theorem one_le_one_add_six_mul_sq {w X : ℝ} (hw : 0 ≤ w) : 1 ≤ 1 + 6 * w * X ^ 2 := by
  have hterm : 0 ≤ 6 * w * X ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hw) (sq_nonneg X)
  linarith only [hterm]

private theorem one_le_correctedLedgerCoefficient_of_defs {delta CX beta Ct1 Ct2 C7 : ℝ} (hdelta
  : 0 < delta) (hdelta1 : delta ≤ 1) (hCX : 1 ≤ CX) (hbeta : 0 < beta) (hCt1 : Ct1 = 3 / delta ^
  2) (hCt2 : Ct2 = (CX / delta ^ 2) ^ beta⁻¹) (hC7 : C7 = Ct1 * 3 * Ct2) : 1 ≤ C7 := by
  rw [hC7, hCt1, hCt2]
  exact one_le_corrected_ledger_coefficient hdelta hdelta1 hCX hbeta

private theorem one_le_sqrt_nat_of_two_le {d : ℕ} (hd : 2 ≤ d) : (1 : ℝ) ≤ Real.sqrt d := by
  rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ d))

private theorem one_le_cadenceStartCoefficient_of_def {C5 Cd z s : ℝ} (hC5 : C5 = 3 * ((100 /
  99) * Cd * z * s)) (hCd : 1 ≤ Cd) (hz : 1 ≤ z) (hs : 1 ≤ s) : 1 ≤ C5 := by
  rw [hC5]
  have h100 : (1 : ℝ) ≤ 100 / 99 := by norm_num
  have hprod := one_le_mul_of_one_le
    (one_le_mul_of_one_le (one_le_mul_of_one_le h100 hCd) hz) hs
  exact one_le_mul_of_one_le (by norm_num) hprod

private theorem one_le_CF_of_def {CF x : ℝ} (hCF : CF = max 1 x) : 1 ≤ CF := by
  rw [hCF]
  exact le_max_left _ _

private theorem one_le_Cns_of_defs {H : ℕ} {C5 CF rate CE Cns : ℝ} (hC5 : 1 ≤ C5) (hCF : 1 ≤ CF)
  (hrate : 0 < rate) (hCE : CE = 8100 * (3 : ℝ) ^ (3 * H) * C5 ^ 4) (hCns : Cns = (3 : ℝ) ^ (H +
  1) * 624 * CE * (3 * CF ^ rate⁻¹) * 3) : 1 ≤ Cns := by
  rw [hCns, hCE]
  exact one_le_corrected_generation_coefficient hC5 hCF hrate

private theorem one_le_CX_of_def {d : ℕ} {Cpre X CX : ℝ} (hCpre : 1 ≤ Cpre) (hCX : CX = 1 + 6 *
  weakCoefficient d Cpre * X ^ 2 * 65536) : 1 ≤ CX := by
  rw [hCX]
  exact one_le_corrected_bad_source_coefficient hCpre

private theorem pair_at_nat_add {A B : ℤ → Prop} (split : ℤ) (N₀ : ℕ) (hN : (N₀ : ℤ) = split) (h
  : ∀ k : ℤ, split ≤ k → A k ∧ B k) : (∀ n : ℕ, A ((N₀ : ℤ) + (n : ℤ))) ∧ ∀ n : ℕ, B ((N₀ : ℤ) +
  (n : ℤ)) := by
  have hs := split_le_nat_add split N₀ hN
  exact ⟨fun n => (h _ (hs n)).1, fun n => (h _ (hs n)).2⟩

private theorem hatExcess_floor_nat_add {d : ℕ} {P : Measure (CoeffSpace d)} {q : Mat d} {l : ℤ}
  {N₀ : ℕ} {delta : ℝ} (hfloor : ∀ k : ℤ, l ≤ k → hatExcessAt P q k ≤ delta) (hlN : l ≤ (N₀ :
  ℤ)) : ∀ m : ℕ, hatExcess P q N₀ m ≤ delta := by
  intro m
  have hscale : l ≤ (N₀ : ℤ) + (m : ℤ) := hlN.trans (Int.le_add_of_nonneg_right
    (Int.natCast_nonneg m))
  simpa only [hatExcess, hatExcessAt] using hfloor ((N₀ : ℤ) + (m : ℤ)) hscale

private theorem capsDeepConstant_le_one_of_kill {d : ℕ} [NeZero d] (Cd g : ℝ)
  (q : Mat d) (G H D n : ℕ) (split : ℤ) (N₀ : ℕ) (hCd : 1 ≤ Cd) (hg1 : g < 1) (hq : q.PosDef)
  (hGD : G + 1 = D) (hN₀ : (N₀ : ℤ) = split) (hbC : boundaryConst Cd g q ≤ (3 : ℝ) ^ (G + 1 :
  ℕ)) (hnH : H ≤ n) (hkill : (10 * (3 : ℝ) ^ (2 * D + H) : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n :
  ℝ) + 1 - (H : ℝ)))) : capsDeepConstant Cd g q (G + 1) split ((N₀ : ℤ) + ((n - H : ℕ) : ℤ))
  ((N₀ : ℤ) + (n : ℤ)) ≤ 1 := by
  rw [capsDeepConstant]
  have hbC0 : (0 : ℝ) < boundaryConst Cd g q := Transport.zero_lt_boundaryConst (by linarith
    only [hCd]) hg1 hq
  have hsubcast : ((n - H : ℕ) : ℤ) = (n : ℤ) - (H : ℤ) := by omega
  have hgd : (G : ℝ) + 1 = (D : ℝ) := by exact_mod_cast hGD
  have hsplR : ((split : ℤ) : ℝ) = (N₀ : ℝ) := by exact_mod_cast hN₀.symm
  have hexp1 : g * (((((N₀ : ℤ) + (n : ℤ)) + ((G + 1 : ℕ) : ℤ) : ℤ) : ℝ) - (((N₀ : ℤ) + ((n - H
    : ℕ) : ℤ) : ℤ) : ℝ)) = g * ((H : ℝ) + (D : ℝ)) := by
    have hcast : ((((N₀ : ℤ) + (n : ℤ)) + ((G + 1 : ℕ) : ℤ) : ℤ) : ℝ) - (((N₀ : ℤ) + ((n - H :
      ℕ) : ℤ) : ℤ) : ℝ) = (H : ℝ) + (D : ℝ) := by
      rw [hsubcast]
      push_cast
      linear_combination hgd
    rw [hcast]
  have hexp2 : (3 / 2 - g) * ((((split - 1 : ℤ) : ℤ) : ℝ) - (((N₀ : ℤ) + ((n - H : ℕ) : ℤ) : ℤ)
    : ℝ)) = -((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ))) := by
    have h1 : ((split - 1 : ℤ) : ℝ) - (((N₀ : ℤ) + ((n - H : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 1 -
      (H : ℝ)) := by
      rw [hsubcast]
      push_cast
      linear_combination hsplR
    rw [h1]
    ring
  rw [hexp1, hexp2]
  have hb1 : boundaryConst Cd g q ≤ (3 : ℝ) ^ (D : ℝ) := by
    have h := hbC
    rw [hGD] at h
    calc
      boundaryConst Cd g q ≤ (3 : ℝ) ^ (D : ℕ) := h
      _ = (3 : ℝ) ^ (D : ℝ) := (Real.rpow_natCast 3 D).symm
  have hb2 : (3 : ℝ) ^ (g * ((H : ℝ) + (D : ℝ))) ≤ (3 : ℝ) ^ ((H : ℝ) + (D : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hHD0 : (0 : ℝ) ≤ (H : ℝ) + (D : ℝ) := by positivity
    nlinarith only [hHD0, hg1]
  have hb3 : (3 : ℝ) ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) ≤ (3 : ℝ) ^ (-((1 / 2 : ℝ) *
    ((n : ℝ) + 1 - (H : ℝ)))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hnH0 : (0 : ℝ) ≤ (n : ℝ) + 1 - (H : ℝ) := by
      have h : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnH
      linarith only [h]
    nlinarith only [hnH0, hg1]
  have hgeom0 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(3 / 2 - g)) := by
    have hle : (3 : ℝ) ^ (-(3 / 2 - g)) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hg1])
    linarith only [hle, three_rpow_neg_half_le_three_fifths]
  have hpows : (3 : ℝ) ^ ((H : ℝ) + (D : ℝ)) * (3 : ℝ) ^ (D : ℝ) = (3 : ℝ) ^ (2 * D + H : ℕ) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast 3 (2 * D + H)]
    congr 1
    push_cast
    ring
  have hdecay0 : (0 : ℝ) < (3 : ℝ) ^ (-((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcombine : (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ))) * (3 : ℝ) ^ (-((1 / 2 : ℝ) *
    ((n : ℝ) + 1 - (H : ℝ)))) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hA0 : (0 : ℝ) ≤ (3 : ℝ) ^ (g * ((H : ℝ) + (D : ℝ))) := by positivity
  have hprod1 : 2 * (2 * boundaryConst Cd g q * (3 : ℝ) ^ (g * ((H : ℝ) + (D : ℝ)))) * ((3 : ℝ)
    ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) * (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))))) ≤ 2 *
    (2 * (3 : ℝ) ^ (D : ℝ) * (3 : ℝ) ^ ((H : ℝ) + (D : ℝ))) * ((3 : ℝ) ^ (-((1 / 2 : ℝ) * ((n :
    ℝ) + 1 - (H : ℝ)))) * (5 / 2)) := by
    have hm1 : 2 * boundaryConst Cd g q * (3 : ℝ) ^ (g * ((H : ℝ) + (D : ℝ))) ≤ 2 * (3 : ℝ) ^ (D
      : ℝ) * (3 : ℝ) ^ ((H : ℝ) + (D : ℝ)) := by
      refine mul_le_mul (by linarith only [hb1]) hb2 hA0 ?_
      positivity
    have hm2 : (3 : ℝ) ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) * (1 / (1 - (3 : ℝ) ^ (-(3 /
      2 - g)))) ≤ (3 : ℝ) ^ (-((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) * (5 / 2) := by
      rw [one_div]
      refine mul_le_mul hb3 (geom_inverse_le_five_halves hg1) ?_ hdecay0.le
      positivity
    have hL0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) * (1 / (1 - (3 :
      ℝ) ^ (-(3 / 2 - g)))) := by
      rw [one_div]
      positivity
    calc
      2 * (2 * boundaryConst Cd g q *
          (3 : ℝ) ^ (g * ((H : ℝ) + (D : ℝ)))) *
          ((3 : ℝ) ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) *
            (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))))) ≤
          2 * (2 * (3 : ℝ) ^ (D : ℝ) * (3 : ℝ) ^ ((H : ℝ) + (D : ℝ))) *
          ((3 : ℝ) ^ (-((3 / 2 - g) * ((n : ℝ) + 1 - (H : ℝ)))) *
            (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))))) := by
        refine mul_le_mul_of_nonneg_right ?_ hL0
        linarith only [hm1]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left hm2 ?_
        positivity
  refine le_trans hprod1 ?_
  have hfinal : 2 * (2 * (3 : ℝ) ^ (D : ℝ) * (3 : ℝ) ^ ((H : ℝ) + (D : ℝ))) * ((3 : ℝ) ^ (-((1 /
    2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) * (5 / 2)) = 10 * (3 : ℝ) ^ (2 * D + H : ℕ) * (3 : ℝ) ^
    (-((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) := by
    rw [← hpows]
    ring
  rw [hfinal]
  calc
    10 * (3 : ℝ) ^ (2 * D + H : ℕ) *
        (3 : ℝ) ^ (-((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) ≤
        (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ))) *
          (3 : ℝ) ^ (-((1 / 2 : ℝ) * ((n : ℝ) + 1 - (H : ℝ)))) := mul_le_mul_of_nonneg_right
            hkill hdecay0.le
    _ = 1 := hcombine

private theorem exists_endpoint_smallness (d : ℕ) (hd : 2 ≤ d) {A : ℝ} (hA : 1 ≤ A) : ∃ cSc
  delta0 : ℝ, 0 < cSc ∧ cSc ≤ 1 / 48 ∧ delta0 = (d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) *
  cSc) ∧ delta0 ≤ 1 / 9 ∧ (128 * A ^ 2) ^ 3 * delta0 ≤ 1 / 3 ∧ 0 < delta0 := by
  let CD : ℝ := (d : ℝ) * (3 + 8 * (d : ℝ) ^ 2)
  have hCD0 : 0 < CD := by
    dsimp only [CD]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith only [hd1]
  have hbtp_cap : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (d : ℝ) * bootstrapTiltPolynomial x ((d : ℝ) * x) ≤
    CD * x := by
    intro x hx0 hx1
    rw [bootstrapTiltPolynomial]
    dsimp only [CD]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have h1 : (1 + x) ^ 2 ≤ 1 + 3 * x := by nlinarith only [hx0, hx1]
    have h2 : 1 + (5 / 4 : ℝ) * ((d : ℝ) * x) + (1 / 4 : ℝ) * ((d : ℝ) * x) ^ 2 ≤ 1 + 2 * (d :
      ℝ) ^ 2 * x := by
      have hxx : x ^ 2 ≤ x := by nlinarith only [hx0, hx1]
      have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hd1]
      have ha : (5 / 4 : ℝ) * ((d : ℝ) * x) ≤ (5 / 4 : ℝ) * ((d : ℝ) ^ 2 * x) := by
        have h := mul_le_mul_of_nonneg_right hdd hx0
        nlinarith only [h]
      have hb : (1 / 4 : ℝ) * ((d : ℝ) * x) ^ 2 ≤ (1 / 4 : ℝ) * ((d : ℝ) ^ 2 * x) := by
        have h1' : ((d : ℝ) * x) ^ 2 = (d : ℝ) ^ 2 * x ^ 2 := by ring
        have h2' : (d : ℝ) ^ 2 * x ^ 2 ≤ (d : ℝ) ^ 2 * x := mul_le_mul_of_nonneg_left hxx
          (sq_nonneg _)
        nlinarith only [h1'.le, h1'.ge, h2']
      nlinarith only [ha, hb, mul_nonneg (sq_nonneg (d : ℝ)) hx0]
    have h2p : (0 : ℝ) ≤ 1 + (5 / 4 : ℝ) * ((d : ℝ) * x) + (1 / 4 : ℝ) * ((d : ℝ) * x) ^ 2 := by
      have hs := sq_nonneg ((d : ℝ) * x)
      nlinarith only [hx0, hd1, hs]
    have hprod : (1 + x) ^ 2 * (1 + (5 / 4 : ℝ) * ((d : ℝ) * x) + (1 / 4 : ℝ) * ((d : ℝ) * x) ^
      2) ≤ (1 + 3 * x) * (1 + 2 * (d : ℝ) ^ 2 * x) := by
      have hmid : (0 : ℝ) ≤ 1 + 3 * x := by linarith only [hx0]
      exact (mul_le_mul_of_nonneg_right h1 h2p).trans
        (mul_le_mul_of_nonneg_left h2 hmid)
    have hexp : (1 + 3 * x) * (1 + 2 * (d : ℝ) ^ 2 * x) - 1 ≤ (3 + 8 * (d : ℝ) ^ 2) * x := by
      have hxx : x ^ 2 ≤ x := by nlinarith only [hx0, hx1]
      have hmul : (d : ℝ) ^ 2 * x ^ 2 ≤ (d : ℝ) ^ 2 * x := mul_le_mul_of_nonneg_left hxx
        (sq_nonneg _)
      nlinarith only [hmul, hx0]
    have hcore : (1 + x) ^ 2 * (1 + (5 / 4 : ℝ) * ((d : ℝ) * x) + (1 / 4 : ℝ) * ((d : ℝ) * x) ^
      2) - 1 ≤ (3 + 8 * (d : ℝ) ^ 2) * x := by
      linarith only [hprod, hexp]
    have hfinal := mul_le_mul_of_nonneg_left hcore
      (by linarith only [hd1] : (0 : ℝ) ≤ (d : ℝ))
    calc
      (d : ℝ) * ((1 + x) ^ 2 *
          (1 + (5 / 4 : ℝ) * ((d : ℝ) * x) +
            (1 / 4 : ℝ) * ((d : ℝ) * x) ^ 2) - 1) ≤
          (d : ℝ) * ((3 + 8 * (d : ℝ) ^ 2) * x) := hfinal
      _ = (d : ℝ) * (3 + 8 * (d : ℝ) ^ 2) * x := by ring
  let cSc : ℝ := min (1 / 48)
    (min (1 / (9 * CD)) (1 / (3 * (128 * A ^ 2) ^ 3 * CD)))
  have hcSc0 : 0 < cSc := by
    dsimp only [cSc]
    have h1 : (0 : ℝ) < 1 / (9 * CD) := by positivity
    have h2 : (0 : ℝ) < 1 / (3 * (128 * A ^ 2) ^ 3 * CD) := by
      have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
      positivity
    exact lt_min (by norm_num) (lt_min h1 h2)
  have hcSc48 : cSc ≤ 1 / 48 := by dsimp only [cSc]; exact min_le_left _ _
  let delta0 : ℝ := (d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) * cSc)
  have hdelta0cap : delta0 ≤ CD * cSc := by
    dsimp only [delta0]
    exact hbtp_cap cSc hcSc0.le (by linarith only [hcSc48])
  have hdelta0_ninth : delta0 ≤ 1 / 9 := by
    have h1 : cSc ≤ 1 / (9 * CD) := by
      dsimp only [cSc]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have h2 : CD * cSc ≤ CD * (1 / (9 * CD)) := mul_le_mul_of_nonneg_left h1 hCD0.le
    have h3 : CD * (1 / (9 * CD)) = 1 / 9 := by field_simp
    linarith only [hdelta0cap, h2, h3.le, h3.ge]
  have hdelta0_gs3 : (128 * A ^ 2) ^ 3 * delta0 ≤ 1 / 3 := by
    have h1 : cSc ≤ 1 / (3 * (128 * A ^ 2) ^ 3 * CD) := by
      dsimp only [cSc]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
    have hpow0 : (0 : ℝ) < (128 * A ^ 2) ^ 3 := by positivity
    have h2 : CD * cSc ≤ CD * (1 / (3 * (128 * A ^ 2) ^ 3 * CD)) := mul_le_mul_of_nonneg_left h1
      hCD0.le
    have h3 : CD * (1 / (3 * (128 * A ^ 2) ^ 3 * CD)) = 1 / (3 * (128 * A ^ 2) ^ 3) := by field_simp
    have h4 : delta0 ≤ 1 / (3 * (128 * A ^ 2) ^ 3) := by
      linarith only [hdelta0cap, h2, h3.le]
    calc
      (128 * A ^ 2) ^ 3 * delta0 ≤
          (128 * A ^ 2) ^ 3 * (1 / (3 * (128 * A ^ 2) ^ 3)) := mul_le_mul_of_nonneg_left h4 hpow0.le
      _ = 1 / 3 := by field_simp
  have hdelta0pos : 0 < delta0 := by
    dsimp only [delta0]
    rw [bootstrapTiltPolynomial]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have hfst : 1 + 2 * cSc ≤ (1 + cSc) ^ 2 := by
      nlinarith only [sq_nonneg cSc]
    have hsec : (1 : ℝ) ≤ 1 + (5 / 4 : ℝ) * ((d : ℝ) * cSc) + (1 / 4 : ℝ) * ((d : ℝ) * cSc) ^ 2
      := by
      have h1 : (0 : ℝ) ≤ (d : ℝ) * cSc := mul_nonneg (by linarith only [hd1]) hcSc0.le
      nlinarith only [h1, sq_nonneg ((d : ℝ) * cSc)]
    have hprod : (1 + 2 * cSc) * 1 ≤ (1 + cSc) ^ 2 * (1 + (5 / 4 : ℝ) * ((d : ℝ) * cSc) + (1 / 4
      : ℝ) * ((d : ℝ) * cSc) ^ 2) := mul_le_mul hfst hsec (by norm_num) (sq_nonneg _)
    nlinarith only [hprod, hcSc0, hd1]
  exact ⟨cSc, delta0, hcSc0, hcSc48, rfl, hdelta0_ninth,
    hdelta0_gs3, hdelta0pos⟩

private theorem zpow_offset_mono {x : ℝ} {split s : ℤ} {G N₀ ns : ℕ}
    (hx : x ≤ (3 : ℝ) ^ (split + ((G + 1 : ℕ) : ℤ) - s))
    (hgen : ∀ n : ℕ, ns ≤ n → split ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) :
    ∀ n : ℕ, ns ≤ n →
      x ≤ (3 : ℝ) ^ (((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
        ((G + 1 : ℕ) : ℤ) - s) := by
  intro n hn
  refine hx.trans (zpow_le_zpow_right₀ (by norm_num) ?_)
  simpa only [add_comm] using sub_le_sub_right
    (add_le_add_right (hgen n hn) ((G + 1 : ℕ) : ℤ)) s

private theorem lin_rate_bounds {A Abar alpha beta S Sbar : ℝ} {cA : ℕ}
    (hA : 1 ≤ A) (hAle : A ≤ Abar) (halpha : 0 < alpha)
    (hbeta : 0 < beta) (hS : 1 ≤ S) (hSle : S ≤ Sbar) :
    0 < linRate A alpha 1 1 (2 * beta) cA S ∧
      linRate Abar alpha 1 1 (2 * beta) cA Sbar ≤
        linRate A alpha 1 1 (2 * beta) cA S ∧
      linRate A alpha 1 1 (2 * beta) cA S ≤ 1 / 4 := by
  have hbeta2 : (0 : ℝ) < 2 * beta := mul_pos (by norm_num) hbeta
  have hpos : 0 < linRate A alpha 1 1 (2 * beta) cA S :=
    linRate_pos hA halpha (by norm_num) (by norm_num) hbeta2 hS
  have hanti : linRate Abar alpha 1 1 (2 * beta) cA Sbar ≤
      linRate A alpha 1 1 (2 * beta) cA S :=
    linRate_anti hA hAle halpha (by norm_num) (by norm_num) hbeta2 hS hSle
  have hcap : linRate A alpha 1 1 (2 * beta) cA S ≤ 1 / 4 := by
    rw [linRate]
    have hcs : 1 ≤ linCs A alpha 1 1 (2 * beta) cA S :=
      linCs_one_le hA halpha (by norm_num) (by norm_num) hbeta2 hS
    have hden : (4 : ℝ) ≤ 4 * linCs A alpha 1 1 (2 * beta) cA S := by
      calc
        (4 : ℝ) = 4 * 1 := by ring
        _ ≤ 4 * linCs A alpha 1 1 (2 * beta) cA S :=
          mul_le_mul_of_nonneg_left hcs (by norm_num)
    exact one_div_le_one_div_of_le (by norm_num) hden
  exact ⟨hpos, hanti, hcap⟩

private theorem two_add_mul_le_rpow_two_add {a k base c : ℝ}
    (hk : 1 ≤ k) (hab : a ≤ base) (hkcap : k ≤ base ^ c)
    (hbase : 3 ≤ base) (hc : 0 ≤ c) :
    2 + a * k ≤ base ^ ((2 : ℝ) + c) := by
  have hbase0 : (0 : ℝ) ≤ base := by linarith only [hbase]
  have hbpos : (0 : ℝ) < base := by linarith only [hbase]
  have h1 : a * k ≤ base * base ^ c := by
    refine mul_le_mul hab hkcap ?_ hbase0
    linarith only [hk]
  have h2 : base ^ ((1 : ℝ) + c) = base * base ^ c := by
    rw [Real.rpow_add hbpos, Real.rpow_one]
  have hx : (1 : ℝ) ≤ base ^ ((1 : ℝ) + c) :=
    Real.one_le_rpow (by linarith only [hbase]) (by linarith only [hc])
  have h4 : base ^ ((2 : ℝ) + c) = base * base ^ ((1 : ℝ) + c) := by
    rw [show (2 : ℝ) + c = 1 + (1 + c) by ring,
      Real.rpow_add hbpos, Real.rpow_one]
  have h5 : 3 * base ^ ((1 : ℝ) + c) ≤
      base * base ^ ((1 : ℝ) + c) :=
    mul_le_mul_of_nonneg_right hbase (by linarith only [hx])
  linarith only [h1, h2.le, h2.ge, h4.le, h4.ge, h5, hx]

private theorem endpoint_reference_ellipticity_bounds (d : ℕ)
    [NeZero d]
    {gB : ℝ}
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gB Ebase Ψbase Kbase Sbase)
    : (1 ≤ aspectRatio Ebase) ∧
    (1 < Kbase) ∧
    ((1 : ℝ) ≤ aspectRatio Ebase * Kbase) ∧
    ((3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase) ∧
    (IsSymmetricBlockMat Ebase) ∧
    (Book.Ch02.BlockPosDef Ebase) ∧
    ((toFullBlockMat Ebase).PosDef) ∧
    (IsSkewMat (canonicalShear Ebase)) := by
  classical
  have haspect1 : 1 ≤ aspectRatio Ebase :=
    Quenched.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hKbase1 : 1 < Kbase := hdag.one_lt_growthWitness
  have haK1 : (1 : ℝ) ≤ aspectRatio Ebase * Kbase := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ aspectRatio Ebase * Kbase := mul_le_mul haspect1 hKbase1.le zero_le_one
            (by linarith only [haspect1])
  have hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase := by
    linarith only [haK1]
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  have hEsym : IsSymmetricBlockMat Ebase := hdag.refBlock_isSymm
  have hEpd : Book.Ch02.BlockPosDef Ebase := hdag.refBlock_posDef
  have hEfullpd : (toFullBlockMat Ebase).PosDef := posDef_toFullBlockMat hEsym hEpd
  have hskew : IsSkewMat (canonicalShear Ebase) := isSkewMat_canonicalShear hEfullpd
  exact ⟨haspect1, hKbase1, haK1, hbase3, hEsym, hEpd, hEfullpd, hskew⟩

private theorem endpoint_recentered_integrability (d : ℕ)
    [NeZero d]
    {cIso gB : ℝ}
    (hcIso0 : (0 : ℝ) ≤ cIso)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gB Ebase Ψbase Kbase Sbase)
    (hstat : HCPoly.Frozen.IsStationaryLaw Pbase)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw Pbase)
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    : (HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew)) ∧
    (HCPoly.Frozen.IsUnitRangeLaw (recenteredLaw Pbase hskew)) ∧
    (IsSymmetricBlockMat (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) ∧
    (Book.Ch02.BlockPosDef (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) ∧
    ((0 : ℝ) ≤ blockSize (Response.skewBlockCongr (canonicalShear Ebase) Ebase) (isotropyReference
      cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ∧
    (∀ m : ℤ, HasFiniteAdaptedMean Pbase (1 : Mat d) m) ∧
    (∀ m : ℤ, Book.Ch02.BlockPosDef (annealedBlock Pbase (centeredCube d m))) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  have hstat' : HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew) :=
    isStationaryLaw_recenteredLaw hstat hskew
  have hunit' : HCPoly.Frozen.IsUnitRangeLaw (recenteredLaw Pbase hskew) :=
    isUnitRangeLaw_recenteredLaw hunit hskew
  have hE'sym : IsSymmetricBlockMat Erec := hdagR.refBlock_isSymm
  have hE'pd : Book.Ch02.BlockPosDef Erec := hdagR.refBlock_posDef
  have hbS : (0 : ℝ) ≤ blockSize Erec (isotropyReference cIso Erec) :=
    PortableHistory.blockSize_nonneg hE'sym
      (isSymmetricBlockMat_isotropyReference cIso hE'sym)
      (blockPosDef_isotropyReference hcIso0 hE'pd)
  have hfin1 : ∀ m : ℤ, HasFiniteAdaptedMean Pbase (1 : Mat d) m := fun m =>
      (finite_adaptedMean_of_coarseEllipticityDagger hdag
        Matrix.PosDef.one m).1
  have hpdAnn : ∀ m : ℤ, Book.Ch02.BlockPosDef (annealedBlock Pbase (centeredCube d m)) := fun
    m => blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  exact ⟨hstat', hunit', hE'sym, hE'pd, hbS, hfin1, hpdAnn⟩

private theorem endpoint_recentered_contrast_geometry (d : ℕ)
    [NeZero d] [Nonempty (Fin d)]
    {cSc : ℝ}
    {gB : ℝ}
     (hcSc48 : cSc ≤ 1 / 48)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase cStar : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gB Ebase Ψbase Kbase Sbase)
    (hann : annealedContrast Pbase 0 - 1 ≤ cStar)
    (hblock : blockContrast Ebase ≤ 1 + cSc)
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (hmetE' : canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase) =
      canonicalMetric Ebase)
    (hEsym : IsSymmetricBlockMat Ebase)
    (hEpd : Book.Ch02.BlockPosDef Ebase)
    (hEfullpd : (toFullBlockMat Ebase).PosDef)
    (hfin1 : ∀ m : ℤ, HasFiniteAdaptedMean Pbase (1 : Mat d) m)
    (hpdAnn : ∀ m : ℤ, Book.Ch02.BlockPosDef (annealedBlock Pbase (centeredCube d m)))
    : (annealedContrast (recenteredLaw Pbase hskew) 0 - 1 ≤ cStar) ∧
    ((schurSigmaStar Ebase).PosDef) ∧
    (toFullBlockMat Ebase = schurBlock (schurSigma Ebase) (schurSigmaStar Ebase)
      (schurSkew Ebase)) ∧
    (blockContrast (Response.skewBlockCongr (canonicalShear Ebase) Ebase) = blockContrast Ebase) ∧
    (blockContrast (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 1 + cSc) ∧
    (refContrast (Response.skewBlockCongr (canonicalShear Ebase) Ebase) - 1 ≤ cSc) ∧
    (BlockMatLoewnerLE (blockSharp Ebase) Ebase) ∧
    (1 ≤ kappaRef Ebase) ∧
    (kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 9 / 8) ∧
    ((canonicalMetric Ebase).PosDef) ∧
    ((canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) = canonicalMetric
      Ebase) ∧
    (witnessEccentricity (canonicalMetric Ebase) ≤ aspectRatio Ebase) ∧
    ((canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef) ∧
    (witnessEccentricity (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) ≤
      aspectRatio Ebase) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  have hannR : annealedContrast (recenteredLaw Pbase hskew) 0 - 1 ≤ cStar := by
    rw [annealedContrast_recenteredLaw 0 (hfin1 0) (hpdAnn 0) hskew]
    exact hann
  have hsigE : (schurSigmaStar Ebase).PosDef := (posDef_lowerRight hEsym hEpd).inv
  have hformE : toFullBlockMat Ebase = schurBlock (schurSigma Ebase) (schurSigmaStar Ebase)
    (schurSkew Ebase) := Initialization.toFullBlockMat_eq_schurBlock hEsym hEpd
  have hbcE' : blockContrast Erec = blockContrast Ebase := blockContrast_skewBlockCongr hsigE
    hformE hskew
  have hblock' : blockContrast Erec ≤ 1 + cSc := by
    rw [hbcE']
    exact hblock
  have hrefE' : refContrast Erec - 1 ≤ cSc := by
    change blockContrast _ - 1 ≤ cSc
    linarith only [hblock']
  have hrefE'48 := hrefE'.trans hcSc48
  have hsharpBase : BlockMatLoewnerLE (blockSharp Ebase) Ebase :=
    Initialization.blockMatLoewnerLE_blockSharp_reference hdag
  have hkap1E : 1 ≤ kappaRef Ebase := Initialization.one_le_kappaRef hEsym hEpd hsharpBase
  have hkapE' : kappaRef Erec ≤ 9 / 8 := by
    have h := kappaRef_le_of_refContrast_le hdagR hrefE'
    linarith only [h, hcSc48]
  have hmAlpd : (canonicalMetric Ebase).PosDef := ShortHop.posDef_canonicalMetric hEfullpd
  have hmetE'2 : mrec = canonicalMetric Ebase := hmetE'
  have heccA : witnessEccentricity (canonicalMetric Ebase) ≤ aspectRatio Ebase :=
    witnessEccentricity_canonicalMetric_le_aspectRatio hdag
  have hmAlpd' : mrec.PosDef := by
    rw [hmetE'2]
    exact hmAlpd
  have heccA' : witnessEccentricity mrec ≤ aspectRatio Ebase := by
    rw [hmetE'2]
    exact heccA
  exact ⟨hannR, hsigE, hformE, hbcE', hblock', hrefE', hsharpBase, hkap1E, hkapE', hmAlpd, hmetE'2,
    heccA, hmAlpd', heccA'⟩

private theorem endpoint_burned_growth_bounds (d : ℕ)
    {cW : ℝ}
    {gB : ℝ}
    {Cdv : ℝ}
     (hcW0 : 0 ≤ cW)
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW : ℕ}
    (hK'cap : burnSplitThreshold d Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)) * Kbase * Kbase ^
      (nW + 1) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (hKbase1 : 1 < Kbase)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
    : ((2 : ℝ) ≤ growthBar Kbase) ∧
    ((1 : ℝ) ≤ burnSplitThreshold d Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase)))
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ))) ∧
    ((1 : ℝ) ≤ (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) ∧
    ((1 : ℝ) ≤ sourceMomentTwo (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) ∧
    ((1 : ℝ) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) cW) ∧
    (growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ 2 * Real.rpow (2 + aspectRatio Ebase * Kbase) cW) := by
  classical
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  have hgK2 : (2 : ℝ) ≤ growthBar Kbase := le_max_left _ _
  have hthr1 : (1 : ℝ) ≤ burnSplitThreshold d Kbase (burnSplitAnchor d 1 Kbase DD)
    (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) := by
    rw [burnSplitThreshold]
    refine le_trans ?_ (le_max_right _ _)
    have h1 : (1 : ℝ) ≤ growthBar Kbase ^ (4 * (d + 1)) := one_le_pow₀ (by linarith only [hgK2])
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ) -
      burnSplitAnchor d 1 Kbase DD + 1) := by
      refine one_le_zpow₀ (by norm_num) ?_
      omega
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ growthBar Kbase ^ (4 * (d + 1)) * (3 : ℝ) ^
          (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ) -
            burnSplitAnchor d 1 Kbase DD + 1) := mul_le_mul h1 h2 zero_le_one (by linarith
              only [h1])
  have hK'1 : (1 : ℝ) ≤ K' := by
    rw [hK'def]
    have hKp : (1 : ℝ) ≤ Kbase ^ (nW + 1) := one_le_pow₀ hKbase1.le
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hthr1 hKbase1.le zero_le_one
            (by linarith only [hthr1])) hKp zero_le_one
          (by nlinarith only [hthr1, hKbase1])
  have hm21 : (1 : ℝ) ≤ sourceMomentTwo K' := one_le_sourceMomentTwo K'
  have hrpowcW1 : (1 : ℝ) ≤ Real.rpow base cW := Real.one_le_rpow (by linarith only [hbase3]) hcW0
  have hgK'cap : growthBar K' ≤ 2 * Real.rpow base cW := by
    refine max_le (by linarith only [hrpowcW1]) ?_
    have h1 : K' ≤ Real.rpow base cW := hK'cap
    linarith only [h1, hrpowcW1]
  exact ⟨hgK2, hthr1, hK'1, hm21, hrpowcW1, hgK'cap⟩

private theorem endpoint_adapted_entry_scale_cost (d : ℕ)
    {lAl : ℤ}
    {CBF cSc cburn cW : ℝ}
    {gB : ℝ}
    {Cdv : ℝ}
     (hCBF0 : 0 < CBF)
    (hcSc0 : 0 < cSc)
    (hcburn0 : 0 ≤ cburn) (hcW0 : 0 ≤ cW)
    (hcburnP : ∀ (E : BlockMat d) (K : ℝ) (mAl : Mat d),
        1 ≤ aspectRatio E → 1 ≤ K →
        0 ≤ kappaRef E → kappaRef E ≤ 1 + 6 * cSc →
        witnessEccentricity mAl ≤ aspectRatio E →
        0 ≤ (1 + K ^ 2) ^ gB * euclideanReferenceRatio Cdv gB K E →
        ∀ sK gap : ℤ,
          (3 : ℝ) ^ sK ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * (3 * growthBar K) →
          (3 : ℝ) ^ gap ≤
            3 * max 1 ((9 / 8 * CBF) * bootstrapAdapterFactor Cdv gB K E mAl / cSc) →
          (3 : ℝ) ^ (sK + 1 + gap) ≤
            Real.rpow (2 + aspectRatio E * K) cburn)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW : ℕ} {sKfd gap : ℤ}
    (hgapcap : (3 : ℝ) ^ gap ≤ 3 * max 1
      (CBF * bootstrapAdapterFactor Cdv gB (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) / cSc))
    (hsKfdC : (3 : ℝ) ^ sKfd ≤ (3 : ℝ) ^ (kZero d : ℤ) * (3 * growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))))
    (hK'cap : burnSplitThreshold d Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)) * Kbase * Kbase ^
      (nW + 1) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (hkapBase6 : kappaRef Ebase ≤ 1 + 6 * cSc)
    (haspect1 : 1 ≤ aspectRatio Ebase)
    (hKbase1 : 1 < Kbase)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
    (hkap1E : 1 ≤ kappaRef Ebase)
    (hkapE' : kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 9 / 8)
    (hmetE'2 : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) =
      canonicalMetric Ebase)
    (heccA : witnessEccentricity (canonicalMetric Ebase) ≤ aspectRatio Ebase)
    (hK'1 : (1 : ℝ) ≤ (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hlAldef : lAl = sKfd + 1 + gap)
    : ((0 : ℝ) ≤ Cdv) ∧
    ((0 : ℝ) ≤ sourceMomentOne (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) ∧
    ((0 : ℝ) ≤ sourceMomentOne (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) * boundaryConst Cdv gB (1 : Mat d)) ∧
    ((0 : ℝ) ≤ (1 + (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ^ 2) ^ gB) ∧
    (∀ EE : BlockMat d, 0 ≤ kappaRef EE → 0 ≤ (1 + (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ^ 2) ^ gB *
      euclideanReferenceRatio Cdv gB (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) EE) ∧
    ((3 : ℝ) ^ gap ≤ 3 * max 1 (9 / 8 * CBF * bootstrapAdapterFactor Cdv gB (burnSplitThreshold d
      Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))
      Ebase (canonicalMetric Ebase) / cSc)) ∧
    ((3 : ℝ) ^ lAl ≤ Real.rpow (2 + aspectRatio Ebase * (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) cburn) ∧
    ((0 : ℝ) ≤ (2 + aspectRatio Ebase * Kbase)) ∧
    (aspectRatio Ebase ≤ (2 + aspectRatio Ebase * Kbase)) ∧
    ((0 : ℝ) < (2 + aspectRatio Ebase * Kbase)) ∧
    ((burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ (2 + aspectRatio Ebase * Kbase) ^ cW) ∧
    (2 + aspectRatio Ebase * (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ (2 + aspectRatio Ebase * Kbase) ^ ((2 : ℝ) + cW)) ∧
    ((3 : ℝ) ^ lAl ≤ (2 + aspectRatio Ebase * Kbase) ^ (((2 : ℝ) + cW) * cburn)) := by
  classical
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  have hCdv0 : (0 : ℝ) ≤ Cdv := by linarith only [hCdv1]
  have hm1nn : (0 : ℝ) ≤ sourceMomentOne K' := by
    have h := one_le_sourceMomentOne (K := K')
    linarith only [h]
  have hmb0 : (0 : ℝ) ≤ sourceMomentOne K' * boundaryConst Cdv gB (1 : Mat d) := by
    rw [boundaryConst]
    have hz : (0 : ℝ) ≤ zetaG gB := by linarith only [hzetagB]
    have he1 : (0 : ℝ) ≤ witnessEccentricity (1 : Mat d) := Real.sqrt_nonneg _
    positivity
  have hpowK'0 : (0 : ℝ) ≤ (1 + K' ^ 2) ^ gB := by positivity
  have hfacnnE : ∀ EE : BlockMat d, 0 ≤ kappaRef EE → 0 ≤ (1 + K' ^ 2) ^ gB *
    euclideanReferenceRatio Cdv gB K' EE := by
    intro EE hkEE
    rw [euclideanReferenceRatio]
    positivity
  have hgapcap' : (3 : ℝ) ^ gap ≤ 3 * max 1 (9 / 8 * CBF * bootstrapAdapterFactor Cdv gB K'
    Ebase (canonicalMetric Ebase) / cSc) := by
    rw [hmetE'2] at hgapcap
    refine le_trans hgapcap ?_
    have hbAF : bootstrapAdapterFactor Cdv gB K' Erec (canonicalMetric Ebase) ≤ 9 / 8 *
      bootstrapAdapterFactor Cdv gB K' Ebase (canonicalMetric Ebase) := by
      rw [bootstrapAdapterFactor, bootstrapAdapterFactor,
        euclideanReferenceRatio, euclideanReferenceRatio]
      have hecc0 : (0 : ℝ) ≤ witnessEccentricity (canonicalMetric Ebase) := Real.sqrt_nonneg _
      have h1 : kappaRef Erec ≤ 9 / 8 * kappaRef Ebase := by
        nlinarith only [hkapE', hkap1E]
      have hstep1 : kappaRef Erec * (sourceMomentOne K' * boundaryConst Cdv gB (1 : Mat d)) ≤
        9 / 8 * kappaRef Ebase * (sourceMomentOne K' * boundaryConst Cdv gB (1 : Mat d)) :=
        mul_le_mul_of_nonneg_right h1 hmb0
      have hstep2 := mul_le_mul_of_nonneg_left hstep1 hpowK'0
      have hstep3 := mul_le_mul_of_nonneg_left hstep2 hecc0
      have hEq : witnessEccentricity (canonicalMetric Ebase) * ((1 + K' ^ 2) ^ gB * (9 / 8 *
        kappaRef Ebase * (sourceMomentOne K' * boundaryConst Cdv gB (1 : Mat d)))) = 9 / 8 *
        (witnessEccentricity (canonicalMetric Ebase) * ((1 + K' ^ 2) ^ gB * (kappaRef Ebase *
        (sourceMomentOne K' * boundaryConst Cdv gB (1 : Mat d))))) := by
        ring
      linarith only [hstep3, hEq.le, hEq.ge]
    have hmono : CBF * bootstrapAdapterFactor Cdv gB K' Erec (canonicalMetric Ebase) / cSc ≤ 9
      / 8 * CBF * bootstrapAdapterFactor Cdv gB K' Ebase (canonicalMetric Ebase) / cSc := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_
        (inv_nonneg.mpr hcSc0.le)
      nlinarith only [hbAF, hCBF0]
    have hmax := max_le_max (le_refl (1 : ℝ)) hmono
    linarith only [hmax]
  have hlAlcap0 : (3 : ℝ) ^ lAl ≤ Real.rpow (2 + aspectRatio Ebase * K') cburn := by
    rw [hlAldef]
    exact hcburnP Ebase K' (canonicalMetric Ebase) haspect1 hK'1
      (by linarith only [hkap1E]) hkapBase6 heccA
      (hfacnnE Ebase (by linarith only [hkap1E])) sKfd gap hsKfdC hgapcap'
  have hbase0 : (0 : ℝ) ≤ base := by linarith only [hbase3]
  have haspb : aspectRatio Ebase ≤ base := by
    rw [hbasedef]
    have h1 : aspectRatio Ebase * 1 ≤ aspectRatio Ebase * Kbase := mul_le_mul_of_nonneg_left
      hKbase1.le
        (by linarith only [haspect1])
    linarith only [h1]
  have hbpos : (0 : ℝ) < base := by linarith only [hbase3]
  have hK'capP : K' ≤ base ^ cW := hK'cap
  have hbaseK' : 2 + aspectRatio Ebase * K' ≤ base ^ ((2 : ℝ) + cW) :=
    two_add_mul_le_rpow_two_add hK'1 haspb hK'capP hbase3 hcW0
  have hlAlcap : (3 : ℝ) ^ lAl ≤ base ^ (((2 : ℝ) + cW) * cburn) := by
    refine le_trans hlAlcap0 ?_
    have haK'0 : (0 : ℝ) ≤ 2 + aspectRatio Ebase * K' := by
      have := mul_nonneg (by linarith only [haspect1] :
        (0:ℝ) ≤ aspectRatio Ebase) (by linarith only [hK'1] : (0:ℝ) ≤ K')
      linarith only [this]
    have h : (2 + aspectRatio Ebase * K') ^ cburn ≤ (base ^ ((2 : ℝ) + cW)) ^ cburn :=
      Real.rpow_le_rpow haK'0 hbaseK' hcburn0
    rwa [← Real.rpow_mul hbase0] at h
  exact ⟨hCdv0, hm1nn, hmb0, hpowK'0, hfacnnE, hgapcap', hlAlcap0, hbase0, haspb, hbpos, hK'capP,
    hbaseK', hlAlcap⟩

private theorem endpoint_actual_recursion_constant_bounds (d : ℕ)
    {Cpre eta delta0 : ℝ} {H : ℕ}
    {cIso M₀ R conv gB Abar : ℝ}
     {cAbar : ℕ}
    (hCpre1 : 1 ≤ Cpre)
    (hdelta0_gs3 : (128 * Abar ^ 2) ^ 3 * delta0 ≤ 1 / 3)
    (hdelta0pos : 0 < delta0)
    (hcIso0 : (0 : ℝ) ≤ cIso)
    (hAbar1 : (1 : ℝ) ≤ Abar)
    (hgB1 : gB < 1)
    (hAbardef : Abar = fusionRecursionConstantIsotropySharp d Cpre eta H
    (absorbedNormalizer 16 16 (designNormalizer R M₀))
    (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
    (rowSplitConstant cIso 1) (isotropyKap2 cIso) 4 1
    (slotCVsum d) (cVmConstant d conv))
    (hcAbardef : cAbar = ⌈Real.logb 3 (24 * Abar) / recursionAlpha gB⌉₊)
    {Ebase : BlockMat d}
    (hE'sym : IsSymmetricBlockMat (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hE'pd : Book.Ch02.BlockPosDef (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    : ((0 : ℝ) ≤ (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ∧
    ((fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) ≤ Abar) ∧
    ((1 : ℝ) ≤ (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv))) ∧
    ((128 * (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) ^ 2) ^ 3 * delta0 ≤ 1 / 3) ∧
    (24 * (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) ≤ (3 : ℝ) ^ (recursionAlpha gB * (cAbar : ℝ))) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  have hMsc0 : (0 : ℝ) ≤ Msc := by
    dsimp only [Msc]
    exact supplyMscSplit_nonneg d _
  have hAle : Aact ≤ Abar := by
    dsimp only [Aact]
    rw [hAbardef]
    exact fusionRecursionConstantIsotropySharp_mono_cD d H
      (by linarith only [hCpre1]) hgB1 (by norm_num)
      (dropConstantIsotropy_isotropyReference_le hE'sym hE'pd hcIso0)
  have hA1' : (1 : ℝ) ≤ Aact := by
    dsimp only [Aact]
    exact one_le_fusionRecursionConstantIsotropySharp d _ _ _ _ _ _ _ _ _ _ _ _
  have hgs3' : (128 * Aact ^ 2) ^ 3 * delta0 ≤ 1 / 3 := cubic_smallness_mono hA1' hAle
    hdelta0pos hdelta0_gs3
  have hcA24' : 24 * Aact ≤ (3 : ℝ) ^ (recursionAlpha gB * (cAbar : ℝ)) :=
    twenty_four_mul_le_three_rpow_rate_ceil hAle hAbar1
      (recursionAlpha_pos hgB1) hcAbardef
  exact ⟨hMsc0, hAle, hA1', hgs3', hcA24'⟩

private theorem endpoint_actual_source_and_rate_bounds (d : ℕ)
    [Nonempty (Fin d)]
    {Cpre eta CsubF delta0 : ℝ} {H : ℕ}
    {cIso L M₀ R Mabs conv gB Abar beta2 MscBar CvBar Ssrc0bar : ℝ}
    {rateBar Cdv : ℝ}
     {cAbar : ℕ}
    (hCpre1 : 1 ≤ Cpre)
    (hCsubF0 : 0 < CsubF)
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hdelta0pos : 0 < delta0)
    (hR1 : (1 : ℝ) ≤ R)
    (hrho1 : contrastRho gB < 1)
    (halphaB : (0 : ℝ) < recursionAlpha gB)
    (hbeta20 : (0 : ℝ) < beta2)
    (hLdef : L = isotropyLoadScale cIso (isotropyKap2 cIso))
    (hMabsdef : Mabs = absorbedNormalizer 16 16 (designNormalizer R M₀))
    (hMscBardef : MscBar = (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * ((9 / 8 : ℝ) * 4) * (2 * (4 : ℝ)) *
      Real.sqrt 2)
    (hCvBardef : CvBar = vsumSourceConstant d CsubF MscBar 1)
    (hSsrc0bardef : Ssrc0bar = 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed Mabs L (contrastRho gB) CvBar (conv * CvBar)
      0 ^ 2)
    (hrateBardef : rateBar = linRate Abar (recursionAlpha gB) 1 1 (2 * beta2) cAbar Ssrc0bar)
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW ns : ℕ}
    (hsharpE' : BlockMatLoewnerLE (blockSharp (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hM₀' : metricFactorValue (Response.skewBlockCongr (canonicalShear Ebase) Ebase) (1 + cIso)
      (isotropyKap2 cIso) ≤ M₀)
    (hconv0 : (0 : ℝ) ≤ conv)
    (hE'sym : IsSymmetricBlockMat (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hE'pd : Book.Ch02.BlockPosDef (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hkapE' : kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 9 / 8)
    (hMsc0 : (0 : ℝ) ≤ (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
    (hAle : (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) ≤ Abar)
    (hA1' : (1 : ℝ) ≤ (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)))
    : (0 ≤ absorbedNormalizer 16 16 (designNormalizer R M₀)) ∧
    (1 ≤ kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) ∧
    ((supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) ≤ MscBar) ∧
    (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) delta0 ≤ CvBar) ∧
    (0 ≤ vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
      Ebase) Ebase)) delta0) ∧
    (0 ≤ weakSourceGroupSummed (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) (vsumSourceConstant d CsubF
      (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) delta0) (conv *
        vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0) ∧
    (weakSourceGroupSummed (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) (vsumSourceConstant d CsubF
      (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) delta0) (conv *
        vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ≤ weakSourceGroupSummed Mabs
      L (contrastRho gB) CvBar (conv * CvBar) 0) ∧
    (1 ≤ (1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)) ∧
    ((1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2) ≤ Ssrc0bar) ∧
    (1 ≤ (1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
        (badSourceLegConstantAtLevel
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
      (3 : ℝ) ^ (2 * beta2 * (ns : ℝ)))) ∧
    (1 ≤ (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv))) ∧
    ((fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) ≤ Abar) ∧
    (0 < (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2))) ∧
    (rateBar ≤ (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2))) ∧
    ((linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)) ≤ 1 / 4) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  let S0act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF Msc delta0)
      (conv * vsumSourceConstant d CsubF Msc delta0) 0 ^ 2
  let S2act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))
  let rateAct : ℝ := linRate Aact (recursionAlpha gB) 1 1 (2 * beta2) cAbar S0act
  have hMabs0 : 0 ≤ absorbedNormalizer 16 16 (designNormalizer R M₀) :=
    absorbedNormalizer_nonneg (by norm_num) (by norm_num)
      (designNormalizer_nonneg hR1
        (le_trans (metricFactorValue_nonneg _ _ _) hM₀'))
  have hkap1rec : 1 ≤ kappaRef Erec := by
    exact Initialization.one_le_kappaRef hE'sym hE'pd hsharpE'
  have hMscLe : Msc ≤ MscBar := by
    dsimp only [Msc]
    rw [hMscBardef]
    exact supplyMscSplit_le hkapE'
  have hCvLe : vsumSourceConstant d CsubF Msc delta0 ≤ CvBar := by
    rw [hCvBardef]
    exact (vsumSourceConstant_mono hCsubF0.le hMscLe).trans
      (vsumSourceConstant_mono_delta
        (hdelta0_ninth.trans (by norm_num : (1 / 9 : ℝ) ≤ 1)))
  have hCv0 : 0 ≤ vsumSourceConstant d CsubF Msc delta0 := vsumSourceConstant_nonneg
    hCsubF0.le hMsc0 hdelta0pos.le
  have hGroup0 : 0 ≤ weakSourceGroupSummed (absorbedNormalizer 16 16 (designNormalizer R M₀))
    (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) (vsumSourceConstant d CsubF
    Msc delta0) (conv * vsumSourceConstant d CsubF Msc delta0) 0 :=
    weakSourceGroupSummed_nonneg hMabs0 hrho1 hCv0
      (mul_nonneg hconv0 hCv0) (by norm_num)
  have hGroupLe : weakSourceGroupSummed (absorbedNormalizer 16 16 (designNormalizer R M₀))
    (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) (vsumSourceConstant d CsubF
    Msc delta0) (conv * vsumSourceConstant d CsubF Msc delta0) 0 ≤ weakSourceGroupSummed Mabs
    L (contrastRho gB) CvBar (conv * CvBar) 0 := by
    have hconvLe := mul_le_mul_of_nonneg_left hCvLe hconv0
    have hscaled := weakSourceGroupSummed_le_scaled
      (M := absorbedNormalizer 16 16 (designNormalizer R M₀))
      (L := isotropyLoadScale cIso (isotropyKap2 cIso))
      (rho := contrastRho gB)
      (vsum := vsumSourceConstant d CsubF Msc delta0)
      (vmsrc := conv * vsumSourceConstant d CsubF Msc delta0)
      (bsrc := 0) (Cv := CvBar) (Cm := conv * CvBar) (Cb := 0) (w := 1)
      hMabs0 hrho1 (by simpa only [mul_one] using hCvLe)
      (by simpa only [mul_one] using hconvLe) (by norm_num)
    simpa only [mul_one, hMabsdef, hLdef] using hscaled
  have hS0act1 : 1 ≤ S0act := by
    dsimp only [S0act]
    exact one_le_one_add_six_mul_sq
      (weakCoefficient_nonneg d (by linarith only [hCpre1]))
  have hS0actLe : S0act ≤ Ssrc0bar := by
    dsimp only [S0act]
    rw [hSsrc0bardef]
    have hwC0 := weakCoefficient_nonneg d
      (by linarith only [hCpre1] : 0 ≤ Cpre)
    exact source_coefficient_mono_sq hwC0 hGroup0 hGroupLe
  have hS2act1 : 1 ≤ S2act := by
    dsimp only [S2act]
    exact one_le_corrected_source_coefficient (d := d)
      (X := weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
        (badSourceLegConstantAtLevel
          (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R))
      (t := 2 * beta2 * (ns : ℝ)) hCpre1
  have hAact1 : 1 ≤ Aact := by
    simpa only [Aact] using hA1'
  have hAactLe : Aact ≤ Abar := by
    simpa only [Aact] using hAle
  have hrateBounds := lin_rate_bounds (cA := cAbar) hAact1 hAactLe
    halphaB hbeta20 hS0act1 hS0actLe
  have hrateAct0 : 0 < rateAct := by
    dsimp only [rateAct]
    exact hrateBounds.1
  have hrateCmp : rateBar ≤ rateAct := by
    rw [hrateBardef]
    dsimp only [rateAct]
    exact hrateBounds.2.1
  have hrate4 : rateAct ≤ 1 / 4 := by
    dsimp only [rateAct]
    exact hrateBounds.2.2
  exact ⟨hMabs0, hkap1rec, hMscLe, hCvLe, hCv0, hGroup0, hGroupLe, hS0act1, hS0actLe, hS2act1,
    hAact1, hAactLe, hrateAct0, hrateCmp, hrate4⟩

private theorem endpoint_burned_maximum_envelope (d : ℕ) (hd : 2 ≤ d)
    {lAl : ℤ} {Gacc : ℕ}
    [NeZero d]
    {cIso R gB : ℝ}
    {Cdv : ℝ}
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hcIso0 : (0 : ℝ) ≤ cIso)
    (hgBrho : gB ≤ contrastRho gB)
    (hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    {ns N₀ : ℕ} {sKfd gap : ℤ}
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (_hlAldef : lAl = sKfd + 1 + gap)
    (hkZlAl : (kZero d : ℤ) ≤ lAl)
    (hGaccdef : Gacc = burnSplitDepth d Cdv gB (aspectRatio Ebase) - 1)
    (hGaccD : Gacc + 1 = burnSplitDepth d Cdv gB (aspectRatio Ebase))
    (hw : IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)))
    (hqnorm : ‖roundedGrid lAl (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase))‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    (hqpd : ((roundedGrid lAl (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)))).PosDef)
    (hdepth : (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
      (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) - burnSplitAnchor d 1
      Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) = ((2 * (burnSplitDepth d Cdv gB
        (aspectRatio Ebase)) : ℕ) : ℤ))
    (haspect1 : 1 ≤ aspectRatio Ebase)
    (hstat' : HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew))
    (hmAlpd' : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef)
    (heccA' : witnessEccentricity (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) ≤ aspectRatio Ebase)
        (hRdef : R = 4 / (1 + cIso))
    : (∀ᵐ a ∂(recenteredLaw Pbase hskew), ∀ m : ℤ, burnSplitSource gB (Response.skewBlockCongr
      (canonicalShear Ebase) Ebase)
      ((burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (recenteredSource Sbase hskew) a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m → BlockMatLoewnerLE (coarseBlock (standardCell d
      k w) a) (blockScale ((3 : ℝ) ^ (gB * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) - (k : ℝ))
      0)) (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ∧
    (boundaryConst Cdv gB (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      ≤ (3 : ℝ) ^ (burnSplitDepth d Cdv gB (aspectRatio Ebase))) ∧
    (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂(recenteredLaw Pbase hskew),
      Response.diagonalWeakMaximum (contrastRho gB) ((roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) ((N₀ : ℤ) + (n : ℤ))
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) a ≤
        ENNReal.ofReal (R * ((max 1 (3 * burnSplitSource gB (Response.skewBlockCongr
        (canonicalShear Ebase) Ebase)
      ((burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (recenteredSource Sbase hskew) a * (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) + ((Gacc +
      1 : ℕ) : ℝ))))) ^ gB / 2))) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  have hdagN := coarseEllipticityDagger_normalizedGauge hdagR
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  have hbC := three_pow_reindex hGaccD
    (boundaryConst_le_three_pow_burnSplitDepth hd hCdv1 hgB haspect1 heccA')
  let qrec : Mat d := roundedGrid lAl mrec
  have hQenvP : ∀ᵐ a ∂(recenteredLaw Pbase hskew), ∀ m : ℤ, burnSplitSource gB Erec
    ((burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase DD)
    (recenteredSource Sbase hskew) a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
    standardCellCenter k w ∈ centeredCube d m → BlockMatLoewnerLE (coarseBlock (standardCell d
    k w) a) (blockScale ((3 : ℝ) ^ (gB * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) - (k : ℝ))
    0)) Erec) := by
    have hme := mesoEnvelope_of_successorScale hstat' hdagN (le_refl 1)
      hw hdepth
    filter_upwards [hme] with a ha
    intro m hm k hk w hw'
    have h2 := ha m (le_trans (le_max_right _ _) hm) k hk w hw'
    rw [hGaccD]
    exact h2
  have hbC' : boundaryConst Cdv gB mrec ≤ (3 : ℝ) ^ DD := by
    have h := hbC
    rw [hGaccD] at h
    exact h
  have henvMaxP : ∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂(recenteredLaw Pbase hskew),
    Response.diagonalWeakMaximum (contrastRho gB) (qrec) ((N₀ : ℤ) + (n : ℤ))
    (isotropyReference cIso Erec) a ≤ ENNReal.ofReal (R * ((max 1 (3 * burnSplitSource gB Erec
    ((burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase DD)
    (recenteredSource Sbase hskew) a * (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) + ((Gacc +
    1 : ℕ) : ℝ))))) ^ gB / 2)) := by
    intro n hn
    have hgeo : ∀ k : ℤ, k ≤ (N₀ : ℤ) + (n : ℤ) → ∀ w ∈ Response.alignedIndex (qrec) k ((N₀ :
      ℤ) + (n : ℤ)), adaptedCellAt (qrec) k w ⊆ centeredCube d ((N₀ : ℤ) + (n : ℤ) + (DD : ℤ))
      := by
      intro k hk w hw'
      refine (Response.adaptedCellAt_subset_of_mem_alignedIndex hqpd hk
        hw').trans ?_
      refine (Selection.adaptedCell_subset_centeredCube_add
        (by omega : 1 ≤ d) hqnorm).trans (Window.centeredCube_mono ?_)
      omega
    have h := henvMax_burnsplit_at_burnSplitSource hd hstat' hgB hdagN
      (le_refl 1) hw hdepth hkZlAl hCdvle hmAlpd' hbC' hgBrho
      ((N₀ : ℤ) + (n : ℤ)) hgeo hcIso0
    rw [hGaccD]
    simpa only [hRdef] using h
  exact ⟨hQenvP, hbC', henvMaxP⟩

private theorem endpoint_corrected_initial_ledger_bound (d : ℕ) (hd : 2 ≤ d)
    {Gacc : ℕ}
    {Cpre eta CsubF delta0 cW CBrev : ℝ} {H : ℕ}
    {cIso M₀ R conv gB beta2 : ℝ}
    {rateBar Cdv CdvZ C5 CE CF cF CnsC cns : ℝ}
    {Ct1 CX ct2 Ct2u C7 : ℝ} {cAbar : ℕ}
    (hCpre1 : 1 ≤ Cpre)
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hdelta0pos : 0 < delta0)
     (hcW0 : 0 ≤ cW) (hCBrev0 : 0 < CBrev)
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hR1 : (1 : ℝ) ≤ R)
    (hrho1 : contrastRho gB < 1)
    (hbeta20 : (0 : ℝ) < beta2)
    (hrateBar0 : 0 < rateBar)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    (hct20 : 0 ≤ ct2)
    (hCdvZdef : CdvZ = Cdv * zetaG gB)
    (hC5def : C5 = 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d))
    (hCEdef : CE = 8100 * 3 ^ (3 * H) * C5 ^ 4)
    (hCFdef : CF = max 1 (CBrev * (45 / 2) * CdvZ * C5))
    (hcFdef : cF = 4 + 3 * cW)
    (hCnsCdef : CnsC = (3 : ℝ) ^ (H + 1) * 624 * CE * (3 * CF ^ rateBar⁻¹) * 3)
    (hcnsdef : cns = 4 * cW + 4 + cF / rateBar)
    (hCt1def : Ct1 = 3 / delta0 ^ 2)
    (hCXdef : CX = 1 +
    (6 * weakCoefficient d Cpre *
    ((16 * absorbedNormalizer 16 16 (designNormalizer R M₀) / (1 - contrastRho gB)) *
    (Real.sqrt 2 * Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
    R * 6)) ^ 2) * 65536)
    (hct2def : ct2 = 16 * cW / (2 * beta2))
    (hCt2udef : Ct2u = (CX / delta0 ^ 2) ^ (2 * beta2)⁻¹)
    (hC7def : C7 = Ct1 * 3 * Ct2u)
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW nsBv nsEv nsFv ns : ℕ}
    (hGaccD : Gacc + 1 = (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
    (hnsSum : ns ≤ (H + 1) + nsBv + nsEv + nsFv)
    (hnsBvCap : (3 : ℝ) ^ nsBv ≤ 3 * (13 * growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ^ 4))
    (hnsEvCap : (3 : ℝ) ^ nsEv ≤
      8100 * (3 : ℝ) ^ (3 * H) * (3 : ℝ) ^ (4 * (burnSplitDepth d Cdv gB (aspectRatio Ebase))))
    (hnsFvCap : (3 : ℝ) ^ nsFv ≤ 3 * (max 1 (CBrev * reverseAdapterFactor Cdv gB
      (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (canonicalMetric ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))) Gacc)) ^ rateBar⁻¹)
    (haspect1 : 1 ≤ aspectRatio Ebase)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
    (hkapE' : kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 9 / 8)
    (heccA' : witnessEccentricity (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) ≤ aspectRatio Ebase)
    (hK'1 : (1 : ℝ) ≤ (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hgK'cap : growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ 2 * Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (haspb : aspectRatio Ebase ≤ (2 + aspectRatio Ebase * Kbase))
        (hAact1 : 1 ≤ (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)))
    (hMabs0 : 0 ≤ absorbedNormalizer 16 16 (designNormalizer R M₀))
    (hS2act1 : 1 ≤ (1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
        (badSourceLegConstantAtLevel
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
      (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))))
    (hkap1rec : 1 ≤ kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    : (1 ≤ C7) ∧
    ((3 : ℝ) ^ ((linR ns cAbar (fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2)
      (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2) 1 (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) delta0 0) : ℝ) ≤ CnsC ^ 2 * C7 * Real.rpow (2 + aspectRatio
      Ebase * Kbase) (2 * cns + ct2)) := by
  classical
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  let Eband : BlockMat d := Erec
  let adapter : ℝ := CBrev * reverseAdapterFactor Cdv gB K' Eband
    (canonicalMetric Eband) Gacc
  let rAFv : ℝ := max 1 adapter
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  let S0act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF Msc delta0)
      (conv * vsumSourceConstant d CsubF Msc delta0) 0 ^ 2
  let S2act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))
  let startAct : ℕ := linR ns cAbar Aact (recursionAlpha gB) 1 1 (2 * beta2)
      S0act 1 S2act delta0 0
  have hsqrtD1 := one_le_sqrt_nat_of_two_le hd
  have hC5one := one_le_cadenceStartCoefficient_of_def hC5def hCdv1 hzetagB hsqrtD1
  have hCFone := one_le_CF_of_def hCFdef
  have hCnsone := one_le_Cns_of_defs hC5one hCFone hrateBar0
    hCEdef hCnsCdef
  have hCXone := one_le_CX_of_def hCpre1 hCXdef
  have hC7one : 1 ≤ C7 := by
    exact one_le_correctedLedgerCoefficient_of_defs hdelta0pos
      (hdelta0_ninth.trans (by norm_num)) hCXone (by linarith only [hbeta20])
      hCt1def hCt2udef hC7def
  have hGeneration : (3 : ℝ) ^ ns ≤ CnsC * Real.rpow base cns := by
    refine corrected_generation_power_cap d hd
      (E := Erec) (mAl := mrec)
      hgB hK'1 haspect1 haspb hbase3 hcW0 hrateBar0 hCdv1 hzetagB
      (heccA'.trans haspb) hkap1rec hkapE' hgK'cap hDDdef hGaccD
      hCBrev0.le hCdvZdef hC5def hCEdef hCFdef hcFdef hCnsCdef hcnsdef
      hnsSum hnsBvCap hnsEvCap ?_
    simpa only [rAFv, adapter, Eband] using! hnsFvCap
  have hSource := corrected_normalized_source_cap
      (d := d) (ns := ns) (A := Aact) (delta := delta0)
      (beta := 2 * beta2) (base := base) (cW := cW) (Cpre := Cpre)
      (M := absorbedNormalizer 16 16 (designNormalizer R M₀))
      (L := isotropyLoadScale cIso (isotropyKap2 cIso))
      (rho := contrastRho gB) (K := K') (R := R) (CX := CX)
      (S2 := S2act) (ct2 := ct2) hAact1 hdelta0pos
      (by linarith only [hbeta20]) hbase3 hcW0 hCpre1 hMabs0 hrho1 hR1
      hgK'cap hCXdef rfl hct2def
  have hStartRaw := corrected_cadence_initial_ledger_power_cap
      (ns := ns) (cA := cAbar) (A := Aact)
      (alpha := recursionAlpha gB) (S0 := S0act) (S2 := S2act)
      (d0 := delta0) (beta := 2 * beta2) (base := base)
      (Cns := CnsC) (cns := cns) (CX := CX) (Ct1 := Ct1)
      (Ct2u := Ct2u) (C7 := C7) (ct2 := ct2)
      hbase3 hAact1 hdelta0pos (by linarith only [hdelta0_ninth])
      (by linarith only [hbeta20]) hCnsone hct20 hCXone hS2act1
      hGeneration hSource hCt1def hCt2udef hC7def
  have hStart : (3 : ℝ) ^ (startAct : ℝ) ≤ CnsC ^ 2 * C7 * Real.rpow base (2 * cns + ct2) := by
    simpa only [startAct] using hStartRaw
  exact ⟨hC7one, hStart⟩

private theorem endpoint_corrected_entry_power_cap (d : ℕ) (hd : 2 ≤ d)
    {lAl : ℤ} {Gacc : ℕ}
    [NeZero d]
    {cburn cW cC6u : ℝ}
    {gB : ℝ}
    {Cdv iexp CdvZ C5 C6 c6 CentryCap : ℝ}
    (hcC6uP : ∀ base : ℝ, 3 ≤ base → C6 ≤ base ^ cC6u)
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    (hiexp0 : 0 < iexp)
    (hiexpdef : iexp = (1 - gB)⁻¹)
    (hCdvZdef : CdvZ = Cdv * zetaG gB)
    (hC5def : C5 = 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d))
    (hC6def : C6 = 31104 * ((32 * CdvZ * C5) ^ iexp))
    (hc6def : c6 = (2 + cW) * cburn + 3 * cW + 2 * iexp)
    (hCentryCapdef : CentryCap = 2 * cC6u + 2 * c6)
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW N₀ : ℕ} {sKw : ℤ}
    (hN₀Z : (N₀ : ℤ) = (isotropySplit (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) (1 / 8 / 2) Cdv gB
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (Gacc + 1) sKw))
    (hGaccD : Gacc + 1 = (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
    (hsKwC : (3 : ℝ) ^ sKw ≤ (3 : ℝ) ^ lAl * (3 * growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))))
    (hgK'2 : (2 : ℝ) ≤ growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (haspect1 : 1 ≤ aspectRatio Ebase)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
    (hmAlpd' : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef)
    (heccA' : witnessEccentricity (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) ≤ aspectRatio Ebase)
    (hm21 : (1 : ℝ) ≤ sourceMomentTwo (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hrpowcW1 : (1 : ℝ) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (hgK'cap : growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ 2 * Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (haspb : aspectRatio Ebase ≤ (2 + aspectRatio Ebase * Kbase))
    (hbpos : (0 : ℝ) < (2 + aspectRatio Ebase * Kbase))
    (hlAlcap : (3 : ℝ) ^ lAl ≤ (2 + aspectRatio Ebase * Kbase) ^ (((2 : ℝ) + cW) * cburn))
    : ((3 : ℝ) ^ (2 * N₀) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) CentryCap) := by
  classical
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  let split : ℤ := isotropySplit K' (1 / 8 / 2) Cdv gB
    mrec
    (Gacc + 1) sKw
  have heETcap := euclidean_entry_threshold_power_cap
    (K := K') (base := base) (cW := cW) (s := sKw)
    hgK'2 hgK'cap hrpowcW1 hm21
  have hDcap := burn_split_depth_power_cap
    (d := d) (E := Ebase) (Cd := Cdv) (g := gB) (base := base)
    (C5 := C5) (D := DD) hd hDDdef hCdv1 haspect1 hzetagB haspb hC5def
  have htiltcap := tilt_gap_power_cap
    (d := d) (Cd := Cdv) (g := gB) (base := base) (C5 := C5)
    (CdvZ := CdvZ) (iexp := iexp) (m := mrec) (G := Gacc) (D := DD)
    hd hgB hmAlpd' hCdv1 hzetagB (heccA'.trans haspb) hbase3
    hC5def hCdvZdef hGaccD hDcap hiexpdef hiexp0
  have hsplitcap := isotropy_split_power_cap
    (K := K') (Cd := Cdv) (g := gB) (base := base) (cW := cW)
    (cburn := cburn) (CdvZ := CdvZ) (C5 := C5) (iexp := iexp)
    (C6 := C6) (c6 := c6) (m := mrec) (G := Gacc) (s := sKw)
    (l := lAl) (split := split) rfl heETcap htiltcap hsKwC hlAlcap
    hgK'cap hgK'2 hbpos hC6def hc6def
  have hentryCap : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base CentryCap :=
    entry_exponent_of_integer_split_cap hbase3 hN₀Z
    hsplitcap (hcC6uP base hbase3) hCentryCapdef
  exact hentryCap

private theorem endpoint_corrected_outer_transfer_bound (d : ℕ)
    {lAl : ℤ} {Gacc : ℕ}
    [NeZero d]
    {Cpre eta CsubF cSc delta0 CBrev : ℝ} {H : ℕ}
    {cIso M₀ R conv gB beta2 : ℝ}
    {rateBar Cdv : ℝ}
     {cAbar : ℕ}
     (hcSc48 : cSc ≤ 1 / 48)
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hCBrevP : ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P gB E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ mAl : Mat d, mAl.PosDef →
              ∀ G : ℕ, ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G →
                ∀ n₀ mOut : ℕ,
                  0 < Prop42Scalar.correctedTiltScale n₀ mOut →
                  Prop42Scalar.correctedTiltScale n₀ mOut < mOut →
                  l ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) →
                  0 ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) +
                    (G : ℤ) - 1 - sK →
                  ∀ A : ℝ, CBrev * reverseAdapterFactor Cd gB K E mAl G ≤ A →
                    A * Real.rpow (3 : ℝ)
                        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                          ℕ) : ℝ)) ≤ 1 →
                    ∃ c : ℝ, 0 ≤ c ∧
                      BlockMatLoewnerLE
                        (blockSub (annealedBlock P (centeredCube d (mOut : ℤ)))
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)))
                        (blockScale c E) ∧
                      c * blockSize E
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)) ≤
                        1 ∧
                      (9 / 2 : ℝ) *
                          (c * blockSize E
                            (adaptedMean P (roundedGrid l mAl)
                              (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ))) ≤
                        (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ)
                          (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                            ℕ) : ℝ)))
    (hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase cStar : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hcStar : cStar ∈ Set.Ioc 0 cSc)
    {nW nsFv ns N₀ : ℕ} {sKw : ℤ}
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl (canonicalMetric (Response.skewBlockCongr
      (canonicalShear Ebase) Ebase))))
    (hkZlAl : (kZero d : ℤ) ≤ lAl)
    (hsKwG : growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ (3 : ℝ) ^ sKw)
      (hnsF : nsFv ≤ ns)
    (hnsFvLow : (max 1 (CBrev * reverseAdapterFactor Cdv gB (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (canonicalMetric ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))) Gacc)) ≤ (3 : ℝ) ^
        (rateBar * (nsFv : ℝ)))
    (hfloorAt : ∀ k : ℤ, lAl ≤ k →
      hatExcessAt (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) k ≤ delta0)
    (hw : IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)))
    (hnn : 2 * normalizedGauge Ψbase 1 ≤ Kbase ^ nW)
    (hqnorm : ‖roundedGrid lAl (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase))‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    (hfin' : ∀ k : ℤ, HasFiniteAdaptedMean (recenteredLaw Pbase hskew) ((roundedGrid lAl
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) k)
    (hstat' : HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew))
    (hunit' : HCPoly.Frozen.IsUnitRangeLaw (recenteredLaw Pbase hskew))
    (hannR : annealedContrast (recenteredLaw Pbase hskew) 0 - 1 ≤ cStar)
    (hmAlpd' : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef)
    (hfloor0 : 0 ≤ hatExcess (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) N₀ 0)
    (hsKw0' : (0 : ℤ) ≤ sKw)
        (hrateAct0 : 0 < (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)))
    (hrateCmp : rateBar ≤ (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)))
    (hlAlN₀ : lAl ≤ (N₀ : ℤ))
    (hsourceBelow : sKw + 2 ≤ (N₀ : ℤ))
    : (∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast (recenteredLaw Pbase hskew) (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
            (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          (9 / 2 : ℝ) *
            ((1 + hatExcess (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
              (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) N₀ 0) *
              Real.rpow (3 : ℝ) ((linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
        weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2)) * ((linR ns cAbar (fusionRecursionConstantIsotropySharp d
        Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2)
      (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2) 1 (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) delta0 0) : ℝ))) *
            Real.rpow (3 : ℝ) (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  have hdagN := coarseEllipticityDagger_normalizedGauge hdagR
  have hdag' := coarseEllipticityDagger_burnSplitSource hstat' hdagN
    (le_refl 1) hw hnn
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  let qrec : Mat d := roundedGrid lAl mrec
  let Eband : BlockMat d := Erec
  let adapter : ℝ := CBrev * reverseAdapterFactor Cdv gB K' Eband
    (canonicalMetric Eband) Gacc
  let rAFv : ℝ := max 1 adapter
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  let S0act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF Msc delta0)
      (conv * vsumSourceConstant d CsubF Msc delta0) 0 ^ 2
  let S2act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))
  let rateAct : ℝ := linRate Aact (recursionAlpha gB) 1 1 (2 * beta2) cAbar S0act
  let startAct : ℕ := linR ns cAbar Aact (recursionAlpha gB) 1 1 (2 * beta2)
      S0act 1 S2act delta0 0
  have hpack : ∀ m : ℕ, 2 * N₀ < m → ∀ A : ℝ, CBrev * reverseAdapterFactor Cdv gB K' Erec mrec
    Gacc ≤ A → A * Real.rpow (3 : ℝ) (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ)) ≤
    1 → ∃ c : ℝ, 0 ≤ c ∧ BlockMatLoewnerLE (blockSub (annealedBlock (recenteredLaw Pbase
    hskew) (centeredCube d (m : ℤ))) (adaptedMean (recenteredLaw Pbase hskew) qrec
    (Prop42Scalar.correctedTiltScale N₀ m : ℤ))) (blockScale c Erec) ∧ c * blockSize Erec
    (adaptedMean (recenteredLaw Pbase hskew) qrec (Prop42Scalar.correctedTiltScale N₀ m : ℤ))
    ≤ 1 ∧ (9 / 2 : ℝ) * (c * blockSize Erec (adaptedMean (recenteredLaw Pbase hskew) qrec
    (Prop42Scalar.correctedTiltScale N₀ m : ℤ))) ≤ (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ) (-((m -
    Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ)) := by
    intro m hm A hA hAcap
    refine hCBrevP _ _ _ _ _
      (isProbabilityMeasure_recenteredLaw Pbase hskew) hstat' hunit'
      hdag' Cdv hCdvle sKw hsKw0' hsKwG lAl hkZlAl
      mrec hmAlpd' Gacc hqnorm N₀ m ?_ ?_ ?_ ?_ A hA hAcap
    all_goals simp only [Prop42Scalar.correctedTiltScale]
    all_goals omega
  have hx1 : ∀ m : ℕ, 2 * N₀ < m → (d : ℝ) * (adaptedHattedContrast (recenteredLaw Pbase
    hskew) qrec (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1) ≤ 1 := by
    intro m hm
    have hlscale : lAl ≤ (Prop42Scalar.correctedTiltScale N₀ m : ℤ) := by
      simp only [Prop42Scalar.correctedTiltScale]
      omega
    have hf := hfloorAt
      (Prop42Scalar.correctedTiltScale N₀ m : ℤ) hlscale
    rw [hatExcessAt] at hf
    linarith only [hf, hdelta0_ninth]
  have hnFstart : nsFv ≤ startAct := by
    exact hnsF.trans (by
      dsimp only [startAct]
      exact ns_le_linR ns cAbar Aact (recursionAlpha gB) 1 1
        (2 * beta2) S0act 1 S2act delta0 0)
  have hadapter : CBrev * reverseAdapterFactor Cdv gB K' Erec mrec Gacc ≤ Real.rpow (3 : ℝ)
    (rateAct * (nsFv : ℝ)) := by
    have hleft : CBrev * reverseAdapterFactor Cdv gB K' Erec mrec Gacc ≤ rAFv := by
      change adapter ≤ rAFv
      exact le_max_right _ _
    have hmono : Real.rpow (3 : ℝ) (rateBar * (nsFv : ℝ)) ≤ Real.rpow (3 : ℝ) (rateAct * (nsFv
      : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hrateCmp (Nat.cast_nonneg _))
    exact hleft.trans (hnsFvLow.trans hmono)
  have htransferCap : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast (recenteredLaw Pbase hskew) (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast (recenteredLaw Pbase hskew) qrec
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          (9 / 2 : ℝ) *
            ((1 + hatExcess (recenteredLaw Pbase hskew) qrec N₀ 0) *
              Real.rpow (3 : ℝ) (rateAct * (startAct : ℝ))) *
            Real.rpow (3 : ℝ) (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ)) :=
              outer_transfer_of_corrected_tilt_inputs_of_finite_band
    (d := d) (P := recenteredLaw Pbase hskew) (g := gB) (E := Erec)
    (K := K') (l := lAl) (q := qrec) (n₀ := N₀) (nF := nsFv)
    (R := startAct) (cStar := cStar) (rate := rateAct)
    (floor0 := hatExcess (recenteredLaw Pbase hskew) qrec N₀ 0)
    (adapter := CBrev * reverseAdapterFactor Cdv gB K' Erec mrec Gacc)
    hstat' hdag' hgrid hfin' hannR
    (by linarith only [hcStar.2, hcSc48]) hrateAct0.le hfloor0
    hnFstart hadapter hpack hx1
  exact htransferCap

private theorem endpoint_drop_and_conversion_bounds (d : ℕ)
    {delta0 : ℝ}
    {cIso conv : ℝ}
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hdelta0pos : 0 < delta0)
    (hcIso0 : (0 : ℝ) ≤ cIso)
    (hkap1 : (1 : ℝ) ≤ isotropyKap2 cIso)
    (hconvdef : conv = meanSlotConversionAt d (1 + cIso) (isotropyKap2 cIso))
    {Ebase : BlockMat d}
    (hE'sym : IsSymmetricBlockMat (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hE'pd : Book.Ch02.BlockPosDef (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hbS : (0 : ℝ) ≤ blockSize (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
    : (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) * delta0 ≤
    1) ∧
    ((0 : ℝ) ≤ conv) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  have hdropch : dropConstantIsotropy (1 + cIso) Erec (isotropyReference cIso Erec) * delta0 ≤
    1 := by
    have h4 := dropConstantIsotropy_isotropyReference_le hE'sym hE'pd hcIso0
    have h0 := dropConstantIsotropy_nonneg (by linarith only [hcIso0] :
      (0:ℝ) ≤ 1 + cIso) hbS
    nlinarith only [h4, h0, hdelta0_ninth, hdelta0pos]
  have hconv0 : (0 : ℝ) ≤ conv := by
    rw [hconvdef]
    exact meanSlotConversionAt_nonneg d (by linarith only [hcIso0])
      (by linarith only [hkap1])
  exact ⟨hdropch, hconv0⟩

private theorem endpoint_corrected_prefactor_bound (d : ℕ) (hd : 2 ≤ d)
    {lAl : ℤ}
    [NeZero d]
    {Cpre eta CsubF delta0 CBrev cC8u : ℝ} {H : ℕ}
    {cIso M₀ R conv gB beta2 : ℝ}
    {rateBar Cdv CdvZ C5 CE CF CnsC cns : ℝ}
    {ct2 C7 C8 CprefCap : ℝ} {cAbar : ℕ}
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hcC8uP : ∀ base : ℝ, 3 ≤ base → C8 ≤ base ^ cC8u)
    (hrateBar0 : 0 < rateBar)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    (hcns0 : 0 ≤ cns)
    (hct20 : 0 ≤ ct2)
    (hC5def : C5 = 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d))
    (hCEdef : CE = 8100 * 3 ^ (3 * H) * C5 ^ 4)
    (hCFdef : CF = max 1 (CBrev * (45 / 2) * CdvZ * C5))
    (hCnsCdef : CnsC = (3 : ℝ) ^ (H + 1) * 624 * CE * (3 * CF ^ rateBar⁻¹) * 3)
    (hC8def : C8 = 36 * CnsC ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹)
    (hCprefCapdef : CprefCap = cC8u + cns / 2 + ct2 / 4)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Kbase : ℝ}
    {nW ns N₀ : ℕ}
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl (canonicalMetric (Response.skewBlockCongr
      (canonicalShear Ebase) Ebase))))
    (hlAlN₀ : lAl ≤ (N₀ : ℤ))
    (hfloorAt : ∀ k : ℤ, lAl ≤ k →
      hatExcessAt (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) k ≤ delta0)
    (hfin' : ∀ k : ℤ, HasFiniteAdaptedMean (recenteredLaw Pbase hskew) ((roundedGrid lAl
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) k)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
        (hC7one : 1 ≤ C7)
    (hStart : (3 : ℝ) ^ ((linR ns cAbar (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2)
        (1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2) 1 (1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
        (badSourceLegConstantAtLevel
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
      (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) delta0 0) : ℝ) ≤ CnsC ^ 2 * C7 * Real.rpow (2 + aspectRatio
        Ebase * Kbase) (2 * cns + ct2))
    (hrate4 : (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)) ≤ 1 / 4)
    (hrateAct0 : 0 < (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
        (rowSplitConstant cIso 1) (isotropyKap2 cIso)
        (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
          (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
        (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) 1 1 (2 * beta2) cAbar (1 + 6 *
          weakCoefficient d Cpre *
      weakSourceGroupSummed
        (absorbedNormalizer 16 16 (designNormalizer R M₀))
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
        (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
          Ebase) Ebase)) delta0)
        (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr
          (canonicalShear Ebase) Ebase)) delta0) 0 ^ 2)))
    : (0 ≤ hatExcess (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) N₀ 0) ∧
    (9 / 2 * ((1 + hatExcess (recenteredLaw Pbase hskew) (roundedGrid lAl
    (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) N₀ 0) * (3 : ℝ) ^
      (linRate (fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) (1 : ℝ) (1 : ℝ) (2 * beta2) cAbar (1
        + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2) * ((linR ns cAbar (fusionRecursionConstantIsotropySharp d
        Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB)
    (1 : ℝ) (1 : ℝ) (2 * beta2) (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2) (1 : ℝ) (1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) (burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1)) R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) delta0 0 : ℕ) : ℝ))) * (Real.rpow (3 : ℝ) (linRate
      (fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
        (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) 1
      (slotCVsum d) (cVmConstant d conv)) (recursionAlpha gB) (1 : ℝ) (1 : ℝ) (2 * beta2) cAbar (1
        + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear Ebase)
        Ebase)) delta0)
      (conv * vsumSourceConstant d CsubF (supplyMscSplit d (Response.skewBlockCongr (canonicalShear
        Ebase) Ebase)) delta0) 0 ^ 2) / 2) +
    1) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) CprefCap) := by
  classical
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  let qrec : Mat d := roundedGrid lAl mrec
  have hfloorN := hatExcess_floor_nat_add hfloorAt hlAlN₀
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  let S0act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF Msc delta0)
      (conv * vsumSourceConstant d CsubF Msc delta0) 0 ^ 2
  let S2act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))
  have hsqrtD1 := one_le_sqrt_nat_of_two_le hd
  have hC5one := one_le_cadenceStartCoefficient_of_def hC5def hCdv1 hzetagB hsqrtD1
  have hCFone := one_le_CF_of_def hCFdef
  have hCnsone := one_le_Cns_of_defs hC5one hCFone hrateBar0
    hCEdef hCnsCdef
  have hfloor0 : 0 ≤ hatExcess (recenteredLaw Pbase hskew) qrec N₀ 0 := hatExcess_nonneg hgrid
    hfin' N₀ 0
  have hprefCap :  9 / 2 * ((1 + hatExcess (recenteredLaw Pbase hskew) (roundedGrid lAl
    (canonicalMetric Erec)) N₀ 0) * (3 : ℝ) ^ (linRate Aact (recursionAlpha gB) (1 : ℝ) (1 : ℝ) (2
      * beta2) cAbar S0act * ((linR ns cAbar Aact (recursionAlpha gB)
    (1 : ℝ) (1 : ℝ) (2 * beta2) S0act (1 : ℝ) S2act delta0 0 : ℕ) : ℝ))) * (Real.rpow (3 : ℝ)
      (linRate Aact (recursionAlpha gB) (1 : ℝ) (1 : ℝ) (2 * beta2) cAbar S0act / 2) +
    1) ≤ Real.rpow base CprefCap   := corrected_endpoint_prefactor_cap
    (P := recenteredLaw Pbase hskew) (lAl := lAl) (E := Erec)
    (N₀ := N₀) (ns := ns) (cA := cAbar) (A := Aact)
    (alpha := recursionAlpha gB) (b0 := 1) (bA := 1) (b2 := 2 * beta2)
    (S0 := S0act) (S1 := 1) (S2 := S2act) (d0 := delta0)
    (base := base) (Cns := CnsC) (C7 := C7) (cns := cns)
    (ct2 := ct2) (C := C8) (cC := cC8u) (Cpref := CprefCap)
    hbase3 hfloor0 (le_trans (hfloorN 0) hdelta0_ninth)
    hrateAct0.le hrate4 hCnsone hC7one hcns0 hct20 hStart hC8def
    (hcC8uP base hbase3) (by rw [hCprefCapdef]; ring)
  exact ⟨hfloor0, hprefCap⟩

private theorem endpoint_source_rate_and_offset_bounds {gB beta2 : ℝ}
    {N₀ Gacc : ℕ} {sKw : ℤ}
    (hbeta2def : beta2 = min (1 / 2) (contrastAlpha gB))
    (hsourceBelow : sKw + 2 ≤ (N₀ : ℤ)) :
    (beta2 ≤ 1 / 2) ∧ (beta2 ≤ contrastAlpha gB) ∧
      ((0 : ℤ) ≤ (N₀ : ℤ) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw) := by
  have hbetaHalf : beta2 ≤ 1 / 2 := by
    rw [hbeta2def]
    exact min_le_left _ _
  have hbetaAlpha : beta2 ≤ contrastAlpha gB := by
    rw [hbeta2def]
    exact min_le_right _ _
  have hoffset : (0 : ℤ) ≤ (N₀ : ℤ) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw := by
    omega
  exact ⟨hbetaHalf, hbetaAlpha, hoffset⟩

private theorem endpoint_decay_from_corrected_cadence (d : ℕ) (hd : 2 ≤ d)
    [NeZero d] [Nonempty (Fin d)] {g : ℝ}
    {lAl : ℤ} {Gacc : ℕ}
    {Cpre eta CsubF cSc delta0 cburn cW CBrev cC6u cC8u : ℝ} {H : ℕ}
    {cIso L M₀ R Mabs conv gB Abar beta2 MscBar CvBar Ssrc0bar : ℝ}
    {rateBar alpha Cdv iexp CdvZ C5 C6 c6 CentryCap CE CF cF CnsC cns : ℝ}
    {Ct1 CX ct2 Ct2u C7 C8 CprefCap : ℝ} {cAbar : ℕ}
    (hCpre1 : 1 ≤ Cpre) (heta : 0 < eta)
    (hCsubF0 : 0 < CsubF)
     (hcSc48 : cSc ≤ 1 / 48)
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hdelta0_gs3 : (128 * Abar ^ 2) ^ 3 * delta0 ≤ 1 / 3)
    (hdelta0pos : 0 < delta0)
     (hcW0 : 0 ≤ cW) (hCBrev0 : 0 < CBrev)
    (hcC6uP : ∀ base : ℝ, 3 ≤ base → C6 ≤ base ^ cC6u)
    (hcC8uP : ∀ base : ℝ, 3 ≤ base → C8 ≤ base ^ cC8u)
    (hfamP : ∀ {g : ℝ}, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
        {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ},
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        HCPoly.Frozen.IsStationaryLaw P →
      ∀ {lAl : ℤ}, (kZero d : ℤ) ≤ lAl →
      ∀ {Cd : ℝ}, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
      ∀ {mAl : Mat d}, mAl.PosDef →
      IsRoundedGrid lAl (roundedGrid lAl mAl) →
      ∀ {Gacc : ℕ},
        ‖roundedGrid lAl mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc →
      boundaryConst Cd g mAl ≤ (3 : ℝ) ^ (Gacc + 1 : ℕ) →
      (∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
        ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
          BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
            (blockScale
              ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) -
                (k : ℝ)) 0)) E)) →
      ∀ {rho : ℝ}, 0 < rho → rho < 1 → g ≤ rho →
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw →
      ∀ {delta : ℝ}, 0 ≤ delta → delta ≤ 1 / 9 →
      (∀ k : ℤ, lAl ≤ k → hatExcessAt P (roundedGrid lAl mAl) k ≤ delta) →
      ∀ {Csub : ℝ}, 0 < Csub →
      (∀ (j' p' : ℤ), lAl ≤ j' → j' ≤ p' →
        ∃ Z : Finset (Fin d → ℤ),
          (↑Z : Set (Fin d → ℤ)) =
              {w | adaptedCellCenter (roundedGrid lAl mAl) j' w ∈
                adaptedCell (roundedGrid lAl mAl) p'} ∧
            Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
            lqSchattenSize P 2
                (fun a ↦ blockSub
                  (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                    ∑ w ∈ Z,
                      toFullBlockMat
                        (coarseBlock
                          (adaptedCellAt (roundedGrid lAl mAl) j' w) a)))
                  (adaptedMean P (roundedGrid lAl mAl) j'))
                  (adaptedMean P (roundedGrid lAl mAl) p') ≤
              ENNReal.ofReal
                  (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                lqSchattenSize P 2
                  (fun a ↦ blockSub
                    (coarseBlock (adaptedCell (roundedGrid lAl mAl) j') a)
                    (adaptedMean P (roundedGrid lAl mAl) j'))
                  (adaptedMean P (roundedGrid lAl mAl) p')) →
      ∀ {N₀ ns : ℕ},
        H + 1 ≤ ns →
        lAl ≤ (N₀ : ℤ) + ((ns - H : ℕ) : ℤ) →
        (∀ n : ℕ, ns ≤ n →
          lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n →
          sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → sourceMomentTwo K ≤ (3 : ℝ) ^
          (((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
            ((Gacc + 1 : ℕ) : ℤ) - sKw)) →
      ∀ (M : ℕ),
        (∀ n : ℕ, ns ≤ n →
          1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
              growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
            (3 : ℝ) ^ ((M : ℝ) *
              ((((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
                ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) →
      ∀ {sigma cEnt : ℝ}, refContrast E - 1 ≤ sigma → 0 ≤ sigma → 0 < cEnt →
      nearIdentityDefect cEnt sigma < 1 →
      0 ≤ euclideanEntryThreshold K (cEnt / 2) sKw →
      lAl ≤ isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw →
      (∀ n : ℕ, ns ≤ n →
        isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤
          (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
      sourceMomentTwo K ≤ (3 : ℝ) ^
        (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw +
          ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      ∀ {cDeep : ℝ},
      (∀ n : ℕ, ns ≤ n →
        capsDeepConstant Cd g mAl (Gacc + 1)
          (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw)
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) ((N₀ : ℤ) + (n : ℤ)) ≤ cDeep) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ))
            (isotropyReference (nearIdentityDefect cEnt sigma) E) a ≤
          ENNReal.ofReal (R *
            ((max 1 (3 * S a *
              (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) +
                ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2))) →
      ∀ (S0 SStar0 K0 : ℕ → Mat d),
        (∀ m : ℕ, (S0 m).PosDef) → (∀ m : ℕ, (SStar0 m).PosDef) →
        (∀ m : ℕ, toFullBlockMat
            (adaptedMean P (roundedGrid lAl mAl) ((N₀ : ℤ) + (m : ℤ))) =
          schurBlock (S0 m) (SStar0 m) (K0 m)) →
      ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
        adaptedHattedContrast P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
          4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
                (16 * (d : ℝ) *
                  (adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                    adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + (n : ℤ)))) +
              rowValue2Isotropy d
                (rowSplitConstant (nearIdentityDefect cEnt sigma) cDeep)
                (isotropyKap2 (nearIdentityDefect cEnt sigma))
                (hatExcessAt P (roundedGrid lAl mAl)
                  ((N₀ : ℤ) + (n : ℤ))) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
                (Response.maxGroupConstantAtLevel lev)
                (Response.energyGoodConstantAtLevel lev) P mAl
                (Response.responseSkew (K0 n))
                (isotropyReference (nearIdentityDefect cEnt sigma) E)
                (loadScaleOfScalar (1 + nearIdentityDefect cEnt sigma)
                  (isotropyKap2 (nearIdentityDefect cEnt sigma))) mAl rho
                (n - ns)
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) +
                    ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) lev ((N₀ : ℤ) + (n : ℤ)) lAl
                (fun j => slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) j)
                (slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) 0)
                (meanDrop2ValueIsotropy P lAl (1 + nearIdentityDefect cEnt sigma)
                  mAl E (isotropyReference (nearIdentityDefect cEnt sigma) E)
                  ((N₀ : ℤ) + (n : ℤ)))
                (meanSlotConversionAt d (1 + nearIdentityDefect cEnt sigma)
                    (isotropyKap2 (nearIdentityDefect cEnt sigma)) *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                    (n - min n m) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl)
                ((N₀ : ℤ) + (n : ℤ)) ^ 2))
    (hCBrevP : ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P gB E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ mAl : Mat d, mAl.PosDef →
              ∀ G : ℕ, ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G →
                ∀ n₀ mOut : ℕ,
                  0 < Prop42Scalar.correctedTiltScale n₀ mOut →
                  Prop42Scalar.correctedTiltScale n₀ mOut < mOut →
                  l ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) →
                  0 ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) +
                    (G : ℤ) - 1 - sK →
                  ∀ A : ℝ, CBrev * reverseAdapterFactor Cd gB K E mAl G ≤ A →
                    A * Real.rpow (3 : ℝ)
                        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                          ℕ) : ℝ)) ≤ 1 →
                    ∃ c : ℝ, 0 ≤ c ∧
                      BlockMatLoewnerLE
                        (blockSub (annealedBlock P (centeredCube d (mOut : ℤ)))
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)))
                        (blockScale c E) ∧
                      c * blockSize E
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)) ≤
                        1 ∧
                      (9 / 2 : ℝ) *
                          (c * blockSize E
                            (adaptedMean P (roundedGrid l mAl)
                              (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ))) ≤
                        (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ)
                          (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                            ℕ) : ℝ)))
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hcIso0 : (0 : ℝ) ≤ cIso)
    (hcIso1 : cIso < 1)
    (hkap1 : (1 : ℝ) ≤ isotropyKap2 cIso)
    (hR1 : (1 : ℝ) ≤ R)
    (hAbar1 : (1 : ℝ) ≤ Abar)
    (hgB1 : gB < 1)
    (hrho0 : 0 < contrastRho gB)
    (hrho1 : contrastRho gB < 1)
    (hgBrho : gB ≤ contrastRho gB)
    (halphaB : (0 : ℝ) < recursionAlpha gB)
    (hbeta20 : (0 : ℝ) < beta2)
    (hrateBar0 : 0 < rateBar)
    (hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    (hiexp0 : 0 < iexp)
    (hcns0 : 0 ≤ cns)
    (hct20 : 0 ≤ ct2)
    (_hCprefCap0 : 0 ≤ CprefCap)
    (hLdef : L = isotropyLoadScale cIso (isotropyKap2 cIso))
    (hMabsdef : Mabs = absorbedNormalizer 16 16 (designNormalizer R M₀))
    (hconvdef : conv = meanSlotConversionAt d (1 + cIso) (isotropyKap2 cIso))
    (hAbardef : Abar = fusionRecursionConstantIsotropySharp d Cpre eta H
    (absorbedNormalizer 16 16 (designNormalizer R M₀))
    (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
    (rowSplitConstant cIso 1) (isotropyKap2 cIso) 4 1
    (slotCVsum d) (cVmConstant d conv))
    (hbeta2def : beta2 = min (1 / 2) (contrastAlpha gB))
    (hMscBardef : MscBar = (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * ((9 / 8 : ℝ) * 4) * (2 * (4 : ℝ)) *
      Real.sqrt 2)
    (hCvBardef : CvBar = vsumSourceConstant d CsubF MscBar 1)
    (hSsrc0bardef : Ssrc0bar = 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed Mabs L (contrastRho gB) CvBar (conv * CvBar)
      0 ^ 2)
    (hcAbardef : cAbar = ⌈Real.logb 3 (24 * Abar) / recursionAlpha gB⌉₊)
    (hrateBardef : rateBar = linRate Abar (recursionAlpha gB) 1 1 (2 * beta2) cAbar Ssrc0bar)
    (hiexpdef : iexp = (1 - gB)⁻¹)
    (hCdvZdef : CdvZ = Cdv * zetaG gB)
    (hC5def : C5 = 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d))
    (hC6def : C6 = 31104 * ((32 * CdvZ * C5) ^ iexp))
    (hc6def : c6 = (2 + cW) * cburn + 3 * cW + 2 * iexp)
    (hCentryCapdef : CentryCap = 2 * cC6u + 2 * c6)
    (hCEdef : CE = 8100 * 3 ^ (3 * H) * C5 ^ 4)
    (hCFdef : CF = max 1 (CBrev * (45 / 2) * CdvZ * C5))
    (hcFdef : cF = 4 + 3 * cW)
    (hCnsCdef : CnsC = (3 : ℝ) ^ (H + 1) * 624 * CE * (3 * CF ^ rateBar⁻¹) * 3)
    (hcnsdef : cns = 4 * cW + 4 + cF / rateBar)
    (hCt1def : Ct1 = 3 / delta0 ^ 2)
    (hCXdef : CX = 1 +
    (6 * weakCoefficient d Cpre *
    ((16 * absorbedNormalizer 16 16 (designNormalizer R M₀) / (1 - contrastRho gB)) *
    (Real.sqrt 2 * Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
    R * 6)) ^ 2) * 65536)
    (hct2def : ct2 = 16 * cW / (2 * beta2))
    (hCt2udef : Ct2u = (CX / delta0 ^ 2) ^ (2 * beta2)⁻¹)
    (hC7def : C7 = Ct1 * 3 * Ct2u)
    (hC8def : C8 = 36 * CnsC ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹)
    (hCprefCapdef : CprefCap = cC8u + cns / 2 + ct2 / 4)
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase cStar : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hcStar : cStar ∈ Set.Ioc 0 cSc)
    {nW nsBv nsEv nsFv ns N₀ : ℕ} {sKfd gap sKw : ℤ}
    (hlAldef : lAl = sKfd + 1 + gap)
    (_hGaccdef : Gacc = burnSplitDepth d Cdv gB (aspectRatio Ebase) - 1)
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase g Ebase Ψbase Kbase Sbase)
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (hsharpE' : BlockMatLoewnerLE (blockSharp (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    {S0f SStar0f K0f : ℕ → Mat d}
    (hS0f : ∀ n : ℕ, (S0f n).PosDef)
    (hStar0f : ∀ n : ℕ, (SStar0f n).PosDef)
    (hformf : ∀ n : ℕ, toFullBlockMat
      (adaptedMean (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ((N₀ : ℤ) + (n : ℤ))) =
        schurBlock (S0f n) (SStar0f n) (K0f n))
    (hrecE' : canonicalShear (Response.skewBlockCongr (canonicalShear Ebase) Ebase) = 0)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl (canonicalMetric (Response.skewBlockCongr
      (canonicalShear Ebase) Ebase))))
    (hkZlAl : (kZero d : ℤ) ≤ lAl)
    (hlAlN₀ : lAl ≤ (N₀ : ℤ))
    (hN₀Z : (N₀ : ℤ) = (isotropySplit (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) (1 / 8 / 2) Cdv gB
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (Gacc + 1) sKw))
    (hGaccD : Gacc + 1 = (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
    (hsKwF : lAl ≤ sKw)
    (hsKwG : growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ (3 : ℝ) ^ sKw)
    (hsKwC : (3 : ℝ) ^ sKw ≤ (3 : ℝ) ^ lAl * (3 * growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))))
    (hnsH : H + 1 ≤ ns) (hnsE : nsEv ≤ ns) (hnsF : nsFv ≤ ns)
    (hnsSum : ns ≤ (H + 1) + nsBv + nsEv + nsFv)
    (hnsBvCap : (3 : ℝ) ^ nsBv ≤ 3 * (13 * growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ^ 4))
    (hnsEvCap : (3 : ℝ) ^ nsEv ≤
      8100 * (3 : ℝ) ^ (3 * H) * (3 : ℝ) ^ (4 * (burnSplitDepth d Cdv gB (aspectRatio Ebase))))
    (hnsEvKill : (10 * (3 : ℝ) ^ (2 * (burnSplitDepth d Cdv gB (aspectRatio Ebase))
    + H) : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * ((nsEv : ℝ) + 1 - (H : ℝ))))
    (hnsFvLow : (max 1 (CBrev * reverseAdapterFactor Cdv gB (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (canonicalMetric ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))) Gacc)) ≤ (3 : ℝ) ^
        (rateBar * (nsFv : ℝ)))
    (hnsFvCap : (3 : ℝ) ^ nsFv ≤ 3 * (max 1 (CBrev * reverseAdapterFactor Cdv gB
      (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (canonicalMetric ((Response.skewBlockCongr (canonicalShear Ebase) Ebase))) Gacc)) ^ rateBar⁻¹)
    (hlAlnsH : lAl ≤ (N₀ : ℤ) + ((ns - H : ℕ) : ℤ))
    (hlAlgen : ∀ n : ℕ, ns ≤ n → lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ))
    (hsKwgen : ∀ n : ℕ, ns ≤ n → sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ))
    (hsplitgen : ∀ n : ℕ, ns ≤ n → (isotropySplit (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) (1 / 8 / 2) Cdv gB
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
      (Gacc + 1) sKw) ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ))
    (hfloorAt : ∀ k : ℤ, lAl ≤ k →
      hatExcessAt (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) k ≤ delta0)
    (henvC : ∀ n : ℕ, BlockMatLoewnerLE
      (adaptedMean (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ((N₀ : ℤ) + (n : ℤ)))
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
    (hcompC : ∀ n : ℕ, BlockMatLoewnerLE (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
      (blockScale (isotropyKap2 cIso)
        (adaptedMean (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
          (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) ((N₀ : ℤ) + (n : ℤ)))))
    (hsubdiv : (∀ j' p' : ℤ, sKfd + 1 + gap ≤ j' → j' ≤ p' →
                      ∃ Z : Finset (Fin d → ℤ),
                        (↑Z : Set (Fin d → ℤ)) =
                            {w | adaptedCellCenter
                              (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) j' w ∈
                              adaptedCell (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) p'} ∧
                          Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
                          lqSchattenSize (recenteredLaw Pbase hskew) 2
                              (fun a ↦ blockSub
                                (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                                  ∑ w ∈ Z,
                                    toFullBlockMat
                                      (coarseBlock
                                        (adaptedCellAt
                                          (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                            (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
                                          j' w) a)))
                                (adaptedMean (recenteredLaw Pbase hskew)
                                  (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                    (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) j'))
                                (adaptedMean (recenteredLaw Pbase hskew)
                                  (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                    (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) p') ≤
                            ENNReal.ofReal
                                (CsubF * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                              lqSchattenSize (recenteredLaw Pbase hskew) 2
                                (fun a ↦ blockSub
                                  (coarseBlock
                                    (adaptedCell
                                      (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                        (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
                                        j') a)
                                  (adaptedMean (recenteredLaw Pbase hskew)
                                    (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                      (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) j'))
                                (adaptedMean (recenteredLaw Pbase hskew)
                                  (roundedGrid (sKfd + 1 + gap) (canonicalMetric
                                    (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) p')))
    (hw : IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)))
    (hnn : 2 * normalizedGauge Ψbase 1 ≤ Kbase ^ nW)
    (hlAl0 : (0 : ℤ) ≤ lAl)
    (hqnorm : ‖roundedGrid lAl (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase))‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc)
    (hkEnt0 : (0 : ℤ) ≤ euclideanEntryThreshold (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) (1 / 8 / 2) sKw)
    (hfin' : ∀ k : ℤ, HasFiniteAdaptedMean (recenteredLaw Pbase hskew) ((roundedGrid lAl
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) k)
    (hM₀' : metricFactorValue (Response.skewBlockCongr (canonicalShear Ebase) Ebase) (1 + cIso)
      (isotropyKap2 cIso) ≤ M₀)
    (hgK'2 : (2 : ℝ) ≤ growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hm2gen : ∀ n : ℕ, ns ≤ n → sourceMomentTwo (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ (3 : ℝ) ^ (((N₀ : ℤ) + (n : ℤ) - ((n -
      ns : ℕ) : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - sKw))
    (hMcond : ∀ n : ℕ, ns ≤ n → 1 + 2 * ((2 + 1 : ℕ) : ℝ) * (1 + Real.log (growthBar
      (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))) *
      growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ^ IndependentSums.natTriangular (2 + 1) ≤ (3 : ℝ) ^ (((1 : ℕ) : ℝ)
        * ((((N₀ :
      ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)))
    (haspect1 : 1 ≤ aspectRatio Ebase)
    (hbase3 : (3 : ℝ) ≤ 2 + aspectRatio Ebase * Kbase)
    (hstat' : HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew))
    (hunit' : HCPoly.Frozen.IsUnitRangeLaw (recenteredLaw Pbase hskew))
    (hE'sym : IsSymmetricBlockMat (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hE'pd : Book.Ch02.BlockPosDef (Response.skewBlockCongr (canonicalShear Ebase) Ebase))
    (hbS : (0 : ℝ) ≤ blockSize (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
    (hannR : annealedContrast (recenteredLaw Pbase hskew) 0 - 1 ≤ cStar)
    (hrefE' : refContrast (Response.skewBlockCongr (canonicalShear Ebase) Ebase) - 1 ≤ cSc)
    (hkapE' : kappaRef (Response.skewBlockCongr (canonicalShear Ebase) Ebase) ≤ 9 / 8)
    (hmAlpd' : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef)
    (heccA' : witnessEccentricity (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)) ≤ aspectRatio Ebase)
    (hK'1 : (1 : ℝ) ≤ (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hm21 : (1 : ℝ) ≤ sourceMomentTwo (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)))
    (hrpowcW1 : (1 : ℝ) ≤ Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (hgK'cap : growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1)) ≤ 2 * Real.rpow (2 + aspectRatio Ebase * Kbase) cW)
    (haspb : aspectRatio Ebase ≤ (2 + aspectRatio Ebase * Kbase))
    (hbpos : (0 : ℝ) < (2 + aspectRatio Ebase * Kbase))
    (hlAlcap : (3 : ℝ) ^ lAl ≤ (2 + aspectRatio Ebase * Kbase) ^ (((2 : ℝ) + cW) * cburn))
    (hQenvP : ∀ᵐ a ∂(recenteredLaw Pbase hskew), ∀ m : ℤ, burnSplitSource gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase)
      ((burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (recenteredSource Sbase hskew) a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m → BlockMatLoewnerLE (coarseBlock (standardCell d
      k w) a) (blockScale ((3 : ℝ) ^ (gB * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) - (k : ℝ))
      0)) (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))
    (henvMaxP : ∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂(recenteredLaw Pbase hskew),
      Response.diagonalWeakMaximum (contrastRho gB) ((roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) ((N₀ : ℤ) + (n : ℤ))
      (isotropyReference cIso (Response.skewBlockCongr (canonicalShear Ebase) Ebase)) a ≤
        ENNReal.ofReal (R * ((max 1 (3 * burnSplitSource gB (Response.skewBlockCongr
        (canonicalShear Ebase) Ebase)
      ((burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) - burnSplitAnchor d 1 Kbase
        (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
      (recenteredSource Sbase hskew) a * (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) + ((Gacc +
      1 : ℕ) : ℝ))))) ^ gB / 2)))
        {CdelayS : ℝ}
    (hCprefCap0 : 0 ≤ CprefCap)
    (hCdelaySdef : CdelayS = CentryCap + (1 + CprefCap / (rateBar / 2)))
    (halphadef : alpha = rateBar / 2)
    (hcIsodef : cIso = nearIdentityDefect (1 / 8) (1 / 48))
    : ∃ m0 : ℕ, (3 : ℝ) ^ m0 ≤
      (2 + aspectRatio Ebase * Kbase) ^ CdelayS ∧
      ∀ j : ℕ, annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
        (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
  classical
  have hrefE'48 := hrefE'.trans hcSc48
  set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  have hdagN := coarseEllipticityDagger_normalizedGauge hdagR
  have hdag' := coarseEllipticityDagger_burnSplitSource hstat' hdagN
    (le_refl 1) hw hnn
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  have hbC := three_pow_reindex hGaccD
    (boundaryConst_le_three_pow_burnSplitDepth hd hCdv1 hgB haspect1 heccA')
  let split : ℤ := isotropySplit K' (1 / 8 / 2) Cdv gB
    mrec
    (Gacc + 1) sKw
  have hsKwsplit := le_isotropySplit (d := d) K' (1 / 8 / 2)
    Cdv gB mrec (Gacc + 1) sKw
  have hm2split := sourceMomentTwo_le_isotropySplit_tail (d := d) K' Cdv gB mrec (Gacc + 1) sKw
  have hlAlsplit := le_of_le_add_two hsKwF hsKwsplit
  let qrec : Mat d := roundedGrid lAl mrec
  have hfloorN := hatExcess_floor_nat_add hfloorAt hlAlN₀
  let Eband : BlockMat d := Erec
  let adapter : ℝ := CBrev * reverseAdapterFactor Cdv gB K' Eband
    (canonicalMetric Eband) Gacc
  let rAFv : ℝ := max 1 adapter
  have hcapsDeep := fun (n : ℕ) (hn : ns ≤ n) =>
    capsDeepConstant_le_one_of_kill Cdv gB
      mrec
      Gacc H DD n split N₀ hCdv1 hgB1 hmAlpd' hGaccD hN₀Z hbC
      ((Nat.le_succ H).trans (hnsH.trans hn))
      (deepKill_mono H DD nsEv n (hnsE.trans hn) hnsEvKill)
  obtain ⟨hdropch, hconv0⟩ :=
    endpoint_drop_and_conversion_bounds d hdelta0_ninth hdelta0pos hcIso0 hkap1
      hconvdef hE'sym hE'pd hbS
  let Msc : ℝ := supplyMscSplit d Erec
  let Aact : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
      (rowSplitConstant cIso 1) (isotropyKap2 cIso)
      (dropConstantIsotropy (1 + cIso) Erec
        (isotropyReference cIso Erec)) 1
      (slotCVsum d) (cVmConstant d conv)
  obtain ⟨hMsc0, hAle, hA1', hgs3', hcA24'⟩ :=
    endpoint_actual_recursion_constant_bounds d hCpre1 hdelta0_gs3 hdelta0pos hcIso0 hAbar1 hgB1
      hAbardef hcAbardef hE'sym
      hE'pd
  let S0act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB)
      (vsumSourceConstant d CsubF Msc delta0)
      (conv * vsumSourceConstant d CsubF Msc delta0) 0 ^ 2
  let S2act : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed
      (absorbedNormalizer 16 16 (designNormalizer R M₀))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) (contrastRho gB) 0 0
      (badSourceLegConstantAtLevel
        (isotropyLoadScale cIso (isotropyKap2 cIso)) K' R) ^ 2 *
    (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))
  let rateAct : ℝ := linRate Aact (recursionAlpha gB) 1 1 (2 * beta2) cAbar S0act
  let startAct : ℕ := linR ns cAbar Aact (recursionAlpha gB) 1 1 (2 * beta2)
      S0act 1 S2act delta0 0
  obtain ⟨hMabs0, hkap1rec, hMscLe, hCvLe, hCv0, hGroup0, hGroupLe, hS0act1, hS0actLe, hS2act1,
    hAact1, hAactLe, hrateAct0, hrateCmp, hrate4⟩ :=
    endpoint_actual_source_and_rate_bounds d hCpre1 hCsubF0
      hdelta0_ninth hdelta0pos hR1 hrho1 halphaB hbeta20 hLdef hMabsdef hMscBardef hCvBardef
      hSsrc0bardef hrateBardef hsharpE' hM₀' hconv0 hE'sym hE'pd hkapE' hMsc0 hAle hA1'
  have hsqrtD1 := one_le_sqrt_nat_of_two_le hd
  have hC5one := one_le_cadenceStartCoefficient_of_def hC5def hCdv1 hzetagB hsqrtD1
  have hCFone := one_le_CF_of_def hCFdef
  have hCnsone := one_le_Cns_of_defs hC5one hCFone hrateBar0
    hCEdef hCnsCdef
  have hCXone := one_le_CX_of_def hCpre1 hCXdef
  obtain ⟨hC7one, hStart⟩ :=
    endpoint_corrected_initial_ledger_bound d hd hCpre1 hdelta0_ninth hdelta0pos hcW0 hCBrev0 hgB
      hR1 hrho1 hbeta20 hrateBar0 hCdv1 hzetagB hct20 hCdvZdef hC5def hCEdef hCFdef hcFdef hCnsCdef
      hcnsdef hCt1def hCXdef hct2def hCt2udef hC7def hGaccD hnsSum hnsBvCap hnsEvCap hnsFvCap
      haspect1 hbase3 hkapE' heccA' hK'1 hgK'cap haspb hAact1 hMabs0 hS2act1 hkap1rec
  obtain ⟨hbetaHalf, hbetaAlpha, hoffset⟩ :=
    endpoint_source_rate_and_offset_bounds hbeta2def
      (by rw [hN₀Z]; exact hsKwsplit)
  have hsrcP := corrected_source_pricing_endpoint_branch
    (d := d) (Cpre := Cpre)
    (Mabs := absorbedNormalizer 16 16 (designNormalizer R M₀))
    (L := isotropyLoadScale cIso (isotropyKap2 cIso))
    (Csub := CsubF) (Msc := Msc) (delta := delta0) (conv := conv)
    (K := K') (R := R) (g := gB) (beta2 := beta2) (ns := ns)
    (N₀ := N₀) (Gacc := Gacc) (sKw := sKw) hd
    (by linarith only [hCpre1]) hMabs0 hCsubF0.le hMsc0
    hdelta0pos.le hconv0 hR1 hgB1 hbetaHalf hbetaAlpha hoffset
  have hfamAct := fun (m : ℕ) (hm : ns ≤ m) (n : ℕ) (hn : ns ≤ n) =>
    hfamP hgB hdag' hstat' hkZlAl hCdvle hmAlpd' hgrid hqnorm hbC
      hQenvP hrho0 hrho1 hgBrho hsKwG hdelta0pos.le hdelta0_ninth
      hfloorAt hCsubF0 (by simpa only [hlAldef] using hsubdiv)
      hnsH hlAlnsH hlAlgen hsKwgen hm2gen 1
      hMcond hrefE'48 (by norm_num) (by norm_num) (by simpa only [hcIsodef] using hcIso1) hkEnt0
      hlAlsplit hsplitgen hm2split hcapsDeep hR1 hR1 (by simpa only [hcIsodef] using henvMaxP)
      S0f SStar0f K0f hS0f hStar0f hformf m hm n hn
  have hentryCap :=
    endpoint_corrected_entry_power_cap d hd hcC6uP hgB hCdv1 hzetagB hiexp0 hiexpdef hCdvZdef
      hC5def hC6def
      hc6def hCentryCapdef hN₀Z hGaccD hsKwC hgK'2 haspect1 hbase3 hmAlpd' heccA' hm21 hrpowcW1
      hgK'cap haspb hbpos hlAlcap
  obtain ⟨hfloor0, hprefCap⟩ :=
    endpoint_corrected_prefactor_bound d hd hdelta0_ninth hcC8uP
      hrateBar0 hCdv1 hzetagB hcns0 hct20 hC5def hCEdef hCFdef hCnsCdef hC8def hCprefCapdef hskew
      hgrid hlAlN₀ hfloorAt hfin' hbase3 hC7one hStart hrate4 hrateAct0
  have hsKw0' : (0 : ℤ) ≤ sKw := hlAl0.trans hsKwF
  have htransferCap :=
    endpoint_corrected_outer_transfer_bound d hcSc48
      hdelta0_ninth hCBrevP hCdvle hcStar hskew hdagR hgrid hkZlAl hsKwG hnsF hnsFvLow hfloorAt hw
      hnn hqnorm hfin' hstat' hunit' hannR hmAlpd' hfloor0 hsKw0' hrateAct0 hrateCmp
      hlAlN₀ (by rw [hN₀Z]; exact hsKwsplit)
  have hCpre0 : (0 : ℝ) ≤ Cpre := zero_le_one.trans hCpre1
  have hone0 : (0 : ℝ) ≤ 1 := zero_le_one
  have honepos : (0 : ℝ) < 1 := one_pos
  have hb2pos : (0 : ℝ) < 2 * beta2 := mul_pos (by norm_num) hbeta20
  have hkeyRaw := hcore_body_of_corrected_design
      (d := d) (P := recenteredLaw Pbase hskew) (lAl := lAl) (E := Erec)
      (N₀ := N₀) (g := gB) (Cpre := Cpre) (eta := eta) (H := H)
      (cIso := cIso) (cDeep := 1) (S0 := S0f) (SStar0 := SStar0f)
      (K0 := K0f) (Csub := CsubF) (Msc := Msc) (delta0 := delta0)
      (conv := conv) (deltaDrop := 1) (M₀ := M₀) (K := K') (R := R)
      (Gacc := Gacc) (sKw := sKw) (ns := ns) (A := Aact)
      (Ssrc0 := S0act) (Ssrc1 := 1) (Ssrc2 := S2act)
      (b0 := 1) (bA := 1) (b2 := 2 * beta2) (cA := cAbar)
      (base := base) (Centry := CentryCap) (Cpref := CprefCap)
      hd hstat' hgrid hfin' hlAlN₀ hgB.1 hgB1 hCpre0 heta hE'sym hE'pd
      hsharpE' hrecE' hcIso0 hcIso1 hone0 hS0f hStar0f hformf henvC hcompC
      hCsubF0.le hMsc0 hdelta0pos hconv0 hone0 hbS hfloorN
      hdropch hM₀' hR1 hnsH rfl hA1' hS0act1 (le_refl (1 : ℝ))
      hS2act1 honepos honepos hb2pos
      hgs3' hcA24' (by simpa only [hcIsodef, hconvdef] using hfamAct) hsrcP hbase3 hCprefCap0
        hentryCap
      hprefCap htransferCap
  have hkey : ∃ m₀ : ℕ, (3 : ℝ) ^ m₀ ≤ Real.rpow base (CentryCap + (1 + CprefCap / (rateAct /
    2))) ∧ ∀ j : ℕ, annealedContrast (recenteredLaw Pbase hskew) ((m₀ + j : ℕ) : ℤ) - 1 ≤
    Real.rpow (3 : ℝ) (-(rateAct / 2) * (j : ℝ)) := by
    simpa only [rateAct] using hkeyRaw
  have hfin1 : ∀ m : ℤ, HasFiniteAdaptedMean Pbase (1 : Mat d) m :=
    fun m => (finite_adaptedMean_of_coarseEllipticityDagger hdag Matrix.PosDef.one m).1
  have hpdAnn : ∀ m : ℤ, Book.Ch02.BlockPosDef
      (annealedBlock Pbase (centeredCube d m)) :=
    fun m => blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  obtain ⟨m₀, hm₀, hdecay⟩ := hcore_body_carry_back hskew hfin1 hpdAnn hkey
  refine ⟨m₀, ?_, ?_⟩
  · exact hm₀.trans (terminal_delay_mono hbase3 hCprefCap0 hrateBar0
      hrateCmp hCdelaySdef)
  · intro j
    refine (hdecay j).trans ?_
    rw [halphadef]
    exact terminal_decay_mono hrateCmp j

private theorem endpoint_normalized_burn_window (d : ℕ) (hd : 2 ≤ d)
    {gB : ℝ}
    {Cdv : ℝ}
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv)
    {Pbase : Measure (CoeffSpace d)}
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gB Ebase Ψbase Kbase Sbase)
    (haspect1 : 1 ≤ aspectRatio Ebase)
    : ((0 : ℝ) < Ψbase 1) ∧
    (normalizedGauge Ψbase 1 = 1) ∧
    (1 ≤ burnSplitDepth d Cdv gB (aspectRatio Ebase)) ∧
    (IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ))) := by
  classical
  have hΨ1 : (0 : ℝ) < Ψbase 1 := lt_of_lt_of_le one_pos (hdag.gauge_admissible.2 zero_le_one)
  have hΨn1 : normalizedGauge Ψbase 1 = 1 := normalizedGauge_one hΨ1
  have hD1 : 1 ≤ burnSplitDepth d Cdv gB (aspectRatio Ebase) := by
    have h := succ_canonicalGridEnlargement_le_burnSplitDepth hd hCdvle
      hgB haspect1
    omega
  have hw : IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
    (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
    Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)) :=
    isCoupledWindow_burnSplitAnchor hd hD1
  exact ⟨hΨ1, hΨn1, hD1, hw⟩

private theorem endpoint_grid_mean_integrability (d : ℕ)
    {lAl : ℤ}
    [NeZero d]
    {gB : ℝ}
    {Cdv : ℝ}
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    {nW : ℕ}
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (hkZlAl : (kZero d : ℤ) ≤ lAl)
    (hnn : 2 * normalizedGauge Ψbase 1 ≤ Kbase ^ nW)
    (hstat' : HCPoly.Frozen.IsStationaryLaw (recenteredLaw Pbase hskew))
    (hmAlpd' : (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase)).PosDef)
    (hw : IsCoupledWindow d 1 Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)))
    : (((roundedGrid lAl (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase)
      Ebase)))).PosDef) ∧
    (∀ k : ℤ, HasFiniteAdaptedMean (recenteredLaw Pbase hskew) ((roundedGrid lAl (canonicalMetric
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase)))) k) ∧
    (∀ k : ℤ, Book.Ch02.BlockPosDef (adaptedMean (recenteredLaw Pbase hskew) ((roundedGrid lAl
      (canonicalMetric (Response.skewBlockCongr (canonicalShear Ebase) Ebase))))
      k)) := by
  classical
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  let mrec : Mat d := canonicalMetric Erec
  have hdagN := coarseEllipticityDagger_normalizedGauge hdagR
  have hdag' := coarseEllipticityDagger_burnSplitSource hstat' hdagN
    (le_refl 1) hw hnn
  let qrec : Mat d := roundedGrid lAl mrec
  have hqpd : (qrec).PosDef := Recurrence.posDef_roundedGrid hkZlAl hmAlpd'
  have hfin' : ∀ k : ℤ, HasFiniteAdaptedMean (recenteredLaw Pbase hskew) (qrec) k := fun k =>
      (finite_adaptedMean_of_coarseEllipticityDagger hdag' hqpd k).1
  have hpdM : ∀ k : ℤ, Book.Ch02.BlockPosDef (adaptedMean (recenteredLaw Pbase hskew) (qrec)
    k) := fun k =>
      (finite_adaptedMean_of_coarseEllipticityDagger hdag' hqpd k).2
  exact ⟨hqpd, hfin', hpdM⟩

private theorem endpoint_metric_and_floor_certificates (d : ℕ)
    {lAl : ℤ}
    [NeZero d]
    {cSc delta0 : ℝ}
    {cIso M₀ gB : ℝ}
    {Cdv : ℝ}
     (hcSc48 : cSc ≤ 1 / 48)
    (hcF0 : (0 : ℝ) ≤ 1 + cIso)
    (hkap0 : (0 : ℝ) ≤ isotropyKap2 cIso)
    (hM₀def : M₀ = isotropyMetricFactor cIso (1 / 48))
    {Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {Kbase : ℝ}
    {Sbase : CoeffSpace d → ℝ}
    {nW N₀ : ℕ}
    (hskew : IsSkewMat (canonicalShear Ebase))
    (hdagR : HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw Pbase hskew) gB
      (Response.skewBlockCongr (canonicalShear Ebase) Ebase) Ψbase Kbase (recenteredSource Sbase
        hskew))
    (hfloorAt : ∀ k : ℤ, lAl ≤ k →
      hatExcessAt (recenteredLaw Pbase hskew) (roundedGrid lAl (canonicalMetric
        (Response.skewBlockCongr (canonicalShear Ebase) Ebase))) k ≤ delta0)
    (hlAlN₀ : lAl ≤ (N₀ : ℤ))
    (hrefE' : refContrast (Response.skewBlockCongr (canonicalShear Ebase) Ebase) - 1 ≤ cSc)
    : (metricFactorValue (Response.skewBlockCongr (canonicalShear Ebase) Ebase) (1 + cIso)
      (isotropyKap2 cIso) ≤ M₀) ∧
    ((2 : ℝ) ≤ growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) ∧
    ((0 : ℝ) < growthBar (burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)))
        (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio Ebase)) + ((2 *
          (burnSplitDepth d Cdv gB (aspectRatio Ebase)) : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1))) := by
  classical
  have hrefE'48 := hrefE'.trans hcSc48
  let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
  set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
  set K' : ℝ := burnSplitThreshold d Kbase
      (burnSplitAnchor d 1 Kbase DD)
      (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
    Kbase * Kbase ^ (nW + 1) with hK'def
  have hM₀' : metricFactorValue Erec (1 + cIso) (isotropyKap2 cIso) ≤ M₀ := by
    rw [hM₀def]
    exact metricFactorValue_le_isotropyMetricFactor
      (cIso := cIso) (cF := 1 + cIso) (kap := isotropyKap2 cIso)
      hdagR hrefE'48 hcF0 hkap0 le_rfl le_rfl
  have hfloorN := hatExcess_floor_nat_add hfloorAt hlAlN₀
  have hgK'2 : (2 : ℝ) ≤ growthBar K' := le_max_left _ _
  have hgK'0 : (0 : ℝ) < growthBar K' := by linarith only [hgK'2]
  exact ⟨hM₀', hgK'2, hgK'0⟩

private theorem endpoint_bootstrap_smallness_bound (d : ℕ)
    {cSc delta0 : ℝ}
    (hcSc0 : 0 < cSc)
    (hdelta0def : delta0 = (d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) * cSc))
      {cStar : ℝ}
    (hcStar : cStar ∈ Set.Ioc 0 cSc)
    : ((d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) * cStar) ≤ delta0) := by
  classical
  have hbtp : (d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) * cStar) ≤ delta0 := by
    rw [hdelta0def]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
    refine bootstrapTiltPolynomial_le hcSc0.le le_rfl ?_ ?_
    · have := hcStar.1
      positivity
    · exact mul_le_mul_of_nonneg_left hcStar.2 (Nat.cast_nonneg d)
  exact hbtp

private theorem corrected_endpoint_decay_of_uniform_parameters (d : ℕ) (hd : 2 ≤ d)
    [NeZero d] [Nonempty (Fin d)] {g : ℝ}
    {Cpre eta CsubF CBF cSc delta0 cburn cW CBrev cC6u cC8u : ℝ} {H : ℕ}
    {cIso L M₀ R Mabs conv gB Abar beta2 MscBar CvBar Ssrc0bar : ℝ}
    {rateBar alpha Cdv iexp CdvZ C5 C6 c6 CentryCap CE CF cF CnsC cns : ℝ}
    {Ct1 CX ct2 Ct2u C7 C8 CprefCap CdelayS : ℝ} {cAbar : ℕ}
    (hCpre1 : 1 ≤ Cpre) (heta : 0 < eta)
    (hCsubF0 : 0 < CsubF) (hCBF0 : 0 < CBF)
    (hcSc0 : 0 < cSc) (hcSc48 : cSc ≤ 1 / 48)
    (hdelta0def : delta0 = (d : ℝ) * bootstrapTiltPolynomial cSc ((d : ℝ) * cSc))
    (hdelta0_ninth : delta0 ≤ 1 / 9)
    (hdelta0_gs3 : (128 * Abar ^ 2) ^ 3 * delta0 ≤ 1 / 3)
    (hdelta0pos : 0 < delta0)
    (hcburn0 : 0 ≤ cburn) (hcW0 : 0 ≤ cW) (hCBrev0 : 0 < CBrev)
    (hcC6uP : ∀ base : ℝ, 3 ≤ base → C6 ≤ base ^ cC6u)
    (hcC8uP : ∀ base : ℝ, 3 ≤ base → C8 ≤ base ^ cC8u)
    (hfamP : ∀ {g : ℝ}, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
        {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ},
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        HCPoly.Frozen.IsStationaryLaw P →
      ∀ {lAl : ℤ}, (kZero d : ℤ) ≤ lAl →
      ∀ {Cd : ℝ}, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
      ∀ {mAl : Mat d}, mAl.PosDef →
      IsRoundedGrid lAl (roundedGrid lAl mAl) →
      ∀ {Gacc : ℕ},
        ‖roundedGrid lAl mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc →
      boundaryConst Cd g mAl ≤ (3 : ℝ) ^ (Gacc + 1 : ℕ) →
      (∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
        ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
          BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
            (blockScale
              ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * ((Gacc + 1 : ℕ) : ℝ) -
                (k : ℝ)) 0)) E)) →
      ∀ {rho : ℝ}, 0 < rho → rho < 1 → g ≤ rho →
      ∀ {sKw : ℤ}, growthBar K ≤ (3 : ℝ) ^ sKw →
      ∀ {delta : ℝ}, 0 ≤ delta → delta ≤ 1 / 9 →
      (∀ k : ℤ, lAl ≤ k → hatExcessAt P (roundedGrid lAl mAl) k ≤ delta) →
      ∀ {Csub : ℝ}, 0 < Csub →
      (∀ (j' p' : ℤ), lAl ≤ j' → j' ≤ p' →
        ∃ Z : Finset (Fin d → ℤ),
          (↑Z : Set (Fin d → ℤ)) =
              {w | adaptedCellCenter (roundedGrid lAl mAl) j' w ∈
                adaptedCell (roundedGrid lAl mAl) p'} ∧
            Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
            lqSchattenSize P 2
                (fun a ↦ blockSub
                  (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                    ∑ w ∈ Z,
                      toFullBlockMat
                        (coarseBlock
                          (adaptedCellAt (roundedGrid lAl mAl) j' w) a)))
                  (adaptedMean P (roundedGrid lAl mAl) j'))
                  (adaptedMean P (roundedGrid lAl mAl) p') ≤
              ENNReal.ofReal
                  (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                lqSchattenSize P 2
                  (fun a ↦ blockSub
                    (coarseBlock (adaptedCell (roundedGrid lAl mAl) j') a)
                    (adaptedMean P (roundedGrid lAl mAl) j'))
                  (adaptedMean P (roundedGrid lAl mAl) p')) →
      ∀ {N₀ ns : ℕ},
        H + 1 ≤ ns →
        lAl ≤ (N₀ : ℤ) + ((ns - H : ℕ) : ℤ) →
        (∀ n : ℕ, ns ≤ n →
          lAl ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n →
          sKw ≤ (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
        (∀ n : ℕ, ns ≤ n → sourceMomentTwo K ≤ (3 : ℝ) ^
          (((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
            ((Gacc + 1 : ℕ) : ℤ) - sKw)) →
      ∀ (M : ℕ),
        (∀ n : ℕ, ns ≤ n →
          1 + 2 * ((2 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
              growthBar K ^ IndependentSums.natTriangular (2 + M) ≤
            (3 : ℝ) ^ ((M : ℝ) *
              ((((N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) +
                ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ))) →
      ∀ {sigma cEnt : ℝ}, refContrast E - 1 ≤ sigma → 0 ≤ sigma → 0 < cEnt →
      nearIdentityDefect cEnt sigma < 1 →
      0 ≤ euclideanEntryThreshold K (cEnt / 2) sKw →
      lAl ≤ isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw →
      (∀ n : ℕ, ns ≤ n →
        isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw ≤
          (N₀ : ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) →
      sourceMomentTwo K ≤ (3 : ℝ) ^
        (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw +
          ((Gacc + 1 : ℕ) : ℤ) - sKw) →
      ∀ {cDeep : ℝ},
      (∀ n : ℕ, ns ≤ n →
        capsDeepConstant Cd g mAl (Gacc + 1)
          (isotropySplit K (cEnt / 2) Cd g mAl (Gacc + 1) sKw)
          ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) ((N₀ : ℤ) + (n : ℤ)) ≤ cDeep) →
      ∀ {R lev : ℝ}, 1 ≤ R → 1 ≤ lev →
      (∀ n : ℕ, ns ≤ n → ∀ᵐ a ∂P,
        Response.diagonalWeakMaximum rho (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ))
            (isotropyReference (nearIdentityDefect cEnt sigma) E) a ≤
          ENNReal.ofReal (R *
            ((max 1 (3 * S a *
              (3 : ℝ) ^ (-((((N₀ : ℤ) + (n : ℤ) : ℤ) : ℝ) +
                ((Gacc + 1 : ℕ) : ℝ))))) ^ g / 2))) →
      ∀ (S0 SStar0 K0 : ℕ → Mat d),
        (∀ m : ℕ, (S0 m).PosDef) → (∀ m : ℕ, (SStar0 m).PosDef) →
        (∀ m : ℕ, toFullBlockMat
            (adaptedMean P (roundedGrid lAl mAl) ((N₀ : ℤ) + (m : ℤ))) =
          schurBlock (S0 m) (SStar0 m) (K0 m)) →
      ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
        adaptedHattedContrast P (roundedGrid lAl mAl)
            ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
          4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
                (16 * (d : ℝ) *
                  (adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                    adaptedHattedContrast P (roundedGrid lAl mAl)
                      ((N₀ : ℤ) + (n : ℤ)))) +
              rowValue2Isotropy d
                (rowSplitConstant (nearIdentityDefect cEnt sigma) cDeep)
                (isotropyKap2 (nearIdentityDefect cEnt sigma))
                (hatExcessAt P (roundedGrid lAl mAl)
                  ((N₀ : ℤ) + (n : ℤ))) +
              weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
                (Response.maxGroupConstantAtLevel lev)
                (Response.energyGoodConstantAtLevel lev) P mAl
                (Response.responseSkew (K0 n))
                (isotropyReference (nearIdentityDefect cEnt sigma) E)
                (loadScaleOfScalar (1 + nearIdentityDefect cEnt sigma)
                  (isotropyKap2 (nearIdentityDefect cEnt sigma))) mAl rho
                (n - ns)
                (R ^ 4 * badMomentMajorant K
                  (((N₀ : ℤ) + (n : ℤ)) +
                    ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw))
                (R / 2) lev ((N₀ : ℤ) + (n : ℤ)) lAl
                (fun j => slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) j)
                (slotFamilyValue d Csub (supplyMscSplit d E) delta
                  (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                  (n - min n m) 0)
                (meanDrop2ValueIsotropy P lAl (1 + nearIdentityDefect cEnt sigma)
                  mAl E (isotropyReference (nearIdentityDefect cEnt sigma) E)
                  ((N₀ : ℤ) + (n : ℤ)))
                (meanSlotConversionAt d (1 + nearIdentityDefect cEnt sigma)
                    (isotropyKap2 (nearIdentityDefect cEnt sigma)) *
                  slotFamilyValue d Csub (supplyMscSplit d E) delta
                    (hatExcess P (roundedGrid lAl mAl) N₀ (min n m))
                    (n - min n m) 0)) +
            2 * ((3 * (d : ℝ) + 4) *
              hatExcessAt P (roundedGrid lAl mAl)
                ((N₀ : ℤ) + (n : ℤ)) ^ 2))
    (hdataP : ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P gB E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, (kZero d : ℤ) ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ mAl : Mat d, mAl.PosDef →
              ∀ sigma delta cStar : ℝ, 0 < sigma →
                (d : ℝ) *
                    bootstrapTiltPolynomial sigma ((d : ℝ) * cStar) ≤ delta →
                  annealedContrast P 0 - 1 ≤ cStar →
                  ∃ gap : ℤ, 1 ≤ gap ∧
                    (3 : ℝ) ^ gap ≤
                      3 * max 1 (CBF * bootstrapAdapterFactor Cd gB K E mAl /
                        sigma) ∧
                    (kZero d : ℤ) ≤ sK + 1 + gap ∧
                    IsRoundedGrid (sK + 1 + gap)
                      (roundedGrid (sK + 1 + gap) mAl) ∧
                    (∀ k : ℤ, sK + 1 + gap ≤ k →
                      hatExcessAt P (roundedGrid (sK + 1 + gap) mAl) k ≤
                        delta) ∧
                    (∀ j' p' : ℤ, sK + 1 + gap ≤ j' → j' ≤ p' →
                      ∃ Z : Finset (Fin d → ℤ),
                        (↑Z : Set (Fin d → ℤ)) =
                            {w | adaptedCellCenter
                              (roundedGrid (sK + 1 + gap) mAl) j' w ∈
                              adaptedCell (roundedGrid (sK + 1 + gap) mAl) p'} ∧
                          Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
                          lqSchattenSize P 2
                              (fun a ↦ blockSub
                                (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                                  ∑ w ∈ Z,
                                    toFullBlockMat
                                      (coarseBlock
                                        (adaptedCellAt
                                          (roundedGrid (sK + 1 + gap) mAl)
                                          j' w) a)))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) j'))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) p') ≤
                            ENNReal.ofReal
                                (CsubF * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                              lqSchattenSize P 2
                                (fun a ↦ blockSub
                                  (coarseBlock
                                    (adaptedCell
                                      (roundedGrid (sK + 1 + gap) mAl) j') a)
                                  (adaptedMean P
                                    (roundedGrid (sK + 1 + gap) mAl) j'))
                                (adaptedMean P
                                  (roundedGrid (sK + 1 + gap) mAl) p')))
    (hcburnP : ∀ (E : BlockMat d) (K : ℝ) (mAl : Mat d),
        1 ≤ aspectRatio E → 1 ≤ K →
        0 ≤ kappaRef E → kappaRef E ≤ 1 + 6 * cSc →
        witnessEccentricity mAl ≤ aspectRatio E →
        0 ≤ (1 + K ^ 2) ^ gB * euclideanReferenceRatio Cdv gB K E →
        ∀ sK gap : ℤ,
          (3 : ℝ) ^ sK ≤ (3 : ℝ) ^ ((kZero d : ℕ) : ℤ) * (3 * growthBar K) →
          (3 : ℝ) ^ gap ≤
            3 * max 1 ((9 / 8 * CBF) * bootstrapAdapterFactor Cdv gB K E mAl / cSc) →
          (3 : ℝ) ^ (sK + 1 + gap) ≤
            Real.rpow (2 + aspectRatio E * K) cburn)
    (hcWP : ∀ K Pi : ℝ, 1 < K → 1 ≤ Pi →
        ∀ n : ℕ, K ^ (n + 2) ≤ 2 * K ^ 3 →
        burnSplitThreshold d K
            (burnSplitAnchor d 1 K (burnSplitDepth d Cdv gB Pi))
            (burnSplitAnchor d 1 K (burnSplitDepth d Cdv gB Pi) +
              ((2 * burnSplitDepth d Cdv gB Pi : ℕ) : ℤ)) *
          K * K ^ (n + 1) ≤ Real.rpow (2 + Pi * K) cW)
    (hCBrevP : ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P gB E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ mAl : Mat d, mAl.PosDef →
              ∀ G : ℕ, ‖roundedGrid l mAl‖ * Real.sqrt d ≤ (3 : ℝ) ^ G →
                ∀ n₀ mOut : ℕ,
                  0 < Prop42Scalar.correctedTiltScale n₀ mOut →
                  Prop42Scalar.correctedTiltScale n₀ mOut < mOut →
                  l ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) →
                  0 ≤ (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ) +
                    (G : ℤ) - 1 - sK →
                  ∀ A : ℝ, CBrev * reverseAdapterFactor Cd gB K E mAl G ≤ A →
                    A * Real.rpow (3 : ℝ)
                        (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                          ℕ) : ℝ)) ≤ 1 →
                    ∃ c : ℝ, 0 ≤ c ∧
                      BlockMatLoewnerLE
                        (blockSub (annealedBlock P (centeredCube d (mOut : ℤ)))
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)))
                        (blockScale c E) ∧
                      c * blockSize E
                          (adaptedMean P (roundedGrid l mAl)
                            (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ)) ≤
                        1 ∧
                      (9 / 2 : ℝ) *
                          (c * blockSize E
                            (adaptedMean P (roundedGrid l mAl)
                              (Prop42Scalar.correctedTiltScale n₀ mOut : ℤ))) ≤
                        (9 / 2 : ℝ) * A * Real.rpow (3 : ℝ)
                          (-((mOut - Prop42Scalar.correctedTiltScale n₀ mOut :
                            ℕ) : ℝ)))
    (hgB : gB ∈ Set.Ico (0 : ℝ) 1)
    (hcIso0 : (0 : ℝ) ≤ cIso)
    (hcIso1 : cIso < 1)
    (hkap1 : (1 : ℝ) ≤ isotropyKap2 cIso)
    (hR1 : (1 : ℝ) ≤ R)
    (hAbar1 : (1 : ℝ) ≤ Abar)
    (_hgB0 : (0 : ℝ) ≤ gB)
    (hgB1 : gB < 1)
    (hrho0 : 0 < contrastRho gB)
    (hrho1 : contrastRho gB < 1)
    (hgBrho : gB ≤ contrastRho gB)
    (halphaB : (0 : ℝ) < recursionAlpha gB)
    (hbeta20 : (0 : ℝ) < beta2)
    (hrateBar0 : 0 < rateBar)
    (hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv)
    (hCdv1 : (1 : ℝ) ≤ Cdv)
    (hzetagB : (1 : ℝ) ≤ zetaG gB)
    (hiexp0 : 0 < iexp)
    (hcns0 : 0 ≤ cns)
    (hct20 : 0 ≤ ct2)
    (hCprefCap0 : 0 ≤ CprefCap)
    (hsigma0 : (0 : ℝ) ≤ 1 / 48)
    (hcEnt0 : (0 : ℝ) < 1 / 8)
    (hcF0 : (0 : ℝ) ≤ 1 + cIso)
    (hkap0 : (0 : ℝ) ≤ isotropyKap2 cIso)
    (hLdef : L = isotropyLoadScale cIso (isotropyKap2 cIso))
    (hM₀def : M₀ = isotropyMetricFactor cIso (1 / 48))
    (hRdef : R = 4 / (1 + cIso))
    (hMabsdef : Mabs = absorbedNormalizer 16 16 (designNormalizer R M₀))
    (hconvdef : conv = meanSlotConversionAt d (1 + cIso) (isotropyKap2 cIso))
    (hgBdef : gB = (1 + g) / 2)
    (hAbardef : Abar = fusionRecursionConstantIsotropySharp d Cpre eta H
    (absorbedNormalizer 16 16 (designNormalizer R M₀))
    (isotropyLoadScale cIso (isotropyKap2 cIso)) gB
    (rowSplitConstant cIso 1) (isotropyKap2 cIso) 4 1
    (slotCVsum d) (cVmConstant d conv))
    (hbeta2def : beta2 = min (1 / 2) (contrastAlpha gB))
    (hMscBardef : MscBar = (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * ((9 / 8 : ℝ) * 4) * (2 * (4 : ℝ)) *
      Real.sqrt 2)
    (hCvBardef : CvBar = vsumSourceConstant d CsubF MscBar 1)
    (hSsrc0bardef : Ssrc0bar = 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed Mabs L (contrastRho gB) CvBar (conv * CvBar)
      0 ^ 2)
    (hcAbardef : cAbar = ⌈Real.logb 3 (24 * Abar) / recursionAlpha gB⌉₊)
    (hrateBardef : rateBar = linRate Abar (recursionAlpha gB) 1 1 (2 * beta2) cAbar Ssrc0bar)
    (halphadef : alpha = rateBar / 2)
    (hiexpdef : iexp = (1 - gB)⁻¹)
    (hCdvZdef : CdvZ = Cdv * zetaG gB)
    (hC5def : C5 = 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d))
    (hC6def : C6 = 31104 * ((32 * CdvZ * C5) ^ iexp))
    (hc6def : c6 = (2 + cW) * cburn + 3 * cW + 2 * iexp)
    (hCentryCapdef : CentryCap = 2 * cC6u + 2 * c6)
    (hCEdef : CE = 8100 * 3 ^ (3 * H) * C5 ^ 4)
    (hCFdef : CF = max 1 (CBrev * (45 / 2) * CdvZ * C5))
    (hcFdef : cF = 4 + 3 * cW)
    (hCnsCdef : CnsC = (3 : ℝ) ^ (H + 1) * 624 * CE * (3 * CF ^ rateBar⁻¹) * 3)
    (hcnsdef : cns = 4 * cW + 4 + cF / rateBar)
    (hCt1def : Ct1 = 3 / delta0 ^ 2)
    (hCXdef : CX = 1 +
    (6 * weakCoefficient d Cpre *
    ((16 * absorbedNormalizer 16 16 (designNormalizer R M₀) / (1 - contrastRho gB)) *
    (Real.sqrt 2 * Real.sqrt (isotropyLoadScale cIso (isotropyKap2 cIso) + 1) *
    R * 6)) ^ 2) * 65536)
    (hct2def : ct2 = 16 * cW / (2 * beta2))
    (hCt2udef : Ct2u = (CX / delta0 ^ 2) ^ (2 * beta2)⁻¹)
    (hC7def : C7 = Ct1 * 3 * Ct2u)
    (hC8def : C8 = 36 * CnsC ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹)
    (hCprefCapdef : CprefCap = cC8u + cns / 2 + ct2 / 4)
    (hCdelaySdef : CdelayS = CentryCap + (1 + CprefCap / (rateBar / 2)))
        (hcIsodef : cIso = nearIdentityDefect (1 / 8) (1 / 48))
    : (∀ (cStar gBase : ℝ) (Pbase : Measure (CoeffSpace d)) (Ebase : BlockMat d) (Ψbase
    : ℝ → ℝ) (Kbase : ℝ) (Sbase : CoeffSpace d → ℝ), cStar ∈ Set.Ioc 0 cSc → gBase = (1 + g) / 2
    → MeasureTheory.IsProbabilityMeasure Pbase → HCPoly.Frozen.IsStationaryLaw Pbase →
    HCPoly.Frozen.IsUnitRangeLaw Pbase → HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase
    Ψbase Kbase Sbase → annealedContrast Pbase 0 - 1 ≤ cStar → blockContrast Ebase ≤ 1 + cSc → ∃
    m0 : ℕ, (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ CdelayS ∧ ∀ j : ℕ, annealedContrast
    Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ))) := by
  classical
  have hbody : ∀ (cStar gBase : ℝ) (Pbase : Measure (CoeffSpace d)) (Ebase : BlockMat d) (Ψbase
    : ℝ → ℝ) (Kbase : ℝ) (Sbase : CoeffSpace d → ℝ), cStar ∈ Set.Ioc 0 cSc → gBase = (1 + g) / 2
    → MeasureTheory.IsProbabilityMeasure Pbase → HCPoly.Frozen.IsStationaryLaw Pbase →
    HCPoly.Frozen.IsUnitRangeLaw Pbase → HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase
    Ψbase Kbase Sbase → annealedContrast Pbase 0 - 1 ≤ cStar → blockContrast Ebase ≤ 1 + cSc → ∃
    m0 : ℕ, (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ CdelayS ∧ ∀ j : ℕ, annealedContrast
    Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
    intro cStar gBase Pbase Ebase Ψbase Kbase Sbase hcStar hgBase hprob
      hstat hunit hdag hann hblock
    have := hprob
    subst hgBase
    rw [← hgBdef] at hdag
    set base : ℝ := 2 + aspectRatio Ebase * Kbase with hbasedef
    obtain ⟨haspect1, hKbase1, haK1, hbase3, hEsym, hEpd, hEfullpd, hskew⟩ :=
      endpoint_reference_ellipticity_bounds d hdag
    let Erec : BlockMat d := Response.skewBlockCongr (canonicalShear Ebase) Ebase
    let mrec : Mat d := canonicalMetric Erec
    obtain ⟨hdagR, hrecE', hmetE', hsharpE'⟩ := recentered_certificates hdag hEfullpd hskew
    obtain ⟨hstat', hunit', hE'sym, hE'pd, hbS, hfin1, hpdAnn⟩ :=
      endpoint_recentered_integrability d hcIso0 hdag hstat hunit hskew hdagR
    obtain ⟨hannR, hsigE, hformE, hbcE', hblock', hrefE', hsharpBase, hkap1E, hkapE', hmAlpd,
      hmetE'2, heccA, hmAlpd', heccA'⟩ :=
      endpoint_recentered_contrast_geometry d
        hcSc48 hdag hann hblock hskew hdagR hmetE' hEsym hEpd hEfullpd hfin1 hpdAnn
    have hrefE'48 := hrefE'.trans hcSc48
    have hdagN := coarseEllipticityDagger_normalizedGauge hdagR
    obtain ⟨hΨ1, hΨn1, hD1, hw⟩ :=
      endpoint_normalized_burn_window d hd hgB hCdvle hdag
        haspect1
    obtain ⟨nW, hnW2, hnWcap⟩ := exists_minimal_two_pow hKbase1
    have hnn : 2 * normalizedGauge Ψbase 1 ≤ Kbase ^ nW := by
      rw [hΨn1]
      simpa using hnW2
    have hdag' := coarseEllipticityDagger_burnSplitSource hstat' hdagN
      (le_refl 1) hw hnn
    have hK'cap : burnSplitThreshold d Kbase (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB
      (aspectRatio Ebase))) (burnSplitAnchor d 1 Kbase (burnSplitDepth d Cdv gB (aspectRatio
      Ebase)) + ((2 * burnSplitDepth d Cdv gB (aspectRatio Ebase) : ℕ) : ℤ)) * Kbase * Kbase ^
      (nW + 1) ≤ Real.rpow base cW := hcWP Kbase (aspectRatio Ebase) hKbase1 haspect1 nW hnWcap
    set DD : ℕ := burnSplitDepth d Cdv gB (aspectRatio Ebase) with hDDdef
    set K' : ℝ := burnSplitThreshold d Kbase
        (burnSplitAnchor d 1 Kbase DD)
        (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) *
      Kbase * Kbase ^ (nW + 1) with hK'def
    obtain ⟨hgK2, hthr1, hK'1, hm21, hrpowcW1, hgK'cap⟩ :=
      endpoint_burned_growth_bounds d hcW0 hK'cap hKbase1 hbase3
    obtain ⟨sKfd, hsKfdF, hsKfdG, hsKfdC⟩ := exists_source_scale_minimal K' (floor := (kZero d : ℤ))
        (Int.natCast_nonneg _)
    have hbtp :=
      endpoint_bootstrap_smallness_bound d hcSc0 hdelta0def hcStar
    obtain ⟨gap, hgap1, hgapcap, hkZlAl, hgrid, hfloorAt, hsubdiv⟩ := hdataP _ _ _ _ _
      (isProbabilityMeasure_recenteredLaw Pbase hskew)
        hstat' hunit' hdag' Cdv hCdvle sKfd hsKfdF hsKfdG _ hmAlpd'
        cSc delta0 cStar hcSc0 hbtp hannR
    set lAl : ℤ := sKfd + 1 + gap with hlAldef
    have hlAl0 : (0 : ℤ) ≤ lAl := le_trans (Int.natCast_nonneg _) hkZlAl
    have hsKfdlAl : sKfd ≤ lAl := by
      rw [hlAldef]
      omega
    have hkapBase6 : kappaRef Ebase ≤ 1 + 6 * cSc := kappaRef_le_of_refContrast_le hdag
        (by
          change blockContrast Ebase - 1 ≤ cSc
          linarith only [hblock])
    obtain ⟨hCdv0, hm1nn, hmb0, hpowK'0, hfacnnE, hgapcap', hlAlcap0, hbase0, haspb, hbpos,
      hK'capP, hbaseK', hlAlcap⟩ :=
      endpoint_adapted_entry_scale_cost d hCBF0 hcSc0 hcburn0 hcW0 hcburnP hCdv1 hzetagB hgapcap
        hsKfdC
        hK'cap hkapBase6 haspect1 hKbase1 hbase3 hkap1E hkapE' hmetE'2 heccA hK'1 hlAldef
    obtain ⟨sKw, hsKwF, hsKwG, hsKwC⟩ := exists_source_scale_minimal K' (floor := lAl) hlAl0
    have hsKw0 := hlAl0.trans hsKwF
    set Gacc : ℕ := DD - 1 with hGaccdef
    obtain ⟨hGaccD, hcge⟩ := pred_depth_accounts DD Gacc
      (canonicalGridEnlargement d (aspectRatio Ebase)) hD1 hGaccdef
      (succ_canonicalGridEnlargement_le_burnSplitDepth hd hCdvle hgB haspect1)
    have hqnorm : ‖roundedGrid lAl mrec‖ * Real.sqrt d ≤ (3 : ℝ) ^ Gacc := by
      refine le_trans (norm_roundedGrid_mul_sqrt_le_canonicalGridEnlargement
        hd hkZlAl hmAlpd' haspect1 heccA') ?_
      exact three_pow_mono hcge
    have hbC := three_pow_reindex hGaccD
      (boundaryConst_le_three_pow_burnSplitDepth hd hCdv1 hgB haspect1 heccA')
    let split : ℤ := isotropySplit K' (1 / 8 / 2) Cdv gB
      mrec
      (Gacc + 1) sKw
    have hsKwsplit := le_isotropySplit (d := d) K' (1 / 8 / 2)
      Cdv gB mrec (Gacc + 1) sKw
    have hm2split := sourceMomentTwo_le_isotropySplit_tail (d := d) K' Cdv gB mrec (Gacc + 1) sKw
    have hkEnt0 : (0 : ℤ) ≤ euclideanEntryThreshold K' (1 / 8 / 2) sKw :=
      zero_le_euclideanEntryThreshold_of_nonneg K' (1 / 8 / 2) sKw hsKw0
    have hcarr := isotropy_carriers_of_isotropySplit (d := d)
      (P := recenteredLaw Pbase hskew)
      (E := Erec)
      (K := K') (l := lAl) (Cd := Cdv)
      (nu := mrec)
      (Gacc := Gacc) (sK := sKw) (sigma := 1 / 48) (cEnt := 1 / 8)
      hd hgB hdag' hstat' hkZlAl hCdvle hmAlpd' hqnorm hsKwG hrefE'48
      hsigma0 hcEnt0 (by simpa only [hcIsodef] using hcIso1) hkEnt0 hm2split
    rw [← hcIsodef] at hcarr
    have hlAlsplit := le_of_le_add_two hsKwF hsKwsplit
    obtain ⟨N₀, hN₀Z, hlAlN₀⟩ := exists_nat_eq_with_lower lAl split hlAl0 hlAlsplit
    let qrec : Mat d := roundedGrid lAl mrec
    obtain ⟨hqpd, hfin', hpdM⟩ :=
      endpoint_grid_mean_integrability d hskew hdagR hkZlAl hnn
        hstat' hmAlpd' hw
    obtain ⟨S0f, SStar0f, K0f, hS0f, hStar0f, hformf⟩ := exists_schur_families hgrid hfin' N₀
    obtain ⟨henvC, hcompC⟩ := pair_at_nat_add split N₀ hN₀Z hcarr
    obtain ⟨hM₀', hgK'2, hgK'0⟩ :=
      endpoint_metric_and_floor_certificates d hcSc48 hcF0 hkap0
        hM₀def hskew hdagR hfloorAt hlAlN₀ hrefE'
    obtain ⟨nsBv, hnsBvLow, hnsBvCap⟩ := exists_three_pow_sandwich
        (one_le_thirteen_mul_pow_four hgK'2)
    obtain ⟨nsEv, hnsEvH, hnsEvKill, hnsEvCap⟩ := exists_deep_kill_generation H DD
    let Eband : BlockMat d := Erec
    let adapter : ℝ := CBrev * reverseAdapterFactor Cdv gB K' Eband
      (canonicalMetric Eband) Gacc
    let rAFv : ℝ := max 1 adapter
    have hrAFv1 : (1 : ℝ) ≤ rAFv := le_max_left _ _
    obtain ⟨nsFv, hnsFvLow, hnsFvCap⟩ := exists_rate_generation hrAFv1 hrateBar0
    obtain ⟨ns, hnsH, hnsB, hnsE, hnsF, hnsSum⟩ := exists_generation_max H nsBv nsEv nsFv
    have hgB0 : (0 : ℝ) ≤ gB := hgB.1
    have hcapsDeep := fun (n : ℕ) (hn : ns ≤ n) =>
      capsDeepConstant_le_one_of_kill Cdv gB
        mrec
        Gacc H DD n split N₀ hCdv1 hgB1 hmAlpd' hGaccD hN₀Z hbC
        ((Nat.le_succ H).trans (hnsH.trans hn))
        (deepKill_mono H DD nsEv n (hnsE.trans hn) hnsEvKill)
    obtain ⟨hlAlnsH, hlAlgen, hsKwgen, hsplitgen, hBgen⟩ := generation_index_bounds lAl sKw
      split N₀ ns H nsBv Gacc
        hlAlN₀ hsKwsplit hN₀Z hnsB
    have hm2gen : ∀ n : ℕ, ns ≤ n → sourceMomentTwo K' ≤ (3 : ℝ) ^ (((N₀ : ℤ) + (n : ℤ) - ((n -
      ns : ℕ) : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - sKw) := by
      exact zpow_offset_mono (x := sourceMomentTwo K') (split := split)
        (s := sKw) (G := Gacc) (N₀ := N₀) (ns := ns) hm2split hsplitgen
    have hMcond : ∀ n : ℕ, ns ≤ n → 1 + 2 * ((2 + 1 : ℕ) : ℝ) * (1 + Real.log (growthBar K')) *
      growthBar K' ^ IndependentSums.natTriangular (2 + 1) ≤ (3 : ℝ) ^ (((1 : ℕ) : ℝ) * ((((N₀ :
      ℤ) + (n : ℤ) - ((n - ns : ℕ) : ℤ)) + ((Gacc + 1 : ℕ) : ℤ) - 1 - sKw : ℤ) : ℝ)) := by
      intro n hn
      exact growth_row_bound_of_generation hgK'2 hnsBvLow (hBgen n hn)
    have hdepth : (burnSplitAnchor d 1 Kbase DD + ((2 * DD : ℕ) : ℤ)) - burnSplitAnchor d 1
      Kbase DD = ((2 * DD : ℕ) : ℤ) := by omega
    obtain ⟨hQenvP, hbC', henvMaxP⟩ :=
      endpoint_burned_maximum_envelope d hd
        (lAl := lAl) (Gacc := Gacc) (sKfd := sKfd) (gap := gap)
        hgB hcIso0 hgBrho hCdvle hCdv1 hskew
        hdagR hlAldef hkZlAl hGaccdef hGaccD hw hqnorm hqpd hdepth
        haspect1 hstat' hmAlpd' heccA' hRdef
    exact endpoint_decay_from_corrected_cadence d hd
      (g := gB) (lAl := lAl) (Gacc := Gacc) (sKfd := sKfd) (gap := gap)
      hCpre1 heta
      hCsubF0 hcSc48 hdelta0_ninth hdelta0_gs3 hdelta0pos hcW0 hCBrev0 hcC6uP hcC8uP hfamP hCBrevP
      hgB hcIso0 hcIso1 hkap1 hR1 hAbar1 hgB1 hrho0 hrho1 hgBrho halphaB hbeta20 hrateBar0 hCdvle
      hCdv1 hzetagB hiexp0 hcns0 hct20 hCprefCap0 hLdef hMabsdef hconvdef hAbardef hbeta2def
      hMscBardef hCvBardef hSsrc0bardef hcAbardef hrateBardef hiexpdef hCdvZdef hC5def hC6def hc6def
      hCentryCapdef hCEdef hCFdef hcFdef hCnsCdef hcnsdef hCt1def hCXdef hct2def hCt2udef hC7def
      hC8def hCprefCapdef hcStar hlAldef hGaccdef
      hskew hdag hdagR hsharpE' hS0f hStar0f hformf hrecE' hgrid hkZlAl hlAlN₀
      hN₀Z hGaccD hsKwF hsKwG hsKwC hnsH hnsE hnsF hnsSum hnsBvCap hnsEvCap hnsEvKill hnsFvLow
      hnsFvCap hlAlnsH hlAlgen hsKwgen hsplitgen hfloorAt henvC hcompC hsubdiv hw hnn hlAl0 hqnorm
      hkEnt0 hfin' hM₀' hgK'2 hm2gen hMcond haspect1 hbase3 hstat' hunit' hE'sym hE'pd hbS hannR
      hrefE' hkapE' hmAlpd' heccA' hK'1 hm21 hrpowcW1 hgK'cap haspb hbpos hlAlcap hQenvP henvMaxP
      hCprefCap0 hCdelaySdef halphadef hcIsodef
  exact hbody

theorem endpoint_hcore_body_corrected_core (d : ℕ) (hd : 2 ≤ d) : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1
  → ∃ cSc : ℝ, 0 < cSc ∧ ∃ alpha Cdelay : ℝ, 0 < alpha ∧ 0 ≤ Cdelay ∧ ∀ (cStar gBase : ℝ) (Pbase
  : Measure (CoeffSpace d)) (Ebase : BlockMat d) (Ψbase : ℝ → ℝ) (Kbase : ℝ) (Sbase : CoeffSpace
  d → ℝ), cStar ∈ Set.Ioc 0 cSc → gBase = (1 + g) / 2 → MeasureTheory.IsProbabilityMeasure Pbase
  → HCPoly.Frozen.IsStationaryLaw Pbase → HCPoly.Frozen.IsUnitRangeLaw Pbase →
  HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase Ψbase Kbase Sbase → annealedContrast
  Pbase 0 - 1 ≤ cStar → blockContrast Ebase ≤ 1 + cSc → ∃ m0 : ℕ, (3 : ℝ) ^ m0 ≤ (2 +
  aspectRatio Ebase * Kbase) ^ Cdelay ∧ ∀ j : ℕ, annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤
  (3 : ℝ) ^ (-alpha * (j : ℝ)) := by
  intro g hg
  have : NeZero d := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨Cpre, H, eta, hCpre1, hH4, heta, hfamP⟩ :=
    exists_one_step_family_at_isotropy_var_at_level_conv_family_min d hd
  have hgB : (1 + g) / 2 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith only [hg.1], by linarith only [hg.2]⟩
  obtain ⟨CsubF, CBF, hCsubF0, hCBF0, hdataP⟩ := exists_endpoint_frozen_data_minimal d hd ((1 +
    g) / 2) hgB
  set cIso : ℝ := nearIdentityDefect (1 / 8) (1 / 48) with hcIsodef
  have hcIsoval : cIso = 17 / 64 := by
    rw [hcIsodef, nearIdentityDefect]
    norm_num
  have hcIso0 : (0 : ℝ) ≤ cIso := by rw [hcIsoval]; norm_num
  have hcIso1 : cIso < 1 := by rw [hcIsoval]; norm_num
  set kap : ℝ := isotropyKap2 cIso with hkapdef
  have hkap1 : (1 : ℝ) ≤ kap := one_le_isotropyKap2 hcIso0 hcIso1
  set L : ℝ := isotropyLoadScale cIso kap with hLdef
  set M₀ : ℝ := isotropyMetricFactor cIso (1 / 48) with hM₀def
  set R : ℝ := 4 / (1 + cIso) with hRdef
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hRdef, hcIsoval]
    norm_num
  set Mabs : ℝ := absorbedNormalizer 16 16 (designNormalizer R M₀)
    with hMabsdef
  set cRow : ℝ := rowSplitConstant cIso 1 with hcRowdef
  set conv : ℝ := meanSlotConversionAt d (1 + cIso) kap with hconvdef
  set gB : ℝ := (1 + g) / 2 with hgBdef
  set Abar : ℝ := fusionRecursionConstantIsotropySharp d Cpre eta H Mabs L gB
    cRow kap 4 1 (slotCVsum d) (cVmConstant d conv) with hAbardef
  have hAbar1 : (1 : ℝ) ≤ Abar := one_le_fusionRecursionConstantIsotropySharp d Cpre eta H Mabs L gB
      cRow kap 4 1 (slotCVsum d) (cVmConstant d conv)
  have hgB0 : (0 : ℝ) ≤ gB := hgB.1
  have hgB1 : gB < 1 := hgB.2
  have hrho0 : 0 < contrastRho gB := contrastRho_pos hgB.1
  have hrho1 : contrastRho gB < 1 := contrastRho_lt_one hgB1
  have hgBrho : gB ≤ contrastRho gB := le_contrastRho hgB1
  have halphaB : (0 : ℝ) < recursionAlpha gB := recursionAlpha_pos hgB1
  set beta2 : ℝ := min (1 / 2) (contrastAlpha gB) with hbeta2def
  have hbeta20 : (0 : ℝ) < beta2 := by
    rw [hbeta2def]
    refine lt_min (by norm_num) ?_
    rw [contrastAlpha]
    linarith only [hgB1]
  set MscBar : ℝ := (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * ((9 / 8 : ℝ) * 4) * (2 * (4 : ℝ)) *
      Real.sqrt 2 with hMscBardef
  set CvBar : ℝ := vsumSourceConstant d CsubF MscBar 1 with hCvBardef
  set Ssrc0bar : ℝ := 1 + 6 * weakCoefficient d Cpre *
    weakSourceGroupSummed Mabs L (contrastRho gB) CvBar (conv * CvBar)
      0 ^ 2 with hSsrc0bardef
  have hSsrc0bar1 : (1 : ℝ) ≤ Ssrc0bar := by
    rw [hSsrc0bardef]
    have hwC0 : 0 ≤ weakCoefficient d Cpre := weakCoefficient_nonneg d (by linarith only [hCpre1])
    nlinarith only [hwC0, sq_nonneg (weakSourceGroupSummed Mabs L
      (contrastRho gB) CvBar (conv * CvBar) 0)]
  set cAbar : ℕ := ⌈Real.logb 3 (24 * Abar) / recursionAlpha gB⌉₊
    with hcAbardef
  set rateBar : ℝ := linRate Abar (recursionAlpha gB) 1 1 (2 * beta2) cAbar Ssrc0bar
    with hrateBardef
  have hrateBar0 : 0 < rateBar := by
    rw [hrateBardef]
    exact linRate_pos hAbar1 halphaB (by norm_num) (by norm_num)
      (by linarith only [hbeta20]) hSsrc0bar1
  obtain ⟨cSc, delta0, hcSc0, hcSc48, hdelta0def, hdelta0_ninth, hdelta0_gs3, hdelta0pos⟩ :=
    exists_endpoint_smallness d hd hAbar1
  set alpha : ℝ := rateBar / 2 with halphadef
  have halpha0 : 0 < alpha := by
    rw [halphadef]
    linarith only [hrateBar0]
  set Cdv : ℝ := max 1 (12 * (d : ℝ) * Real.sqrt d) with hCdvdef
  have hCdvle : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cdv := le_of_eq hCdvdef.symm
  have hCdv1 : (1 : ℝ) ≤ Cdv := (le_max_left _ _).trans hCdvle
  have hgB1 : gB < 1 := hgB.2
  have hzetagB : (1 : ℝ) ≤ zetaG gB := by
    have hlt : (3 : ℝ) ^ (-(1 - gB)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith only [hgB1])
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 - gB)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [zetaG]
    rw [le_inv_comm₀ (by norm_num) (by linarith only [hlt, hpos])]
    linarith only [hpos]
  obtain ⟨cburn, hcburn0, hcburnP⟩ := exists_burnIn_exponent_canonical d
    Cdv gB cSc (9 / 8 * CBF) (by linarith only [hCdv1])
    (by linarith only [hgB1]) (by linarith only [hzetagB])
    hcSc0 (by linarith only [hCBF0])
  obtain ⟨cW, hcW0, hcWP⟩ := exists_burnSplit_witness_exponent d hd
    hCdvle hgB
  obtain ⟨CBrev, hCBrev0, hCBrevP⟩ := exists_corrected_tilt_transfer_inputs d hd gB hgB
  set iexp : ℝ := (1 - gB)⁻¹ with hiexpdef
  have hiexp0 : 0 < iexp := by
    rw [hiexpdef]
    have : 0 < 1 - gB := by linarith only [hgB1]
    positivity
  set CdvZ : ℝ := Cdv * zetaG gB with hCdvZdef
  set C5 : ℝ := 3 * ((100 / 99) * Cdv * zetaG gB * Real.sqrt d)
    with hC5def
  set C6 : ℝ := 31104 * ((32 * CdvZ * C5) ^ iexp) with hC6def
  set c6 : ℝ := (2 + cW) * cburn + 3 * cW + 2 * iexp with hc6def
  have hc60 : 0 ≤ c6 := by
    rw [hc6def]
    have h1 : 0 ≤ (2 + cW) * cburn := by positivity
    linarith only [h1, hcW0, hiexp0.le]
  obtain ⟨cC6u, hcC6u0, hcC6uP⟩ := exists_rpow_ge_uniform C6
  set CentryCap : ℝ := 2 * cC6u + 2 * c6 with hCentryCapdef
  have hCentryCap0 : 0 ≤ CentryCap := by
    rw [hCentryCapdef]
    linarith only [hcC6u0, hc60]
  set CE : ℝ := 8100 * 3 ^ (3 * H) * C5 ^ 4 with hCEdef
  set CF : ℝ := max 1 (CBrev * (45 / 2) * CdvZ * C5) with hCFdef
  set cF : ℝ := 4 + 3 * cW with hcFdef
  set CnsC : ℝ := (3 : ℝ) ^ (H + 1) * 624 * CE * (3 * CF ^ rateBar⁻¹) * 3 with hCnsCdef
  set cns : ℝ := 4 * cW + 4 + cF / rateBar with hcnsdef
  have hcns0 : 0 ≤ cns := by
    rw [hcnsdef, hcFdef]
    have h1 : 0 ≤ (4 + 3 * cW) / rateBar := by positivity
    linarith only [hcW0, h1]
  set Ct1 : ℝ := 3 / delta0 ^ 2 with hCt1def
  set CX : ℝ := 1 +
    (6 * weakCoefficient d Cpre *
      ((16 * Mabs / (1 - contrastRho gB)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * R * 6)) ^ 2) * 65536
    with hCXdef
  set ct2 : ℝ := 16 * cW / (2 * beta2) with hct2def
  have hct20 : 0 ≤ ct2 := by
    rw [hct2def]
    positivity
  set Ct2u : ℝ := (CX / delta0 ^ 2) ^ (2 * beta2)⁻¹ with hCt2udef
  set C7 : ℝ := Ct1 * 3 * Ct2u with hC7def
  set C8 : ℝ := 36 * CnsC ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ with hC8def
  obtain ⟨cC8u, hcC8u0, hcC8uP⟩ := exists_rpow_ge_uniform C8
  set CprefCap : ℝ := cC8u + cns / 2 + ct2 / 4 with hCprefCapdef
  have hCprefCap0 : 0 ≤ CprefCap := by
    rw [hCprefCapdef]
    linarith only [hcC8u0, hcns0, hct20]
  set CdelayS : ℝ := CentryCap + (1 + CprefCap / (rateBar / 2))
    with hCdelaySdef
  have hCdelayS0 : 0 ≤ CdelayS := by
    rw [hCdelaySdef]
    have h1 : 0 ≤ CprefCap / (rateBar / 2) := by positivity
    linarith only [hCentryCap0, h1]
  have hsigma0 : (0 : ℝ) ≤ 1 / 48 := by norm_num
  have hcEnt0 : (0 : ℝ) < 1 / 8 := by norm_num
  have hcF0 : (0 : ℝ) ≤ 1 + cIso := by linarith only [hcIso0]
  have hkap0 : (0 : ℝ) ≤ isotropyKap2 cIso := zero_le_one.trans (one_le_isotropyKap2 hcIso0 hcIso1)
  have hbody :=
    corrected_endpoint_decay_of_uniform_parameters d hd hCpre1 heta hCsubF0 hCBF0
      hcSc0 hcSc48 hdelta0def hdelta0_ninth hdelta0_gs3 hdelta0pos hcburn0 hcW0 hCBrev0 hcC6uP
      hcC8uP hfamP hdataP hcburnP hcWP hCBrevP hgB hcIso0 hcIso1 hkap1 hR1 hAbar1 hgB0 hgB1 hrho0
      hrho1 hgBrho halphaB hbeta20 hrateBar0 hCdvle hCdv1 hzetagB hiexp0 hcns0 hct20 hCprefCap0
      hsigma0 hcEnt0 hcF0 hkap0 hLdef hM₀def hRdef hMabsdef hconvdef hgBdef hAbardef
      hbeta2def hMscBardef
      hCvBardef hSsrc0bardef hcAbardef hrateBardef halphadef hiexpdef hCdvZdef hC5def hC6def hc6def
      hCentryCapdef hCEdef hCFdef hcFdef hCnsCdef hcnsdef hCt1def hCXdef hct2def hCt2udef hC7def
      hC8def hCprefCapdef hCdelaySdef hcIsodef
  exact ⟨cSc, hcSc0, alpha, CdelayS, halpha0, hCdelayS0, hbody⟩
end
