/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTerm
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BadSetDefinitions

/-!
# WaveTailProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A fixed-profile wave-tail estimate

This internal analytic provider collapses the explicit geometric series in
`waveTailGainScale` at the manuscript's fixed `b = 2⁻²⁰` and `sigma₂ = 2 /
sigma`.  It proves a dimension-only `C(d) sigma⁻¹ 3^{-(d/8)k₀}` scale used by a
proposed wave endpoint.
-/


namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

private theorem hsepTailConst_le_half {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    hsepTailConst sigma bfaProfileB ≤ hsepTailConst (1 / 2) bfaProfileB := by
  have hsigma1 : sigma < 1 := hsigma.trans_lt (by norm_num)
  have hbase :
      (1 - (1 / 2 : ℝ)) * bfaProfileB * Real.log 3 ≤
        (1 - sigma) * bfaProfileB * Real.log 3 := by
    have hbLog : 0 ≤ bfaProfileB * Real.log 3 :=
      mul_nonneg bfaProfileB_pos.le
        (lt_trans zero_lt_one one_lt_log_three).le
    nlinarith
  have hleftPos : 0 < 1 - Real.exp
      (-((1 - (1 / 2 : ℝ)) * bfaProfileB * Real.log 3)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have : 0 < (1 - (1 / 2 : ℝ)) * bfaProfileB * Real.log 3 := by
      exact mul_pos (mul_pos (by norm_num) bfaProfileB_pos)
        (lt_trans zero_lt_one one_lt_log_three)
    linarith
  have hrightPos : 0 < 1 - Real.exp
      (-((1 - sigma) * bfaProfileB * Real.log 3)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have : 0 < (1 - sigma) * bfaProfileB * Real.log 3 := by
      exact mul_pos (mul_pos (by linarith) bfaProfileB_pos)
        (lt_trans zero_lt_one one_lt_log_three)
    linarith
  have hden :
      1 - Real.exp (-((1 - (1 / 2 : ℝ)) * bfaProfileB * Real.log 3)) ≤
        1 - Real.exp (-((1 - sigma) * bfaProfileB * Real.log 3)) := by
    have hexp : Real.exp (-((1 - sigma) * bfaProfileB * Real.log 3)) ≤
        Real.exp (-((1 - (1 / 2 : ℝ)) * bfaProfileB * Real.log 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  unfold hsepTailConst
  have hinv := (inv_le_inv₀ hrightPos hleftPos).2 hden
  linarith

private theorem hsepAmplitude_le_half {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    hsepAmplitude sigma bfaProfileB ≤ hsepAmplitude (1 / 2) bfaProfileB := by
  have htail := hsepTailConst_le_half hsigma0 hsigma
  have htailTwo := two_le_hsepTailConst
    (sigma := sigma) (b := bfaProfileB) hsigma bfaProfileB_pos
  have htailTwo' := two_le_hsepTailConst
    (sigma := (1 / 2 : ℝ)) (b := bfaProfileB) (by norm_num) bfaProfileB_pos
  have hlog := Real.log_le_log (by linarith) htail
  have hleft : 0 ≤ 1 + Real.log (hsepTailConst sigma bfaProfileB) := by
    have := Real.log_nonneg
      (by linarith : (1 : ℝ) ≤ hsepTailConst sigma bfaProfileB)
    linarith
  have hright : 0 ≤ 1 + Real.log (hsepTailConst (1 / 2) bfaProfileB) := by
    have := Real.log_nonneg
      (by linarith : (1 : ℝ) ≤ hsepTailConst (1 / 2) bfaProfileB)
    linarith
  have hab :
      1 + Real.log (hsepTailConst sigma bfaProfileB) ≤
        1 + Real.log (hsepTailConst (1 / 2) bfaProfileB) := by
    linarith
  have hsq := (sq_le_sq₀ hleft hright).2 hab
  simpa [hsepAmplitude] using
    add_le_add_left (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) 3

private theorem tsum_three_rpow_neg_le_two_mul_inv {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∑' i : ℕ, ((3 : ℝ) ^ (-u)) ^ i) ≤ 2 * u⁻¹ := by
  set r : ℝ := (3 : ℝ) ^ (-u) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : (∑' i : ℕ, r ^ i) = (1 - r)⁻¹ :=
    tsum_geometric_of_lt_one hr0.le hr1
  have hlog : (1 : ℝ) ≤ Real.log 3 := one_lt_log_three.le
  have h3u : (1 : ℝ) + u ≤ (3 : ℝ) ^ u := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.add_one_le_exp (Real.log 3 * u)]
  have hden : (0 : ℝ) < 1 + u := by linarith
  have hru : r ≤ (1 + u)⁻¹ := by
    rw [hr, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    exact inv_anti₀ hden h3u
  have hone_sub : u / (1 + u) ≤ 1 - r := by
    have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
      field_simp
      ring
    linarith [hid ▸ (sub_le_sub_left hru 1)]
  have hpos : (0 : ℝ) < 1 - r := by
    linarith [div_pos hu0 hden]
  rw [hsum]
  have hstep : (1 - r)⁻¹ ≤ (u / (1 + u))⁻¹ :=
    inv_anti₀ (div_pos hu0 hden) hone_sub
  calc
    (1 - r)⁻¹ ≤ (u / (1 + u))⁻¹ := hstep
    _ = (1 + u) / u := by rw [inv_div]
    _ ≤ 2 / u := (div_le_div_iff_of_pos_right hu0).2 (by linarith)
    _ = 2 * u⁻¹ := by rw [div_eq_mul_inv]

private theorem waveIndicatorSeries_le {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    (∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
      (hsepAmplitude sigma bfaProfileB) i) ≤
      hsepAmplitude (1 / 2) bfaProfileB *
        (8 * bfaProfileB⁻¹) * sigma⁻¹ := by
  set q : ℝ := (1 - sigma) / (2 / sigma) with hqdef
  set K : ℝ := hsepAmplitude sigma bfaProfileB with hKdef
  set H : ℝ := hsepAmplitude (1 / 2) bfaProfileB with hHdef
  set u : ℝ := bfaProfileB * q with hudef
  set r : ℝ := (3 : ℝ) ^ (-u) with hrdef
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma0
  have hqeq : q = sigma * (1 - sigma) / 2 := by
    rw [hqdef]
    field_simp
  have hsigma1 : sigma < 1 := hsigma.trans_lt (by norm_num)
  have hq0 : 0 < q := by
    rw [hqeq]
    exact div_pos (mul_pos hsigma0 (by linarith)) (by norm_num)
  have hq1 : q ≤ 1 := by
    rw [hqeq]
    have hprod : sigma * (1 - sigma) ≤ (1 / 2 : ℝ) * 1 :=
      mul_le_mul hsigma (by linarith) (by linarith) (by norm_num)
    linarith
  have hqLower : sigma / 4 ≤ q := by
    rw [hqeq]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - sigma := by linarith
    have := mul_le_mul_of_nonneg_left hhalf hsigma0.le
    nlinarith
  have hu0 : 0 < u := by rw [hudef]; exact mul_pos bfaProfileB_pos hq0
  have hu1 : u ≤ 1 := by
    rw [hudef]
    calc
      bfaProfileB * q ≤ (1 / 8 : ℝ) * 1 :=
        mul_le_mul bfaProfileB_le_one_eighth hq1 hq0.le (by norm_num)
      _ ≤ 1 := by norm_num
  have hKpos : 0 < K := by rw [hKdef]; exact hsepAmplitude_pos _ _
  have hKone : 1 ≤ K := by
    rw [hKdef, hsepAmplitude]
    nlinarith [sq_nonneg (1 + Real.log (hsepTailConst sigma bfaProfileB))]
  have hKH : K ≤ H := by
    rw [hKdef, hHdef]
    exact hsepAmplitude_le_half hsigma0 hsigma
  have hH0 : 0 ≤ H := le_trans (by norm_num : (0 : ℝ) ≤ 1) (hKone.trans hKH)
  have hKpow : K ^ q ≤ H := by
    calc
      K ^ q ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKone hq1
      _ = K := by rw [Real.rpow_one]
      _ ≤ H := hKH
  have hterm : ∀ i : ℕ,
      truncationIndicatorScale bfaProfileB sigma (2 / sigma)
          (hsepAmplitude sigma bfaProfileB) i = K ^ q * r ^ i := by
    intro i
    rw [truncationIndicatorScale]
    change (K * (3 : ℝ) ^ (-(bfaProfileB * (i : ℝ)))) ^ q = K ^ q * r ^ i
    rw [Real.mul_rpow hKpos.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
    congr 1
    rw [hrdef, hudef]
    calc
      ((3 : ℝ) ^ (-(bfaProfileB * (i : ℝ)))) ^
          q =
          (3 : ℝ) ^ (-(bfaProfileB * (i : ℝ)) *
            q) := by
              rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 : ℝ) ^ (-(bfaProfileB * q) *
          (i : ℝ)) := by
        apply congrArg (fun x : ℝ => (3 : ℝ) ^ x)
        ring
      _ = ((3 : ℝ) ^ (-(bfaProfileB * q))) ^
          (i : ℝ) := by rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = ((3 : ℝ) ^ (-(bfaProfileB * q))) ^ i := by
          exact Real.rpow_natCast _ i
  have hseries :
      (∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
        (hsepAmplitude sigma bfaProfileB) i) = K ^ q * (∑' i : ℕ, r ^ i) := by
    calc
      (∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
        (hsepAmplitude sigma bfaProfileB) i) = ∑' i : ℕ, K ^ q * r ^ i :=
          tsum_congr hterm
      _ = K ^ q * (∑' i : ℕ, r ^ i) := tsum_mul_left
  have hgeom : (∑' i : ℕ, r ^ i) ≤ 2 * u⁻¹ := by
    rw [hrdef]
    exact tsum_three_rpow_neg_le_two_mul_inv hu0 hu1
  have hgeom0 : 0 ≤ (∑' i : ℕ, r ^ i) := by
    exact tsum_nonneg fun _ => pow_nonneg (Real.rpow_nonneg (by norm_num) _) _
  have huLower : bfaProfileB * (sigma / 4) ≤ u := by
    rw [hudef]
    exact mul_le_mul_of_nonneg_left hqLower bfaProfileB_pos.le
  have huInv : u⁻¹ ≤ (bfaProfileB * (sigma / 4))⁻¹ :=
    inv_anti₀ (mul_pos bfaProfileB_pos (div_pos hsigma0 (by norm_num))) huLower
  have hpole : 2 * u⁻¹ ≤ (8 * bfaProfileB⁻¹) * sigma⁻¹ := by
    calc
      2 * u⁻¹ ≤ 2 * (bfaProfileB * (sigma / 4))⁻¹ :=
        mul_le_mul_of_nonneg_left huInv (by norm_num)
      _ = (8 * bfaProfileB⁻¹) * sigma⁻¹ := by
        field_simp
        ring
  rw [hseries]
  calc
    K ^ q * (∑' i : ℕ, r ^ i) ≤ K ^ q * (2 * u⁻¹) :=
      mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hKpos.le q)
    _ ≤ H * (2 * u⁻¹) :=
      mul_le_mul_of_nonneg_right hKpow (by positivity)
    _ ≤ H * ((8 * bfaProfileB⁻¹) * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hpole hH0
    _ = H * (8 * bfaProfileB⁻¹) * sigma⁻¹ := by ring

private theorem waveGammaTriangle_le {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    IndependentSums.gammaTriangleConst (2 * (2 / sigma) / (2 + 2 / sigma)) ≤
      16384 := by
  set tau : ℝ := 2 * (2 / sigma) / (2 + 2 / sigma) with htaudef
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma0
  have hone : 0 < 1 + sigma := by linarith
  have htau : tau = 2 / (1 + sigma) := by
    rw [htaudef]
    field_simp
    ring
  have htau0 : 0 < tau := by rw [htau]; positivity
  have htauInv : tau⁻¹ = (1 + sigma) / 2 := by
    rw [htau]
    field_simp
  have htauInv0 : 0 ≤ tau⁻¹ := (inv_pos.mpr htau0).le
  have htauInv1 : tau⁻¹ ≤ 1 := by rw [htauInv]; linarith
  have hbaseOne : 1 ≤ 1 + tau⁻¹ := by linarith
  have hbaseTwo : 1 + tau⁻¹ ≤ 2 := by linarith
  have hpow : (1 + tau⁻¹) ^ tau⁻¹ ≤ 2 := by
    calc
      (1 + tau⁻¹) ^ tau⁻¹ ≤ (1 + tau⁻¹) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne htauInv1
      _ = 1 + tau⁻¹ := by rw [Real.rpow_one]
      _ ≤ 2 := hbaseTwo
  have hgrowth : IndependentSums.gammaGrowthConst tau = 2 := by
    rw [IndependentSums.gammaGrowthConst, max_eq_left hpow]
  rw [IndependentSums.gammaTriangleConst, hgrowth]
  norm_num

private theorem waveGammaProduct_le {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) ≤ 2 := by
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma0
  have htau : 2 * (2 / sigma) / (2 + 2 / sigma) = 2 / (1 + sigma) := by
    field_simp
    ring
  have htauInv : (2 * (2 / sigma) / (2 + 2 / sigma))⁻¹ = (1 + sigma) / 2 := by
    rw [htau]
    field_simp
  change (2 : ℝ) ^ ((2 * (2 / sigma) / (2 + 2 / sigma))⁻¹) ≤ 2
  calc
    (2 : ℝ) ^ ((2 * (2 / sigma) / (2 + 2 / sigma))⁻¹) ≤
        (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [htauInv]; linarith)
    _ = 2 := by rw [Real.rpow_one]

/-- A fully explicit dimensional constant for the fixed `b = 2⁻²⁰` wave tail. -/
def waveTailProfileConst (d : ℕ) : ℝ :=
  16384 *
    (2 *
      (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) * waveL4HeadConst d *
        (hsepAmplitude (1 / 2) bfaProfileB * (8 * bfaProfileB⁻¹))))

/-- At the exact deterministic Whitney gap, the explicit wave-tail series is
bounded by the manuscript's `C(d) sigma⁻¹ 3^{-(d/8)k₀}` scale. -/
theorem waveTailGainScale_profile_le (M : ABKModel d) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    {lout ell : ℤ} {k₀ k : ℕ}
    (hgap : lout - ell = (whitneyScaleSeq bfaProfileB 0 k₀ k : ℕ)) :
    waveTailGainScale d bfaProfileB sigma (2 / sigma) lout ell ≤
      waveTailProfileConst d * sigma⁻¹ *
        (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
  have hd2 : 2 ≤ d := M.shellPrefix.dimension
  have hseries := waveIndicatorSeries_le hsigma0 hsigma
  have htri := waveGammaTriangle_le hsigma0 hsigma
  have hprod := waveGammaProduct_le hsigma0 hsigma
  have hG0 : 0 ≤ streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_nonneg (streamIncrementLpGainConst_pos d _).le _
  have hhead0 : 0 ≤ waveL4HeadConst d := waveL4HeadConst_nonneg d
  have hH0 : 0 ≤ hsepAmplitude (1 / 2) bfaProfileB :=
    (hsepAmplitude_pos _ _).le
  have hsigmaInv0 : 0 ≤ sigma⁻¹ := (inv_pos.mpr hsigma0).le
  have hB0 : 0 ≤ 8 * bfaProfileB⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr bfaProfileB_pos.le)
  have hseries0 : 0 ≤ ∑' i : ℕ,
      truncationIndicatorScale bfaProfileB sigma (2 / sigma)
        (hsepAmplitude sigma bfaProfileB) i :=
    tsum_nonneg fun i => (truncationIndicatorScale_pos
      (hsepAmplitude_pos sigma bfaProfileB) i).le
  have hprod0 : 0 ≤ HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) := by
    change 0 ≤ (2 : ℝ) ^ ((2 * (2 / sigma) / (2 + 2 / sigma))⁻¹)
    positivity
  have htri0 : 0 ≤ IndependentSums.gammaTriangleConst
      (2 * (2 / sigma) / (2 + 2 / sigma)) :=
    IndependentSums.gammaTriangleConst_pos.le
  have hgapNat : k₀ ≤ whitneyScaleSeq bfaProfileB 0 k₀ k := by
    simpa using add_le_whitneyScaleSeq bfaProfileB 0 k₀ k
  have hgapReal : (k₀ : ℝ) ≤ (lout : ℝ) - (ell : ℝ) := by
    have hcast : (k₀ : ℤ) ≤ lout - ell := by
      rw [hgap]
      exact_mod_cast hgapNat
    exact_mod_cast hcast
  have hdecay :
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) ≤
        (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    nlinarith
  rw [waveTailGainScale]
  have hprefactor :
      IndependentSums.gammaTriangleConst (2 * (2 / sigma) / (2 + 2 / sigma)) *
          (HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                (hsepAmplitude sigma bfaProfileB) i)) ≤
        waveTailProfileConst d * sigma⁻¹ := by
    have hA0 : 0 ≤ streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
        waveL4HeadConst d := mul_nonneg hG0 hhead0
    have hPS0 : 0 ≤ HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) *
        (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
          waveL4HeadConst d *
          ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
            (hsepAmplitude sigma bfaProfileB) i) :=
      mul_nonneg hprod0 (mul_nonneg hA0 hseries0)
    have hprodStep :
        HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                (hsepAmplitude sigma bfaProfileB) i) ≤
          2 *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                (hsepAmplitude sigma bfaProfileB) i) :=
      mul_le_mul_of_nonneg_right hprod (mul_nonneg hA0 hseries0)
    have hseriesStep :
        streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
            waveL4HeadConst d *
            (∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
              (hsepAmplitude sigma bfaProfileB) i) ≤
          streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
            waveL4HeadConst d *
            (hsepAmplitude (1 / 2) bfaProfileB *
              (8 * bfaProfileB⁻¹) * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hseries hA0
    calc
      IndependentSums.gammaTriangleConst (2 * (2 / sigma) / (2 + 2 / sigma)) *
          (HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                (hsepAmplitude sigma bfaProfileB) i)) ≤
          16384 *
            (HCPolySupport.Book.Ch04.gammaProductConst 2 (2 / sigma) *
              (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
                waveL4HeadConst d *
                ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                  (hsepAmplitude sigma bfaProfileB) i)) :=
        mul_le_mul_of_nonneg_right htri hPS0
      _ ≤ 16384 *
          (2 *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              ∑' i : ℕ, truncationIndicatorScale bfaProfileB sigma (2 / sigma)
                (hsepAmplitude sigma bfaProfileB) i)) :=
        mul_le_mul_of_nonneg_left hprodStep (by norm_num)
      _ ≤ 16384 *
          (2 *
            (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              waveL4HeadConst d *
              (hsepAmplitude (1 / 2) bfaProfileB *
                (8 * bfaProfileB⁻¹) * sigma⁻¹))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hseriesStep (by norm_num)) (by norm_num)
      _ = waveTailProfileConst d * sigma⁻¹ := by
        rw [waveTailProfileConst]
        ring
  have hconst0 : 0 ≤ waveTailProfileConst d := by
    rw [waveTailProfileConst]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hG0 hhead0) (mul_nonneg hH0 hB0)))
  exact mul_le_mul hprefactor hdecay
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    (mul_nonneg hconst0 hsigmaInv0)


end

end Algsuperdiff.Section3.Provider.Multiscale
