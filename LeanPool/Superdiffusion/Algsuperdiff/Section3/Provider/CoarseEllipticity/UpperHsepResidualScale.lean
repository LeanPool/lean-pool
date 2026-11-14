/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperProfileExponents

/-!
# UpperHsepResidualScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform upper-profile hsep residual scale

This file isolates the numerical comparison for the exact scale returned by
`HsepReduction` at the Section 3.3 upper-profile parameters.  The constants
below are universal (hence, in particular, safe wherever a dimension-only
constant is allowed), and the comparison is uniform in the terminal exponent
`sigma`.

This is an internal scale-arithmetic helper.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

/-- The exact amplitude returned by `HsepReduction` after specializing its
internal exponents to the Section 3.3 upper profile. -/
def upperHsepResidualScale (sigma gamma : ℝ) : ℝ :=
  HCPolySupport.Book.Ch04.gammaProductConst
      (upperProfileBaseSigma sigma) (upperProfileHsepAuxSigma sigma) *
    hsepAmplitude (upperProfileSigma sigma) bfaProfileB *
    truncationIndicatorScale bfaProfileB (upperProfileSigma sigma)
      (upperProfileHsepAuxSigma sigma)
      (hsepAmplitude (upperProfileSigma sigma) bfaProfileB)
      ⌊(81 * gamma)⁻¹⌋₊

/-- Fixed exponential rate retained from the truncation depth
`floor((81 gamma)^{-1})`. -/
def upperHsepResidualRate : ℝ := bfaProfileB * Real.log 3 / 81

/-- A universal amplitude for the exact upper-profile hsep residual scale. -/
def upperHsepResidualConst : ℝ :=
  32 * superposedFluxHsepConst *
    (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
      Real.exp (bfaProfileB * Real.log 3)

theorem upperHsepResidualRate_pos : 0 < upperHsepResidualRate := by
  unfold upperHsepResidualRate
  exact div_pos
    (mul_pos bfaProfileB_pos (lt_trans zero_lt_one one_lt_log_three))
    (by norm_num)

theorem upperHsepResidualConst_pos : 0 < upperHsepResidualConst := by
  unfold upperHsepResidualConst
  have hH : 0 < superposedFluxHsepConst := superposedFluxHsepConst_pos
  positivity


theorem upperHsepResidualScale_pos (sigma gamma : ℝ) :
    0 < upperHsepResidualScale sigma gamma := by
  unfold upperHsepResidualScale
  exact mul_pos
    (mul_pos (by positivity) (hsepAmplitude_pos _ _))
    (truncationIndicatorScale_pos (hsepAmplitude_pos _ _) _)

private theorem upperProfileHsepTau_one_fifth_le {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    (1 : ℝ) / 5 ≤ upperProfileHsepTau sigma := by
  have hden : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hsigmaSq : sigma ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
  rw [upperProfileHsepTau]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
  nlinarith

private theorem upperProfileHsep_scaleExponent_eq {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileBaseSigma sigma / upperProfileHsepAuxSigma sigma =
      (upperProfileBaseSigma sigma - upperProfileHsepTau sigma) /
        upperProfileHsepTau sigma := by
  have hA : 0 < upperProfileBaseSigma sigma :=
    upperProfileBaseSigma_pos hsigma0 hsigma
  have hT : 0 < upperProfileHsepTau sigma :=
    upperProfileHsepTau_pos hsigma0 hsigma
  have hsub : 0 < upperProfileBaseSigma sigma - upperProfileHsepTau sigma :=
    sub_pos.mpr (upperProfileHsepTau_lt_base hsigma0 hsigma)
  rw [upperProfileHsepAuxSigma]
  field_simp [hA.ne', hT.ne', hsub.ne']

private theorem upperProfileHsep_scaleExponent_one_le {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    1 ≤ upperProfileBaseSigma sigma / upperProfileHsepAuxSigma sigma := by
  have hden : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hA2T : 2 * upperProfileHsepTau sigma ≤
      upperProfileBaseSigma sigma := by
    rw [upperProfileHsepTau, upperProfileBaseSigma, upperProfileSigma]
    rw [show 2 * (4 * (1 - sigma) / (8 + 3 * sigma + sigma ^ 2)) =
        8 * (1 - sigma) / (8 + 3 * sigma + sigma ^ 2) by ring,
      show 1 - sigma / 4 = (4 - sigma) / 4 by ring]
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
    nlinarith [sq_nonneg sigma, mul_nonneg hsigma0.le (sq_nonneg (1 - sigma))]
  rw [upperProfileHsep_scaleExponent_eq hsigma0 hsigma]
  rw [le_div_iff₀ (upperProfileHsepTau_pos hsigma0 hsigma)]
  linarith

private theorem upperProfileHsep_scaleExponent_le_four {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileBaseSigma sigma / upperProfileHsepAuxSigma sigma ≤ 4 := by
  have hden : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
  have hsigmaSq : sigma ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
  have hsigmaCube : 0 ≤ sigma ^ 3 := by positivity
  have hA5T : upperProfileBaseSigma sigma ≤
      5 * upperProfileHsepTau sigma := by
    rw [upperProfileHsepTau, upperProfileBaseSigma, upperProfileSigma]
    rw [show 1 - sigma / 4 = (4 - sigma) / 4 by ring,
      show 5 * (4 * (1 - sigma) / (8 + 3 * sigma + sigma ^ 2)) =
        20 * (1 - sigma) / (8 + 3 * sigma + sigma ^ 2) by ring]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden]
    nlinarith
  rw [upperProfileHsep_scaleExponent_eq hsigma0 hsigma]
  rw [div_le_iff₀ (upperProfileHsepTau_pos hsigma0 hsigma)]
  linarith

private theorem gammaProductConst_upperProfile_le_thirty_two {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileBaseSigma sigma) (upperProfileHsepAuxSigma sigma) ≤ 32 := by
  have hT : 0 < upperProfileHsepTau sigma :=
    upperProfileHsepTau_pos hsigma0 hsigma
  have hTlower : (1 : ℝ) / 5 ≤ upperProfileHsepTau sigma :=
    upperProfileHsepTau_one_fifth_le hsigma0 hsigma
  have hinv : (upperProfileHsepTau sigma)⁻¹ ≤ (5 : ℝ) :=
    (inv_le_iff_one_le_mul₀ hT).2 (by nlinarith)
  change (2 : ℝ) ^
      (((upperProfileBaseSigma sigma * upperProfileHsepAuxSigma sigma) /
        (upperProfileBaseSigma sigma + upperProfileHsepAuxSigma sigma))⁻¹) ≤ 32
  rw [upperProfile_hsep_productSigma_eq hsigma0 hsigma]
  calc
    (2 : ℝ) ^ (upperProfileHsepTau sigma)⁻¹ ≤ (2 : ℝ) ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
    _ = 32 := by norm_num

private theorem three_rpow_neg_bfa_floor_le (gamma : ℝ) :
    (3 : ℝ) ^
        (-(bfaProfileB * ((⌊(81 * gamma)⁻¹⌋₊ : ℕ) : ℝ))) ≤
      Real.exp (bfaProfileB * Real.log 3) *
        Real.exp (-(upperHsepResidualRate * gamma⁻¹)) := by
  have hfloorLt : (81 * gamma)⁻¹ <
      ((⌊(81 * gamma)⁻¹⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfloor : (81 * gamma)⁻¹ - 1 ≤
      ((⌊(81 * gamma)⁻¹⌋₊ : ℕ) : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfloor bfaProfileB_pos.le
  have hlog : 0 < Real.log 3 := lt_trans zero_lt_one one_lt_log_three
  have hmulLog := mul_le_mul_of_nonneg_right hmul hlog.le
  have hargEq :
      bfaProfileB * (81 * gamma)⁻¹ * Real.log 3 =
        upperHsepResidualRate * gamma⁻¹ := by
    unfold upperHsepResidualRate
    rw [mul_inv_rev]
    norm_num
    ring
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← hargEq]
  nlinarith

private theorem truncationIndicatorScale_upperProfile_le {sigma gamma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    truncationIndicatorScale bfaProfileB (upperProfileSigma sigma)
        (upperProfileHsepAuxSigma sigma)
        (hsepAmplitude (upperProfileSigma sigma) bfaProfileB)
        ⌊(81 * gamma)⁻¹⌋₊ ≤
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
        Real.exp (bfaProfileB * Real.log 3) *
        Real.exp (-(upperHsepResidualRate * gamma⁻¹)) := by
  let K : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB
  let i : ℕ := ⌊(81 * gamma)⁻¹⌋₊
  let r : ℝ := (3 : ℝ) ^ (-(bfaProfileB * (i : ℝ)))
  let q : ℝ := upperProfileBaseSigma sigma / upperProfileHsepAuxSigma sigma
  let x : ℝ := K * r
  have hsigmaInternal0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaInternal : upperProfileSigma sigma ≤ (1 : ℝ) / 8 := by
    rw [upperProfileSigma]
    linarith
  have hKpos : 0 < K := hsepAmplitude_pos _ _
  have hKle : K ≤ superposedFluxHsepConst := by
    exact hsepAmplitude_le_superposedFluxHsepConst hsigmaInternal0 hsigmaInternal
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrle : r ≤ 1 := by
    dsimp only [r]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg bfaProfileB_pos.le (Nat.cast_nonneg _)))
  have hq1 : 1 ≤ q := by
    exact upperProfileHsep_scaleExponent_one_le hsigma0 hsigma
  have hq4 : q ≤ 4 := by
    exact upperProfileHsep_scaleExponent_le_four hsigma0 hsigma
  have hxpos : 0 < x := mul_pos hKpos hrpos
  have hxpow : x ^ q ≤ x + x ^ 4 := by
    by_cases hxone : x ≤ 1
    · exact (Real.rpow_le_self_of_le_one hxpos.le hxone hq1).trans
        (le_add_of_nonneg_right (by positivity))
    · have hxone' : 1 ≤ x := le_of_not_ge hxone
      have hp := Real.rpow_le_rpow_of_exponent_le hxone' hq4
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast] at hp
      exact hp.trans (le_add_of_nonneg_left hxpos.le)
  have hxle : x ≤ superposedFluxHsepConst * r :=
    mul_le_mul_of_nonneg_right hKle hrpos.le
  have hxfour : x ^ 4 ≤ (superposedFluxHsepConst * r) ^ 4 :=
    pow_le_pow_left₀ hxpos.le hxle 4
  have hrSq : r ^ 2 ≤ r := by nlinarith [hrpos.le]
  have hrFour : r ^ 4 ≤ r := by
    calc
      r ^ 4 = r ^ 2 * r ^ 2 := by ring
      _ ≤ r * r := mul_le_mul hrSq hrSq (sq_nonneg r) hrpos.le
      _ ≤ r := by simpa [pow_two] using hrSq
  have hHfour : (superposedFluxHsepConst * r) ^ 4 ≤
      superposedFluxHsepConst ^ 4 * r := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hrFour (by positivity)
  have hprod : x + x ^ 4 ≤
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) * r := by
    calc
      x + x ^ 4 ≤ superposedFluxHsepConst * r +
          (superposedFluxHsepConst * r) ^ 4 := add_le_add hxle hxfour
      _ ≤ superposedFluxHsepConst * r +
          superposedFluxHsepConst ^ 4 * r := add_le_add le_rfl hHfour
      _ = (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) * r := by ring
  have hrExp : r ≤ Real.exp (bfaProfileB * Real.log 3) *
      Real.exp (-(upperHsepResidualRate * gamma⁻¹)) := by
    exact three_rpow_neg_bfa_floor_le gamma
  have hHsum : 0 ≤ superposedFluxHsepConst + superposedFluxHsepConst ^ 4 := by
    exact add_nonneg superposedFluxHsepConst_pos.le
      (pow_nonneg superposedFluxHsepConst_pos.le 4)
  unfold truncationIndicatorScale
  have hexponent : (1 - upperProfileSigma sigma) /
      upperProfileHsepAuxSigma sigma = q := by
    rfl
  rw [hexponent]
  change x ^ q ≤ _
  calc
    x ^ q ≤ x + x ^ 4 := hxpow
    _ ≤ (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) * r := hprod
    _ ≤ (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
        (Real.exp (bfaProfileB * Real.log 3) *
          Real.exp (-(upperHsepResidualRate * gamma⁻¹))) :=
      mul_le_mul_of_nonneg_left hrExp hHsum
    _ = _ := by ring

/-- The exact upper-profile hsep residual scale is bounded by one universal
amplitude times a fixed-rate exponential.  The constants are selected before
`sigma`, `E`, and `gamma`, so the estimate is uniform in all three runtime
parameters on the displayed window. -/
theorem upperHsepResidualScale_le_exp {sigma E gamma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hE : 1 ≤ E) (hgamma : 0 < gamma) :
    upperHsepResidualScale sigma gamma ≤
      upperHsepResidualConst *
        Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * gamma⁻¹))) := by
  have hprod := gammaProductConst_upperProfile_le_thirty_two hsigma0 hsigma
  have hsigmaInternal0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaInternal : upperProfileSigma sigma ≤ (1 : ℝ) / 8 := by
    rw [upperProfileSigma]
    linarith
  have hK := hsepAmplitude_le_superposedFluxHsepConst
    hsigmaInternal0 hsigmaInternal
  have htrunc := truncationIndicatorScale_upperProfile_le
    (gamma := gamma) hsigma0 hsigma
  have hprod0 : 0 ≤ HCPolySupport.Book.Ch04.gammaProductConst
      (upperProfileBaseSigma sigma) (upperProfileHsepAuxSigma sigma) := by
    positivity
  have hK0 : 0 ≤ hsepAmplitude (upperProfileSigma sigma) bfaProfileB :=
    (hsepAmplitude_pos _ _).le
  have htrunc0 : 0 ≤ truncationIndicatorScale bfaProfileB
      (upperProfileSigma sigma) (upperProfileHsepAuxSigma sigma)
      (hsepAmplitude (upperProfileSigma sigma) bfaProfileB)
      ⌊(81 * gamma)⁻¹⌋₊ :=
    (truncationIndicatorScale_pos (hsepAmplitude_pos _ _) _).le
  have hgammaInv0 : 0 ≤ gamma⁻¹ := inv_nonneg.mpr hgamma.le
  have hEInv0 : 0 ≤ E⁻¹ :=
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hE)).le
  have hEInv1 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE
  have hEInvSq : E⁻¹ ^ 2 ≤ 1 := by nlinarith
  have hX : E⁻¹ ^ 2 * gamma⁻¹ ≤ gamma⁻¹ :=
    mul_le_of_le_one_left hgammaInv0 hEInvSq
  have hrate : upperHsepResidualRate * (E⁻¹ ^ 2 * gamma⁻¹) ≤
      upperHsepResidualRate * gamma⁻¹ :=
    mul_le_mul_of_nonneg_left hX upperHsepResidualRate_pos.le
  have hexp : Real.exp (-(upperHsepResidualRate * gamma⁻¹)) ≤
      Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * gamma⁻¹))) :=
    Real.exp_le_exp.mpr (neg_le_neg hrate)
  have hcoefficient0 : 0 ≤ 32 * superposedFluxHsepConst *
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
      Real.exp (bfaProfileB * Real.log 3) := by
    have hH0 : 0 ≤ superposedFluxHsepConst := superposedFluxHsepConst_pos.le
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hH0)
        (add_nonneg hH0 (pow_nonneg hH0 4)))
      (Real.exp_pos _).le
  unfold upperHsepResidualScale upperHsepResidualConst
  calc
    _ ≤ (32 * superposedFluxHsepConst) *
        ((superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
          Real.exp (bfaProfileB * Real.log 3) *
          Real.exp (-(upperHsepResidualRate * gamma⁻¹))) := by
      exact mul_le_mul (mul_le_mul hprod hK hK0 (by norm_num)) htrunc htrunc0
        (mul_nonneg (by positivity) superposedFluxHsepConst_pos.le)
    _ = (32 * superposedFluxHsepConst *
          (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
          Real.exp (bfaProfileB * Real.log 3)) *
        Real.exp (-(upperHsepResidualRate * gamma⁻¹)) := by ring
    _ ≤ (32 * superposedFluxHsepConst *
          (superposedFluxHsepConst + superposedFluxHsepConst ^ 4) *
          Real.exp (bfaProfileB * Real.log 3)) *
          Real.exp (-(upperHsepResidualRate *
          (E⁻¹ ^ 2 * gamma⁻¹))) :=
      mul_le_mul_of_nonneg_left hexp hcoefficient0

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
