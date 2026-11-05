/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteFamilyFiveIndep

/-!
# SiteTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Surviving elementary bounds for the site-tail construction

This module retains the logarithmic bounds, the set identity for the complement
of the good-cube event, and the Gaussian shell estimate used by the successor
site-tail construction.
-/
namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The logarithmic weight of the moment bounds -/

/-- The scaling parameter is at most `1/4`, so its logarithmic weight is at
least `log 4 > 1`. -/
theorem one_le_abs_log_gamma (M : ABKModel d) : 1 ≤ |Real.log M.gamma| := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hquarter : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h1 : Real.log M.gamma ≤ Real.log (1 / 4 : ℝ) := Real.log_le_log hg hq
  rw [hquarter] at h1
  have h2 : Real.log M.gamma ≤ -1 := by linarith only [h1, hlog2]
  rw [abs_of_neg (by linarith only [h2])]
  linarith only [h2]

theorem abs_log_gamma_pos (M : ABKModel d) : 0 < |Real.log M.gamma| :=
  lt_of_lt_of_le zero_lt_one (one_le_abs_log_gamma M)

/-! ## 2. The good-cube complement -/

/-- The good cube event fails exactly when one of the two localized quantities
exceeds its threshold. -/
theorem compl_goodCubeEvent_eq (M : ABKModel d) (Creg : ℝ) (n : ℤ) (y : Vec d)
    (ep : ℝ) :
    (goodCubeEvent M Creg n y ep)ᶜ =
      {omega | ENNReal.ofReal ep < localizedError M n y omega} ∪
        {omega | ENNReal.ofReal (2 * Creg) < localizedRegularity M n y omega} := by
  ext omega
  simp only [goodCubeEvent, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union,
    Set.mem_ofPred_eq, not_and_or, not_le]

/-! ## 3. The shell estimate -/

private theorem rpow3_combine (K a b c e : ℝ) :
    (3 : ℝ) ^ a * ((3 : ℝ) ^ b * (3 : ℝ) ^ c * (K * (3 : ℝ) ^ e)) =
      K * (3 : ℝ) ^ (a + b + c + e) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [Real.rpow_add h3 (a + b + c) e, Real.rpow_add h3 (a + b) c, Real.rpow_add h3 a b]
  ring

private theorem rpow3_sq (x : ℝ) : ((3 : ℝ) ^ x) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * x) := by
  rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), two_mul]

/-- **The shell leg.**  The scale-`L` shell event has the Gaussian tail
`exp(-C_0² ε² γ^{-1} 3^{a L})` at the exponent `a = 5/4`, uniformly in the cube
scale and the site: the normalization `3^{(2-γ) n}` of the large-scale sum
cancels the shell amplitude `3^{-n} 3^{(γ-1)(n+L)}` exactly. -/
theorem measureReal_shellExcessEvent_le (M : ABKModel d) {C0 ep : ℝ}
    (hC0 : 0 < C0) (hep : 0 < ep)
    (hgate : 1 ≤ C0 * ep * (Real.sqrt M.gamma)⁻¹)
    (n : ℤ) (L : ℕ) (z : Percolation.Site d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (shellExcessEvent M C0 ep n L z) ≤
      Real.exp (-(C0 ^ 2 * ep ^ 2 * M.gamma⁻¹ *
        (3 : ℝ) ^ (sitePathExponent * (L : ℝ)))) := by
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  set y : Vec d := rescaledLatticePoint n z with hy
  set Xf : Cutoff.CutoffSample d → ℝ := fun omega =>
    Section4.Support.shellW1InfGradNorm n
      (ShellField.translate y (omega.1 (n + (L : ℤ)))) with hXf
  set A : ℝ := (3 : ℝ) ^ (-n) * Real.rpow 3 ((M.gamma - 1) * ((n + (L : ℤ) : ℤ) : ℝ))
    with hA
  set t : ℝ := C0 * ep * (Real.sqrt M.gamma)⁻¹ *
    (3 : ℝ) ^ ((7 / 8 - M.gamma) * (L : ℝ)) with ht
  have hexp0 : (0 : ℝ) ≤ (7 / 8 - M.gamma) * (L : ℝ) :=
    mul_nonneg (by linarith only [hq]) (Nat.cast_nonneg L)
  have h38 : (1 : ℝ) ≤ (3 : ℝ) ^ ((7 / 8 - M.gamma) * (L : ℝ)) :=
    Real.one_le_rpow (by norm_num) hexp0
  have ht1 : 1 ≤ t := by
    refine le_trans hgate ?_
    exact le_mul_of_one_le_right (by linarith only [hgate]) h38
  have hzpow : ((3 : ℝ) ^ (-n : ℤ)) = Real.rpow 3 (-(n : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-n)]
    norm_num
  have hpow : Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) * (A * t) =
      shellThreshold M C0 ep L := by
    rw [shellThreshold, shellDecayBase_pow, hA, ht, hzpow,
      show ((n + (L : ℤ) : ℤ) : ℝ) = (n : ℝ) + (L : ℝ) by push_cast; ring]
    change (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        ((3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ ((M.gamma - 1) * ((n : ℝ) + (L : ℝ))) *
          (C0 * ep * (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ ((7 / 8 - M.gamma) * (L : ℝ)))) =
      C0 * ep * (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (-((L : ℝ) / 8))
    rw [rpow3_combine, show (-((L : ℝ) / 8)) =
      (2 - M.gamma) * (n : ℝ) + -(n : ℝ) + (M.gamma - 1) * ((n : ℝ) + (L : ℝ)) +
        (7 / 8 - M.gamma) * (L : ℝ) by ring]
  have hpospow : (0 : ℝ) < Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hset : shellExcessEvent M C0 ep n L z = upperTailEvent Xf (A * t) := by
    ext omega
    rw [shellExcessEvent, Set.mem_ofPred_eq, largeScaleShellTerm, ← hpow]
    constructor
    · intro h
      exact lt_of_mul_lt_mul_left h hpospow.le
    · intro h
      exact mul_lt_mul_of_pos_left h hpospow
  have hbigO : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xf A :=
    Section4.Provider.BoundsEaL.isBigOWith_gammaSigma_shellW1InfGradNorm_translate M
      (by omega : n ≤ n + (L : ℤ)) y
  have htail := (isBigOWith_gammaSigma_iff.mp hbigO) ht1
  rw [← hset] at htail
  refine le_trans htail (Real.exp_le_exp.2 (neg_le_neg ?_))
  have ht2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : t ^ (2 : ℕ) =
      C0 ^ 2 * ep ^ 2 * M.gamma⁻¹ * (3 : ℝ) ^ (2 * ((7 / 8 - M.gamma) * (L : ℝ))) := by
    rw [ht, mul_pow, rpow3_sq, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hg.le]
  have hmono : (3 : ℝ) ^ (sitePathExponent * (L : ℝ)) ≤
      (3 : ℝ) ^ (2 * ((7 / 8 - M.gamma) * (L : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcoef : sitePathExponent ≤ 2 * (7 / 8 - M.gamma) := by
      have h := sitePathExponent_le_two_mul_one_sub M
      linarith only [h]
    calc sitePathExponent * (L : ℝ) ≤ (2 * (7 / 8 - M.gamma)) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg L)
      _ = 2 * ((7 / 8 - M.gamma) * (L : ℝ)) := by ring
  rw [ht2, hsq]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

end

end Algsuperdiff.Section5.Support
