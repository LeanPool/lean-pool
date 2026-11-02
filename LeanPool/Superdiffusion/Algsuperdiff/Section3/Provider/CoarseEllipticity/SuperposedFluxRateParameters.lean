/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLocalParameters

/-!
# SuperposedFluxRateParameters

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Integer rate parameters for the superposed-flux local payoff

This file selects the two integer parameters left open by
`SuperposedFluxLocalParameters`.  Write

```text
R = siteRateBase d / 2 * (E⁻² * gamma⁻¹).
```

We take `k₀ = floor R` and `kp = floor (R / 8)`.  Thus `k₀` is the manuscript's
`c E⁻² gamma⁻¹` depth, with the coefficient supplied by the proved percolation
rate, and `kp` retains a fixed fraction of the same rate.  In particular, this
is not the merely qualitative `kp = 0` choice from
`ConclusionFeasibility.lean`.

The amended bad-cluster entropy gate, already implied by the frozen maximum
and fifth-root hypotheses at `b = 2⁻²⁰` and `sigma / 4`, makes `R` large enough
to absorb the overlap prefactor `9 * 99^d`.  The floor loss costs one unit:
both terms in the raw collar cap are at most `exp (-R / 4)`, while the overlap
prefactor is at most `exp (R / 8)`.  This leaves `exp (-R / 8)`, which is at
most `exp (-kp)`.

These choices are internal proof parameters, not manuscript-stated or frozen
declarations.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-! ## Rate-compatible real parameters -/

/-- The layer slack used by the final rate estimate.  Unlike the preliminary
`sigma`-scaled choice, this is proportional to `gamma`, so multiplying it by
the primary depth leaves a dimension-only exponent. -/
def superposedFluxRateEps (M : ABKModel d) : ℝ := M.gamma

/-- The collar exponent used by the final rate estimate.  Its excess over the
fixed profile slope is proportional to `gamma` for the same reason. -/
def superposedFluxRateBeta (M : ABKModel d) : ℝ := bfaProfileB + 2 * M.gamma

/-- The corrected percolation rate available to the first Step-3 layer sum. -/
def superposedFluxRate (M : ABKModel d) (E : ℝ) : ℝ :=
  siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)

/-- The source-faithful primary depth `k₀ = floor R`. -/
noncomputable def superposedFluxPrimaryDepth (M : ABKModel d) (E : ℝ) : ℕ :=
  ⌊superposedFluxRate M E⌋₊

/-- The retained rare-rate depth `kp = floor (R / 8)`. -/
noncomputable def superposedFluxRareDepth (M : ABKModel d) (E : ℝ) : ℕ :=
  ⌊superposedFluxRate M E / 8⌋₊

theorem superposedFluxRate_pos (M : ABKModel d) {E : ℝ} (hE : 0 < E) :
    0 < superposedFluxRate M E := by
  unfold superposedFluxRate
  have hsite : 0 < siteRateBase d := siteRateBase_pos d
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  positivity

/-- The exact floor windows of the two selected integer parameters. -/
theorem superposedFluxDepth_floorWindows (M : ABKModel d) {E : ℝ} (hE : 0 < E) :
    ((superposedFluxPrimaryDepth M E : ℕ) : ℝ) ≤ superposedFluxRate M E ∧
      superposedFluxRate M E < (superposedFluxPrimaryDepth M E : ℝ) + 1 ∧
      ((superposedFluxRareDepth M E : ℕ) : ℝ) ≤ superposedFluxRate M E / 8 ∧
      superposedFluxRate M E / 8 < (superposedFluxRareDepth M E : ℝ) + 1 := by
  have hrate : 0 ≤ superposedFluxRate M E := (superposedFluxRate_pos M hE).le
  have hrateEight : 0 ≤ superposedFluxRate M E / 8 := by positivity
  exact ⟨Nat.floor_le hrate, Nat.lt_floor_add_one _, Nat.floor_le hrateEight,
    Nat.lt_floor_add_one _⟩

private theorem three_le_rate_and_two_mul_overlap_le_exp_rate_div_eight
    (hd : 2 ≤ d) (M : ABKModel d) {sigma E : ℝ} (hE : 1 ≤ E)
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    3 ≤ superposedFluxRate M E ∧
      2 * (9 * (99 : ℝ) ^ d) ≤ Real.exp (superposedFluxRate M E / 8) := by
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ E :=
    (le_max_left _ _).trans hmax
  have hsigmaProfile : 0 < bfaProfileSigma sigma := bfaProfileSigma_pos hsigma
  have hsigmaProfileHalf : bfaProfileSigma sigma ≤ (1 : ℝ) / 2 :=
    bfaProfileSigma_le_one_half hsigmaHalf
  have hEexp : Real.exp (badClustersConst d / bfaProfileSigma sigma) ≤ E :=
    exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate hsigma hexp
  have hEb : badClustersConst d / bfaProfileB ≤ E :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate hsigma hsigmaHalf hexp
  have hgamma : M.gamma ≤ E ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate hE M.shellPrefix.gamma_pos hEgamma
  have hentropy := entropyGate_of_admissible M hd hsigmaProfile hsigmaProfileHalf
    bfaProfileB_pos (bfaProfileB_le_one_eighth.trans (by norm_num)) hEexp hEb hgamma
  have hrate0 : 0 ≤ superposedFluxRate M E :=
    (superposedFluxRate_pos M (lt_of_lt_of_le zero_lt_one hE)).le
  have hexpNeg : Real.exp (-(40 / bfaProfileSigma sigma)) ≤ 1 := by
    have harg : -(40 / bfaProfileSigma sigma) ≤ 0 :=
      neg_nonpos.mpr (div_nonneg (by norm_num) hsigmaProfile.le)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr harg
  have hsiteRate : siteRateSq M E / 2 = superposedFluxRate M E := by
    unfold siteRateSq superposedFluxRate
    ring
  have hrateLarge : 1 + 2 * (d : ℝ) / bfaProfileB ≤ superposedFluxRate M E := by
    calc
      1 + 2 * (d : ℝ) / bfaProfileB ≤
          Real.exp (-(40 / bfaProfileSigma sigma)) * siteRateSq M E / 2 := hentropy
      _ = Real.exp (-(40 / bfaProfileSigma sigma)) * superposedFluxRate M E := by
        rw [← hsiteRate]
        ring
      _ ≤ 1 * superposedFluxRate M E :=
        mul_le_mul_of_nonneg_right hexpNeg hrate0
      _ = superposedFluxRate M E := one_mul _
  have hdReal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlinear : 18 + 99 * (d : ℝ) ≤ superposedFluxRate M E / 8 := by
    norm_num [bfaProfileB] at hrateLarge
    nlinarith
  have heighteen : (18 : ℝ) ≤ Real.exp 18 := by
    linarith [Real.add_one_le_exp (18 : ℝ)]
  have hninetynine : (99 : ℝ) ≤ Real.exp 99 := by
    linarith [Real.add_one_le_exp (99 : ℝ)]
  have hpow : (99 : ℝ) ^ d ≤ (Real.exp 99) ^ d :=
    pow_le_pow_left₀ (by norm_num) hninetynine d
  have hmul : (18 : ℝ) * (99 : ℝ) ^ d ≤ Real.exp 18 * (Real.exp 99) ^ d :=
    mul_le_mul heighteen hpow (by positivity) (Real.exp_pos _).le
  have hexpPow : (Real.exp 99) ^ d = Real.exp (99 * (d : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨by nlinarith [hlinear], ?_⟩
  calc
    2 * (9 * (99 : ℝ) ^ d) = (18 : ℝ) * (99 : ℝ) ^ d := by ring
    _ ≤ Real.exp 18 * (Real.exp 99) ^ d := hmul
    _ = Real.exp (18 + 99 * (d : ℝ)) := by rw [hexpPow, ← Real.exp_add]
    _ ≤ Real.exp (superposedFluxRate M E / 8) := Real.exp_le_exp.mpr hlinear

/-- The two source-faithful integer choices discharge the primary-depth floor, the
upper rate constraint used, and the exact cap consumed by
`slstar_descendantGrid_allL_ae_and_isBigOWith_of_gates`. -/
theorem superposedFluxRateParameterGates_of_profileAuxiliaryMaxGate
    (hd : 2 ≤ d) (M : ABKModel d) {sigma E : ℝ} (hE : 1 ≤ E)
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    3 ≤ superposedFluxPrimaryDepth M E ∧
      ((superposedFluxPrimaryDepth M E : ℕ) : ℝ) ≤
        siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹) ∧
      9 * (99 : ℝ) ^ d *
          (Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
            (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2))) ≤
        Real.exp (-(superposedFluxRareDepth M E : ℝ)) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hrate0 : 0 ≤ superposedFluxRate M E := (superposedFluxRate_pos M hE0).le
  obtain ⟨hk₀le, hk₀upper, hkple, _⟩ := superposedFluxDepth_floorWindows M hE0
  obtain ⟨hrateThree, hpref⟩ :=
    three_le_rate_and_two_mul_overlap_le_exp_rate_div_eight hd M hE hsigma
      hsigmaHalf hmax hEgamma
  have hrateTwo : 2 ≤ superposedFluxRate M E := by linarith
  have hk₀lower : superposedFluxRate M E - 1 <
      (superposedFluxPrimaryDepth M E : ℝ) := by linarith
  have hk₀half : superposedFluxRate M E / 2 ≤
      (superposedFluxPrimaryDepth M E : ℝ) := by linarith
  have hk₀three : 3 ≤ superposedFluxPrimaryDepth M E :=
    Nat.le_floor hrateThree
  have hfirst : Real.exp (-superposedFluxRate M E) ≤
      Real.exp (-(superposedFluxRate M E / 4)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hsecond : (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2)) ≤
      Real.exp (-(superposedFluxRate M E / 4)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_le_exp.mpr ?_
    have hk₀0 : 0 ≤ (superposedFluxPrimaryDepth M E : ℝ) := Nat.cast_nonneg _
    have hlog : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
    have hprod : 0 ≤ (Real.log 3 - 1) * (superposedFluxPrimaryDepth M E : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hlog) hk₀0
    nlinarith [hprod]
  have hsum : Real.exp (-superposedFluxRate M E) +
        (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2)) ≤
      2 * Real.exp (-(superposedFluxRate M E / 4)) := by
    linarith
  have hscaled : 9 * (99 : ℝ) ^ d *
        (Real.exp (-superposedFluxRate M E) +
          (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2))) ≤
      Real.exp (-(superposedFluxRate M E / 8)) := by
    calc
      9 * (99 : ℝ) ^ d *
            (Real.exp (-superposedFluxRate M E) +
              (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2))) ≤
          9 * (99 : ℝ) ^ d *
            (2 * Real.exp (-(superposedFluxRate M E / 4))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 * (9 * (99 : ℝ) ^ d)) *
          Real.exp (-(superposedFluxRate M E / 4)) := by ring
      _ ≤ Real.exp (superposedFluxRate M E / 8) *
          Real.exp (-(superposedFluxRate M E / 4)) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ = Real.exp (-(superposedFluxRate M E / 8)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hkp : Real.exp (-(superposedFluxRate M E / 8)) ≤
      Real.exp (-(superposedFluxRareDepth M E : ℝ)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact ⟨hk₀three, by simpa only [superposedFluxRate] using hk₀le,
    by simpa only [superposedFluxRate] using hscaled.trans hkp⟩


/-- The rate-compatible real choices together with the two integer choices
discharge the complete scalar interface of the local payoff.  Their local
exponent is exactly `7 * gamma`; consequently every occurrence of the primary
depth in the eventual profile estimate is multiplied by `gamma`.

The `hmax` argument is an internal conditional A obligation inherited from
`profileAuxiliaryConst`; it is discharged downstream because the terminal
constant `superposedFluxLowerConst d` dominates `profileAuxiliaryConst d`.
Thus no numerical gate remains exposed by the terminal lower-leg composition,
even though this intermediate helper remains conditional. -/
theorem superposedFluxRateCompatible_allParameterGates_of_profileAuxiliaryMaxGate
    (hd : 2 ≤ d) (M : ABKModel d) {sigma E : ℝ} (hE : 1 ≤ E)
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    0 < superposedFluxRateEps M ∧
      0 < superposedFluxRateBeta M ∧
      9 * superposedFluxRateBeta M ≤ 1 ∧
      2 * bfaProfileB + 2 * M.gamma + superposedFluxRateEps M ≤
        2 * superposedFluxRateBeta M ∧
      4 * (2 * M.gamma + superposedFluxRateEps M) ≤
        1 - superposedFluxRateBeta M ∧
      3 ≤ superposedFluxPrimaryDepth M E ∧
      ((superposedFluxPrimaryDepth M E : ℕ) : ℝ) ≤
        siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹) ∧
      9 * (99 : ℝ) ^ d *
          (Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
            (3 : ℝ) ^ (-((superposedFluxPrimaryDepth M E : ℝ) / 2))) ≤
        Real.exp (-(superposedFluxRareDepth M E : ℝ)) ∧
      superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M) = 7 * M.gamma ∧
      superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M) ≤ bfaProfileB ∧
      (1 - sigma) / 2 ≤
        bfaTau (bfaProfileSigma sigma)
          (superposedFluxLocalExponent M bfaProfileB
            (superposedFluxRateEps M) (superposedFluxRateBeta M))
          bfaProfileB := by
  have hgamma :=
    gamma_le_three_div_thirty_two_mul_bfaProfileB_mul_sigma_of_profileAuxiliaryMaxGate
      M hE hsigma hmax hEgamma
  have hgammaB : M.gamma ≤ (3 / 64 : ℝ) * bfaProfileB := by
    calc
      M.gamma ≤ (3 / 32 : ℝ) * bfaProfileB * sigma := hgamma
      _ ≤ (3 / 32 : ℝ) * bfaProfileB * (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsigmaHalf
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ = (3 / 64 : ℝ) * bfaProfileB := by ring
  have heps : 0 < superposedFluxRateEps M := by
    exact M.shellPrefix.gamma_pos
  have hbeta : 0 < superposedFluxRateBeta M := by
    unfold superposedFluxRateBeta
    exact add_pos bfaProfileB_pos (mul_pos (by norm_num) M.shellPrefix.gamma_pos)
  have hbeta9 : 9 * superposedFluxRateBeta M ≤ 1 := by
    have hfixed : 9 * ((35 / 32 : ℝ) * bfaProfileB) ≤ 1 := by
      norm_num [bfaProfileB]
    unfold superposedFluxRateBeta
    nlinarith
  have hbetab :
      2 * bfaProfileB + 2 * M.gamma + superposedFluxRateEps M ≤
        2 * superposedFluxRateBeta M := by
    unfold superposedFluxRateEps superposedFluxRateBeta
    linarith [M.shellPrefix.gamma_pos]
  have hgammaWin :
      4 * (2 * M.gamma + superposedFluxRateEps M) ≤
        1 - superposedFluxRateBeta M := by
    have hfixed : (53 / 32 : ℝ) * bfaProfileB ≤ 1 := by
      norm_num [bfaProfileB]
    unfold superposedFluxRateEps superposedFluxRateBeta
    nlinarith
  have hlocalEq :
      superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M) =
        7 * M.gamma := by
    unfold superposedFluxLocalExponent superposedFluxRateEps
      superposedFluxRateBeta
    ring
  have hlocal :
      superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M) ≤
        bfaProfileB := by
    rw [hlocalEq]
    nlinarith [bfaProfileB_pos]
  have hlocalSmall :
      superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M) ≤
        (3 / 2 : ℝ) * bfaProfileB * sigma := by
    rw [hlocalEq]
    nlinarith
  have hlocalPos :
      0 < superposedFluxLocalExponent M bfaProfileB
        (superposedFluxRateEps M) (superposedFluxRateBeta M) := by
    rw [hlocalEq]
    positivity
  have htau : (1 - sigma) / 2 ≤
      bfaTau (bfaProfileSigma sigma)
        (superposedFluxLocalExponent M bfaProfileB
          (superposedFluxRateEps M) (superposedFluxRateBeta M))
        bfaProfileB :=
    half_one_sub_le_bfaTau_profileSigma hsigma hsigmaHalf hlocalPos
      bfaProfileB_pos hlocalSmall
  obtain ⟨hk₀, hk₀rate, hcap⟩ :=
    superposedFluxRateParameterGates_of_profileAuxiliaryMaxGate hd M hE hsigma
      hsigmaHalf hmax hEgamma
  exact ⟨heps, hbeta, hbeta9, hbetab, hgammaWin, hk₀, hk₀rate, hcap,
    hlocalEq, hlocal, htau⟩

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
