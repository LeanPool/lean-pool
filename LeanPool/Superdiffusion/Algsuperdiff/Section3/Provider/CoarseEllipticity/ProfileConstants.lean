/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.WaveBandMean
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaLocalLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaPerCube

/-!
# ProfileConstants

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Parameter arithmetic for the coarse-ellipticity profiles

This file isolates the part of the constant selection for ABK26
`p.cg.ellipticity.bounds` that follows from the exact frozen gates.  It fixes
the manuscript's Step-3 parameter `b = 2^{-20}`, makes the outer
`sigma ↦ sigma / 4` substitution explicit, and proves that a dimension-only
threshold supplies:

* the exponential and `b^{-1}` gates of `e.hsep.tails`;
* the four raw localization/oscillation gates used by the bad-cluster proof;
* the smallness of `gamma / b` needed to retain the frozen Orlicz exponent; and
* the large-rate absorption of a dimension-only prefactor into the frozen rare
  exponential.

## Frozen maximum versus the preliminary package

The older hsep interface assumes the stronger preliminary package

```text
badClustersConst d <= E * cstar M.
```

The frozen hypothesis supplies only `cstar M⁻¹ <= E`, so those two statements
remain non-interchangeable.  The declarations in the raw-gate section below do
not assert the stronger package.  They instead derive exactly what the proof
uses: `4 <= E`, `unitGate M`, `gamma <= 1/20`, `E⁻² <= cstar`, and
`gamma <= E⁻⁵`.  The percolation providers consume those consequences through
their `_of_gates` interfaces.  Final selection of `Clow`, `Cup`, and `Ccg`
still belongs to the coarse-ellipticity assembly.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

/-! ## The fixed Step-3 parameters -/

/-- The manuscript's fixed Whitney-slope parameter `b = 2^{-20}`. -/
def bfaProfileB : ℝ := (2 ^ 20 : ℝ)⁻¹

/-- The `sigma ↦ sigma / 4` substitution used before the two scale sums. -/
def bfaProfileSigma (sigma : ℝ) : ℝ := sigma / 4

theorem bfaProfileB_pos : 0 < bfaProfileB := by
  rw [bfaProfileB]
  positivity

theorem bfaProfileB_le_one_ninth : bfaProfileB ≤ (1 : ℝ) / 9 := by
  rw [bfaProfileB]
  norm_num

theorem bfaProfileB_le_one_eighth : bfaProfileB ≤ (1 : ℝ) / 8 := by
  exact bfaProfileB_le_one_ninth.trans (by norm_num)

theorem bfaProfileSigma_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < bfaProfileSigma sigma := by
  rw [bfaProfileSigma]
  positivity

theorem bfaProfileSigma_le_one_eighth {sigma : ℝ} (hsigma : sigma ≤ 1 / 2) :
    bfaProfileSigma sigma ≤ (1 : ℝ) / 8 := by
  rw [bfaProfileSigma]
  linarith

theorem bfaProfileSigma_le_one_half {sigma : ℝ} (hsigma : sigma ≤ 1 / 2) :
    bfaProfileSigma sigma ≤ (1 : ℝ) / 2 :=
  (bfaProfileSigma_le_one_eighth hsigma).trans (by norm_num)

/-! ## A dimension-only gate constant -/

/-- A dimension-only constant sufficient for the hsep exponential gate, the
fixed `b^{-1}` gate, and the Orlicz-index comparison.  It deliberately does not
encode the unavailable `E * cstar` gate. -/
def profileAuxiliaryConst (d : ℕ) : ℝ :=
  max (4 * badClustersConst d)
    (max (badClustersConst d / bfaProfileB) (2 / (15 * bfaProfileB)))

theorem profileAuxiliaryConst_pos (d : ℕ) : 0 < profileAuxiliaryConst d := by
  have hfour : 0 < (4 : ℝ) * badClustersConst d :=
    mul_pos (by norm_num) (badClustersConst_pos d)
  refine lt_of_lt_of_le hfour ?_
  exact le_max_left _ _

theorem four_mul_badClustersConst_le_profileAuxiliaryConst (d : ℕ) :
    4 * badClustersConst d ≤ profileAuxiliaryConst d :=
  le_max_left _ _

theorem badClustersConst_div_bfaProfileB_le_profileAuxiliaryConst (d : ℕ) :
    badClustersConst d / bfaProfileB ≤ profileAuxiliaryConst d :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem two_div_fifteen_mul_bfaProfileB_le_profileAuxiliaryConst (d : ℕ) :
    2 / (15 * bfaProfileB) ≤ profileAuxiliaryConst d :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The frozen exponential gate at `sigma` supplies the hsep gate at the
auxiliary index `sigma / 4`. -/
theorem exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate
    {d : ℕ} {sigma E : ℝ} (hsigma : 0 < sigma)
    (hgate : Real.exp (profileAuxiliaryConst d / sigma) ≤ E) :
    Real.exp (badClustersConst d / bfaProfileSigma sigma) ≤ E := by
  have harg : badClustersConst d / bfaProfileSigma sigma ≤
      profileAuxiliaryConst d / sigma := by
    rw [bfaProfileSigma]
    have hfour := four_mul_badClustersConst_le_profileAuxiliaryConst d
    calc
      badClustersConst d / (sigma / 4) = (4 * badClustersConst d) / sigma := by
        field_simp
      _ ≤ profileAuxiliaryConst d / sigma :=
        div_le_div_of_nonneg_right hfour hsigma.le
  exact (Real.exp_le_exp.2 harg).trans hgate

/-- The same frozen exponential gate pays the fixed `b^{-1}` threshold. -/
theorem badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
    {d : ℕ} {sigma E : ℝ} (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hgate : Real.exp (profileAuxiliaryConst d / sigma) ≤ E) :
    badClustersConst d / bfaProfileB ≤ E := by
  have hCnonneg : 0 ≤ profileAuxiliaryConst d := (profileAuxiliaryConst_pos d).le
  have hsigmaOne : sigma ≤ 1 := hsigmaHalf.trans (by norm_num)
  have hinv : 1 ≤ sigma⁻¹ := one_le_inv_of_le_one hsigma hsigmaOne
  have hCdiv : profileAuxiliaryConst d ≤ profileAuxiliaryConst d / sigma := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right hCnonneg hinv
  have hself : profileAuxiliaryConst d / sigma ≤
      Real.exp (profileAuxiliaryConst d / sigma) := by
    linarith [Real.add_one_le_exp (profileAuxiliaryConst d / sigma)]
  exact (badClustersConst_div_bfaProfileB_le_profileAuxiliaryConst d).trans
    (hCdiv.trans (hself.trans hgate))

/-! ## The raw bad-event gates from the frozen maximum -/

/-- The exponential branch of the frozen maximum is already large enough to
force the local-probability gate `4 <= E`. -/
theorem four_le_of_profileAuxiliaryMaxGate {d : ℕ} {M : ABKModel d} {sigma E : ℝ}
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hgate : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E) :
    4 ≤ E := by
  have hC0 : 0 ≤ profileAuxiliaryConst d := (profileAuxiliaryConst_pos d).le
  have hsigmaOne : sigma ≤ 1 := hsigmaHalf.trans (by norm_num)
  have hinv : 1 ≤ sigma⁻¹ := one_le_inv_of_le_one hsigma hsigmaOne
  have hCdiv : profileAuxiliaryConst d ≤ profileAuxiliaryConst d / sigma := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right hC0 hinv
  have hself : profileAuxiliaryConst d / sigma ≤
      Real.exp (profileAuxiliaryConst d / sigma) := by
    linarith [Real.add_one_le_exp (profileAuxiliaryConst d / sigma)]
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ E :=
    (le_max_left _ _).trans hgate
  have hC4 : (4 : ℝ) ≤ profileAuxiliaryConst d := by
    have hbad := twentyOne_le_badClustersConst d
    have hfour := four_mul_badClustersConst_le_profileAuxiliaryConst d
    linarith
  exact hC4.trans (hCdiv.trans (hself.trans hexp))

/-- The inverse branch of the frozen maximum, rewritten without inversion. -/
theorem inv_le_cstar_of_profileAuxiliaryMaxGate {d : ℕ} {M : ABKModel d}
    {sigma E : ℝ} (hE : 1 ≤ E)
    (hgate : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E) :
    E⁻¹ ≤ Algsuperdiff.Section3.Disorder.cstar M := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  exact (inv_le_comm₀ hE0 hc).2 ((le_max_right _ _).trans hgate)

/-- The inverse branch also gives the weaker square-inverse gate used by the
printed oscillation tail. -/
theorem inv_sq_le_cstar_of_profileAuxiliaryMaxGate {d : ℕ} {M : ABKModel d}
    {sigma E : ℝ} (hE : 1 ≤ E)
    (hgate : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E) :
    E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hinv0 : (0 : ℝ) ≤ E⁻¹ := (inv_pos.2 hE0).le
  have hinv1 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE
  have hsquare : E⁻¹ ^ 2 ≤ E⁻¹ := by nlinarith
  exact hsquare.trans (inv_le_cstar_of_profileAuxiliaryMaxGate hE hgate)

/-- A lower bound on `cstar * gamma⁻¹` opens the threshold of the oscillation
weak-Orlicz tail. -/
theorem unitGate_of_cstar_mul_gammaInv {d : ℕ} (M : ABKModel d)
    (hratio : 25 / deltaOsc d ^ 2 ≤
      Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) :
    unitGate M := by
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hdelta : 0 < deltaOsc d := deltaOsc_pos d
  have hsq : Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
      (Real.sqrt M.gamma)⁻¹ =
      Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_inv]
  have hfive : (5 : ℝ) / deltaOsc d ≤
      Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) := by
    have hnn : (0 : ℝ) ≤ 5 / deltaOsc d := by positivity
    rw [show (5 : ℝ) / deltaOsc d = Real.sqrt ((5 / deltaOsc d) ^ 2) by
      rw [Real.sqrt_sq hnn]]
    refine Real.sqrt_le_sqrt ?_
    have h25 : (5 / deltaOsc d) ^ 2 = 25 / deltaOsc d ^ 2 := by
      field_simp
      norm_num
    rw [h25]
    exact hratio
  unfold unitGate
  rw [mul_assoc, mul_assoc, hsq]
  have hstep : (1 / 5 : ℝ) * (deltaOsc d * (5 / deltaOsc d)) = 1 := by
    field_simp
  calc
    (1 : ℝ) = (1 / 5 : ℝ) * (deltaOsc d * (5 / deltaOsc d)) := hstep.symm
    _ ≤ (1 / 5 : ℝ) * (deltaOsc d *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hfive hdelta.le

/-- The exact frozen maximum and fifth-root gates imply the oscillation
threshold gate, without the stronger preliminary assumption
`C <= E * cstar`. -/
theorem unitGate_of_profileAuxiliaryMaxGate {d : ℕ} (M : ABKModel d)
    {sigma E : ℝ} (hE : 1 ≤ E) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    unitGate M := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hEne : E ≠ 0 := ne_of_gt hE0
  have hc : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hinvC := inv_le_cstar_of_profileAuxiliaryMaxGate (M := M) hE hmax
  have hgamma5 : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ :=
    gamma_le_inv_pow_five hE hg hEgamma
  have hgammaInv : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ (pow_pos hE0 5) hg]
    exact hgamma5
  have hE4ratio : E ^ 4 ≤
      Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
    have hmul := mul_le_mul hinvC hgammaInv (pow_nonneg hE0.le 5) hc.le
    have heq : E⁻¹ * E ^ (5 : ℕ) = E ^ 4 := by field_simp
    rwa [heq] at hmul
  have hAprofile : 25 / deltaOsc d ^ 2 ≤ profileAuxiliaryConst d := by
    calc
      25 / deltaOsc d ^ 2 ≤ admissibleConst d := le_max_left _ _
      _ ≤ badClustersConst d := admissibleConst_le_badClustersConst d
      _ ≤ 4 * badClustersConst d := by
        have hbad := badClustersConst_pos d
        nlinarith
      _ ≤ profileAuxiliaryConst d := four_mul_badClustersConst_le_profileAuxiliaryConst d
  have hC0 : 0 ≤ profileAuxiliaryConst d := (profileAuxiliaryConst_pos d).le
  have hsigmaOne : sigma ≤ 1 := hsigmaHalf.trans (by norm_num)
  have hinvSigma : 1 ≤ sigma⁻¹ := one_le_inv_of_le_one hsigma hsigmaOne
  have hCdiv : profileAuxiliaryConst d ≤ profileAuxiliaryConst d / sigma := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right hC0 hinvSigma
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ E :=
    (le_max_left _ _).trans hmax
  have hargExp : profileAuxiliaryConst d / sigma ≤
      Real.exp (profileAuxiliaryConst d / sigma) := by
    linarith [Real.add_one_le_exp (profileAuxiliaryConst d / sigma)]
  have hAE : 25 / deltaOsc d ^ 2 ≤ E :=
    hAprofile.trans (hCdiv.trans (hargExp.trans hexp))
  have hEpow : E ≤ E ^ 4 := by
    have hcube : (1 : ℝ) ≤ E ^ 3 := one_le_pow₀ hE
    calc
      E = E * 1 := (mul_one E).symm
      _ ≤ E * E ^ 3 := mul_le_mul_of_nonneg_left hcube hE0.le
      _ = E ^ 4 := by ring
  exact unitGate_of_cstar_mul_gammaInv M (hAE.trans (hEpow.trans hE4ratio))

/-- The frozen fifth-root gate in the integer-power form consumed by the
percolation and multiscale providers. -/
theorem gamma_le_zpow_neg_five_of_frozenGate {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma : 0 < gamma) (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ))) :
    gamma ≤ E ^ (-5 : ℤ) := by
  have h := gamma_le_inv_pow_five hE hgamma hEgamma
  have hpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rwa [hpow]

/-- The four raw probability gates and the integer fifth-power tuning obtained
from the exact frozen hypotheses. -/
theorem badEventGates_of_profileAuxiliaryMaxGate {d : ℕ} (M : ABKModel d)
    {sigma E : ℝ} (hE : 1 ≤ E) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    4 ≤ E ∧ unitGate M ∧ M.gamma ≤ 1 / 20 ∧
      E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M ∧
      M.gamma ≤ E ^ (-5 : ℤ) := by
  have hE4 := four_le_of_profileAuxiliaryMaxGate hsigma hsigmaHalf hmax
  have hgamma := gamma_le_zpow_neg_five_of_frozenGate hE M.shellPrefix.gamma_pos hEgamma
  exact ⟨hE4, unitGate_of_profileAuxiliaryMaxGate M hE hsigma hsigmaHalf hmax hEgamma,
    gamma_le_one_div_twenty_of_four_le M hE4 hgamma,
    inv_sq_le_cstar_of_profileAuxiliaryMaxGate hE hmax, hgamma⟩

/-! ## The frozen exponent after the `sigma / 4` substitution -/

/-- The elementary decay estimate used to turn the exponential threshold into
`gamma / b = O(sigma)`. -/
theorem zpow_neg_five_le_three_halves_mul_of_exp_div_le
    {C b sigma E : ℝ} (hC : 0 < C) (hb : 0 < b) (hsigma : 0 < sigma)
    (hfloor : 2 / (15 * b) ≤ C) (hgate : Real.exp (C / sigma) ≤ E) :
    E ^ (-5 : ℤ) ≤ (3 / 2 : ℝ) * b * sigma := by
  have hE : 0 < E := (Real.exp_pos _).trans_le hgate
  have hinv : E⁻¹ ≤ (Real.exp (C / sigma))⁻¹ :=
    by simpa only [one_div] using
      one_div_le_one_div_of_le (Real.exp_pos (C / sigma)) hgate
  have hpow : (E⁻¹) ^ 5 ≤ ((Real.exp (C / sigma))⁻¹) ^ 5 :=
    pow_le_pow_left₀ (inv_nonneg.2 hE.le) hinv 5
  have hpow' : E ^ (-5 : ℤ) ≤ Real.exp (-(5 * C / sigma)) := by
    have hEpow : E ^ (-5 : ℤ) = (E⁻¹) ^ 5 := by
      calc
        E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
          rw [zpow_neg]
          norm_cast
        _ = (E⁻¹) ^ 5 := (inv_pow E 5).symm
    have hexpPow : ((Real.exp (C / sigma))⁻¹) ^ 5 =
        Real.exp (-(5 * C / sigma)) := by
      calc
        ((Real.exp (C / sigma))⁻¹) ^ 5 =
            (Real.exp (-(C / sigma))) ^ 5 := by rw [Real.exp_neg]
        _ = Real.exp ((5 : ℝ) * (-(C / sigma))) :=
          (Real.exp_nat_mul (-(C / sigma)) 5).symm
        _ = Real.exp (-(5 * C / sigma)) := by
          congr 1
          ring_nf
    rw [hEpow, ← hexpPow]
    exact hpow
  have hx : 0 < 5 * C / sigma := by positivity
  have hxexp : 5 * C / sigma ≤ Real.exp (5 * C / sigma) := by
    linarith [Real.add_one_le_exp (5 * C / sigma)]
  have hexpInv : Real.exp (-(5 * C / sigma)) ≤ (5 * C / sigma)⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hx hxexp
  have hbc : 2 ≤ 15 * b * C := by
    have hpos : 0 < 15 * b := by positivity
    have h := (div_le_iff₀ hpos).mp hfloor
    nlinarith
  have hcoef : (5 * C)⁻¹ ≤ (3 / 2 : ℝ) * b := by
    rw [inv_le_iff_one_le_mul₀ (by positivity : 0 < 5 * C)]
    nlinarith
  have hinvEval : (5 * C / sigma)⁻¹ = sigma * (5 * C)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  calc
    E ^ (-5 : ℤ) ≤ Real.exp (-(5 * C / sigma)) := hpow'
    _ ≤ (5 * C / sigma)⁻¹ := hexpInv
    _ = sigma * (5 * C)⁻¹ := hinvEval
    _ ≤ sigma * ((3 / 2 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left hcoef hsigma.le
    _ = (3 / 2 : ℝ) * b * sigma := by ring_nf

theorem zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
    {d : ℕ} {sigma E : ℝ} (hsigma : 0 < sigma)
    (hgate : Real.exp (profileAuxiliaryConst d / sigma) ≤ E) :
    E ^ (-5 : ℤ) ≤ (3 / 2 : ℝ) * bfaProfileB * sigma := by
  exact zpow_neg_five_le_three_halves_mul_of_exp_div_le
    (profileAuxiliaryConst_pos d) bfaProfileB_pos hsigma
    (two_div_fifteen_mul_bfaProfileB_le_profileAuxiliaryConst d) hgate

/-- If `gamma / b` is paid by the frozen exponential gate, the internal B lane is
at least as strong as the frozen `Gamma_{(1-sigma)/2}` lane. -/
theorem half_one_sub_le_bfaTau_profileSigma {sigma gam b : ℝ}
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2) (hgam : 0 < gam)
    (hb : 0 < b) (hsmall : gam ≤ (3 / 2 : ℝ) * b * sigma) :
    (1 - sigma) / 2 ≤ bfaTau (bfaProfileSigma sigma) gam b := by
  have hsigmaOne : sigma ≤ 1 := hsigmaHalf.trans (by norm_num)
  have hgam' : (1 - sigma) * gam ≤ (3 / 2 : ℝ) * b * sigma := by
    calc
      (1 - sigma) * gam ≤ 1 * gam :=
        mul_le_mul_of_nonneg_right (by linarith) hgam.le
      _ = gam := one_mul _
      _ ≤ (3 / 2 : ℝ) * b * sigma := hsmall
  rw [bfaTau, bfaPower, bfaProfileSigma]
  have hden : 0 < (gam + 2 * b) / b := by positivity
  rw [le_div_iff₀ hden]
  field_simp
  nlinarith


/-! ## Absorbing dimension-only factors at a large rare rate -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
