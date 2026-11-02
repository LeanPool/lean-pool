/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQPresplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQLtTwoPresplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileCloseEndpoint

/-!
# SuperposedFluxLowerProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Quantitative profile and exact lower coarse-ellipticity provider

This file develops the quantitative profile needed to turn the sharp
superposed-flux payoff into the representative and three exponent branches.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Filter MeasureTheory Topology
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

private theorem sq_le_one_of_nonneg_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 ≤ 1 := by
  simpa only [pow_two, mul_one] using mul_self_le_mul_self hx0 hx1

private theorem sharp_good_exponent_chunk {g p q s : ℝ}
    (hg : g ≤ 1 / 20) (hp : g * p ≤ s / 16) (hq : g * q ≤ s / 2)
    (hs : 0 ≤ s) :
    3 * g * (p + 1) + 3 * g * q ≤ 2 * s + 2 := by
  calc
    3 * g * (p + 1) + 3 * g * q = 3 * (g * p + g) + 3 * (g * q) := by ring
    _ ≤ 3 * (s / 16 + 1 / 20) + 3 * (s / 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hp hg) (by norm_num))
        (mul_le_mul_of_nonneg_left hq (by norm_num))
    _ ≤ 2 * s + 2 := by linarith only [hs]

private theorem inv_sq_le_one_of_one_le {E : ℝ} (hE : 1 ≤ E) :
    E⁻¹ ^ 2 ≤ 1 := by
  have h0 : 0 ≤ E⁻¹ := (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hE)).le
  have h1 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE
  exact sq_le_one_of_nonneg_of_le_one h0 h1

private theorem gamma_mul_superposedFluxRate (M : ABKModel d) (E : ℝ) :
    M.gamma * superposedFluxRate M E = siteRateBase d / 2 * E⁻¹ ^ 2 := by
  unfold superposedFluxRate
  rw [show M.gamma *
      (siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)) =
    siteRateBase d / 2 * E⁻¹ ^ 2 * (M.gamma * M.gamma⁻¹) by ring,
    mul_inv_cancel₀ M.shellPrefix.gamma_pos.ne', mul_one]

private theorem gamma_mul_superposedFluxRate_le (M : ABKModel d) {E : ℝ}
    (hE : 1 ≤ E) :
    M.gamma * superposedFluxRate M E ≤ siteRateBase d / 2 := by
  rw [gamma_mul_superposedFluxRate]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (inv_sq_le_one_of_one_le hE)
      (div_nonneg (siteRateBase_pos d).le (by norm_num : (0 : ℝ) ≤ 2))

private theorem sharp_good_power_le (M : ABKModel d) {E : ℝ}
    (hE : 1 ≤ E) (hgamma20 : M.gamma ≤ 1 / 20)
    {k₀ kp k : ℕ}
    (hk₀ : (k₀ : ℝ) ≤ superposedFluxRate M E)
    (hkp : (kp : ℝ) ≤ superposedFluxRate M E / 8) :
    (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ ((3 * M.gamma) * ((kp : ℝ) + 1)) *
        (3 : ℝ) ^ ((3 * M.gamma) * (k₀ : ℝ)) ≤
      (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (2 * siteRateBase d + 2) := by
  have hg0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hr0 : 0 ≤ superposedFluxRate M E :=
    (superposedFluxRate_pos M (lt_of_lt_of_le zero_lt_one hE)).le
  have hkp' : M.gamma * (kp : ℝ) ≤ siteRateBase d / 16 := by
    have hmul := mul_le_mul_of_nonneg_left hkp hg0
    have hrate := gamma_mul_superposedFluxRate_le M hE
    calc
      M.gamma * (kp : ℝ) ≤ M.gamma * (superposedFluxRate M E / 8) := hmul
      _ = (M.gamma * superposedFluxRate M E) / 8 := by ring
      _ ≤ (siteRateBase d / 2) / 8 :=
        div_le_div_of_nonneg_right hrate (by norm_num)
      _ = siteRateBase d / 16 := by ring
  have hk₀' : M.gamma * (k₀ : ℝ) ≤ siteRateBase d / 2 :=
    (mul_le_mul_of_nonneg_left hk₀ hg0).trans
      (gamma_mul_superposedFluxRate_le M hE)
  have hsite0 : 0 ≤ siteRateBase d := (siteRateBase_pos d).le
  have hexp :
      M.gamma * (k : ℝ) + 3 * M.gamma * ((kp : ℝ) + 1) +
          3 * M.gamma * (k₀ : ℝ) ≤
        M.gamma * (k : ℝ) + (2 * siteRateBase d + 2) := by
    calc
      M.gamma * (k : ℝ) + 3 * M.gamma * ((kp : ℝ) + 1) +
          3 * M.gamma * (k₀ : ℝ) =
        M.gamma * (k : ℝ) +
          (3 * M.gamma * ((kp : ℝ) + 1) + 3 * M.gamma * (k₀ : ℝ)) := by ring
      _ ≤ M.gamma * (k : ℝ) + (2 * siteRateBase d + 2) :=
        add_le_add_right (sharp_good_exponent_chunk hgamma20 hkp' hk₀' hsite0) _
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

private theorem sharp_collar_power_le (M : ABKModel d) {E beta : ℝ}
    (hE : 1 ≤ E) (hbeta9 : 9 * beta ≤ 1) {k₀ k : ℕ}
    (hk₀ : (k₀ : ℝ) ≤ superposedFluxRate M E) :
    (3 : ℝ) ^ (M.gamma * (k : ℝ)) * (3 : ℝ) ^ (2 * beta) *
        (3 : ℝ) ^ ((3 * M.gamma) * (k₀ : ℝ)) ≤
      (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (2 * siteRateBase d + 2) := by
  have hg0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hk₀' : M.gamma * (k₀ : ℝ) ≤ siteRateBase d / 2 :=
    (mul_le_mul_of_nonneg_left hk₀ hg0).trans
      (gamma_mul_superposedFluxRate_le M hE)
  have hsite0 : 0 ≤ siteRateBase d := (siteRateBase_pos d).le
  have hexp : M.gamma * (k : ℝ) + 2 * beta + 3 * M.gamma * (k₀ : ℝ) ≤
      M.gamma * (k : ℝ) + (2 * siteRateBase d + 2) := by
    linarith only [hbeta9, hk₀', hsite0]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- The sharp deterministic slot has the required dimension-only geometric
profile. -/
theorem superposedFluxSharpConst_le_profile (hd : 2 ≤ d) (M : ABKModel d)
    (m : ℤ) (k : ℕ) {E : ℝ} (hE : 1 ≤ E)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hbeta9 : 9 * superposedFluxRateBeta M ≤ 1)
    (hk₀ : ((superposedFluxPrimaryDepth M E : ℕ) : ℝ) ≤
      superposedFluxRate M E) :
    superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
        (superposedFluxRateEps M) (superposedFluxRateBeta M)
        (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E) ≤
      superposedFluxSharpDetConst d * (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  obtain ⟨_, _, hkp, _⟩ := superposedFluxDepth_floorWindows M hE0
  have hgood := sharp_good_power_le M hE hgamma20 hk₀ hkp (k := k)
  have hcollar := sharp_collar_power_le M hE hbeta9 hk₀ (k := k)
  have hI : 0 ≤ (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr three_rpow_neg_quarter_lt_one)).le
  have hK : 0 ≤ superposedFluxKBase d := by
    unfold superposedFluxKBase
    exact mul_nonneg (by norm_num) (simplexCrudeConst_nonneg d (by norm_num))
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmass : 0 ≤ 6 * (d : ℝ) := mul_nonneg (by norm_num) hd0
  have hsqrt : 0 ≤ Real.sqrt (6 * (d : ℝ)) := Real.sqrt_nonneg _
  let per : ℝ :=
    (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
      (superposedFluxKBase d * (6 * (d : ℝ)) +
        8 * (superposedDivConst d) ^ 2 * superposedFluxKBase d *
          Real.sqrt (6 * (d : ℝ))) *
      (3 : ℝ) ^ (2 * siteRateBase d + 2) *
      (3 : ℝ) ^ (M.gamma * (k : ℝ))
  rw [superposedFluxSharpConst, superposedFluxCoordinateConst, Finset.sum_mul]
  calc
    _ ≤ ∑ _j : Fin d, per := by
      apply Finset.sum_le_sum
      intro j _
      rw [layerSumConst,
      ktotConst_flux_basis_eq M (m - 1 - (k : ℤ)) (m - 1) j]
      have hscale :
          M.gamma * (((m - 1 : ℤ) : ℝ) - ((m - 1 - (k : ℤ) : ℤ) : ℝ)) =
            M.gamma * (k : ℝ) := by
        push_cast
        ring
      rw [hscale]
      change _ ≤ per
      calc
        (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
            (superposedFluxKBase d * (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                (6 * (d : ℝ)) *
                (3 : ℝ) ^ ((2 * M.gamma + superposedFluxRateEps M) *
                  (((superposedFluxRareDepth M E : ℕ) : ℝ) + 1)) +
              2 * (4 * (superposedDivConst d) ^ 2 *
                  (superposedFluxKBase d *
                    (3 : ℝ) ^ (M.gamma * (k : ℝ))) *
                Real.sqrt (6 * (d : ℝ))) *
                (3 : ℝ) ^ (2 * superposedFluxRateBeta M)) *
            (3 : ℝ) ^
              ((2 * M.gamma + superposedFluxRateEps M) *
                ((superposedFluxPrimaryDepth M E : ℕ) : ℝ)) =
          (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
            (superposedFluxKBase d * (6 * (d : ℝ)) *
                ((3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                  (3 : ℝ) ^ ((3 * M.gamma) *
                    (((superposedFluxRareDepth M E : ℕ) : ℝ) + 1)) *
                  (3 : ℝ) ^ ((3 * M.gamma) *
                    ((superposedFluxPrimaryDepth M E : ℕ) : ℝ))) +
              8 * (superposedDivConst d) ^ 2 * superposedFluxKBase d *
                Real.sqrt (6 * (d : ℝ)) *
                ((3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                  (3 : ℝ) ^ (2 * superposedFluxRateBeta M) *
                  (3 : ℝ) ^ ((3 * M.gamma) *
                    ((superposedFluxPrimaryDepth M E : ℕ) : ℝ)))) := by
          unfold superposedFluxRateEps
          ring_nf
        _ ≤ (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
            (superposedFluxKBase d * (6 * (d : ℝ)) *
                ((3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                  (3 : ℝ) ^ (2 * siteRateBase d + 2)) +
              8 * (superposedDivConst d) ^ 2 * superposedFluxKBase d *
                Real.sqrt (6 * (d : ℝ)) *
                ((3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                  (3 : ℝ) ^ (2 * siteRateBase d + 2))) := by
          gcongr
        _ = per := by
          dsimp only [per]
          ring
    _ = superposedFluxSharpDetConst d *
        (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      dsimp only [per]
      unfold superposedFluxSharpDetConst
      ring

/-! ## Exponential rate of the sharp random slot -/

/-- The retained rare rate after paying the collar shift. -/
def superposedFluxSharpRareRate (d : ℕ) : ℝ := siteRateBase d / 1152

theorem superposedFluxSharpRareRate_pos (d : ℕ) :
    0 < superposedFluxSharpRareRate d := by
  unfold superposedFluxSharpRareRate
  exact div_pos (siteRateBase_pos d) (by norm_num)

/-- The collar shift consumes at most half of the `kp/36` rate. -/
theorem superposedFluxSharpRare_le_exp_rate (M : ABKModel d)
    {sigma E : ℝ} (hE : 1 ≤ E) (hsigma : 0 < sigma)
    (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    superposedFluxSharpRare (superposedFluxRateBeta M)
        (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E) ≤
      Real.exp (1 / 36 : ℝ) *
        Real.exp (-(superposedFluxSharpRareRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
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
  have hbeta : superposedFluxRateBeta M ≤ (35 / 32 : ℝ) * bfaProfileB := by
    unfold superposedFluxRateBeta
    linarith only [hgammaB]
  have hbeta0 : 0 ≤ superposedFluxRateBeta M := by
    unfold superposedFluxRateBeta
    exact add_nonneg bfaProfileB_pos.le
      (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
  have hcoef :
      2 * superposedFluxRateBeta M * Real.log 3 ≤ (1 / 576 : ℝ) := by
    have hlog : Real.log 3 ≤ 2 := log_three_le_two
    calc
      2 * superposedFluxRateBeta M * Real.log 3 ≤
          2 * ((35 / 32 : ℝ) * bfaProfileB) * Real.log 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbeta (by norm_num))
          (lt_trans zero_lt_one one_lt_log_three).le
      _ ≤ 2 * ((35 / 32 : ℝ) * bfaProfileB) * 2 :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) bfaProfileB_pos.le))
      _ ≤ (1 / 576 : ℝ) := by norm_num [bfaProfileB]
  have hcoef0 : 0 ≤ 2 * superposedFluxRateBeta M * Real.log 3 :=
    mul_nonneg (mul_nonneg (by norm_num) hbeta0)
      (lt_trans zero_lt_one one_lt_log_three).le
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  obtain ⟨hk₀, _, hkp, hkpUpper⟩ := superposedFluxDepth_floorWindows M hE0
  have hrate0 : 0 ≤ superposedFluxRate M E :=
    (superposedFluxRate_pos M hE0).le
  have hprimary :
      2 * superposedFluxRateBeta M *
          (superposedFluxPrimaryDepth M E : ℝ) * Real.log 3 ≤
        superposedFluxRate M E / 576 := by
    have hmulDepth := mul_le_mul hcoef hk₀ (Nat.cast_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 576)
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hmulDepth
  have hrareFloor : superposedFluxRate M E / 8 - 1 ≤
      (superposedFluxRareDepth M E : ℝ) := by
    linarith
  have hexponent :
      2 * superposedFluxRateBeta M *
          (superposedFluxPrimaryDepth M E : ℝ) * Real.log 3 -
          (superposedFluxRareDepth M E : ℝ) / 36 ≤
        1 / 36 - superposedFluxRate M E / 576 := by
    linarith only [hprimary, hrareFloor]
  have hrateEq : superposedFluxRate M E / 576 =
      superposedFluxSharpRareRate d * (E⁻¹ ^ 2 * M.gamma⁻¹) := by
    unfold superposedFluxRate superposedFluxSharpRareRate
    ring
  unfold superposedFluxSharpRare superposedFluxRare
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← hrateEq]
  linarith only [hexponent]

/-! ## Uniform constants on the fixed B parameter window -/

/-- Uniform amplitude of the minimal-separation tail on
`0 < sigma / 4 ≤ 1/8`. -/
def superposedFluxHsepConst : ℝ :=
  hsepAmplitude (1 / 8) bfaProfileB

theorem superposedFluxHsepConst_pos : 0 < superposedFluxHsepConst := by
  unfold superposedFluxHsepConst
  exact hsepAmplitude_pos _ _

private theorem hsepTailConst_le_profile {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8) :
    hsepTailConst sigma bfaProfileB ≤ hsepTailConst (1 / 8) bfaProfileB := by
  have hs1 : sigma < 1 := hsigma.trans_lt (by norm_num)
  have hbase :
      (1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3 ≤
        (1 - sigma) * bfaProfileB * Real.log 3 := by
    have hbLog : 0 ≤ bfaProfileB * Real.log 3 :=
      mul_nonneg bfaProfileB_pos.le (lt_trans zero_lt_one one_lt_log_three).le
    calc
      (1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3 =
          (1 - (1 / 8 : ℝ)) * (bfaProfileB * Real.log 3) := by ring
      _ ≤ (1 - sigma) * (bfaProfileB * Real.log 3) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hsigma 1) hbLog
      _ = (1 - sigma) * bfaProfileB * Real.log 3 := by ring
  have hleftPos : 0 < 1 - Real.exp
      (-((1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have : 0 < (1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3 := by
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
  have hden : 1 - Real.exp
        (-((1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3)) ≤
      1 - Real.exp (-((1 - sigma) * bfaProfileB * Real.log 3)) := by
    have hexp : Real.exp (-((1 - sigma) * bfaProfileB * Real.log 3)) ≤
        Real.exp (-((1 - (1 / 8 : ℝ)) * bfaProfileB * Real.log 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  unfold hsepTailConst
  have hinv := (inv_le_inv₀ hrightPos hleftPos).2 hden
  linarith

theorem hsepAmplitude_le_superposedFluxHsepConst {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8) :
    hsepAmplitude sigma bfaProfileB ≤ superposedFluxHsepConst := by
  have htail := hsepTailConst_le_profile hsigma0 hsigma
  have htailTwo := two_le_hsepTailConst
    (sigma := sigma) (b := bfaProfileB) (hsigma.trans (by norm_num)) bfaProfileB_pos
  have htailTwo' := two_le_hsepTailConst
    (sigma := (1 / 8 : ℝ)) (b := bfaProfileB) (by norm_num) bfaProfileB_pos
  have hlog := Real.log_le_log (by linarith) htail
  have hleft : 0 ≤ 1 + Real.log (hsepTailConst sigma bfaProfileB) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ hsepTailConst sigma bfaProfileB)
    linarith
  have hright : 0 ≤ 1 + Real.log (hsepTailConst (1 / 8) bfaProfileB) := by
    have := Real.log_nonneg
      (by linarith : (1 : ℝ) ≤ hsepTailConst (1 / 8) bfaProfileB)
    linarith
  have hab :
      1 + Real.log (hsepTailConst sigma bfaProfileB) ≤
        1 + Real.log (hsepTailConst (1 / 8) bfaProfileB) := by
    linarith
  have hsq := (sq_le_sq₀ hleft hright).2 hab
  simpa [superposedFluxHsepConst, hsepAmplitude] using
    add_le_add_left (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)) 3

/-- A uniform bound for the triangle constant once the B exponent is at least
`1/4`. -/
def superposedFluxTriangleConst : ℝ := 4 * (625 : ℝ) ^ (12 : ℝ)

theorem gammaTriangleConst_le_superposedFluxTriangleConst {tau : ℝ}
    (htau : 1 / 4 ≤ tau) :
    gammaTriangleConst tau ≤ superposedFluxTriangleConst := by
  have htau0 : 0 < tau := lt_of_lt_of_le (by norm_num) htau
  have hinv : tau⁻¹ ≤ (4 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htau0).2 (by linarith only [htau])
  have hinv0 : 0 ≤ tau⁻¹ := (inv_pos.mpr htau0).le
  have hbase : 1 + tau⁻¹ ≤ (5 : ℝ) := by linarith
  have hp1 : (1 + tau⁻¹) ^ tau⁻¹ ≤ (5 : ℝ) ^ tau⁻¹ :=
    Real.rpow_le_rpow (by linarith) hbase hinv0
  have hp2 : (5 : ℝ) ^ tau⁻¹ ≤ (5 : ℝ) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
  have hgrowth : gammaGrowthConst tau ≤ (625 : ℝ) := by
    unfold gammaGrowthConst
    refine max_le (by norm_num) ?_
    calc
      (1 + tau⁻¹) ^ tau⁻¹ ≤ (5 : ℝ) ^ tau⁻¹ := hp1
      _ ≤ (5 : ℝ) ^ (4 : ℝ) := hp2
      _ = 625 := by norm_num
  unfold gammaTriangleConst superposedFluxTriangleConst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow
      (le_trans zero_le_two (two_le_gammaGrowthConst tau)) hgrowth (by norm_num))
    (by norm_num)

private theorem bfaPower_le_three {gam b : ℝ} (hb : 0 < b) (hgamb : gam ≤ b) :
    bfaPower gam b ≤ 3 := by
  rw [bfaPower, div_le_iff₀ hb]
  linarith

theorem one_fourth_le_bfaTau_of_eighth_window {sigma gam b : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8)
    (hgam : 0 < gam) (hb : 0 < b) (hgamb : gam ≤ b) :
    1 / 4 ≤ bfaTau sigma gam b := by
  have hp0 : 0 < bfaPower gam b := bfaPower_pos hgam hb
  have hp3 : bfaPower gam b ≤ 3 := bfaPower_le_three hb hgamb
  rw [bfaTau, le_div_iff₀ hp0]
  calc
    1 / 4 * bfaPower gam b ≤ 1 / 4 * 3 :=
      mul_le_mul_of_nonneg_left hp3 (by norm_num)
    _ = 3 / 4 := by norm_num
    _ ≤ 3 / 4 + sigma := le_add_of_nonneg_right hsigma0.le
    _ ≤ 1 - sigma := by linarith only [hsigma]

theorem gammaProductConst_le_sixteen_of_eighth_window {sigma gam b : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8)
    (hgam : 0 < gam) (hb : 0 < b) (hgamb : gam ≤ b) :
    HCPolySupport.Book.Ch04.gammaProductConst (1 - sigma)
        (bfaSigmaTwo sigma gam b) ≤ 16 := by
  have hsigma1 : sigma < 1 := hsigma.trans_lt (by norm_num)
  have htau0 : 0 < bfaTau sigma gam b := bfaTau_pos hsigma1 hgam hb
  have htau : 1 / 4 ≤ bfaTau sigma gam b :=
    one_fourth_le_bfaTau_of_eighth_window hsigma0 hsigma hgam hb hgamb
  have hinv : (bfaTau sigma gam b)⁻¹ ≤ (4 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htau0).2 (by linarith only [htau])
  change (2 : ℝ) ^
      (((1 - sigma) * bfaSigmaTwo sigma gam b /
        ((1 - sigma) + bfaSigmaTwo sigma gam b))⁻¹) ≤ 16
  rw [prodSigma_bfaSigmaTwo_eq_bfaTau hsigma1 hgam hb]
  calc
    (2 : ℝ) ^ (bfaTau sigma gam b)⁻¹ ≤ (2 : ℝ) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
    _ = 16 := by norm_num

theorem hsepAmplitude_rpow_bfaPower_le_profile_cube {sigma gam : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8)
    (hgamb : gam ≤ bfaProfileB) :
    hsepAmplitude sigma bfaProfileB ^ bfaPower gam bfaProfileB ≤
      superposedFluxHsepConst ^ (3 : ℝ) := by
  have hK : hsepAmplitude sigma bfaProfileB ≤ superposedFluxHsepConst :=
    hsepAmplitude_le_superposedFluxHsepConst hsigma0 hsigma
  have hKone : 1 ≤ hsepAmplitude sigma bfaProfileB := by
    unfold hsepAmplitude
    linarith only [sq_nonneg (1 + Real.log (hsepTailConst sigma bfaProfileB))]
  have hp3 : bfaPower gam bfaProfileB ≤ 3 :=
    bfaPower_le_three bfaProfileB_pos hgamb
  have hpow : hsepAmplitude sigma bfaProfileB ^ bfaPower gam bfaProfileB ≤
      hsepAmplitude sigma bfaProfileB ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hKone hp3
  have hcube : hsepAmplitude sigma bfaProfileB ^ (3 : ℝ) ≤
      superposedFluxHsepConst ^ (3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hK (by norm_num)
  exact hpow.trans hcube

private theorem three_rpow_neg_b_floor_le {b gam : ℝ}
    (hb : 0 < b) (hgam : 0 < gam) :
    (3 : ℝ) ^ (-(b * ((⌊(81 * gam)⁻¹⌋₊ : ℕ) : ℝ))) ≤
      Real.exp (b * Real.log 3) *
        Real.exp (-((b * Real.log 3 / 81) * gam⁻¹)) := by
  have harg0 : 0 ≤ (81 * gam)⁻¹ := by positivity
  have hfloorLt : (81 * gam)⁻¹ < ((⌊(81 * gam)⁻¹⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor : (81 * gam)⁻¹ - 1 ≤ ((⌊(81 * gam)⁻¹⌋₊ : ℕ) : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfloor hb.le
  have hlog : 0 < Real.log 3 := lt_trans zero_lt_one one_lt_log_three
  have hmulLog := mul_le_mul_of_nonneg_right hmul hlog.le
  have hargEq :
      b * (81 * gam)⁻¹ * Real.log 3 = (b * Real.log 3 / 81) * gam⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    ring
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← hargEq]
  linarith only [hmulLog]

private theorem truncationIndicatorScale_le_profile {sigma gam : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 8)
    (hgam : 0 < gam) (hgamb : gam ≤ bfaProfileB) :
    truncationIndicatorScale bfaProfileB sigma (bfaSigmaTwo sigma gam bfaProfileB)
        (hsepAmplitude sigma bfaProfileB) ⌊(81 * gam)⁻¹⌋₊ ≤
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
        Real.exp (bfaProfileB * Real.log 3) *
        Real.exp (-((bfaProfileB * Real.log 3 / 81) * gam⁻¹)) := by
  let K : ℝ := hsepAmplitude sigma bfaProfileB
  let i : ℕ := ⌊(81 * gam)⁻¹⌋₊
  let r : ℝ := (3 : ℝ) ^ (-(bfaProfileB * (i : ℝ)))
  let p : ℝ := bfaPower gam bfaProfileB - 1
  have hKpos : 0 < K := hsepAmplitude_pos sigma bfaProfileB
  have hKle : K ≤ superposedFluxHsepConst :=
    hsepAmplitude_le_superposedFluxHsepConst hsigma0 hsigma
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrle : r ≤ 1 := by
    dsimp only [r]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg bfaProfileB_pos.le (Nat.cast_nonneg _)))
  have hp1 : 1 ≤ p := by
    dsimp only [p]
    linarith [two_le_bfaPower hgam.le bfaProfileB_pos]
  have hp2 : p ≤ 2 := by
    dsimp only [p]
    linarith [bfaPower_le_three bfaProfileB_pos hgamb]
  have hexponent :
      (1 - sigma) / bfaSigmaTwo sigma gam bfaProfileB = p := by
    have hsigma1 : sigma < 1 := hsigma.trans_lt (by norm_num)
    have hpone : 1 < bfaPower gam bfaProfileB :=
      one_lt_bfaPower hgam bfaProfileB_pos
    rw [bfaSigmaTwo]
    dsimp only [p]
    field_simp [ne_of_gt (by linarith : 0 < 1 - sigma),
      ne_of_gt (by linarith : 0 < bfaPower gam bfaProfileB - 1)]
  let x : ℝ := K * r
  have hxpos : 0 < x := mul_pos hKpos hrpos
  have hxpow : x ^ p ≤ x + x ^ 2 := by
    by_cases hxone : x ≤ 1
    · exact (Real.rpow_le_self_of_le_one hxpos.le hxone hp1).trans
        (le_add_of_nonneg_right (sq_nonneg x))
    · have hxone' : 1 ≤ x := le_of_not_ge hxone
      have hp := Real.rpow_le_rpow_of_exponent_le hxone' hp2
      rw [Real.rpow_two] at hp
      exact hp.trans (le_add_of_nonneg_left hxpos.le)
  have hxle : x ≤ superposedFluxHsepConst * r :=
    mul_le_mul_of_nonneg_right hKle hrpos.le
  have hHpos : 0 < superposedFluxHsepConst := superposedFluxHsepConst_pos
  have hxsq : x ^ 2 ≤ (superposedFluxHsepConst * r) ^ 2 :=
    pow_le_pow_left₀ hxpos.le hxle 2
  have hrSq : r ^ 2 ≤ r := by
    simpa only [pow_two] using mul_le_of_le_one_right hrpos.le hrle
  have hHrSq : (superposedFluxHsepConst * r) ^ 2 ≤
      superposedFluxHsepConst ^ 2 * r := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hrSq (sq_nonneg superposedFluxHsepConst)
  have hprod : x + x ^ 2 ≤
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) * r := by
    calc
      x + x ^ 2 ≤ superposedFluxHsepConst * r +
          (superposedFluxHsepConst * r) ^ 2 := add_le_add hxle hxsq
      _ ≤ superposedFluxHsepConst * r + superposedFluxHsepConst ^ 2 * r := by
        exact add_le_add le_rfl hHrSq
      _ = (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) * r := by ring
  have hrExp : r ≤ Real.exp (bfaProfileB * Real.log 3) *
      Real.exp (-((bfaProfileB * Real.log 3 / 81) * gam⁻¹)) := by
    exact three_rpow_neg_b_floor_le bfaProfileB_pos hgam
  have hHsum : 0 ≤ superposedFluxHsepConst + superposedFluxHsepConst ^ 2 := by
    positivity
  unfold truncationIndicatorScale
  rw [hexponent]
  change x ^ p ≤ _
  calc
    x ^ p ≤ x + x ^ 2 := hxpow
    _ ≤ (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) * r := hprod
    _ ≤ (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
        (Real.exp (bfaProfileB * Real.log 3) *
          Real.exp (-((bfaProfileB * Real.log 3 / 81) * gam⁻¹))) :=
      mul_le_mul_of_nonneg_left hrExp hHsum
    _ = _ := by ring

/-! ## The uniform sharp B lane at a dimension-only rate -/

/-- Exponential rate retained from the truncated minimal-separation lane after
the local exponent is specialized to `7 * gamma`. -/
def superposedFluxBfaTruncRate : ℝ := bfaProfileB * Real.log 3 / 567

theorem superposedFluxBfaTruncRate_pos : 0 < superposedFluxBfaTruncRate := by
  unfold superposedFluxBfaTruncRate
  exact div_pos (mul_pos bfaProfileB_pos
    (lt_trans zero_lt_one one_lt_log_three)) (by norm_num)

/-- The common exponential rate of the truncation and retained rare lanes. -/
def superposedFluxBfaRate (d : ℕ) : ℝ :=
  min superposedFluxBfaTruncRate (superposedFluxSharpRareRate d)

theorem superposedFluxBfaRate_pos (d : ℕ) : 0 < superposedFluxBfaRate d := by
  unfold superposedFluxBfaRate
  exact lt_min superposedFluxBfaTruncRate_pos (superposedFluxSharpRareRate_pos d)

/-- Dimension-only amplitude multiplying the common exponential B rate. -/
def superposedFluxBfaConst (d : ℕ) : ℝ :=
  superposedFluxTriangleConst * superposedFluxSharpDetConst d *
    (16 * superposedFluxHsepConst *
        (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
        Real.exp (bfaProfileB * Real.log 3) +
      Real.exp (1 / 36 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ))

theorem superposedFluxBfaConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < superposedFluxBfaConst d := by
  unfold superposedFluxBfaConst
  have hdet : 0 < superposedFluxSharpDetConst d :=
    superposedFluxSharpDetConst_pos hd
  have htri : 0 < superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    positivity
  have hH : 0 < superposedFluxHsepConst := superposedFluxHsepConst_pos
  have hfirst : 0 < 16 * superposedFluxHsepConst *
      (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
      Real.exp (bfaProfileB * Real.log 3) := by positivity
  have hsecond : 0 < Real.exp (1 / 36 : ℝ) *
      superposedFluxHsepConst ^ (3 : ℝ) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hH _)
  exact mul_pos (mul_pos htri hdet) (add_pos hfirst hsecond)

/-- The exact sharp B amplitude has a dimension-only prefactor, the required
`3^(gamma k)` collar, and a strictly positive multiple of `E⁻² gamma⁻¹` in its
exponential rate. -/
theorem bfaLaneScale_sharp_le_exp_profile (hd : 2 ≤ d) (M : ABKModel d)
    (m : ℤ) (k : ℕ) {sigma E : ℝ} (hE : 1 ≤ E)
    (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    bfaLaneScale (bfaProfileSigma sigma) bfaProfileB (7 * M.gamma)
        (superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
          (superposedFluxRateEps M) (superposedFluxRateBeta M)
          (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E))
        (superposedFluxSharpRare (superposedFluxRateBeta M)
          (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E)) ≤
      superposedFluxBfaConst d * (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
        Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨heps, hbeta, hbeta9, _hbetab, _hgammaWin, _hk₀three, hk₀,
      _hcap, _hlocalEq, hlocalb, _htau⟩ :=
    superposedFluxRateCompatible_allParameterGates_of_profileAuxiliaryMaxGate
      hd M hE hsigma hsigmaHalf hmax hEgamma
  have hsigmaB0 : 0 < bfaProfileSigma sigma := bfaProfileSigma_pos hsigma
  have hsigmaB : bfaProfileSigma sigma ≤ 1 / 8 :=
    bfaProfileSigma_le_one_eighth hsigmaHalf
  have hgam7 : 0 < 7 * M.gamma := mul_pos (by norm_num) M.shellPrefix.gamma_pos
  have hlocal7 : 7 * M.gamma ≤ bfaProfileB := by
    rw [← _hlocalEq]
    exact hlocalb
  have hgamma20 : M.gamma ≤ 1 / 20 :=
    (badEventGates_of_profileAuxiliaryMaxGate M hE hsigma hsigmaHalf hmax
      hEgamma).2.2.1
  let Cpre : ℝ :=
    superposedFluxSharpConst M (m - 1 - (k : ℤ)) (m - 1)
      (superposedFluxRateEps M) (superposedFluxRateBeta M)
      (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E)
  let eps : ℝ := superposedFluxSharpRare (superposedFluxRateBeta M)
    (superposedFluxPrimaryDepth M E) (superposedFluxRareDepth M E)
  let X : ℝ := E⁻¹ ^ 2 * M.gamma⁻¹
  let G : ℝ := (3 : ℝ) ^ (M.gamma * (k : ℝ))
  have hCprePos : 0 < Cpre := by
    dsimp only [Cpre]
    exact superposedFluxSharpConst_pos hd M _ _ _ _ _ _
  have hepsPos : 0 < eps := by
    dsimp only [eps]
    exact superposedFluxSharpRare_pos _ _ _
  have hCpre : Cpre ≤ superposedFluxSharpDetConst d * G := by
    dsimp only [Cpre, G]
    exact superposedFluxSharpConst_le_profile hd M m k hE hgamma20 hbeta9 hk₀
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hXgamma : X ≤ M.gamma⁻¹ := by
    dsimp only [X]
    exact mul_le_of_le_one_left (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
      (inv_sq_le_one_of_one_le hE)
  have htruncRateEq :
      (bfaProfileB * Real.log 3 / 81) * (7 * M.gamma)⁻¹ =
        superposedFluxBfaTruncRate * M.gamma⁻¹ := by
    unfold superposedFluxBfaTruncRate
    rw [mul_inv_rev]
    norm_num
    ring
  have htrunc := truncationIndicatorScale_le_profile hsigmaB0 hsigmaB hgam7 hlocal7
  rw [htruncRateEq] at htrunc
  have hrateTrunc : superposedFluxBfaRate d * X ≤
      superposedFluxBfaTruncRate * M.gamma⁻¹ := by
    exact mul_le_mul (min_le_left _ _) hXgamma
      (by positivity) superposedFluxBfaTruncRate_pos.le
  have hexpTrunc : Real.exp (-(superposedFluxBfaTruncRate * M.gamma⁻¹)) ≤
      Real.exp (-(superposedFluxBfaRate d * X)) :=
    Real.exp_le_exp.mpr (neg_le_neg hrateTrunc)
  have hrare := superposedFluxSharpRare_le_exp_rate M hE hsigma hsigmaHalf hmax hEgamma
  have hrateRare : superposedFluxBfaRate d * X ≤
      superposedFluxSharpRareRate d * X :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hX0
  have hexpRare : Real.exp (-(superposedFluxSharpRareRate d * X)) ≤
      Real.exp (-(superposedFluxBfaRate d * X)) :=
    Real.exp_le_exp.mpr (neg_le_neg hrateRare)
  have hprod := gammaProductConst_le_sixteen_of_eighth_window
    hsigmaB0 hsigmaB hgam7 bfaProfileB_pos hlocal7
  have hK := hsepAmplitude_le_superposedFluxHsepConst hsigmaB0 hsigmaB
  have hKpow := hsepAmplitude_rpow_bfaPower_le_profile_cube
    hsigmaB0 hsigmaB hlocal7
  let T : ℝ := 16 * superposedFluxHsepConst *
    (superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
      Real.exp (bfaProfileB * Real.log 3)
  let R : ℝ := Real.exp (1 / 36 : ℝ) *
    superposedFluxHsepConst ^ (3 : ℝ)
  have hH0 : 0 ≤ superposedFluxHsepConst := superposedFluxHsepConst_pos.le
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hH0)
        (add_nonneg hH0 (sq_nonneg superposedFluxHsepConst)))
      (Real.exp_pos _).le
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hH0 _)
  have hfirst :
      HCPolySupport.Book.Ch04.gammaProductConst (1 - bfaProfileSigma sigma)
          (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB) *
        hsepAmplitude (bfaProfileSigma sigma) bfaProfileB *
        truncationIndicatorScale bfaProfileB (bfaProfileSigma sigma)
          (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB)
          (hsepAmplitude (bfaProfileSigma sigma) bfaProfileB)
          ⌊(81 * (7 * M.gamma))⁻¹⌋₊ ≤
        T * Real.exp (-(superposedFluxBfaRate d * X)) := by
    have hprod0 : 0 ≤ HCPolySupport.Book.Ch04.gammaProductConst
        (1 - bfaProfileSigma sigma)
        (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB) := by
      positivity
    have hK0 : 0 ≤ hsepAmplitude (bfaProfileSigma sigma) bfaProfileB :=
      (hsepAmplitude_pos _ _).le
    calc
      _ ≤ (16 * superposedFluxHsepConst) *
          ((superposedFluxHsepConst + superposedFluxHsepConst ^ 2) *
            Real.exp (bfaProfileB * Real.log 3) *
            Real.exp (-(superposedFluxBfaTruncRate * M.gamma⁻¹))) := by
        exact mul_le_mul (mul_le_mul hprod hK hK0 (by norm_num)) htrunc
          (truncationIndicatorScale_pos (hsepAmplitude_pos _ _) _).le
          (mul_nonneg (by norm_num) hH0)
      _ = T * Real.exp (-(superposedFluxBfaTruncRate * M.gamma⁻¹)) := by
        dsimp only [T]
        ring
      _ ≤ T * Real.exp (-(superposedFluxBfaRate d * X)) :=
        mul_le_mul_of_nonneg_left hexpTrunc hT0
  have hsecond : eps *
      hsepAmplitude (bfaProfileSigma sigma) bfaProfileB ^
          bfaPower (7 * M.gamma) bfaProfileB ≤
        R * Real.exp (-(superposedFluxBfaRate d * X)) := by
    calc
      eps * hsepAmplitude (bfaProfileSigma sigma) bfaProfileB ^
            bfaPower (7 * M.gamma) bfaProfileB ≤
          (Real.exp (1 / 36 : ℝ) *
            Real.exp (-(superposedFluxSharpRareRate d * X))) *
            superposedFluxHsepConst ^ (3 : ℝ) :=
        mul_le_mul hrare hKpow
          (Real.rpow_nonneg (hsepAmplitude_pos _ _).le _)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = R * Real.exp (-(superposedFluxSharpRareRate d * X)) := by
        dsimp only [R]
        ring
      _ ≤ R * Real.exp (-(superposedFluxBfaRate d * X)) :=
        mul_le_mul_of_nonneg_left hexpRare hR0
  have hinside :
      Cpre * (HCPolySupport.Book.Ch04.gammaProductConst
          (1 - bfaProfileSigma sigma)
          (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB) *
        hsepAmplitude (bfaProfileSigma sigma) bfaProfileB *
        truncationIndicatorScale bfaProfileB (bfaProfileSigma sigma)
          (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB)
          (hsepAmplitude (bfaProfileSigma sigma) bfaProfileB)
          ⌊(81 * (7 * M.gamma))⁻¹⌋₊) +
        Cpre * eps * (hsepAmplitude (bfaProfileSigma sigma) bfaProfileB ^
          bfaPower (7 * M.gamma) bfaProfileB) ≤
      Cpre * (T + R) * Real.exp (-(superposedFluxBfaRate d * X)) := by
    have hfirstC : Cpre *
        (HCPolySupport.Book.Ch04.gammaProductConst
            (1 - bfaProfileSigma sigma)
            (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB) *
          hsepAmplitude (bfaProfileSigma sigma) bfaProfileB *
          truncationIndicatorScale bfaProfileB (bfaProfileSigma sigma)
            (bfaSigmaTwo (bfaProfileSigma sigma) (7 * M.gamma) bfaProfileB)
            (hsepAmplitude (bfaProfileSigma sigma) bfaProfileB)
            ⌊(81 * (7 * M.gamma))⁻¹⌋₊) ≤
        Cpre * (T * Real.exp (-(superposedFluxBfaRate d * X))) :=
      mul_le_mul_of_nonneg_left hfirst hCprePos.le
    have hsecondC : Cpre * eps *
        (hsepAmplitude (bfaProfileSigma sigma) bfaProfileB ^
          bfaPower (7 * M.gamma) bfaProfileB) ≤
        Cpre * (R * Real.exp (-(superposedFluxBfaRate d * X))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hsecond hCprePos.le
    calc
      _ ≤ Cpre * (T * Real.exp (-(superposedFluxBfaRate d * X))) +
          Cpre * (R * Real.exp (-(superposedFluxBfaRate d * X))) :=
        add_le_add hfirstC hsecondC
      _ = _ := by ring
  have hinside0 : 0 ≤ Cpre * (T + R) *
      Real.exp (-(superposedFluxBfaRate d * X)) := by positivity
  unfold bfaLaneScale
  change gammaTriangleConst (bfaTau (bfaProfileSigma sigma)
      (7 * M.gamma) bfaProfileB) * _ ≤ _
  have hTri0 : 0 ≤ superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    positivity
  calc
    _ ≤ gammaTriangleConst (bfaTau (bfaProfileSigma sigma)
          (7 * M.gamma) bfaProfileB) *
        (Cpre * (T + R) * Real.exp (-(superposedFluxBfaRate d * X))) :=
      mul_le_mul_of_nonneg_left hinside gammaTriangleConst_pos.le
    _ ≤ superposedFluxTriangleConst *
        (Cpre * (T + R) * Real.exp (-(superposedFluxBfaRate d * X))) :=
      mul_le_mul_of_nonneg_right
        (gammaTriangleConst_le_superposedFluxTriangleConst
          (one_fourth_le_bfaTau_of_eighth_window hsigmaB0 hsigmaB hgam7
            bfaProfileB_pos hlocal7)) hinside0
    _ ≤ superposedFluxTriangleConst *
        ((superposedFluxSharpDetConst d * G) * (T + R) *
          Real.exp (-(superposedFluxBfaRate d * X))) := by
      have hfactor : 0 ≤ (T + R) *
          Real.exp (-(superposedFluxBfaRate d * X)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hCpre hfactor
      exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hmul) hTri0
    _ = superposedFluxBfaConst d * G *
        Real.exp (-(superposedFluxBfaRate d * X)) := by
      dsimp only [T, R, G]
      unfold superposedFluxBfaConst
      ring
    _ = _ := by rfl

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
