/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeSlotThird

/-!
# PerCubeSlotFirst

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's first summand, evaluated at the anchor's scalar

## What this module does

`PerCubeFirstThird.lintegral_rpow_step3FirstTerm_le` supplies the first
summand's `q`-th moment at the symbolic majorant `4C · R_bracket · R_{B4}²`.
This module evaluates it against the anchor's own slot `K p γ s^{-2}`:

* the bracket is `O(1)` (`PerCubeSlotCommon.bracketMajorant_le`);
* `R_{B4}(4q)²` is `O(q γ s^{-2})`.  Its `Γ₂` lane gives the printed
  `C s^{-1}q^{1/2}γ^{1/2}` squared, i.e. exactly the slot; its `Γ_{1/2}` lane
  gives the printed `C q² e^{−C^{-1}c⋆³γ^{-1}}` squared, and the exponential
  beats the `q`-power on the anchor's own range `q ≤ γ^{-1}` WITH one factor `γ`
  to spare (`SecondTermArithmetic.pow_mul_exp_neg_inv_le_mul`).

That second point is the only place where the printed `Γ_{1/2}` lane has to be
priced; it costs no `p`-restriction whatsoever.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullet (B4), Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The squared `(2,2)`-error majorant -/

/-- The constant of the squared (B4) majorant: the `Γ₂` lane's
`24 C(2)² pen₂² C² c⋆^{-2}` plus the `Γ_{1/2}` lane's, the latter priced by
`x^5 e^{-x} ≤ 5!`. -/
def errSlotSquareBound (d : ℕ) (cst C : ℝ) : ℝ :=
  24 * gammaMomentConst 2 ^ 2 * Proportion.annulusPenalty d 2 1 ^ 2 *
      (C ^ 2 * (cst⁻¹) ^ 2) +
    1536 * gammaMomentConst (1 / 2) ^ 2 * Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
      ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * cst ^ 3)) ^ 5)

theorem annulusPenalty_nonneg (d : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (p : ℕ) :
    0 ≤ Proportion.annulusPenalty d sigma p :=
  le_trans zero_le_one (Proportion.one_le_annulusPenalty d hsigma p)

theorem errSlotSquareBound_pos (d : ℕ) {cst C : ℝ} (hcst : 0 < cst) (hC : 0 < C) :
    0 < errSlotSquareBound d cst C := by
  have h1 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < gammaMomentConst (1 / 2) := gammaMomentConst_pos (by norm_num)
  have h3 : (1 : ℝ) ≤ Proportion.annulusPenalty d 2 1 :=
    Proportion.one_le_annulusPenalty d (by norm_num) 1
  have h4 : (1 : ℝ) ≤ Proportion.annulusPenalty d (1 / 2) 1 :=
    Proportion.one_le_annulusPenalty d (by norm_num) 1
  have h5 : (0 : ℝ) < 2 * (C⁻¹ * cst ^ 3) := by positivity
  have h6 : (0 : ℝ) < (Nat.factorial 5 : ℝ) := by norm_num
  have h7 : (0 : ℝ) < Proportion.annulusPenalty d 2 1 := by linarith only [h3]
  have h8 : (0 : ℝ) < Proportion.annulusPenalty d (1 / 2) 1 := by linarith only [h4]
  rw [errSlotSquareBound]
  positivity

/-- **The squared `(2,2)`-error majorant is `O(q γ s^{-2})`.**

Both printed lanes are evaluated: the `Γ₂` lane is the anchor's own
`(s^{-1}√q√γ)²`, and the `Γ_{1/2}` lane's `q⁴e^{−2C^{-1}c⋆³γ^{-1}}` is at most
`5!(2C^{-1}c⋆³)^{-5} γ` on the anchor's own range `q ≤ γ^{-1}`. -/
theorem errSlotMajorant_sq_le (d : ℕ) (M : ABKModel d) {C s q : ℝ} (hC : 0 < C)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq : 1 ≤ q) (hqg : q ≤ M.gamma⁻¹) :
    errSlotMajorant d M C s (4 * q) ^ 2 ≤
      errSlotSquareBound d (Disorder.cstar M) C * (q * (M.gamma * (s⁻¹ * s⁻¹))) := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hb0 : (0 : ℝ) < C⁻¹ * (Disorder.cstar M) ^ 3 := by positivity
  have hsinv0 : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  have hone : (1 : ℝ) ≤ s⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hs1 hsinv0.le
    rwa [mul_one, inv_mul_cancel₀ (ne_of_gt hs)] at h
  have hsq1 : (1 : ℝ) ≤ s⁻¹ * s⁻¹ := by
    have h := mul_le_mul hone hone zero_le_one (le_trans zero_le_one hone)
    rwa [one_mul] at h
  have hqs1 : (1 : ℝ) ≤ q * (s⁻¹ * s⁻¹) := by
    have h := mul_le_mul hq hsq1 zero_le_one (le_trans zero_le_one hq)
    rwa [one_mul] at h
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqg : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hgam0.le
  have hsqq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hpen2 : (0 : ℝ) ≤ Proportion.annulusPenalty d 2 1 :=
    annulusPenalty_nonneg d (by norm_num) 1
  have hpenh : (0 : ℝ) ≤ Proportion.annulusPenalty d (1 / 2) 1 :=
    annulusPenalty_nonneg d (by norm_num) 1
  -- the two-lane split
  have hsplit : errSlotMajorant d M C s (4 * q) ^ 2 ≤
      2 * (gammaMomentConst 2 * Real.sqrt (4 * q) *
          (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
            (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))) ^ 2 +
        2 * (gammaMomentConst (1 / 2) * (4 * q) ^ (2 : ℕ) *
          (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
            Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))))) ^ 2 := by
    rw [errSlotMajorant, gammaTwoHalfMomentBound]
    exact add_sq_le_two_mul _ _
  -- the `Γ₂` lane, evaluated exactly
  have hlane1 : 2 * (gammaMomentConst 2 * Real.sqrt (4 * q) *
      (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
        (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))) ^ 2 =
      24 * gammaMomentConst 2 ^ 2 * Proportion.annulusPenalty d 2 1 ^ 2 *
        (C ^ 2 * ((Disorder.cstar M)⁻¹) ^ 2) * (q * (M.gamma * (s⁻¹ * s⁻¹))) := by
    rw [sqrt_four_mul]
    have hid : 2 * (gammaMomentConst 2 * (2 * Real.sqrt q) *
        (Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
          (C * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)))) ^ 2 =
        8 * gammaMomentConst 2 ^ 2 * Proportion.annulusPenalty d 2 1 ^ 2 *
          (C ^ 2 * ((Disorder.cstar M)⁻¹) ^ 2) * (s⁻¹ * s⁻¹) *
          (Real.sqrt 3 ^ 2 * (Real.sqrt q ^ 2 * Real.sqrt M.gamma ^ 2)) := by ring
    rw [hid, hsq3, hsqq, hsqg]
    ring
  -- the `Γ_{1/2}` lane, priced by the exponential
  have hexpsq : Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)) ^ 2 =
      Real.exp (-(2 * (C⁻¹ * (Disorder.cstar M) ^ 3) * M.gamma⁻¹)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hexpbound := pow_mul_exp_neg_inv_le_mul
    (a := 2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) (g := M.gamma) (y := q) 4
    (by linarith only [hb0]) hgam0 hq0.le hqg
  have hPT : (0 : ℝ) ≤ gammaMomentConst (1 / 2) ^ 2 *
      Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
      ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) := by
    have h5 : (0 : ℝ) < 2 * (C⁻¹ * (Disorder.cstar M) ^ 3) := by linarith only [hb0]
    have h6 : (0 : ℝ) < (Nat.factorial 5 : ℝ) := by norm_num
    positivity
  have hlane2 : 2 * (gammaMomentConst (1 / 2) * (4 * q) ^ (2 : ℕ) *
      (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
        Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))))) ^ 2 ≤
      1536 * gammaMomentConst (1 / 2) ^ 2 * Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
        ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) *
        (q * (M.gamma * (s⁻¹ * s⁻¹))) := by
    have hid : 2 * (gammaMomentConst (1 / 2) * (4 * q) ^ (2 : ℕ) *
        (Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
          Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))))) ^ 2 =
        512 * (gammaMomentConst (1 / 2) ^ 2 *
            Proportion.annulusPenalty d (1 / 2) 1 ^ 2) * Real.sqrt 3 ^ 2 *
          (q ^ (4 : ℕ) *
            Real.exp (-(C⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)) ^ 2) := by ring
    rw [hid, hsq3, hexpsq]
    have hcoef : (0 : ℝ) ≤ 512 * (gammaMomentConst (1 / 2) ^ 2 *
        Proportion.annulusPenalty d (1 / 2) 1 ^ 2) * 3 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hexpbound hcoef
    have hlift : 1536 * (gammaMomentConst (1 / 2) ^ 2 *
        Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
        ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) * M.gamma) * 1 ≤
        1536 * (gammaMomentConst (1 / 2) ^ 2 *
          Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
          ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) * M.gamma) *
          (q * (s⁻¹ * s⁻¹)) := by
      refine mul_le_mul_of_nonneg_left hqs1 ?_
      have := mul_nonneg hPT hgam0.le
      linarith only [this]
    have hidL : 512 * (gammaMomentConst (1 / 2) ^ 2 *
        Proportion.annulusPenalty d (1 / 2) 1 ^ 2) * 3 *
        ((Nat.factorial (4 + 1) : ℝ) /
          (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ (4 + 1) * M.gamma) =
        1536 * (gammaMomentConst (1 / 2) ^ 2 *
          Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
          ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) * M.gamma) *
          1 := by
      norm_num
      ring
    have hidR : 1536 * (gammaMomentConst (1 / 2) ^ 2 *
        Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
        ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) * M.gamma) *
        (q * (s⁻¹ * s⁻¹)) =
        1536 * gammaMomentConst (1 / 2) ^ 2 *
          Proportion.annulusPenalty d (1 / 2) 1 ^ 2 *
          ((Nat.factorial 5 : ℝ) / (2 * (C⁻¹ * (Disorder.cstar M) ^ 3)) ^ 5) *
          (q * (M.gamma * (s⁻¹ * s⁻¹))) := by ring
    linarith only [hstep, hlift, hidL, hidR]
  rw [errSlotSquareBound, add_mul]
  linarith only [hsplit, hlane1, hlane2]

/-! ## 2. The first summand at the anchor's first slot -/

/-- **The first summand, evaluated.**

`∫⁻ (step3FirstTerm)^q ≤ (ofReal (C_d A q γ s^{-2}))^q`, uniformly in the
descendant scale: this is the anchor's own first slot. -/
theorem exists_lintegral_rpow_step3FirstTerm_slot (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ Creg A : ℝ, 0 < Creg ∧ 0 < A ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar →
        M.gamma ≤ (Creg⁻¹) ^ (10 : ℕ) → M.gamma ≤ 1 / 8 → ∀ Cd : ℝ, 0 ≤ Cd →
          ∀ s : ℝ, 0 < s → s ≤ 1 / 4 → 8 * M.gamma ≤ s →
          ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m → ∀ q : ℝ, 1 ≤ q →
            8 * q ≤ M.gamma⁻¹ →
              (∫⁻ omega : Cutoff.CutoffSample d,
                  ENNReal.ofReal (step3FirstTerm Cd M m R omega s
                    (lFreeGradSlot m (tailSeriesGauge m) R omega)) ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (Cd * A * (q * (M.gamma * (s⁻¹ * s⁻¹)))) ^ q  := by
  classical
  obtain ⟨CB, hCB6, hbrAll⟩ := exists_lintegral_rpow_step3Bracket_le d
  obtain ⟨CE, hCE0, herrAll⟩ := exists_lintegral_rpow_unitCubeHomogenizationError22_le d
  obtain ⟨Cg, hCg0, hgaugeAll⟩ := exists_sigmaBar_gaugePackage d
  have hCB0 : (0 : ℝ) < CB := by linarith only [hCB6]
  refine ⟨max (max CB CE) Cg * cstar⁻¹,
    4 * (1 + slotProductBound d cstar (CB * cstar⁻¹)) *
      errSlotSquareBound d cstar CE, ?_, ?_, ?_⟩
  · exact mul_pos (lt_of_lt_of_le hCB0
      (le_trans (le_max_left CB CE) (le_max_left _ _))) (inv_pos.mpr hcstar)
  · have h1 : (0 : ℝ) ≤ slotProductBound d cstar (CB * cstar⁻¹) :=
      slotProductBound_nonneg d (mul_pos hCB0 (inv_pos.mpr hcstar))
    have h2 : (0 : ℝ) < errSlotSquareBound d cstar CE :=
      errSlotSquareBound_pos d hcstar hCE0
    have h3 : (0 : ℝ) < 4 * (1 + slotProductBound d cstar (CB * cstar⁻¹)) := by
      linarith only [h1]
    exact mul_pos h3 h2
  intro M hcs hreg hgam Cd hCd s hs hs1 hs8 m R hkm q hq h8q
  subst hcs
  have hcs0 : (0 : ℝ) < Disorder.cstar M := hcstar
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hgam2 : M.gamma ≤ 1 / 2 := by linarith only [hgam]
  have hqg : q ≤ M.gamma⁻¹ := by linarith only [h8q, hq0]
  have h4qg : 4 * q ≤ M.gamma⁻¹ := by linarith only [h8q, hq0]
  have h2q : (1 : ℝ) ≤ 2 * q := by linarith only [hq]
  have h4q1 : (1 : ℝ) ≤ 2 * (2 * q) := by linarith only [hq]
  -- the three regimes
  have hregB : M.gamma ≤ (CB⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    refine gamma_regime_of_cstar_scaled (le_trans hreg ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos (lt_of_lt_of_le hCB0
      (le_trans (le_max_left CB CE) (le_max_left _ _))) (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hCB0 (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left CB CE) (le_max_left _ _))
        (inv_pos.mpr hcs0).le)
  have hregE : M.gamma ≤ (CE⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    refine gamma_regime_of_cstar_scaled (le_trans hreg ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos (lt_of_lt_of_le hCB0
      (le_trans (le_max_left CB CE) (le_max_left _ _))) (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hCE0 (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right CB CE) (le_max_left _ _))
        (inv_pos.mpr hcs0).le)
  have hregG : M.gamma ≤ (Cg⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    refine gamma_regime_of_cstar_scaled (le_trans hreg ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos (lt_of_lt_of_le hCB0
      (le_trans (le_max_left CB CE) (le_max_left _ _))) (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hCg0 (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right (le_max_right (max CB CE) Cg) (inv_pos.mpr hcs0).le)
  obtain ⟨hgB5, -, hgB1, -⟩ := hgaugeAll M hregG
  -- the two moment inputs
  have hRB0 : (0 : ℝ) ≤ bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) :=
    bracketMajorant_nonneg d M _ R.scale (by linarith only [hq0])
  have hRE0 : (0 : ℝ) ≤ errSlotMajorant d M CE s (4 * q) := by
    have h1 : (0 : ℝ) ≤ Real.sqrt 3 * (Proportion.annulusPenalty d 2 1 *
        (CE * (Disorder.cstar M)⁻¹ * s⁻¹ * Real.sqrt M.gamma)) := by
      have hpen : (0 : ℝ) ≤ Proportion.annulusPenalty d 2 1 :=
        annulusPenalty_nonneg d (by norm_num) 1
      have hsi : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs).le
      have hci : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.mpr hcs0).le
      have hsg : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
      have hs3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt 3 * (Proportion.annulusPenalty d (1 / 2) 1 *
        Real.exp (-(CE⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹))) := by
      have hpen : (0 : ℝ) ≤ Proportion.annulusPenalty d (1 / 2) 1 :=
        annulusPenalty_nonneg d (by norm_num) 1
      have hs3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      have hex : (0 : ℝ) < Real.exp (-(CE⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹)) :=
        Real.exp_pos _
      positivity
    exact gammaTwoHalfMomentBound_nonneg h1 h2
  have hbracket := hbrAll M hregB m R hkm (2 * q) h2q _
    (step3_gradient_exponent_le_one hgam hs1)
  have herr : (∫⁻ omega : Cutoff.CutoffSample d,
      ENNReal.ofReal (unitCubeHomogenizationError s (.finite 2) (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2)))) ^
        (2 * (2 * q)) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (errSlotMajorant d M CE s (4 * q)) ^ (2 * (2 * q)) := by
    rw [show (2 : ℝ) * (2 * q) = 4 * q from by ring]
    exact herrAll M hregE s ⟨hs8, by linarith only [hs1]⟩ R (4 * q)
      (by linarith only [hq])
  refine le_trans (lintegral_rpow_step3FirstTerm_le M m R hs hgam hCd hq hRB0 hRE0
    (hgB1 m R.scale (by omega)) hbracket herr) ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le
  -- the real evaluation
  have hbr := bracketMajorant_le d M (mul_pos hCB0 (inv_pos.mpr hcs0)) R.scale
    (r := 2 * q) (by linarith only [hq0]) (by linarith only [h4qg]) hgam2 (hgB5 R.scale)
  have hsqbd := errSlotMajorant_sq_le d M hCE0 hs (by linarith only [hs1]) hq hqg
  have hslot0 : (0 : ℝ) ≤ slotProductBound d (Disorder.cstar M)
      (CB * (Disorder.cstar M)⁻¹) :=
    slotProductBound_nonneg d (mul_pos hCB0 (inv_pos.mpr hcs0))
  have hqgs0 : (0 : ℝ) ≤ q * (M.gamma * (s⁻¹ * s⁻¹)) := by
    have hsi : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
    positivity
  have hstep : bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
      errSlotMajorant d M CE s (4 * q) ^ 2 ≤
      (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
        (errSlotSquareBound d (Disorder.cstar M) CE * (q * (M.gamma * (s⁻¹ * s⁻¹)))) :=
    mul_le_mul hbr hsqbd (sq_nonneg _) (by linarith only [hslot0])
  have hfinal := mul_le_mul_of_nonneg_left hstep (by linarith only [hCd] : (0 : ℝ) ≤ 4 * Cd)
  have hidL : 4 * Cd * (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
      errSlotMajorant d M CE s (4 * q) ^ 2) =
      4 * Cd * (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
        errSlotMajorant d M CE s (4 * q) ^ 2) := rfl
  have hidR : 4 * Cd *
      ((1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
        (errSlotSquareBound d (Disorder.cstar M) CE * (q * (M.gamma * (s⁻¹ * s⁻¹))))) =
      Cd * (4 * (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
        errSlotSquareBound d (Disorder.cstar M) CE) * (q * (M.gamma * (s⁻¹ * s⁻¹))) := by
    ring
  linarith only [hfinal, hidL, hidR]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
