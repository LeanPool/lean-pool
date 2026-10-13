/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

/-!
# FlowGates

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Parameter gates for the diffusivity-flow recurrence integration

This module is deterministic parameter-gate infrastructure.  It performs the
scalar bookkeeping that turns a calibration inequality on a flow constant
`Cflow`, together with the two smallness conditions `Cflow c⋆⁻¹ ≤ E` and
`γ ≤ (E⁻¹)¹⁰`, into the three numerical facts that a Section 3.4 assembly needs
when it substitutes the recurrence parameters

  `Eint = Cshell E² |log γ|²`,  `Fint = Cshell`

into `integrate_approx_recurrence`:

* the `γ`-threshold demanded by that lemma at the substituted parameters;
* the absorption of the reported rate into `Cflow c⋆⁻¹ E √γ |log γ|`;
* the bound `Cflow c⋆⁻¹ E √γ |log γ| ≤ 1/4` on that amplitude.

Every hypothesis below is an explicit input binder.  In particular `hcstar32:
cstar ≤ 3/2`, `hcc: cstar ≤ cstarPlus`, `hCshell: 1 ≤ Cshell` and the
calibration `hcal` are *assumed here*, never derived; no model, probability
space, or analytic producer is referenced.

## The calibration hypothesis

All gates share one input inequality on the flow constant,

  `256 * recurrenceIntegrationConstant² * (Cshell (1 + Cshell + cstarPlus)) ≤ Cflow²`.

It is the squared form of the two separate requirements that the arithmetic
actually has: a cube bound `16 C_int Cshell(1+Cshell+cstarPlus) ≤ Cflow³` for the
threshold and the amplitude, and a square bound
`C_int² Cshell(1+Cshell+cstarPlus) ≤ Cflow²` for the rate.  The squared form
above implies both, so a single input suffices.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity

open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

/-! ### Elementary consequences of the calibration hypothesis -/

/-- The calibration hypothesis forces `Cflow` to be at least `384`; the
numerical room comes entirely from `recurrenceIntegrationConstant ≥ 256` (in
fact `Cflow ≥ 5792` follows, so `384` is far from tight).  The floor is `384`
rather than `256` because under `c⋆ ≤ 3/2` the regime condition only returns
`cstar⁻¹ ≥ 2/3`, and `(2/3)·384 = 256` is what `regime_E_ge` must deliver. -/
private theorem flowConstant_ge {Cshell cstarPlus Cflow : ℝ}
    (hCshell : 1 ≤ Cshell) (hP : 0 ≤ cstarPlus) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2) :
    384 ≤ Cflow := by
  have hCint : (256 : ℝ) ≤ recurrenceIntegrationConstant := by
    rw [recurrenceIntegrationConstant_eq]; norm_num
  have hCint2 : (65536 : ℝ) ≤ recurrenceIntegrationConstant ^ 2 := by
    nlinarith only [hCint]
  have hA : (2 : ℝ) ≤ Cshell * (1 + Cshell + cstarPlus) := by
    nlinarith only [hCshell, hP]
  have hprod : (65536 : ℝ) * 2
      ≤ recurrenceIntegrationConstant ^ 2 * (Cshell * (1 + Cshell + cstarPlus)) :=
    mul_le_mul hCint2 hA (by norm_num) (by positivity)
  have hbig : (147456 : ℝ) ≤ Cflow ^ 2 := by linarith only [hcal, hprod]
  have hsq : Real.sqrt ((384 : ℝ) ^ 2) ≤ Real.sqrt (Cflow ^ 2) :=
    Real.sqrt_le_sqrt (by linarith only [hbig])
  rwa [Real.sqrt_sq (by norm_num), Real.sqrt_sq hCflow.le] at hsq

/-- With `cstar ≤ 3/2`, the regime condition `Cflow cstar⁻¹ ≤ E` transports the
lower bound `384 ≤ Cflow` to `256 ≤ E`, since `cstar⁻¹ ≥ 2/3`. -/
private theorem regime_E_ge {cstar Cflow E : ℝ} (hcstar : 0 < cstar)
    (hcstar32 : cstar ≤ 3 / 2) (hCflow : 0 < Cflow) (h384 : 384 ≤ Cflow)
    (hEreg : Cflow * cstar⁻¹ ≤ E) : 256 ≤ E := by
  have hcinv : (2 : ℝ) / 3 ≤ cstar⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar, show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num]
    exact hcstar32
  have hstep : Cflow * (2 / 3) ≤ Cflow * cstar⁻¹ :=
    mul_le_mul_of_nonneg_left hcinv hCflow.le
  linarith only [h384, hstep, hEreg]

/-- `E⁻¹ ≤ 1/256` whenever `256 ≤ E`. -/
private theorem inv_le_of_ge {E : ℝ} (hE : 256 ≤ E) : E⁻¹ ≤ 1 / 256 := by
  have hE0 : (0 : ℝ) < E := by linarith only [hE]
  have h := mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hE0.le)
  rw [inv_mul_cancel₀ (ne_of_gt hE0)] at h
  linarith only [h]

/-- Under the regime conditions the scale parameter is at most `1/3`, hence
strictly below `1`. -/
private theorem gamma_le_third {E gamma : ℝ} (hE : 256 ≤ E)
    (hgammaE : gamma ≤ (E⁻¹) ^ 10) : gamma ≤ 1 / 3 := by
  have hE0 : (0 : ℝ) < E := by linarith only [hE]
  have hinv := inv_le_of_ge hE
  have h1 : (E⁻¹) ^ 10 ≤ ((1 : ℝ) / 256) ^ 10 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hE0.le) hinv 10
  have h2 : ((1 : ℝ) / 256) ^ 10 ≤ 1 / 3 := by norm_num
  linarith only [hgammaE, h1, h2]

/-- Under the regime conditions the logarithmic factor is at least `1`, so the
substituted recurrence parameter `Cshell E² |log γ|²` is at least `1`. -/
private theorem one_le_abs_log {E gamma : ℝ} (hE : 256 ≤ E) (hgamma : 0 < gamma)
    (hgammaE : gamma ≤ (E⁻¹) ^ 10) : 1 ≤ |Real.log gamma| := by
  have hgamma3 : gamma ≤ 1 / 3 := gamma_le_third hE hgammaE
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  have hmono : Real.log gamma ≤ Real.log (1 / 3 : ℝ) := Real.log_le_log hgamma hgamma3
  have h13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hle : Real.log gamma ≤ -1 := by
    rw [h13] at hmono
    linarith only [hmono, hlog3]
  have habs : |Real.log gamma| = -Real.log gamma :=
    abs_of_nonpos (by linarith only [hle])
  rw [habs]
  linarith only [hle]

/-! ### The pure-algebra core of the threshold gate -/

/-- **Threshold core, over abstract reals.**  The square root and the logarithm
enter only through the opaque atoms `g` and `L`, so no numeric tactic ever
unfolds `Real.sqrt`, `Real.log`, or `Real.rpow`.

The chain is: absorb the bracket into `(9/4)(c²)⁻¹(1 + K + P)`, trade `γ L²` for
`16 g`, trade `g` for `(E⁵)⁻¹`, and finally spend `Cflow ≤ cE` cubed.  Under
`c ≤ 3/2` the bracket absorption costs `9/4` (since `(9/4)c⁻² ≥ 1`) and the cube
`c³ ≤ (3/2)c²` costs a further `3/2`, so the cube hypothesis carries
`16·(9/4)·(3/2) = 54` rather than `16`. -/
private theorem regime_product_le_one {c K P E Cint Cflow g L gamma : ℝ}
    (hc : 0 < c) (hc32 : c ≤ 3 / 2) (hK : 1 ≤ K) (hP : 0 ≤ P) (hE1 : 1 ≤ E)
    (hCint : 0 < Cint) (hCflow : 0 < Cflow)
    (hcube : 54 * Cint * (K * (1 + K + P)) ≤ Cflow ^ 3)
    (hEreg : Cflow * c⁻¹ ≤ E) (hgamma : 0 < gamma)
    (hgL : gamma * L ^ 2 ≤ 16 * g) (hg : g ≤ (E ^ 5)⁻¹) :
    gamma * (Cint * (K * E ^ 2 * L ^ 2 *
        (1 + (c ^ 2)⁻¹ * K + (c ^ 2)⁻¹ * P))) ≤ 1 := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
  have hc2pos : (0 : ℝ) < c ^ 2 := pow_pos hc 2
  have hcinv : (4 : ℝ) / 9 ≤ (c ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hc2pos, show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]
    nlinarith only [hc, hc32]
  have hinvpos : (0 : ℝ) < (c ^ 2)⁻¹ := inv_pos.mpr hc2pos
  have hinner : 1 + (c ^ 2)⁻¹ * K + (c ^ 2)⁻¹ * P ≤ 9 / 4 * ((c ^ 2)⁻¹ * (1 + K + P)) := by
    have hKt : (0 : ℝ) ≤ (c ^ 2)⁻¹ * K := mul_nonneg hinvpos.le hK0
    have hPt : (0 : ℝ) ≤ (c ^ 2)⁻¹ * P := mul_nonneg hinvpos.le hP
    have hexp : 9 / 4 * ((c ^ 2)⁻¹ * (1 + K + P))
        = 9 / 4 * (c ^ 2)⁻¹ + 9 / 4 * ((c ^ 2)⁻¹ * K) + 9 / 4 * ((c ^ 2)⁻¹ * P) := by ring
    linarith only [hcinv, hKt, hPt, hexp.le, hexp.ge]
  have hcE : Cflow ≤ c * E := by
    have hmul : c * (Cflow * c⁻¹) ≤ c * E := mul_le_mul_of_nonneg_left hEreg hc.le
    have heq : c * (Cflow * c⁻¹) = Cflow := by
      field_simp
    linarith only [hmul, heq.le, heq.ge]
  have hE3 : (0 : ℝ) ≤ E ^ 3 := by positivity
  have hc3 : Cflow ^ 3 ≤ 3 / 2 * (c ^ 2 * E ^ 3) := by
    have h1 : Cflow ^ 3 ≤ (c * E) ^ 3 := pow_le_pow_left₀ hCflow.le hcE 3
    have h2 : (c * E) ^ 3 = c ^ 3 * E ^ 3 := by ring
    have hcube32 : c ^ 3 ≤ 3 / 2 * c ^ 2 := by nlinarith only [hc, hc32, sq_nonneg c]
    have h3 : c ^ 3 * E ^ 3 ≤ 3 / 2 * c ^ 2 * E ^ 3 := mul_le_mul_of_nonneg_right hcube32 hE3
    linarith only [h1, h2.le, h2.ge, h3]
  have hC3pos : (0 : ℝ) < Cflow ^ 3 := by positivity
  have hc2E3 : (0 : ℝ) < 3 / 2 * (c ^ 2 * E ^ 3) := by positivity
  have hXE : (c ^ 2)⁻¹ * (E ^ 3)⁻¹ ≤ 3 / 2 * (Cflow ^ 3)⁻¹ := by
    have heq : (c ^ 2)⁻¹ * (E ^ 3)⁻¹ = (c ^ 2 * E ^ 3)⁻¹ := by rw [mul_inv]
    have hstep : (3 / 2 * (c ^ 2 * E ^ 3))⁻¹ ≤ (Cflow ^ 3)⁻¹ := by
      rw [inv_le_inv₀ hc2E3 hC3pos]; exact hc3
    have hval : (3 / 2 * (c ^ 2 * E ^ 3))⁻¹ = 2 / 3 * (c ^ 2 * E ^ 3)⁻¹ := by
      rw [mul_inv]; norm_num
    rw [hval] at hstep
    rw [heq]
    linarith only [hstep]
  have hA : (0 : ℝ) ≤ 36 * Cint * (K * (1 + K + P)) := by positivity
  have hcoef1 : (0 : ℝ) ≤ gamma * (Cint * (K * E ^ 2 * L ^ 2)) := by positivity
  have hcoef2 : (0 : ℝ) ≤ 9 / 4 * (Cint * (K * (1 + K + P)) * E ^ 2 * (c ^ 2)⁻¹) := by
    positivity
  have hcoef3 : (0 : ℝ)
      ≤ 36 * Cint * (K * (1 + K + P)) * (E ^ 2 * (c ^ 2)⁻¹) := by positivity
  have hE25 : E ^ 2 * (E ^ 5)⁻¹ = (E ^ 3)⁻¹ := by
    have h5 : (E : ℝ) ^ 5 = E ^ 2 * E ^ 3 := by ring
    rw [h5, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < E ^ 2)), one_mul]
  calc gamma * (Cint * (K * E ^ 2 * L ^ 2 *
          (1 + (c ^ 2)⁻¹ * K + (c ^ 2)⁻¹ * P)))
      = (gamma * (Cint * (K * E ^ 2 * L ^ 2))) *
          (1 + (c ^ 2)⁻¹ * K + (c ^ 2)⁻¹ * P) := by ring
    _ ≤ (gamma * (Cint * (K * E ^ 2 * L ^ 2))) * (9 / 4 * ((c ^ 2)⁻¹ * (1 + K + P))) :=
        mul_le_mul_of_nonneg_left hinner hcoef1
    _ = (9 / 4 * (Cint * (K * (1 + K + P)) * E ^ 2 * (c ^ 2)⁻¹)) * (gamma * L ^ 2) := by ring
    _ ≤ (9 / 4 * (Cint * (K * (1 + K + P)) * E ^ 2 * (c ^ 2)⁻¹)) * (16 * g) :=
        mul_le_mul_of_nonneg_left hgL hcoef2
    _ = 36 * Cint * (K * (1 + K + P)) * (E ^ 2 * (c ^ 2)⁻¹) * g := by ring
    _ ≤ 36 * Cint * (K * (1 + K + P)) * (E ^ 2 * (c ^ 2)⁻¹) * (E ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_left hg hcoef3
    _ = 36 * Cint * (K * (1 + K + P)) * ((c ^ 2)⁻¹ * (E ^ 2 * (E ^ 5)⁻¹)) := by ring
    _ = 36 * Cint * (K * (1 + K + P)) * ((c ^ 2)⁻¹ * (E ^ 3)⁻¹) := by rw [hE25]
    _ ≤ 36 * Cint * (K * (1 + K + P)) * (3 / 2 * (Cflow ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left hXE hA
    _ = 54 * Cint * (K * (1 + K + P)) * (Cflow ^ 3)⁻¹ := by ring
    _ ≤ Cflow ^ 3 * (Cflow ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hcube (inv_nonneg.mpr hC3pos.le)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hC3pos)

/-- The cube form of the calibration hypothesis, which is what the threshold
core consumes. -/
private theorem cube_of_calibration {Cshell cstarPlus Cflow : ℝ}
    (hCshell : 1 ≤ Cshell) (hP : 0 ≤ cstarPlus) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2) :
    54 * recurrenceIntegrationConstant *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 3 := by
  have h384 : 384 ≤ Cflow := flowConstant_ge hCshell hP hCflow hcal
  have hCint : (256 : ℝ) ≤ recurrenceIntegrationConstant := by
    rw [recurrenceIntegrationConstant_eq]; norm_num
  have hA0 : (0 : ℝ) ≤ Cshell * (1 + Cshell + cstarPlus) := by
    have h1 : (0 : ℝ) ≤ Cshell := by linarith only [hCshell]
    positivity
  have hCintA : (0 : ℝ) ≤ recurrenceIntegrationConstant *
      (Cshell * (1 + Cshell + cstarPlus)) :=
    mul_nonneg (by linarith only [hCint]) hA0
  have hstep : (0 : ℝ) ≤ recurrenceIntegrationConstant *
      (Cshell * (1 + Cshell + cstarPlus)) *
        (98304 * recurrenceIntegrationConstant - 54) :=
    mul_nonneg hCintA (by linarith only [hCint])
  have hcubeExpand : Cflow ^ 3 = Cflow * Cflow ^ 2 := by ring
  have hgrow : 384 * Cflow ^ 2 ≤ Cflow * Cflow ^ 2 := by
    nlinarith only [h384, sq_nonneg Cflow]
  linarith only [hcal, hstep, hcubeExpand.le, hcubeExpand.ge, hgrow]

/-! ### The three gates -/

/-- **Gate (i): the `γ`-threshold at the substituted recurrence parameters.**

At `Eint = Cshell E² |log γ|²` and `Fint = Cshell` the smallness condition
demanded by `integrate_approx_recurrence` follows from the calibration
hypothesis together with `Cflow cstar⁻¹ ≤ E` and `γ ≤ (E⁻¹)¹⁰`.  This is where
the tenth inverse power of `E` is spent: `√γ ≤ (E⁻¹)⁵` converts the `E²|log γ|²`
inflation of `Eint` into a decaying factor `E⁻³`. -/
theorem gamma_le_recurrenceIntegration_gate
    {cstar cstarPlus Cshell Cflow E gamma : ℝ}
    (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2) (hcc : cstar ≤ cstarPlus)
    (hCshell : 1 ≤ Cshell) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2)
    (hEreg : Cflow * cstar⁻¹ ≤ E)
    (hgamma : 0 < gamma) (hgammaE : gamma ≤ (E⁻¹) ^ 10) :
    gamma ≤ (recurrenceIntegrationConstant *
      (Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
        (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus)))⁻¹ := by
  have hP : (0 : ℝ) ≤ cstarPlus := le_trans hcstar.le hcc
  have h384 : 384 ≤ Cflow := flowConstant_ge hCshell hP hCflow hcal
  have hE256 : 256 ≤ E := regime_E_ge hcstar hcstar32 hCflow h384 hEreg
  have hE0 : (0 : ℝ) < E := by linarith only [hE256]
  have hE1 : (1 : ℝ) ≤ E := by linarith only [hE256]
  have hgamma1 : gamma ≤ 1 := by
    have := gamma_le_third hE256 hgammaE
    linarith only [this]
  have hCint0 : (0 : ℝ) < recurrenceIntegrationConstant := by
    rw [recurrenceIntegrationConstant_eq]; norm_num
  have hCshell0 : (0 : ℝ) < Cshell := by linarith only [hCshell]
  have hL := one_le_abs_log hE256 hgamma hgammaE
  have hLnn : (0 : ℝ) ≤ |Real.log gamma| := abs_nonneg _
  have hL2 : (1 : ℝ) ≤ |Real.log gamma| ^ 2 := by nlinarith only [hL, hLnn]
  have hbrk : (0 : ℝ) < 1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus := by
    positivity
  have hE2 : (0 : ℝ) < E ^ 2 := by positivity
  have hTheta : (0 : ℝ) < Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
      (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus) :=
    mul_pos (mul_pos (mul_pos hCshell0 hE2) (by linarith only [hL2])) hbrk
  have hDpos : (0 : ℝ) < recurrenceIntegrationConstant *
      (Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
        (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus)) :=
    mul_pos hCint0 hTheta
  have hgL : gamma * |Real.log gamma| ^ 2 ≤ 16 * Real.sqrt gamma :=
    mul_sq_abs_log_le hgamma hgamma1
  have hg : Real.sqrt gamma ≤ (E ^ 5)⁻¹ := by
    have h1 : Real.sqrt gamma ≤ (E⁻¹) ^ 5 := sqrt_le_inv_pow_five hE0 hgammaE
    rwa [inv_pow] at h1
  have hcube := cube_of_calibration hCshell hP hCflow hcal
  have hcore := regime_product_le_one hcstar hcstar32 hCshell hP hE1 hCint0 hCflow
    hcube hEreg hgamma hgL hg
  rw [← one_div, le_div_iff₀ hDpos]
  exact hcore

/-- **Gate (ii): absorption of the reported rate.**

The rate reported by `integrate_approx_recurrence` at the substituted
parameters is at most `Cflow cstar⁻¹ E √γ |log γ|`.  Only the square form of the
calibration hypothesis is used here; no `γ`-smallness is needed. -/
theorem recurrenceIntegration_rate_le
    {cstar cstarPlus Cshell Cflow E gamma : ℝ}
    (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2) (hcc : cstar ≤ cstarPlus)
    (hCshell : 1 ≤ Cshell) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2)
    (hE : 0 ≤ E) (hgamma : 0 ≤ gamma) :
    recurrenceIntegrationConstant *
        Real.sqrt (Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
          (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus) * gamma)
      ≤ Cflow * cstar⁻¹ * E * Real.sqrt gamma * |Real.log gamma| := by
  have hP : (0 : ℝ) ≤ cstarPlus := le_trans hcstar.le hcc
  have hCshell0 : (0 : ℝ) ≤ Cshell := by linarith only [hCshell]
  have hCint0 : (0 : ℝ) < recurrenceIntegrationConstant := by
    rw [recurrenceIntegrationConstant_eq]; norm_num
  have hcinv : (1 : ℝ) ≤ 9 / 4 * (cstar ^ 2)⁻¹ := by
    have h49 : (4 : ℝ) / 9 ≤ (cstar ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (pow_pos hcstar 2),
        show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]
      nlinarith only [hcstar, hcstar32]
    linarith only [h49]
  -- factor the square root
  have hfac : Real.sqrt (Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
        (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus) * gamma)
      = E * |Real.log gamma| * (Real.sqrt gamma *
          Real.sqrt (Cshell *
            (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus))) := by
    rw [show Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
          (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus) * gamma
        = (E * |Real.log gamma|) ^ 2 *
          (gamma * (Cshell *
            (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus))) from by ring,
      Real.sqrt_mul (sq_nonneg (E * |Real.log gamma|)) _,
      Real.sqrt_sq (mul_nonneg hE (abs_nonneg _)),
      Real.sqrt_mul hgamma _]
  -- the inner bracket, absorbed into `(cstar²)⁻¹`
  have hBA : Cshell * (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus)
      ≤ 9 / 4 * (cstar ^ 2)⁻¹ * (Cshell * (1 + Cshell + cstarPlus)) := by
    have hnn : (0 : ℝ) ≤ Cshell * (9 / 4 * (cstar ^ 2)⁻¹ - 1) :=
      mul_nonneg hCshell0 (by linarith only [hcinv])
    have hnn2 : (0 : ℝ) ≤ Cshell * ((cstar ^ 2)⁻¹ * (Cshell + cstarPlus)) :=
      mul_nonneg hCshell0 (mul_nonneg (inv_nonneg.mpr (le_of_lt (pow_pos hcstar 2)))
        (by linarith only [hCshell0, hP]))
    nlinarith only [hnn, hnn2]
  have hsqrtB : Real.sqrt (Cshell *
        (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus))
      ≤ 3 / 2 * cstar⁻¹ * Real.sqrt (Cshell * (1 + Cshell + cstarPlus)) := by
    have h1 := Real.sqrt_le_sqrt hBA
    have h2 : Real.sqrt (9 / 4 * (cstar ^ 2)⁻¹ * (Cshell * (1 + Cshell + cstarPlus)))
        = 3 / 2 * cstar⁻¹ * Real.sqrt (Cshell * (1 + Cshell + cstarPlus)) := by
      rw [show 9 / 4 * (cstar ^ 2)⁻¹ * (Cshell * (1 + Cshell + cstarPlus))
          = (3 / 2 * cstar⁻¹) ^ 2 * (Cshell * (1 + Cshell + cstarPlus)) from by
        rw [mul_pow, ← inv_pow]; ring,
        Real.sqrt_mul (sq_nonneg _) _,
        Real.sqrt_sq (mul_nonneg (by norm_num) (inv_nonneg.mpr hcstar.le))]
    rwa [h2] at h1
  -- the calibration hypothesis, in square-root form
  have hA0 : (0 : ℝ) ≤ Cshell * (1 + Cshell + cstarPlus) := by positivity
  have hsq : (3 / 2 * recurrenceIntegrationConstant) ^ 2 *
      (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2 := by
    have hnn : (0 : ℝ) ≤ recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) := by positivity
    have hexp : (3 / 2 * recurrenceIntegrationConstant) ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus))
        = 9 / 4 * (recurrenceIntegrationConstant ^ 2 *
            (Cshell * (1 + Cshell + cstarPlus))) := by ring
    linarith only [hcal, hnn, hexp.le, hexp.ge]
  have hCintA : 3 / 2 * recurrenceIntegrationConstant *
      Real.sqrt (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow := by
    have h4 : 3 / 2 * recurrenceIntegrationConstant *
        Real.sqrt (Cshell * (1 + Cshell + cstarPlus))
        = Real.sqrt ((3 / 2 * recurrenceIntegrationConstant) ^ 2 *
            (Cshell * (1 + Cshell + cstarPlus))) := by
      rw [Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (by linarith only [hCint0])]
    rw [h4]
    calc Real.sqrt ((3 / 2 * recurrenceIntegrationConstant) ^ 2 *
          (Cshell * (1 + Cshell + cstarPlus)))
        ≤ Real.sqrt (Cflow ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Cflow := Real.sqrt_sq hCflow.le
  -- the coefficient comparison
  have hkey : recurrenceIntegrationConstant *
      Real.sqrt (Cshell *
        (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus))
      ≤ Cflow * cstar⁻¹ := by
    have hstep1 := mul_le_mul_of_nonneg_left hsqrtB hCint0.le
    have hstep2 := mul_le_mul_of_nonneg_left hCintA (inv_nonneg.mpr hcstar.le)
    nlinarith only [hstep1, hstep2]
  have hnn : (0 : ℝ) ≤ E * |Real.log gamma| * Real.sqrt gamma :=
    mul_nonneg (mul_nonneg hE (abs_nonneg _)) (Real.sqrt_nonneg _)
  calc recurrenceIntegrationConstant *
        Real.sqrt (Cshell * E ^ 2 * |Real.log gamma| ^ 2 *
          (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus) * gamma)
      = (recurrenceIntegrationConstant *
          Real.sqrt (Cshell *
            (1 + (cstar ^ 2)⁻¹ * Cshell + (cstar ^ 2)⁻¹ * cstarPlus))) *
          (E * |Real.log gamma| * Real.sqrt gamma) := by rw [hfac]; ring
    _ ≤ (Cflow * cstar⁻¹) * (E * |Real.log gamma| * Real.sqrt gamma) :=
        mul_le_mul_of_nonneg_right hkey hnn
    _ = Cflow * cstar⁻¹ * E * Real.sqrt gamma * |Real.log gamma| := by ring

/-- **Gate (iii): the amplitude is at most `1/4`.**

The squeeze that converts the relative-error estimate into a two-sided bound
needs the deviation coefficient below `1/4`.  Here `√γ |log γ| ≤ 4 √(√γ)` and
`√γ ≤ (E⁻¹)⁵` give `√γ|log γ| ≤ (E⁻¹)²/4` once `E ≥ 256`, and one factor `E`
is returned by the regime condition. -/
theorem flow_amplitude_le_quarter
    {cstar cstarPlus Cshell Cflow E gamma : ℝ}
    (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2) (hcc : cstar ≤ cstarPlus)
    (hCshell : 1 ≤ Cshell) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2)
    (hEreg : Cflow * cstar⁻¹ ≤ E)
    (hgamma : 0 < gamma) (hgammaE : gamma ≤ (E⁻¹) ^ 10) :
    Cflow * cstar⁻¹ * E * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 4 := by
  have hP : (0 : ℝ) ≤ cstarPlus := le_trans hcstar.le hcc
  have h384 : 384 ≤ Cflow := flowConstant_ge hCshell hP hCflow hcal
  have hE256 : 256 ≤ E := regime_E_ge hcstar hcstar32 hCflow h384 hEreg
  have hE0 : (0 : ℝ) < E := by linarith only [hE256]
  have hgamma1 : gamma ≤ 1 := by
    have := gamma_le_third hE256 hgammaE
    linarith only [this]
  -- `√γ |log γ| ≤ 4 √(√γ)`
  have hamp : Real.sqrt gamma * |Real.log gamma| ≤ 4 * Real.sqrt (Real.sqrt gamma) :=
    sqrt_mul_abs_log_le hgamma hgamma1
  -- `√(√γ) ≤ (E⁻¹)² √(E⁻¹)`
  have h5 : Real.sqrt gamma ≤ (E⁻¹) ^ 5 := sqrt_le_inv_pow_five hE0 hgammaE
  have hquarter : Real.sqrt (Real.sqrt gamma) ≤ (E⁻¹) ^ 2 * Real.sqrt E⁻¹ := by
    have h1 : Real.sqrt (Real.sqrt gamma) ≤ Real.sqrt ((E⁻¹) ^ 5) :=
      Real.sqrt_le_sqrt h5
    have h2 : Real.sqrt ((E⁻¹ : ℝ) ^ 5) = (E⁻¹) ^ 2 * Real.sqrt E⁻¹ := by
      rw [show (E⁻¹ : ℝ) ^ 5 = ((E⁻¹) ^ 2) ^ 2 * E⁻¹ from by ring,
        Real.sqrt_mul (sq_nonneg _) _,
        Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr hE0.le) 2)]
    rwa [h2] at h1
  -- `√(E⁻¹) ≤ 1/16`
  have hsixteen : Real.sqrt E⁻¹ ≤ 1 / 16 := by
    have hinv := inv_le_of_ge hE256
    have h1 : Real.sqrt E⁻¹ ≤ Real.sqrt (((1 : ℝ) / 16) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith only [hinv, (by norm_num :
        ((1 : ℝ) / 16) ^ 2 = 1 / 256)])
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hEinv2 : (0 : ℝ) ≤ (E⁻¹) ^ 2 := sq_nonneg _
  have hsmall : Real.sqrt gamma * |Real.log gamma| ≤ (E⁻¹) ^ 2 / 4 := by
    have hstep : Real.sqrt (Real.sqrt gamma) ≤ (E⁻¹) ^ 2 * (1 / 16) := by
      have := mul_le_mul_of_nonneg_left hsixteen hEinv2
      linarith only [hquarter, this]
    linarith only [hamp, hstep]
  -- assemble
  have hcoef : (0 : ℝ) ≤ Cflow * cstar⁻¹ * E :=
    mul_nonneg (mul_nonneg hCflow.le (inv_nonneg.mpr hcstar.le)) hE0.le
  have hEE : E * E⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hE0)
  have hfinal : E * E * ((E⁻¹) ^ 2 / 4) = 1 / 4 := by
    have hrw : E * E * ((E⁻¹) ^ 2 / 4) = (E * E⁻¹) * (E * E⁻¹) / 4 := by ring
    rw [hrw, hEE]
    norm_num
  calc Cflow * cstar⁻¹ * E * Real.sqrt gamma * |Real.log gamma|
      = (Cflow * cstar⁻¹ * E) * (Real.sqrt gamma * |Real.log gamma|) := by ring
    _ ≤ (Cflow * cstar⁻¹ * E) * ((E⁻¹) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hsmall hcoef
    _ ≤ (E * E) * ((E⁻¹) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEreg hE0.le)
          (by positivity)
    _ = 1 / 4 := hfinal

/-- **Companion gate: the substituted recurrence parameters are at least `1`.**

`integrate_approx_recurrence` additionally asks for `1 ≤ Eint` and `1 ≤ Fint`.
At the substitution `Eint = Cshell E² |log γ|²`, `Fint = Cshell` both hold under
the same regime conditions. -/
theorem one_le_recurrence_parameters
    {cstar cstarPlus Cshell Cflow E gamma : ℝ}
    (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2) (hcc : cstar ≤ cstarPlus)
    (hCshell : 1 ≤ Cshell) (hCflow : 0 < Cflow)
    (hcal : 256 * recurrenceIntegrationConstant ^ 2 *
        (Cshell * (1 + Cshell + cstarPlus)) ≤ Cflow ^ 2)
    (hEreg : Cflow * cstar⁻¹ ≤ E)
    (hgamma : 0 < gamma) (hgammaE : gamma ≤ (E⁻¹) ^ 10) :
    1 ≤ Cshell * E ^ 2 * |Real.log gamma| ^ 2 ∧ 1 ≤ Cshell := by
  refine ⟨?_, hCshell⟩
  have hP : (0 : ℝ) ≤ cstarPlus := le_trans hcstar.le hcc
  have h384 : 384 ≤ Cflow := flowConstant_ge hCshell hP hCflow hcal
  have hE256 : 256 ≤ E := regime_E_ge hcstar hcstar32 hCflow h384 hEreg
  have hL := one_le_abs_log hE256 hgamma hgammaE
  have hLnn : (0 : ℝ) ≤ |Real.log gamma| := abs_nonneg _
  have hL2 : (1 : ℝ) ≤ |Real.log gamma| ^ 2 := by nlinarith only [hL, hLnn]
  have hE2 : (1 : ℝ) ≤ E ^ 2 := by nlinarith only [hE256]
  have hstep1 : (0 : ℝ) ≤ (Cshell - 1) * (E ^ 2 - 1) :=
    mul_nonneg (by linarith only [hCshell]) (by linarith only [hE2])
  have hCE : (1 : ℝ) ≤ Cshell * E ^ 2 := by
    nlinarith only [hstep1, hCshell, hE2]
  have hstep2 : (0 : ℝ) ≤ (Cshell * E ^ 2 - 1) * (|Real.log gamma| ^ 2 - 1) :=
    mul_nonneg (by linarith only [hCE]) (by linarith only [hL2])
  nlinarith only [hstep2, hCE, hL2]

end

end Algsuperdiff.Section3.Provider.Diffusivity
