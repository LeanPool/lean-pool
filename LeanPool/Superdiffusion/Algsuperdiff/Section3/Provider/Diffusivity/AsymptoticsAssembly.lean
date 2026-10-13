/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.DisplayBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.SubLandmarkDisplays
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.EndpointSandwich
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowGates
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarPlusUpperBound

/-!
# AsymptoticsAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The diffusivity asymptotics, assembled from the two printed recurrence displays

This module is a **conditional Provider A**.  It wires the already-proved
deterministic flow spine

```text
DisplayBridge -> SubLandmarkDisplays -> FlowGates -> EndpointSandwich
```

into the exact conclusion carried by
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`, taking the two printed
displays `e.what.do.we.have` of `l.approximate.recurrence.formula` as the
single disclosed pair of hypotheses `hforward`/`hreverse`.

## What is NOT supplied here

`hforward` and `hreverse` are the printed conclusion of the source node
`l.approximate.recurrence.formula`, two-sided closure (delivering
`e.what.do.we.have`).  Their whole analytic content -- fresh-shell Dirichlet
and Neumann correctors, the Calderon--Zygmund `L^8` bounds, the mesoscopic
oscillation estimate, the localized variational split, the good-event
coefficient switch and the two one-sided Jensen legs -- is untouched.

## The display constant is a parameter, and it must be

This module takes the second option, and that choice is its central design
decision.  The flow constant that the assembly can offer necessarily grows with
that `C`: the calibration hypothesis of `FlowGates` is quadratic in the
substituted shell constant, so no single `Cflow` serves every `C`.  The display
constant is therefore carried as the leading parameter `Crec` of this theorem,
ahead of the existential, and the disclosed binders are stated at the
manuscript's own reading

```text
Erec = Crec * E^2 * |log gamma|^2 ,      Frec = Crec .
```

This is the only structural addition to the frozen premise list; every premise
of the frozen statement is carried verbatim, and no premise of it is weakened,
strengthened, reordered or dropped.  The parameter does not survive into the
frozen conclusion: a consumer holding the two displays at the manuscript's own
constant `C(d)` instantiates `Crec := C(d)` (or `max (C(d)) 1`) and thereby
recovers the frozen `∃ Cflow` statement exactly, so `Crec` is discharged at the
point of consumption.

## The flow constant is derived here, at the current integration constant

`FlowGates` assumes its calibration

```text
256 * recurrenceIntegrationConstant ^ 2 * (Cshell * (1 + Cshell + cstarPlus))
  <= Cflow ^ 2
```

rather than proving it.  The witness is

```text
Cflow = 16 * recurrenceIntegrationConstant *
          (1 + Cshell * (1 + Cshell + cstarPlusUpperBound d)) ,
Cshell = 974 * Crec ,
```

a function of the dimension `d` and of the display constant `Crec` only.  The
model-dependent `cstarPlus M` is replaced, before `M` is quantified, by the
dimension-only envelope
`Provider.Disorder.cstarPlus_le_cstarPlusUpperBound`, and the calibration is
monotone in that slot, so the calibration is available at the genuine
`Disorder.cstarPlus M` for every standing model.

## Where the shell factor `974` comes from

`DisplayBridge.sigmaBar_le_thirtySix_mul_sigmaBar` produces `K = 36`, but only
from an induction state valid *at the upper endpoint* `m`, and the frozen
premise supplies `S(m_0 - 1, E)` only.  The resulting absolute constant is `974
= 1 + 972 + 1`, where `972` is `324 * cstar * log 3` under `cstar <= 3/2` and
`log 3 <= 2`, and the last `1` is the display error `Crec E^2 |log gamma|^2
gamma <= 1` in the regime.

## The `m_star_star` floor and the shell budget

The disclosed binders quantify over `mStarStar M <= n` only -- exactly the
range delivers.  The scale window bound is the consumer's narrow `(m: real) <=
(n: real) + cstar gamma^{-1}`, not the source's wider `h <= 6 cstar
gamma^{-1}`; the narrower window is the weaker hypothesis here, and it is what
the integration engine demands.

## The regime premises

The frozen premise `M.gamma <= ((E : real)^{-1})^10` is stronger than the
printed `cgamma <= E^{-5}`; the weaker forms the spine needs are derived from
it where required, never assumed separately.  The landmark premise on `m0` is
carried and is not consumed by this route.

## The scale gate on `m0` (-bin statement change)

That landmark premise is `mStarStar M < m0`, **not** the printed `m0 in (mstar,
infty) cap Z`.

## References

* ABK26, `l.approximate.recurrence.formula`, statement, `e.what.do.we.have`.
* ABK26, `l.integrate.approx.recurrence`.
* ABK26, `e.mstarstar`; `d.mathcalS.def`.

## Axiom provenance

`#print axioms
Algsuperdiff.Section3.Provider.Diffusivity.diffusivity_asymptotics_of_recurrence_displays`
reports `[propext, Classical.choice, Quot.sound]` and nothing else -- the three
kernel axioms only, with no incomplete-proof axiom in the list.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

/-! ### The derived flow constant -/

/-- The flow constant offered by the assembly, at dimension `d` and display
constant `Crec`.  It is computed fresh against the current
`recurrenceIntegrationConstant` (see the module header, finding), and it
depends on no model datum: the model-dependent `cstarPlus M` is replaced by the
dimension-only `Provider.Disorder.cstarPlusUpperBound d`. -/
def flowConstant (d : ℕ) (Crec : ℝ) : ℝ :=
  16 * recurrenceIntegrationConstant *
    (1 + 974 * Crec *
      (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d))

private theorem flowConstant_eq (d : ℕ) (Crec : ℝ) :
    flowConstant d Crec =
      16 * recurrenceIntegrationConstant *
        (1 + 974 * Crec *
          (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)) := rfl

private theorem recurrenceIntegrationConstant_pos :
    (0 : ℝ) < recurrenceIntegrationConstant := by
  rw [recurrenceIntegrationConstant_eq]; norm_num

private theorem flowConstant_pos (d : ℕ) {Crec : ℝ} (hCrec : 1 ≤ Crec) :
    0 < flowConstant d Crec := by
  have hP : (0 : ℝ) ≤ Provider.Disorder.cstarPlusUpperBound d :=
    Provider.Disorder.cstarPlusUpperBound_nonneg d
  have hC : (0 : ℝ) < recurrenceIntegrationConstant := recurrenceIntegrationConstant_pos
  have hX : (0 : ℝ) ≤ 974 * Crec * (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d) :=
    mul_nonneg (by linarith only [hCrec]) (by linarith only [hCrec, hP])
  rw [flowConstant_eq]
  have h16 : (0 : ℝ) < 16 * recurrenceIntegrationConstant := by linarith only [hC]
  exact mul_pos h16 (by linarith only [hX])

/-- The lower bound on the flow constant that the regime premise converts into a
lower bound on `E`. -/
private theorem flowConstant_lower (d : ℕ) {Crec : ℝ} (hCrec : 1 ≤ Crec) :
    16 * recurrenceIntegrationConstant * (974 * Crec) ≤ flowConstant d Crec := by
  have hP : (0 : ℝ) ≤ Provider.Disorder.cstarPlusUpperBound d :=
    Provider.Disorder.cstarPlusUpperBound_nonneg d
  have hC : (0 : ℝ) < recurrenceIntegrationConstant := recurrenceIntegrationConstant_pos
  have hS : (0 : ℝ) ≤ 974 * Crec := by linarith only [hCrec]
  have hbracket :
      974 * Crec ≤ 1 + 974 * Crec *
        (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d) := by
    have hone : 974 * Crec * 1
        ≤ 974 * Crec * (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d) :=
      mul_le_mul_of_nonneg_left (by linarith only [hCrec, hP]) hS
    linarith only [hone]
  rw [flowConstant_eq]
  exact mul_le_mul_of_nonneg_left hbracket (by linarith only [hC])

/-- **The calibration hypothesis of `FlowGates`, discharged at the derived flow
constant.**  It is stated at an arbitrary `cp` below the dimension-only envelope
`Provider.Disorder.cstarPlusUpperBound d`, so that it can be used at the genuine
`Disorder.cstarPlus M` of any standing model. -/
private theorem calibration_le (d : ℕ) {Crec cp : ℝ} (hCrec : 1 ≤ Crec)
    (hcp : cp ≤ Provider.Disorder.cstarPlusUpperBound d) :
    256 * recurrenceIntegrationConstant ^ 2 *
        (974 * Crec * (1 + 974 * Crec + cp))
      ≤ flowConstant d Crec ^ 2 := by
  have hP : (0 : ℝ) ≤ Provider.Disorder.cstarPlusUpperBound d :=
    Provider.Disorder.cstarPlusUpperBound_nonneg d
  have hS : (0 : ℝ) ≤ 974 * Crec := by linarith only [hCrec]
  have hcoef : (0 : ℝ) ≤ 256 * recurrenceIntegrationConstant ^ 2 := by positivity
  have hX : (0 : ℝ) ≤ 974 * Crec *
      (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d) :=
    mul_nonneg hS (by linarith only [hCrec, hP])
  have hmono : 974 * Crec * (1 + 974 * Crec + cp)
      ≤ 974 * Crec * (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d) :=
    mul_le_mul_of_nonneg_left (by linarith only [hcp]) hS
  have hsq : 974 * Crec * (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)
      ≤ (1 + 974 * Crec *
          (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)) ^ 2 := by
    nlinarith only [hX]
  have hval : flowConstant d Crec ^ 2
      = 256 * recurrenceIntegrationConstant ^ 2 *
          (1 + 974 * Crec *
            (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)) ^ 2 := by
    rw [flowConstant_eq]; ring
  calc 256 * recurrenceIntegrationConstant ^ 2 * (974 * Crec * (1 + 974 * Crec + cp))
      ≤ 256 * recurrenceIntegrationConstant ^ 2 *
          (974 * Crec *
            (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)) :=
        mul_le_mul_of_nonneg_left hmono hcoef
    _ ≤ 256 * recurrenceIntegrationConstant ^ 2 *
          (1 + 974 * Crec *
            (1 + 974 * Crec + Provider.Disorder.cstarPlusUpperBound d)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoef
    _ = flowConstant d Crec ^ 2 := hval.symm

/-! ### Scalar arithmetic for the quotient bound

The two lemmas of this section are pure real algebra: no `rpow`, `exp` or `log`
occurs in their statements, so the nonlinear arithmetic used to prove them never
meets a transcendental atom. -/

/-- The increment, measured against the induction state's lower bound at the
lower endpoint, is at most the absolute constant `972`.

`c` is `cstar`, `L` is `log 3`, `gi` is `gamma⁻¹`, `gn`/`gm` are `3^{2 gamma n}`
and `3^{2 gamma m}`, `d0` is `m - n`, `A` is the increment and `s` is
`sigmabar_n`.  The numerology is
`A (s)^{-2} <= (81 c^2 L gi gn) * 4 (c gi gn)^{-1} = 324 c L <= 324 * (3/2) * 2`. -/
private theorem increment_ratio_core {c L gi gn gm d0 A s : ℝ}
    (hc : 0 < c) (hc32 : c ≤ 3 / 2) (hL0 : 0 ≤ L) (hL2 : L ≤ 2)
    (hgi : 0 < gi) (hgn : 0 < gn) (hgm : 0 < gm) (hA0 : 0 ≤ A)
    (hA : A ≤ c * L * d0 * gm) (hd0 : d0 ≤ c * gi) (hgmn : gm ≤ 81 * gn)
    (hsn : 1 / 4 * (c * gi * gn) ≤ s ^ 2) :
    A * (s⁻¹) ^ 2 ≤ 972 := by
  have hcL0 : (0 : ℝ) ≤ c * L := mul_nonneg hc.le hL0
  have hcoef : (0 : ℝ) ≤ c * L * (c * gi) :=
    mul_nonneg hcL0 (mul_nonneg hc.le hgi.le)
  have hA1 : A ≤ c * L * (c * gi) * (81 * gn) := by
    calc A ≤ c * L * d0 * gm := hA
      _ ≤ c * L * (c * gi) * gm :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd0 hcL0) hgm.le
      _ ≤ c * L * (c * gi) * (81 * gn) := mul_le_mul_of_nonneg_left hgmn hcoef
  have hden : (0 : ℝ) < c * gi * gn := mul_pos (mul_pos hc hgi) hgn
  have hquarter : (0 : ℝ) < 1 / 4 * (c * gi * gn) := by linarith only [hden]
  have hinv : (s⁻¹) ^ 2 ≤ 4 * (c * gi * gn)⁻¹ := by
    have h1 : (s ^ 2)⁻¹ ≤ (1 / 4 * (c * gi * gn))⁻¹ := inv_anti₀ hquarter hsn
    have h2 : (1 / 4 * (c * gi * gn))⁻¹ = 4 * (c * gi * gn)⁻¹ := by
      rw [mul_inv]; norm_num
    rw [inv_pow]
    linarith only [h1, h2.le, h2.ge]
  have hrhs0 : (0 : ℝ) ≤ c * L * (c * gi) * (81 * gn) := by linarith only [hA0, hA1]
  have hkey : A * (s⁻¹) ^ 2 ≤ (c * L * (c * gi) * (81 * gn)) * (4 * (c * gi * gn)⁻¹) :=
    mul_le_mul hA1 hinv (sq_nonneg _) hrhs0
  have hval : (c * L * (c * gi) * (81 * gn)) * (4 * (c * gi * gn)⁻¹) = 324 * (c * L) := by
    field_simp
    ring
  have hcL : c * L ≤ 3 := by
    have := mul_le_mul hc32 hL2 hL0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith only [this]
  linarith only [hkey, hval.le, hval.ge, hcL]

/-- The regime bound on the display error term: in the regime
`16 Crec <= E` and `gamma <= (E⁻¹)^10`, the printed error coefficient
`Crec E^2 |log gamma|^2` costs at most one unit of `gamma^{-1}`. -/
private theorem display_error_mul_gamma_le_one {Crec Eval gamma : ℝ}
    (hCrec : 1 ≤ Crec) (hE1 : 1 ≤ Eval) (hEbig : 16 * Crec ≤ Eval)
    (hgamma : 0 < gamma) (hgammaE : gamma ≤ (Eval⁻¹) ^ 10) :
    Crec * Eval ^ 2 * |Real.log gamma| ^ 2 * gamma ≤ 1 := by
  have hE0 : (0 : ℝ) < Eval := lt_of_lt_of_le one_pos hE1
  have hEne : Eval ≠ 0 := ne_of_gt hE0
  have hinv1 : Eval⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hE1 (inv_nonneg.mpr hE0.le)
    rwa [mul_one, inv_mul_cancel₀ hEne] at h
  have hgamma1 : gamma ≤ 1 := by
    have h1 : (Eval⁻¹) ^ 10 ≤ (1 : ℝ) ^ 10 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hE0.le) hinv1 10
    have h2 : (1 : ℝ) ^ 10 = 1 := one_pow 10
    linarith only [hgammaE, h1, h2.le, h2.ge]
  have hlog := mul_sq_abs_log_le hgamma hgamma1
  have hsqrt := sqrt_le_inv_pow_five hE0 hgammaE
  have hcoef0 : (0 : ℝ) ≤ Crec * Eval ^ 2 :=
    mul_nonneg (by linarith only [hCrec]) (sq_nonneg _)
  have hstep : gamma * |Real.log gamma| ^ 2 ≤ 16 * (Eval⁻¹) ^ 5 := by
    linarith only [hlog, hsqrt]
  have hpow : Eval ^ 2 * (Eval⁻¹) ^ 5 = (Eval ^ 3)⁻¹ := by
    field_simp
  have hE3pos : (0 : ℝ) < Eval ^ 3 := by positivity
  have hE2one : (1 : ℝ) ≤ Eval ^ 2 := by nlinarith only [hE1]
  have hcube : 16 * Crec ≤ Eval ^ 3 := by
    have h1 : Eval * 1 ≤ Eval * Eval ^ 2 := mul_le_mul_of_nonneg_left hE2one hE0.le
    have h2 : Eval * Eval ^ 2 = Eval ^ 3 := by ring
    linarith only [hEbig, h1, h2.le, h2.ge]
  calc Crec * Eval ^ 2 * |Real.log gamma| ^ 2 * gamma
      = (Crec * Eval ^ 2) * (gamma * |Real.log gamma| ^ 2) := by ring
    _ ≤ (Crec * Eval ^ 2) * (16 * (Eval⁻¹) ^ 5) :=
        mul_le_mul_of_nonneg_left hstep hcoef0
    _ = 16 * Crec * (Eval ^ 2 * (Eval⁻¹) ^ 5) := by ring
    _ = 16 * Crec * (Eval ^ 3)⁻¹ := by rw [hpow]
    _ ≤ Eval ^ 3 * (Eval ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hcube (inv_nonneg.mpr hE3pos.le)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hE3pos)

/-! ### The geometric ratio on the admissible window -/

/-- On the consumer's window `m <= n + cstar gamma^{-1}` with `cstar <= 3/2`, the
geometric factor grows by at most `3 ^ 4 = 81` (the exponent bound established
below is `4`; the sharper `3 ^ 3` is not needed). -/
private theorem rpow_le_eightyOne_mul {gamma c : ℝ} (hgamma : 0 < gamma)
    (hc32 : c ≤ 3 / 2) {n m : ℤ}
    (hrange : (m : ℝ) ≤ (n : ℝ) + c * gamma⁻¹) :
    (3 : ℝ) ^ (2 * gamma * (m : ℝ)) ≤ 81 * (3 : ℝ) ^ (2 * gamma * (n : ℝ)) := by
  have hgnpos : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hd0 : (m : ℝ) - (n : ℝ) ≤ c * gamma⁻¹ := by linarith only [hrange]
  have hexpgap : 2 * gamma * ((m : ℝ) - (n : ℝ)) ≤ 4 := by
    have h1 : gamma * ((m : ℝ) - (n : ℝ)) ≤ gamma * (c * gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hd0 hgamma.le
    have h2 : gamma * (c * gamma⁻¹) = c := by field_simp
    rw [h2] at h1
    linarith only [h1, hc32]
  have hsplit : (3 : ℝ) ^ (2 * gamma * (m : ℝ))
      = (3 : ℝ) ^ (2 * gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have h81 : (3 : ℝ) ^ (4 : ℝ) = 81 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpow : (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) ≤ 81 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexpgap
    rw [h81] at hmono
    exact hmono
  calc (3 : ℝ) ^ (2 * gamma * (m : ℝ))
      = (3 : ℝ) ^ (2 * gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) := hsplit
    _ ≤ (3 : ℝ) ^ (2 * gamma * (n : ℝ)) * 81 :=
        mul_le_mul_of_nonneg_left hpow hgnpos.le
    _ = 81 * (3 : ℝ) ^ (2 * gamma * (n : ℝ)) := by ring

/-! ### The quotient bound from the forward display -/

/-- **The admissible-scale quotient bound, taken from the forward display.**

On the consumer's window, with the induction state available at the *lower*
endpoint only, the printed forward display bounds `sigmabar_m` by the absolute
multiple `974 sigmabar_n`. -/
private theorem sigmaBar_le_of_forward_display_quotient {d : ℕ} (M : ABKModel d)
    {m1 : ℤ} {Eind : {E : ℝ // 1 ≤ E}} {Erec : ℝ} {n m : ℤ}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m1 Eind)
    (hErec : Erec * M.gamma ≤ 1) (hn : n ≤ m1) (hnm : n ≤ m)
    (hrange : (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹)
    (hdisp :
      (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
        1 +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
          Erec * M.gamma) :
    (Annealed.sigmaBar M m : ℝ) ≤ 974 * (Annealed.sigmaBar M n : ℝ) := by
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hposn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [this]
  have hA0 : (0 : ℝ) ≤ recurrenceIncrement (Disorder.cstar M) M.gamma n m :=
    Internal.recurrenceIncrement_nonneg hcstar.le n m
  have hcount : recurrenceIncrement (Disorder.cstar M) M.gamma n m
      ≤ Disorder.cstar M * Real.log 3 * ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    simpa only [geometricTerm] using
      Internal.recurrenceIncrement_le_count hgamma hcstar.le hnm
  have hd0 : (m : ℝ) - (n : ℝ) ≤ Disorder.cstar M * M.gamma⁻¹ := by linarith only [hrange]
  have hgnpos : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgmpos : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgmn := rpow_le_eightyOne_mul hgamma hcstar32 hrange
  have hSn := (hS.1 n hn).1
  have hmax : Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))
      ≤ max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
          (M.nu ^ 2) := le_max_left _ _
  have hsn : 1 / 4 * (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
      ≤ (Annealed.sigmaBar M n : ℝ) ^ 2 := by
    linarith only [hSn, hmax]
  have hcore :=
    increment_ratio_core hcstar hcstar32 hlog0 hlog2 (inv_pos.mpr hgamma) hgnpos hgmpos
      hA0 hcount hd0 hgmn hsn
  have hratio : (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤ 974 := by
    linarith only [hdisp, hcore, hErec]
  have hmul := mul_le_mul_of_nonneg_right hratio hposn.le
  have hleft : (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      (Annealed.sigmaBar M n : ℝ) = (Annealed.sigmaBar M m : ℝ) := by
    field_simp
  linarith only [hmul, hleft.le, hleft.ge]

/-! ### The assembled statement -/

/-- **The diffusivity asymptotics, from the two printed recurrence displays.**

**`hforward` and `hreverse` are disclosed hypotheses, not results.**  They are
the printed conclusion of `l.approximate.recurrence.formula`, which this
repository does not prove; see the module header for what is and is not supplied
here, for the reason the display constant must be a parameter, and for the
freshly derived calibration behind `Cflow`. -/
theorem diffusivity_asymptotics_of_recurrence_displays (d : ℕ) (Crec : ℝ)
    (hCrec : 1 ≤ Crec) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
          (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
            1 +
                recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                  (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
              Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) →
        (∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
          (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
            1 -
                  recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                    (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
                Crec * ((m : ℝ) - (n : ℝ)) ^ 2 *
                  (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
                  (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
              Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2) := by
  refine ⟨flowConstant d Crec, flowConstant_pos d hCrec, ?_⟩
  intro M m0 E _hm0 hS hEreg hgammaE hforward hreverse
  -- standing model facts
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hcc : Disorder.cstar M ≤ Disorder.cstarPlus M := cstar_le_cstarPlus M
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hCflow : 0 < flowConstant d Crec := flowConstant_pos d hCrec
  have hCshell : (1 : ℝ) ≤ 974 * Crec := by linarith only [hCrec]
  have hcal : 256 * recurrenceIntegrationConstant ^ 2 *
      (974 * Crec * (1 + 974 * Crec + Disorder.cstarPlus M)) ≤ flowConstant d Crec ^ 2 :=
    calibration_le d hCrec (Provider.Disorder.cstarPlus_le_cstarPlusUpperBound M)
  -- the regime condition, converted into lower bounds on `E`
  have hcinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar, show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num]
    exact hcstar32
  have hElow : flowConstant d Crec * (2 / 3) ≤ (E : ℝ) := by
    have hstep : flowConstant d Crec * (2 / 3)
        ≤ flowConstant d Crec * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_left hcinv hCflow.le
    linarith only [hstep, hEreg]
  have hEbig : 16 * Crec ≤ (E : ℝ) := by
    have h1 : 16 * recurrenceIntegrationConstant * (974 * Crec) * (2 / 3)
        ≤ flowConstant d Crec * (2 / 3) :=
      mul_le_mul_of_nonneg_right (flowConstant_lower d hCrec) (by norm_num)
    have h2 : 16 * Crec ≤ 16 * recurrenceIntegrationConstant * (974 * Crec) * (2 / 3) := by
      rw [recurrenceIntegrationConstant_eq]
      linarith only [hCrec]
    linarith only [h1, h2, hElow]
  -- the display error coefficient, and its two elementary bounds
  have hErec0 : (0 : ℝ) ≤ Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith only [hCrec]) (sq_nonneg _)) (sq_nonneg _)
  have hErec1 : Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma ≤ 1 :=
    display_error_mul_gamma_le_one hCrec hE1 hEbig hgamma hgammaE
  -- the four parameter gates, at the substituted recurrence parameters
  obtain ⟨hEint, hFint⟩ :=
    one_le_recurrence_parameters hcstar hcstar32 hcc hCshell hCflow hcal hEreg hgamma hgammaE
  have hthr :=
    gamma_le_recurrenceIntegration_gate hcstar hcstar32 hcc hCshell hCflow hcal hEreg
      hgamma hgammaE
  have hrate :=
    recurrenceIntegration_rate_le hcstar hcstar32 hcc hCshell hCflow hcal hE0.le hgamma.le
  have hamp :=
    flow_amplitude_le_quarter hcstar hcstar32 hcc hCshell hCflow hcal hEreg hgamma hgammaE
  -- the two recurrence families, floored at the landmark
  have hupper : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (Annealed.sigmaBar M m : ℝ) ≤
        (1 + 974 * Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) *
            (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
    intro n m hfl hm hnm hr
    have hposn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
    have hbase := sigmaBar_le_of_forward_display M (hforward n m hfl hm hnm hr)
    have hD : (0 : ℝ) ≤ 973 * Crec *
        ((E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma *
          (Annealed.sigmaBar M n : ℝ)) :=
      mul_nonneg (by linarith only [hCrec])
        (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hgamma.le)
          hposn.le)
    linarith only [hbase, hD]
  have hlower : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (1 - 974 * Crec * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) *
              (Annealed.sigmaBar M n : ℝ) +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M m : ℝ) -
          974 * Crec * ((m : ℝ) - (n : ℝ)) ^ 2 *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
            (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))
        ≤ (Annealed.sigmaBar M m : ℝ) := by
    intro n m hfl hm hnm hr
    have hposn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
    have hposm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
    have hK : (Annealed.sigmaBar M m : ℝ) ≤ 974 * (Annealed.sigmaBar M n : ℝ) := by
      rcases eq_or_lt_of_le hnm with heq | hlt
      · rw [← heq]
        linarith only [hposn]
      · have hn1 : n ≤ m0 - 1 := by omega
        exact sigmaBar_le_of_forward_display_quotient M hS hErec1 hn1 hnm hr
          (hforward n m hfl hm hnm hr)
    have hbase :=
      sigmaBar_ge_of_reverse_display M hErec0 hK (hreverse n m hfl hm hnm hr)
    have hD : (0 : ℝ) ≤ 973 * Crec *
        (((m : ℝ) - (n : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
          (Annealed.sigmaBar M m : ℝ) * (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))) :=
      mul_nonneg (by linarith only [hCrec])
        (mul_nonneg
          (mul_nonneg (mul_nonneg (sq_nonneg _)
            (pow_nonneg (inv_nonneg.mpr hposn.le) 4)) hposm.le)
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)
    linarith only [hbase, hD]
  -- the integration engine, floored at the landmark
  have hint :=
    sigmaBar_integrate_approx_recurrence_of_mStarStar_floored M hEint hFint hupper hlower
      hthr
  -- conclusion (i): the relative-error estimate at every scale
  have hconcl : ∀ m : ℤ, m ≤ m0 →
      |(Annealed.sigmaBar M m : ℝ) -
          Real.sqrt
            (M.nu ^ 2 +
              Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
        ≤ flowConstant d Crec * (Disorder.cstar M)⁻¹ * (E : ℝ) *
            Real.sqrt M.gamma * |Real.log M.gamma| *
              (Annealed.sigmaBar M m : ℝ) := by
    intro m hm
    have hposm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
    exact (hint m hm).trans (mul_le_mul_of_nonneg_right hrate hposm.le)
  -- conclusions (ii) and (iii): the endpoint sandwich
  have htheta0 : (0 : ℝ) ≤ flowConstant d Crec * (Disorder.cstar M)⁻¹ * (E : ℝ) *
      Real.sqrt M.gamma * |Real.log M.gamma| :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCflow.le (inv_nonneg.mpr hcstar.le)) hE0.le)
        (Real.sqrt_nonneg _))
      (abs_nonneg _)
  obtain ⟨hs1, hs2⟩ :=
    endpoint_sandwich_of_relative_error htheta0 hamp (hconcl m0 le_rfl)
  exact ⟨hconcl, hs1, hs2⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity
