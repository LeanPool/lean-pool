/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripRemainder
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ShomContinuityCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuityArithmetic

/-!
# ShomContinuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Continuity of `m |-> shom_m`: two-sided ratio control across scales

ABK26, `l.shom.continuity` and its proof; the consuming display
`e.switchtheshoms.betterer.again` of the localization `shom`-switch.

## What is delivered

For the genuine running diffusivity `Annealed.sigmaBar` on the Section 3
carriers, on the premise list of `l.shom.continuity` --- `mstarstar < m0` (the
correction of the printed `mstar < m0`; see the dedicated section below), the
induction state `S(m0-1,E)`, `E >= C cstar^{-1}` and `cgamma <= E^{-10}` ---
and for every pair of integer scales `n <= m <= m0`:

1. the **quarter comparison** `shom_m >= (1/4) shom_n`, and its ratio form
   `shom_n shom_m^{-1} <= 4`, which is the honest constant of the switch step's
   quoted `shom_m^{-1} shom_{l-h} <= 2`;
2. the **growth cap** `shom_m <= 4 . 3^{cgamma (m-n)} shom_n`;
3. its **short-range collapse** `shom_m shom_n^{-1} <= 12` whenever `cgamma
   (m-n) <= 1` (the printed `3^{cgamma h} <= 3` step);
4. the **two-sided defect display** `e.shom.m.vs.shom.n`, at the **printed**
   second entry of the minimum,

```
  |shom_m shom_n^{-1} - 1| + |shom_n shom_m^{-1} - 1|
      <= C . min{1, cgamma (m-n) + E^2 cgamma |log cgamma|^2} . 3^{cgamma (m-n)} .
```

## The route: the three-branch split

The display is proved by one case split on the size of the min-entry and, inside
the small branch, one dichotomy against the flow's relative defect
`delta := Cflow cstar^{-1} E cgamma^{1/2} |log cgamma|`.  Write
`x := cgamma (m-n)` and `Es := E^2 cgamma |log cgamma|^2`.

* **(A) far**, `x + Es >= 1/8`: `ShomContinuityCore.ratioSum_le_of_twoSided`
  gives `<= 8 . 3^{x}` outright from the two-sided envelope, and
  `min{1, x+Es} >= 1/8` absorbs the constant.  No regime input is used.
* **(B) flow**, `x + Es < 1/8` and `delta <= x`: the diffusivity asymptotics
  pin both `shom_m` and `shom_n` to the same profile at relative accuracy
  `delta`, and the profile itself grows by `1 + 4x` across the gap, so the two
  ratio defects sum to at most `8x + 24 delta <= 32 x`.
* **(C) recurrence**, `x + Es < 1/8` and `x < delta`: the sharpened
  `cgamma`-gate `E^4 cgamma^{1/2} |log cgamma| <= 16` (proved below with
  integer powers only, out of `|log g| <= 16 g^{-1/16}` and `cgamma <=
  E^{-10}`) forces `delta <= cstar^2 / 2`, hence `x <= cstar` --- the pair `(n,
  m)` is inside the recurrence producer's window `m <= n + cstar cgamma^{-1}`.

Branch (C) is where the printed entry is produced; branches (A) and (B) never
see it.  The manuscript's medium band `(1/2)min{1,cstar^2} cgamma^{-1} <= m-n
<= cgamma^{-1}` disappears under the sharpened gate ---, which records that the
printed `C = C(d)` is *not* attainable from the quoted input alone but *is*
attainable after the sharpening.

## The scale gate on `m0` (-bin statement change)

The landmark premise carried below is `mStarStar M < m0`, **not** the printed
`m0 in (mstar, infty) cap Z`.  The two producers consumed below are already
stated at the corrected gate, so the change here is the single binder and
nothing else: the proof forwards the premise to them verbatim.

## Inputs consumed, never re-proved

* `Closure.diffusivity_asymptotics_proved` --- the provider export of the
  `Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`: the `shom` flow
  display at every `m <= m0` together with the two-sided envelope at the top
  scale `m0`, gated at the `mStarStar M < m0`.  (The frozen root itself is
  consumed through this export, the frozen roots being outside the default
  build target.)
* `Closure.recurrenceIntegrationBinders_of_twoSidedClosure`, and through it
  `Closure.NodeContract.integrationHypotheses_of_displays`
  (`NodeContract.lean`), `Closure.TwoSidedTargets.sigmaBar_le_of_upperDisplay`
  (`TwoSidedTargets.lean`) and `Closure.TwoSidedTargets.sigmaBar_ge_of_displays`
  (`TwoSidedTargets.lean`), the three conversions that turn the two printed
  displays of `e.what.do.we.have` into the integration binders; the closure
  contract itself is discharged as described above.
* `ApproximateRecurrence.recurrence_binders_of_below_landmark` and its inputs
  `Diffusivity.annealedPlateau_smallScaleBound` (`e.plateau.region.bound`),
  `Provider.Scales.le_mStarStar_iff_rpow_le` (`e.mstarstar`),
  `Provider.Disorder.cstar_le_three_halves` and
  `ApproximateRecurrence.cstar_le_cstarPlus`.
* `Diffusivity.ShomContinuityCore` --- the model-free arithmetic core: the
  comparator `diffMax`, its positivity and geometric growth, the quarter
  comparison `quarter_le_of_twoSided`, and the far branch
  `ratioSum_le_of_twoSided` at the explicit constant `8`.  That file explicitly
  disclaims realizing the node because the short-range branch needs more than
  the envelope; this file supplies the rest.
* `RecurrenceIntegration.Internal.recurrenceIncrement_le_count` and
  `recurrenceIncrement_nonneg` --- the two elementary facts about `A_{n,m}` used
  in branch (C).
* `Localization.ShomContinuityArithmetic` --- this route's own model-free
  arithmetic layer, twenty-three `protected` theorems over abstract reals.  The
  five model-level lemmas of the route (`near_flow_bound`,
  `near_recurrence_bound`, `window_binders`, `slack_bounds`, `defect_display`)
  stayed here and remain `private`.

## References

* ABK26, `l.shom.continuity`; proof.
* ABK26, `e.shom.h.bounds`; `d.mathcalS.def`.
* ABK26, `e.what.do.we.have`; `l.approximate.recurrence.formula`.
* ABK26, `l.integrate.approx.recurrence`; `e.mstarstar`; `p.base.case`.
* ABK26, the localization `shom`-switch.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity

noncomputable section

/-! ## Branches (B) and (C) on the Section 3 carriers -/

/-- **Branch (B): the flow display carries the small-gap regime.**

Both scales are pinned to the same profile `sqrt(nu^2 + cstar cgamma^{-1} 3^{2
cgamma k})` at the same relative accuracy `dl`, and that profile grows by at
most `1 + 4 cgamma (m-n)` across the gap, so the two ratio defects sum to at
most `8 cgamma (m-n) + 24 dl`.  This is read off `e.shom.m.flow` rather than
off the recurrence. -/
private lemma near_flow_bound {d : ℕ} (M : ABKModel d) {n m : ℤ} {dl : ℝ}
    (hnm : n ≤ m) (hdl : dl ≤ 1 / 2)
    (hxsmall : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 1 / 8)
    (hfa : |(Annealed.sigmaBar M m : ℝ) - Real.sqrt (M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))| ≤
      dl * (Annealed.sigmaBar M m : ℝ))
    (hfb : |(Annealed.sigmaBar M n : ℝ) - Real.sqrt (M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))| ≤
      dl * (Annealed.sigmaBar M n : ℝ)) :
    |(Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M n : ℝ) - 1| +
        |(Annealed.sigmaBar M n : ℝ) / (Annealed.sigmaBar M m : ℝ) - 1| ≤
      8 * (M.gamma * ((m : ℝ) - (n : ℝ))) + 24 * dl := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hgeo0 : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) :=
    mul_nonneg hgamma0.le (by linarith)
  have hrpow0 : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) :=
    fun k => Real.rpow_pos_of_pos (by norm_num) _
  have hPn0 : (0 : ℝ) ≤ M.nu ^ 2 +
      Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) := by
    have := hrpow0 n
    positivity
  have hPm0 : (0 : ℝ) ≤ M.nu ^ 2 +
      Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have := hrpow0 m
    positivity
  have hPmono : M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) ≤
      M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hpow : (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) ≤
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hstep : (2 * M.gamma) * (n : ℝ) ≤ (2 * M.gamma) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hcast (by linarith [hgamma0])
      linarith [hstep]
    have hcoef : (0 : ℝ) ≤ Disorder.cstar M * M.gamma⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpow hcoef
    linarith [hmul]
  have hPgrow : M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
      (1 + 4 * (M.gamma * ((m : ℝ) - (n : ℝ)))) ^ 2 *
        (M.nu ^ 2 +
          Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) := by
    have hpow : (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) =
        (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hsplit : Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) =
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
      rw [hpow]
      ring
    have hcoef0 : (0 : ℝ) ≤
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) := by
      have := hrpow0 n
      positivity
    rw [hsplit]
    exact ShomContinuityArithmetic.profile_growth (sq_nonneg M.nu) hcoef0 hgeo0
      (ShomContinuityArithmetic.rpow_three_two_mul_le hgeo0 hxsmall)
  have hBA : Real.sqrt (M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) ≤
      Real.sqrt (M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) :=
    Real.sqrt_le_sqrt hPmono
  have hAB : Real.sqrt (M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤
      (1 + 4 * (M.gamma * ((m : ℝ) - (n : ℝ)))) *
        Real.sqrt (M.nu ^ 2 +
          Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) := by
    refine Provider.Corrector.le_of_sq_le_sq_of_nonneg ?_ ?_
    · rw [Real.sq_sqrt hPm0, mul_pow, Real.sq_sqrt hPn0]
      exact hPgrow
    · have hpos : (0 : ℝ) ≤ 1 + 4 * (M.gamma * ((m : ℝ) - (n : ℝ))) := by linarith [hgeo0]
      positivity
  exact ShomContinuityArithmetic.ratio_defect_le_of_relative hsm hsn hdl hgeo0 hxsmall
    hfa hfb hBA hAB

/-! ## Branch (C) on the Section 3 carriers -/

/-- **The envelope computation at the genuine carriers.**

From the two binders of `l.integrate.approx.recurrence` at an admissible pair
`(n, m)` inside the branch-(C) gate `cgamma (m-n) <= cstar^2 / 2`, together with
the lower envelope of the induction state at `n`, the two ratio defects sum to
at most `6 Eint cgamma + 432 cgamma (m-n) + 23328 F cgamma (m-n)`.

The three legs are the flat slack `Eint cgamma`, the relative increment
`A_{n,m} shom_n^{-2} <= 216 cgamma (m-n)` (using
`shom_n^{-2} <= 4 cstar^{-1} cgamma 3^{-2 cgamma n}` and
`3^{2 cgamma (m-n)} <= 27`), and the relative quadratic remainder
`<= 5832 F cgamma (m-n)` (using the same envelope squared and
`(cgamma (m-n))^2 <= (cstar^2 / 2) cgamma (m-n)`). -/
private lemma near_recurrence_bound {d : ℕ} (M : ABKModel d) {n m : ℤ} {Eint F : ℝ}
    (hEint0 : 0 ≤ Eint) (hF : 1 ≤ F)
    (hu : Eint * M.gamma ≤ 1 / 2) (hnm : n ≤ m)
    (hxcs : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ Disorder.cstar M ^ 2 / 2)
    (hlow : (1 / 4 : ℝ) * ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) n ≤
      (Annealed.sigmaBar M n : ℝ) ^ 2)
    (hup : (Annealed.sigmaBar M m : ℝ) ≤
      (1 + Eint * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
        RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m *
          ((Annealed.sigmaBar M n : ℝ))⁻¹)
    (hlo : (1 - Eint * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
          RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M m : ℝ) -
        F * ((m : ℝ) - (n : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
          (Annealed.sigmaBar M m : ℝ) * (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) ≤
      (Annealed.sigmaBar M m : ℝ)) :
    |(Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M n : ℝ) - 1| +
        |(Annealed.sigmaBar M n : ℝ) / (Annealed.sigmaBar M m : ℝ) - 1| ≤
      6 * (Eint * M.gamma) + 432 * (M.gamma * ((m : ℝ) - (n : ℝ))) +
        23328 * F * (M.gamma * ((m : ℝ) - (n : ℝ))) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hsnne : (Annealed.sigmaBar M n : ℝ) ≠ 0 := ne_of_gt hsn
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hdmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by linarith
  have hF0 : (0 : ℝ) ≤ F := by linarith
  have hx32 : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 3 / 2 := by
    nlinarith only [hxcs, hcs32, hcstar0]
  have hP0 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hT0 : (0 : ℝ) < (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hT27 : (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) ≤ 27 := by
    have hval : (3 : ℝ) ^ (3 : ℝ) = 27 := by
      rw [show (3 : ℝ) ^ (3 : ℝ) = (3 : ℝ) ^ ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith [hx32] : 2 * (M.gamma * ((m : ℝ) - (n : ℝ))) ≤ 3)
    linarith [hmono, hval.le, hval.ge]
  have hPT : (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hPT4 : (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) =
      ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) *
        ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))))) := by
    have hsplit : (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) =
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hsplit, hPT]
  have hdm : ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) n =
      max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
        (M.nu ^ 2) := rfl
  have hlowP : (1 / 4 : ℝ) *
      (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) ≤
      (Annealed.sigmaBar M n : ℝ) ^ 2 := by
    rw [hdm] at hlow
    have hmax : Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) ≤
        max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
          (M.nu ^ 2) := le_max_left _ _
    linarith [hlow, hmax]
  have hA0 : (0 : ℝ) ≤
      RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m :=
    RecurrenceIntegration.Internal.recurrenceIncrement_nonneg hcstar0.le n m
  have hAcount : RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m ≤
      Disorder.cstar M * Real.log 3 * ((m : ℝ) - (n : ℝ)) *
        ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ))))) := by
    have h := RecurrenceIntegration.Internal.recurrenceIncrement_le_count
      (cstar := Disorder.cstar M) (γ := M.gamma) hgamma0 hcstar0.le hnm
    simp only [RecurrenceIntegration.geometricTerm] at h
    rw [hPT] at h
    exact h
  have hai := ShomContinuityArithmetic.increment_ratio_le hcstar0 hgamma0 hP0 hT0 hT27
    (Real.log_nonneg (by norm_num)) Provider.Percolation.log_three_le_two
    hdmn hAcount hlowP rfl
  have hqq := ShomContinuityArithmetic.quad_ratio_le hcstar0 hgamma0 hP0 hT0 hT27 hF hdmn
    hlowP rfl hxcs
  have hqq0 : (0 : ℝ) ≤ F * ((m : ℝ) - (n : ℝ)) ^ 2 *
      (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
      ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) *
        ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ))))))  :=
    mul_nonneg (mul_nonneg (mul_nonneg hF0 (sq_nonneg _))
      (pow_nonneg (inv_nonneg.2 hsn.le) 4)) (by positivity)
  have hidUp : RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m *
      ((Annealed.sigmaBar M n : ℝ))⁻¹ =
      RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma n m *
        (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M n : ℝ) := by
    field_simp
  rw [hidUp] at hup
  have hidLo : F * ((m : ℝ) - (n : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
      (Annealed.sigmaBar M m : ℝ) * (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) =
      F * ((m : ℝ) - (n : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
          ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))) *
            ((3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (n : ℝ)))))) *
        (Annealed.sigmaBar M m : ℝ) := by
    rw [hPT4]
    ring
  rw [hidLo] at hlo
  have hcaps := ShomContinuityArithmetic.ratio_defect_le_of_caps hsm hsn
    (mul_nonneg hEint0 hgamma0.le) hu
    (mul_nonneg hA0 (sq_nonneg _)) hqq0 hup hlo
  linarith [hcaps, hai, hqq]

/-! ## The two producers, stitched over the whole window -/

/-- **The two integration binders at every admissible pair of the window.**

: `l.approximate.recurrence.formula` delivers its two displays only for
`mstarstar <= n`, and the closure feed inherits that binder.  Below the
landmark the two binders are consequences of the base-case plateau alone.
Splitting at `mStarStar M` therefore covers the whole window `m <= n + cstar
cgamma^{-1}`, `m <= m0`, with no lower bound on `n` --- exactly the range
`l.shom.continuity` is stated on.  This is the repository's own stitch
(`integrate_approx_recurrence_of_landmark_floored`, `SubLandmarkDisplays.lean`,
at its two use sites there), performed here at the continuity node's own
constants. -/
private lemma window_binders {d : ℕ} (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} {Crec : ℝ}
    (hgamma128 : M.gamma ≤ 1 / 128)
    (hEs0 : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
    (hmaster : (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) * (E : ℝ) ≤ 256)
    (hE256 : 256 * max 1 Crec ≤ (E : ℝ))
    (hbind : ApproximateRecurrence.Closure.recurrenceFlatError M Crec (E : ℝ) ≤ 1 →
      (∀ a b : ℤ, mStarStar M ≤ a → b ≤ m0 → a ≤ b →
          (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (Annealed.sigmaBar M b : ℝ) ≤
            (1 + ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
                M.gamma) * (Annealed.sigmaBar M a : ℝ) +
              RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
                ((Annealed.sigmaBar M a : ℝ))⁻¹) ∧
        (∀ a b : ℤ, mStarStar M ≤ a → b ≤ m0 → a ≤ b →
          (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (1 - ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
                  M.gamma) * (Annealed.sigmaBar M a : ℝ) +
                RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
                  (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M b : ℝ) -
              max 1 Crec * ((b : ℝ) - (a : ℝ)) ^ 2 *
                (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M b : ℝ) *
                (3 : ℝ) ^ (4 * M.gamma * (b : ℝ)) ≤
            (Annealed.sigmaBar M b : ℝ))) :
    (∀ a b : ℤ, b ≤ m0 → a ≤ b →
        (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
        (Annealed.sigmaBar M b : ℝ) ≤
          (1 + ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
              M.gamma) * (Annealed.sigmaBar M a : ℝ) +
            RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
              ((Annealed.sigmaBar M a : ℝ))⁻¹) ∧
      (∀ a b : ℤ, b ≤ m0 → a ≤ b →
        (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
        (1 - ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
                M.gamma) * (Annealed.sigmaBar M a : ℝ) +
              RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
                (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M b : ℝ) -
            max 1 Crec * ((b : ℝ) - (a : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M b : ℝ) *
              (3 : ℝ) ^ (4 * M.gamma * (b : ℝ)) ≤
          (Annealed.sigmaBar M b : ℝ)) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hCr1 : (1 : ℝ) ≤ max 1 Crec := le_max_left _ _
  have hCrecCr : Crec ≤ max 1 Crec := le_max_right _ _
  have hF0 : (0 : ℝ) ≤ max 1 Crec := by linarith [hCr1]
  have hErrEq : ApproximateRecurrence.Closure.recurrenceFlatError M Crec (E : ℝ)
      = Crec * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    unfold ApproximateRecurrence.Closure.recurrenceFlatError
    rw [sq_abs]
    ring
  have herr : ApproximateRecurrence.Closure.recurrenceFlatError M Crec (E : ℝ) ≤ 1 := by
    rw [hErrEq]
    have hCr := ShomContinuityArithmetic.flat_small
      (Es := (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
      (Ev := (E : ℝ)) (K := max 1 Crec) (c := 1) hE0 hmaster hF0
      (by norm_num) (by linarith [hE256])
    have hstep : Crec * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
        ≤ max 1 Crec * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) :=
      mul_le_mul_of_nonneg_right hCrecCr hEs0
    linarith [hCr, hstep]
  obtain ⟨hbindUp, hbindLo⟩ := hbind herr
  have hEint1 : (1 : ℝ) ≤
      ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) :=
    ApproximateRecurrence.Closure.one_le_recurrenceIntegrationSlack M Crec (E : ℝ)
  constructor
  · intro a b hb hab hr
    rcases le_or_gt (mStarStar M) a with ha | ha
    · exact hbindUp a b ha hb hab hr
    · exact (ApproximateRecurrence.recurrence_binders_of_below_landmark M.nu_pos
        hcstar0 hcs32 (ApproximateRecurrence.cstar_le_cstarPlus M) hgamma0 hgamma128
        hEint1 hF0 (annealedPlateau_smallScaleBound M)
        ((Provider.Scales.le_mStarStar_iff_rpow_le M a).mp (le_of_lt ha)) hab hr).1
  · intro a b hb hab hr
    rcases le_or_gt (mStarStar M) a with ha | ha
    · exact hbindLo a b ha hb hab hr
    · exact (ApproximateRecurrence.recurrence_binders_of_below_landmark M.nu_pos
        hcstar0 hcs32 (ApproximateRecurrence.cstar_le_cstarPlus M) hgamma0 hgamma128
        hEint1 hF0 (annealedPlateau_smallScaleBound M)
        ((Provider.Scales.le_mStarStar_iff_rpow_le M a).mp (le_of_lt ha)) hab hr).2

/-- **The integration slack is small, and is dominated by the printed entry.**

`recurrenceIntegrationSlack M = max 1 ((2 + shellIncrementCap)^2 log^2
cgamma)`, so `slack . cgamma <= cgamma + (2 + shellIncrementCap)(max 1 C) Es`;
the first summand is below `Es` by `le_flat`, and the second is below `1/4` by
the master gate at `E >= 1024 (2 + shellIncrementCap)(max 1 C)`. -/
private lemma slack_bounds {d : ℕ} (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}} {Crec : ℝ}
    (hCrec0 : 0 < Crec) (hgamma1024 : M.gamma ≤ 1 / 1024)
    (hEs0 : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
    (hmaster : (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) * (E : ℝ) ≤ 256)
    (hgEs : M.gamma ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
    (hE1024 : 1024 * ((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      max 1 Crec) ≤ (E : ℝ)) :
    ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) * M.gamma
        ≤ 1 / 2 ∧
      ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) * M.gamma
        ≤ (1 + (2 + ApproximateRecurrence.Closure.shellIncrementCap) * max 1 Crec) *
          ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hcap0 : (0 : ℝ) ≤ ApproximateRecurrence.Closure.shellIncrementCap :=
    ApproximateRecurrence.Closure.shellIncrementCap_pos.le
  have hCr1 : (1 : ℝ) ≤ max 1 Crec := le_max_left _ _
  have hCrecCr : Crec ≤ max 1 Crec := le_max_right _ _
  have hF0 : (0 : ℝ) ≤ max 1 Crec := by linarith [hCr1]
  have hY0 : (0 : ℝ) ≤ (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      (Crec * (E : ℝ) ^ 2 * Real.log M.gamma ^ 2) :=
    mul_nonneg (by linarith)
      (mul_nonneg (mul_nonneg hCrec0.le (sq_nonneg _)) (sq_nonneg _))
  have hslackLe : ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ)
      ≤ 1 + (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
        (Crec * (E : ℝ) ^ 2 * Real.log M.gamma ^ 2) := by
    unfold ApproximateRecurrence.Closure.recurrenceIntegrationSlack
    exact max_le (by linarith [hY0]) (by linarith [hY0])
  have hYid : (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
        (Crec * (E : ℝ) ^ 2 * Real.log M.gamma ^ 2) * M.gamma
      = ((2 + ApproximateRecurrence.Closure.shellIncrementCap) * Crec) *
        ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    rw [sq_abs]
    ring
  have hYmono : ((2 + ApproximateRecurrence.Closure.shellIncrementCap) * Crec) *
        ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))
      ≤ ((2 + ApproximateRecurrence.Closure.shellIncrementCap) * max 1 Crec) *
        ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCrecCr (by linarith)) hEs0
  have hslackEs :
      ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) * M.gamma
        ≤ M.gamma + ((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
          max 1 Crec) * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    have hstep := mul_le_mul_of_nonneg_right hslackLe hgamma0.le
    linarith [hstep, hYid, hYmono]
  have hKfEs : (4 : ℝ) * (((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      max 1 Crec) * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ≤ 1 :=
    ShomContinuityArithmetic.flat_small hE0 hmaster (mul_nonneg (by linarith) hF0)
      (by norm_num)
      (by linarith [hE1024])
  exact ⟨by linarith [hslackEs, hKfEs, hgamma1024], by linarith [hslackEs, hgEs]⟩

/-! ## The defect display: the three-branch dispatch -/

/-- **`e.shom.m.vs.shom.n` at the printed min-entry.**

The conjunct-5 display, from the two envelope families of the induction state
and the asymptotics (`henv`), the flow display (`hflowAll`), and the
recurrence-binder producer of the closure feed (`hbind`, still carrying its
flat error premise).  The three branches are (A) `x + Es >= 1/8`, (B) `x + Es <
1/8` with `delta <= x`, and (C) `x + Es < 1/8` with `x < delta`; only (C) uses
the recurrence, and there the pair is inside the producer's window by the
sharpened `E^4` gate. -/
private lemma defect_display {d : ℕ} (M : ABKModel d) {m0 n m : ℤ}
    {E : {E : ℝ // 1 ≤ E}} {Cflow Crec Cbig : ℝ} (hCrec0 : 0 < Crec)
    (hCbigPos : 0 < Cbig) (hCbig64 : (64 : ℝ) ≤ Cbig)
    (hCbig32Cf : 32 * max 1 Cflow ≤ Cbig) (hCbig384 : 384 * max 1 Crec ≤ Cbig)
    (hCbigKf : 1536 * ((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      max 1 Crec) ≤ Cbig)
    (hCbig6 : 6 * (1 + (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      max 1 Crec) ≤ Cbig)
    (hCbigQ : 432 + 23328 * max 1 Crec ≤ Cbig)
    (hCE : Cbig * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hnm : n ≤ m) (hm : m ≤ m0) (hn : n ≤ m0)
    (hflowAll : ∀ k : ℤ, k ≤ m0 →
      |(Annealed.sigmaBar M k : ℝ) - Real.sqrt (M.nu ^ 2 +
          Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))| ≤
        Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) * Real.sqrt M.gamma *
          |Real.log M.gamma| * (Annealed.sigmaBar M k : ℝ))
    (henv : ∀ k : ℤ, k ≤ m0 →
      (1 / 4 : ℝ) * ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) k ≤
          (Annealed.sigmaBar M k : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M k : ℝ) ^ 2 ≤
          4 * ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) k)
    (hbind : ApproximateRecurrence.Closure.recurrenceFlatError M Crec (E : ℝ) ≤ 1 →
      (∀ a b : ℤ, mStarStar M ≤ a → b ≤ m0 → a ≤ b →
          (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (Annealed.sigmaBar M b : ℝ) ≤
            (1 + ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
                M.gamma) * (Annealed.sigmaBar M a : ℝ) +
              RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
                ((Annealed.sigmaBar M a : ℝ))⁻¹) ∧
        (∀ a b : ℤ, mStarStar M ≤ a → b ≤ m0 → a ≤ b →
          (b : ℝ) ≤ (a : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
          (1 - ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) *
                  M.gamma) * (Annealed.sigmaBar M a : ℝ) +
                RecurrenceIntegration.recurrenceIncrement (Disorder.cstar M) M.gamma a b *
                  (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M b : ℝ) -
              max 1 Crec * ((b : ℝ) - (a : ℝ)) ^ 2 *
                (((Annealed.sigmaBar M a : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M b : ℝ) *
                (3 : ℝ) ^ (4 * M.gamma * (b : ℝ)) ≤
            (Annealed.sigmaBar M b : ℝ))) :
    |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ - 1| +
        |(Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1| ≤
      Cbig * min 1 (M.gamma * ((m : ℝ) - (n : ℝ)) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) *
        (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hsn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hgeo0 : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) :=
    mul_nonneg hgamma0.le (by linarith [hcast])
  have ht1 : (1 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) :=
    Real.one_le_rpow (by norm_num) hgeo0
  have hCf1 : (1 : ℝ) ≤ max 1 Cflow := le_max_left _ _
  have hCr1 : (1 : ℝ) ≤ max 1 Crec := le_max_left _ _
  have hCflowCf : Cflow ≤ max 1 Cflow := le_max_right _ _
  -- `E` is above every threshold the route needs, because `cstar <= 3/2`
  have hcinv23 : (2 / 3 : ℝ) ≤ (Disorder.cstar M)⁻¹ := by
    have hstep : ((3 : ℝ) / 2)⁻¹ ≤ (Disorder.cstar M)⁻¹ := inv_anti₀ hcstar0 hcs32
    have hval : ((3 : ℝ) / 2)⁻¹ = 2 / 3 := by norm_num
    linarith only [hstep, hval.le, hval.ge]
  have hEbig : Cbig * (2 / 3 : ℝ) ≤ (E : ℝ) := by
    have hstep : Cbig * (2 / 3 : ℝ) ≤ Cbig * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_left hcinv23 hCbigPos.le
    linarith only [hstep, hCE]
  have hE2 : (2 : ℝ) ≤ (E : ℝ) := by linarith only [hEbig, hCbig64]
  have hE256 : 256 * max 1 Crec ≤ (E : ℝ) := by linarith only [hEbig, hCbig384]
  have hE1024 : 1024 * ((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
      max 1 Crec) ≤ (E : ℝ) := by linarith only [hEbig, hCbigKf]
  -- the sharpened cgamma-gate and its consequences
  have hgamma1024 : M.gamma ≤ 1 / 1024 :=
    ShomContinuityArithmetic.gamma_small hE2 hgammaE
  have hLog1 : (1 : ℝ) ≤ |Real.log M.gamma| :=
    ShomContinuityArithmetic.one_le_abs_log hgamma0 (by linarith only [hgamma1024])
  have hsg0 : (0 : ℝ) ≤ Real.sqrt M.gamma * |Real.log M.gamma| := by positivity
  have hsgGate : (E : ℝ) ^ 4 * (Real.sqrt M.gamma * |Real.log M.gamma|) ≤ 16 :=
    ShomContinuityArithmetic.pow_four_mul_sqrt_mul_abs_log_le hgamma0 hE1 hgammaE
  have hEsSg : (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)
      = (E : ℝ) ^ 2 * (Real.sqrt M.gamma * |Real.log M.gamma|) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hgamma0.le]
  have hEs0 : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) := by
    positivity
  have hmaster : (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) * (E : ℝ) ≤ 256 := by
    rw [hEsSg]
    exact ShomContinuityArithmetic.flat_master hE1 hsg0 hsgGate
  have hgEs : M.gamma ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) :=
    ShomContinuityArithmetic.le_flat hgamma0.le hE1 hLog1
  obtain ⟨hupperAll, hlowerAll⟩ :=
    window_binders M (by linarith only [hgamma1024]) hEs0 hmaster hE256 hbind
  obtain ⟨hu, huFinal⟩ :=
    slack_bounds M hCrec0 hgamma1024 hEs0 hmaster hgEs hE1024
  have hEint1 : (1 : ℝ) ≤
      ApproximateRecurrence.Closure.recurrenceIntegrationSlack M Crec (E : ℝ) :=
    ApproximateRecurrence.Closure.one_le_recurrenceIntegrationSlack M Crec (E : ℝ)
  -- the flow's relative defect and its gate
  have hCf32E : 32 * max 1 Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    have hstep : 32 * max 1 Cflow * (Disorder.cstar M)⁻¹ ≤ Cbig * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_right hCbig32Cf hcinv0.le
    linarith only [hstep, hCE]
  have hdefect : max 1 Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
      (Real.sqrt M.gamma * |Real.log M.gamma|) ≤ Disorder.cstar M ^ 2 / 2 :=
    ShomContinuityArithmetic.defect_le_cstar_sq hE1 hsgGate hcstar0 hCf1 hCf32E
  have hconv : |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ - 1| +
        |(Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1| =
      |(Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M n : ℝ) - 1| +
        |(Annealed.sigmaBar M n : ℝ) / (Annealed.sigmaBar M m : ℝ) - 1| := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [hconv]
  rcases le_or_gt (1 / 8 : ℝ)
      (M.gamma * ((m : ℝ) - (n : ℝ)) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) with hfar | hnear
  · -- branch (A): the envelope alone gives the un-cancelled `8 . 3^{cgamma (m-n)}`
    have hbase := ShomContinuityCore.ratioSum_le_of_twoSided
      (s := fun k => (Annealed.sigmaBar M k : ℝ)) hgamma0 hcstar0 hnm hsm hsn
      (henv m hm).1 (henv m hm).2 (henv n hn).1 (henv n hn).2
    exact ShomContinuityArithmetic.display_of_far hbase hfar ht1 hCbig64
  · have hxsmall : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 1 / 8 := by
      linarith only [hnear, hEs0]
    have hone : M.gamma * ((m : ℝ) - (n : ℝ)) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) ≤ 1 := by linarith only [hnear]
    have hX0 : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) := by
      linarith only [hgeo0, hEs0]
    refine ShomContinuityArithmetic.display_of_bound ?_ hX0 hone ht1 hCbigPos.le
    rcases le_or_gt (max 1 Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
        (Real.sqrt M.gamma * |Real.log M.gamma|))
        (M.gamma * ((m : ℝ) - (n : ℝ))) with hB | hC
    · -- branch (B): the flow's relative defect controls the ratio
      have hfa := ShomContinuityArithmetic.flow_regroup (hflowAll m hm) hCflowCf hcinv0.le
        hE0.le
        (Real.sqrt_nonneg _) (abs_nonneg _) hsm.le
      have hfb := ShomContinuityArithmetic.flow_regroup (hflowAll n hn) hCflowCf hcinv0.le
        hE0.le
        (Real.sqrt_nonneg _) (abs_nonneg _) hsn.le
      have hnearBound :=
        near_flow_bound M hnm (by linarith only [hB, hxsmall]) hxsmall hfa hfb
      have hs1 : (32 : ℝ) * (M.gamma * ((m : ℝ) - (n : ℝ))) ≤
          Cbig * (M.gamma * ((m : ℝ) - (n : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith only [hCbig64]) hgeo0
      have hs2 : (0 : ℝ) ≤ Cbig *
          ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) :=
        mul_nonneg hCbigPos.le hEs0
      linarith only [hnearBound, hB, hs1, hs2]
    · -- branch (C): the pair is inside the recurrence producer's window
      have hxcs : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ Disorder.cstar M ^ 2 / 2 := by
        linarith only [hC, hdefect]
      have hxle : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ Disorder.cstar M :=
        le_trans hxcs (ShomContinuityArithmetic.sq_half_le hcstar0 hcs32)
      have hwin : (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ := by
        have hmul := mul_le_mul_of_nonneg_left hxle (inv_nonneg.2 hgamma0.le)
        have hid : M.gamma⁻¹ * (M.gamma * ((m : ℝ) - (n : ℝ))) = (m : ℝ) - (n : ℝ) := by
          field_simp
        have hid2 : M.gamma⁻¹ * Disorder.cstar M = Disorder.cstar M * M.gamma⁻¹ := by
          ring
        linarith only [hmul, hid, hid2]
      have hrec := near_recurrence_bound M (by linarith only [hEint1]) hCr1 hu hnm hxcs
        (henv n hn).1 (hupperAll n m hm hnm hwin) (hlowerAll n m hm hnm hwin)
      have hq1 : (6 * (1 + (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
            max 1 Crec)) * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) ≤
          Cbig * ((E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) :=
        mul_le_mul_of_nonneg_right hCbig6 hEs0
      have hq2 : (432 + 23328 * max 1 Crec) * (M.gamma * ((m : ℝ) - (n : ℝ))) ≤
          Cbig * (M.gamma * ((m : ℝ) - (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hCbigQ hgeo0
      linarith only [hrec, huFinal, hq1, hq2]

/-! ## The node's arithmetic on the Section 3 carriers -/

/-- **Continuity of `m |-> shom_m`** (`l.shom.continuity`, ABK26), on the printed
premise list with the landmark gate at `mStarStar M < m0`,
for every pair of integer scales `n <= m <= m0`.

Proved from `Closure.diffusivity_asymptotics_proved` and
`Closure.recurrenceIntegrationBinders_of_twoSidedClosure` together with the
closure contract's two produced obligations
(`closureInteriorBesovEnvelopeInput_proved`, `closureStripRemainder_proved`),
and the below-landmark binder producer
`ApproximateRecurrence.recurrence_binders_of_below_landmark`. -/
theorem shom_continuity (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ m n : ℤ, n ≤ m → m ≤ m0 →
          (1 / 4 : ℝ) * (Annealed.sigmaBar M n : ℝ) ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤ 4 ∧
          (Annealed.sigmaBar M m : ℝ) ≤
            4 * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) *
              (Annealed.sigmaBar M n : ℝ) ∧
          (M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 1 →
            (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤ 12) ∧
          |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ - 1| +
              |(Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1| ≤
            C * min 1 (M.gamma * ((m : ℝ) - (n : ℝ)) +
                (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) *
              (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
  by_cases hd : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    obtain ⟨Cflow, -, hflow⟩ :=
      ApproximateRecurrence.Closure.diffusivity_asymptotics_proved d hd
    obtain ⟨Crec, hCrec0, hbind⟩ :=
      ApproximateRecurrence.Closure.recurrenceIntegrationBinders_of_twoSidedClosure hd
        (ApproximateRecurrence.Closure.twoSidedClosure_of_interiorEnvelope d
          (ApproximateRecurrence.Closure.closureInteriorBesovEnvelopeInput_proved d hd)
          (ApproximateRecurrence.Closure.closureStripRemainder_proved d hd))
    have hcap0 : (0 : ℝ) ≤ ApproximateRecurrence.Closure.shellIncrementCap :=
      ApproximateRecurrence.Closure.shellIncrementCap_pos.le
    have hCf1 : (1 : ℝ) ≤ max 1 Cflow := le_max_left _ _
    have hCr1 : (1 : ℝ) ≤ max 1 Crec := le_max_left _ _
    have hcapCr : (0 : ℝ) ≤ ApproximateRecurrence.Closure.shellIncrementCap * max 1 Crec :=
      mul_nonneg hcap0 (by linarith)
    obtain ⟨Cbig, hCbig_def⟩ : ∃ z : ℝ, z =
        4096 + 32 * max 1 Cflow +
          1536 * ((2 + ApproximateRecurrence.Closure.shellIncrementCap) * max 1 Crec) +
          262144 * max 1 Crec := ⟨_, rfl⟩
    have hCbigPos : (0 : ℝ) < Cbig := by rw [hCbig_def]; linarith
    have hCbig64 : (64 : ℝ) ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbig32Cf : 32 * max 1 Cflow ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbig384 : 384 * max 1 Crec ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbigKf : 1536 * ((2 + ApproximateRecurrence.Closure.shellIncrementCap) *
        max 1 Crec) ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbig6 : 6 * (1 + (2 + ApproximateRecurrence.Closure.shellIncrementCap) *
        max 1 Crec) ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbigQ : 432 + 23328 * max 1 Crec ≤ Cbig := by rw [hCbig_def]; linarith
    have hCbigCflow : Cflow ≤ Cbig := by
      rw [hCbig_def]
      linarith [le_max_right 1 Cflow]
    have hCbigCrec : Crec ≤ Cbig := by
      rw [hCbig_def]
      linarith [le_max_right 1 Crec]
    refine ⟨Cbig, hCbigPos, ?_⟩
    intro M m0 E hm0 hstate hCE hgammaE m n hnm hm
    have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
    have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
    have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
    have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
    have hn : n ≤ m0 := le_trans hnm hm
    have hsm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
    have hsn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hCflowE : Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
      have hstep : Cflow * (Disorder.cstar M)⁻¹ ≤ Cbig * (Disorder.cstar M)⁻¹ :=
        mul_le_mul_of_nonneg_right hCbigCflow hcinv0.le
      linarith [hstep, hCE]
    obtain ⟨hflowAll, hsandLo, hsandHi⟩ := hflow M m0 E hm0 hstate hCflowE hgammaE
    -- the comparator of `ShomContinuityCore` is the induction state's profile
    have hdm : ∀ k : ℤ,
        ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) k =
          max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
            (M.nu ^ 2) := fun _ => rfl
    -- the two-sided envelope at every scale below `m0`
    have henv : ∀ k : ℤ, k ≤ m0 →
        (1 / 4 : ℝ) * ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) k ≤
            (Annealed.sigmaBar M k : ℝ) ^ 2 ∧
          (Annealed.sigmaBar M k : ℝ) ^ 2 ≤
            4 * ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) k := by
      intro k hk
      rw [hdm k]
      rcases eq_or_lt_of_le hk with hk0 | hk0
      · subst hk0
        exact ⟨hsandLo, hsandHi⟩
      · exact hstate.1 k (by omega)
    -- conclusion 1: the quarter comparison
    have hquarter : (1 / 4 : ℝ) * (Annealed.sigmaBar M n : ℝ) ≤
        (Annealed.sigmaBar M m : ℝ) :=
      ShomContinuityCore.quarter_le_of_twoSided
        (s := fun k => (Annealed.sigmaBar M k : ℝ)) hgamma0 hcstar0 hnm hsm
        (henv m hm).1 (henv n hn).2
    -- conclusion 2: its ratio form
    have hratioDown : (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤ 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hsm]
      linarith [hquarter]
    -- the geometric factor
    have hgeo0 : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) :=
      mul_nonneg hgamma0.le (by linarith [hcast])
    have ht1 : (1 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) :=
      Real.one_le_rpow (by norm_num) hgeo0
    -- conclusion 3: the growth cap
    have hcomp : ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) m ≤
        (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) *
          ShomContinuityCore.diffMax M.nu M.gamma (Disorder.cstar M) n := by
      have hbase := ShomContinuityCore.diffMax_le_rpow_mul (nu := M.nu)
        (cstar := Disorder.cstar M) hgamma0 hnm
      have hsq : (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (n : ℝ))) =
          (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      rw [hsq] at hbase
      linarith [hbase]
    have hgrowth : (Annealed.sigmaBar M m : ℝ) ≤
        4 * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) * (Annealed.sigmaBar M n : ℝ) :=
      ShomContinuityArithmetic.growth_from_sq hsn ht1 (henv m hm).2 hcomp (henv n hn).1
    -- conclusion 4: the short-range collapse
    have hcollapse : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 1 →
        (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤ 12 := by
      intro hsmall
      have ht3 : (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) ≤ 3 := by
        have hstep := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num) hsmall
        rwa [Real.rpow_one] at hstep
      rw [← div_eq_mul_inv]
      exact ShomContinuityArithmetic.collapse_of_growth hsn hgrowth ht3
    -- conclusion 5: the defect display, through the three-branch dispatch
    have hCrecE : Crec * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
      have hstep : Crec * (Disorder.cstar M)⁻¹ ≤ Cbig * (Disorder.cstar M)⁻¹ :=
        mul_le_mul_of_nonneg_right hCbigCrec hcinv0.le
      linarith [hstep, hCE]
    have hgamma5 : M.gamma ≤ ((E : ℝ)) ^ (-5 : ℤ) := by
      have hid : ((E : ℝ)) ^ (-5 : ℤ) = ((E : ℝ)⁻¹) ^ (5 : ℕ) := by
        rw [zpow_neg, inv_pow, ← zpow_natCast ((E : ℝ)) 5]
        norm_num
      have hmono : ((E : ℝ)⁻¹) ^ (10 : ℕ) ≤ ((E : ℝ)⁻¹) ^ (5 : ℕ) :=
        pow_le_pow_of_le_one (by positivity)
          (by rw [inv_le_one₀ hE0]; exact hE1) (by norm_num)
      rw [hid]
      linarith [hgammaE, hmono]
    exact ⟨hquarter, hratioDown, hgrowth, hcollapse,
      defect_display M hCrec0 hCbigPos hCbig64 hCbig32Cf hCbig384 hCbigKf hCbig6
        hCbigQ hCE hgammaE hnm hm hn hflowAll henv
        (hbind M m0 E hm0 hstate hCrecE hgamma5)⟩
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd⟩

end

end Algsuperdiff.Section3.Provider.Localization
