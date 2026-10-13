/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ScaleSummation

/-!
# LowerLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The lower leg of `p.cg.ellipticity.bounds`, reduced to a family-split payload

`p.cg.ellipticity.bounds` (ABK26, statement) is split by
`Provider/CoarseEllipticity/Assembly.lean` into two independent legs, each with
its own constant; `coarse_ellipticity_bounds_of_legs` recomposes them into the
frozen statement verbatim.  This module is the **lower leg's** reduction layer:
it proves that leg from an analytic *payload* in the exact shape the source's
"after summing over `n`" step produces.

## The leg's shape, and why it is a *family* statement

The frozen lower display is a `Probability.IsLowerIntegerFamilyOrlicz`: one
measurable witness `Y`, one deterministic shift
`lowerEllipticityProfile Ccg gamma s q`, and the domination clause

```
dominates : forall omega, forall L, m - 1 <= L -> X L omega <= b + Y omega
```

quantified over **every** cutoff index `L >= m - 1` with a **single** witness.
That is the Lean reading of the source's `sup_{L >= m-1}` on the left of
`e.cg.ellip.lower`.  Two structural consequences drive everything below.

1. `dominates` is **pointwise in `omega`**, not almost everywhere.  Every
   payload binder and every constructor below is therefore **pointwise by
   construction**; no theorem in this module produces, consumes or upgrades an
   almost-everywhere witness.
2. The deterministic shift `b` is a *number*, so the source's `sup_L` costs
   nothing extra once the majorant is `L`-free.

## The single lane

`e.cg.ellip.lower` carries **one** exceptional lane `Gamma_{(1-sigma)/2}` and
no ordinary `Gamma_1` lane states this explicitly ("the corrected lane lives on
the U leg only --- `e.cg.ellip.lower` has no ordinary lane, so every
lower-leg-only consumer is untouched a fortiori").  The lower leg's summation
is therefore a **two**-slot statement, not an instance of the three-slot one.
It is not carried in this module: the payload binder below is exactly its
output, and the two ingredients such a summation rests on
(`ScaleSummation.measurable_tsum_of_nonneg`,
`ScaleSummation.isBigOWith_gammaSigma_tsum_weighted`) are proved in
`ScaleSummation.lean`.

## What is proved here

* `isLowerIntegerFamilyOrlicz_of_familySplit` --- model-free.  A pointwise
  family split `X L omega <= Ydet omega + Y omega` with `Ydet <= b`
  deterministic and `Y` carrying a `Gamma_sigma` tail *is* the frozen carrier.
  The witness handed to `IsLowerIntegerFamilyOrliczWithWitness` is `Y` itself
  and its `dominates` clause is discharged pointwise.
* `coarse_ellipticity_lower_leg_body_of_familySplitPayload` --- **the
  reduction**: from the family-split payload the lower leg's `forall`-body, in
  the exact shape `coarse_ellipticity_bounds_body_of_legs` consumes as `hlow`.
  It is a conditional reduction: the lower leg follows once the analytic
  payload is actually proved.

## The historical conditional route retained in this module

This module itself does not produce its `payload`.  The list below records the
obligations of this historical conditional route; it is not the current global
status of the lower leg.  The concrete downstream theorem
`superposedFlux_coarse_ellipticity_lower_leg` now supplies the lower leg without
exposing this payload as a theorem hypothesis.  The separate downstream theorem
`superposedFlux_coarse_ellipticity_upper_leg` supplies the upper leg.

Nothing below produces that payload: within these helpers it remains a proof
obligation rather than a source premise.  Concretely this retained route asks
its caller for:

* The frozen `p.base.case` is now proved, but its application and the
  `l.mathcal.E.to.Lambdas` passage are not performed here.
* `p.bfA.multiscalebound` --- the per-scale block estimate `e.slstar.multiscale`,
  which is what a producer of the family-split payload must supply at the
  source's own grid weights `w_k = mass * gridWeight rho k`, together with the
  `e.maxy.bound` grid lift of `GridWeights.gridSupAbs_descendants_isBigOWith`.
* `hgrid` --- the on-grid bound of the target by a weighted series of grid
  maxima.

`Provider/CoarseEllipticity/LowerLegProfile.lean` splits that slot into the
three source branches.

## References

* ABK26, `p.cg.ellipticity.bounds`, statement (`e.cg.ellip.lower`), proof (the
  "after summing over `n`" step and the intermediate `e.cg.ellip.lower.pre`),
  small-`m` branch.
* `Algsuperdiff/Section3/Provider/CoarseEllipticity/Assembly.lean` (the leg
  split), `.../ScaleSummation.lean` and `.../GridWeights.lean`
  (the summation infrastructure reused here),
  `Algsuperdiff/Section3/Provider/BadEvents/CubeEllipticity.lean` (the
  centered-cube literal identities).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-! ## 1. The model-free family constructor -/

/-- **A pointwise family split is the frozen lower carrier.**

The source's `sup_{L >= L0} X_L <= b + O_{Gamma_sigma}(A)` is, in this
repository, `Probability.IsLowerIntegerFamilyOrlicz`: one measurable witness
controlling every index at once.  This lemma builds it from a split
`X L omega <= Ydet omega + Y omega` that is **pointwise in `omega`** and uniform
in `L`, with `Ydet` bounded by the deterministic shift.

The witness handed over is `Y` itself, so no witness surgery of any kind occurs
and the `dominates` field is discharged at every sample point; see the module
docstring for why an almost-everywhere split would *not* suffice. -/
theorem isLowerIntegerFamilyOrlicz_of_familySplit {sigmaTail : ℝ}
    {X : ℤ → Omega → ℝ} {Ydet Y : Omega → ℝ} {L0 : ℤ} {b A : ℝ}
    (hsigmaTail : 0 < sigmaTail) (hA : 0 < A)
    (hXmeas : ∀ L : ℤ, L0 ≤ L → Measurable (X L))
    (hYmeas : Measurable Y)
    (hdom : ∀ omega, ∀ L : ℤ, L0 ≤ L → X L omega ≤ Ydet omega + Y omega)
    (hdet : ∀ omega, Ydet omega ≤ b)
    (htail : IsBigOWith mu (gammaSigma sigmaTail) Y A) :
    Probability.IsLowerIntegerFamilyOrlicz mu (gammaSigma sigmaTail) X L0 b A := by
  refine ⟨Y, Probability.isAdmissibleTail_gammaSigma hsigmaTail, hA, hXmeas,
    hYmeas, ?_, htail⟩
  intro omega L hL
  have h1 := hdom omega L hL
  have h2 := hdet omega
  linarith

/-! ## 2. The scale summation, in the lower leg's two-slot family shape

The summation itself is not carried in this module; its output is the payload
binder of section 3. -/


/-! ## 3. The leg, reduced to the family-split payload -/

/-- **The lower leg's `forall`-body from the family-split payload.**

The payload is the analytic output of the lower summation in the shape that
step produces it: a pointwise, `L`-uniform split of the whole family `sup_{L >=
m-1} lambda_{s,q}^{-1}(cu_m; a_L) shom_{m-1}` into a deterministic `Ydet`
bounded by the source profile `lowerEllipticityProfile Clow gamma s q`, and one
measurable exceptional lane `Y` at the frozen rare scale `exp(-Clow^{-1} E^{-2}
gamma^{-1})`.

Nothing but the definition of the frozen carrier and the source's own window is
used: `0 < (1-sigma)/2` comes from `sigma in (0,1/2]`, the tail scale is a
positive exponential, and the observables' measurability is the proved
`Observable.measurable_cutoffLowerEllipticityInv`.  The reduction is uniform in
`q`. -/
theorem coarse_ellipticity_lower_leg_body_of_familySplitPayload (d : ℕ)
    {Clow : ℝ}
    (payload :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : Cutoff.CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                      Ydet omega + Y omega) ∧
                (∀ omega,
                  Ydet omega ≤ lowerEllipticityProfile Clow M.gamma s q) ∧
                Measurable Y ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) :
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
          max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ q : CoarseEllipticityExponent,
            ∀ s : ℝ,
              ∀ hsWindow : s ∈ Set.Icc
                (M.gamma / 2 +
                  Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              Probability.IsLowerIntegerFamilyOrlicz
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma
                    ((1 - sigma) / 2))
                  (fun L : ℤ =>
                    fun omega =>
                      Observable.cutoffLowerEllipticityInv
                          M m L s
                          (by
                            exact
                              (add_pos
                                (div_pos M.shellPrefix.gamma_pos (by norm_num))
                              (Real.exp_pos
                                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 *
                                    M.gamma⁻¹)))).trans_le hsWindow.1)
                          q omega *
                        (Annealed.sigmaBar M (m - 1) : ℝ))
                  (m - 1)
                  (lowerEllipticityProfile Clow M.gamma s q)
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  intro M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  obtain ⟨Ydet, Y, hdom, hdet, hYmeas, htail⟩ :=
    payload M m E hstate sigma hsigma hE1 hE2 q s hsWindow
  refine isLowerIntegerFamilyOrlicz_of_familySplit (Ydet := Ydet) ?_
    (Real.exp_pos _) ?_ hYmeas hdom hdet htail
  · have hsig := hsigma.2
    linarith
  · intro L _
    exact (Observable.measurable_cutoffLowerEllipticityInv M m L s _ q).mul_const _


end Algsuperdiff.Section3.Provider.CoarseEllipticity
