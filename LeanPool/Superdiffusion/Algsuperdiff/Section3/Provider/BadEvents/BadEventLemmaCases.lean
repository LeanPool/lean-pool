/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaOscillation

/-!
# BadEventLemmaCases

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse-ellipticity branch and the umbrella of `l.bad.event.lemma`

ABK26's Lemma `l.bad.event.lemma` decomposes the failure of the good local
sensitivity event `Q(m,n,z)` of `e.good.local.events` into an oscillation branch
(implemented locally in `BadEventLemmaOscillation.lean`) and a
coarse-ellipticity branch, and concludes the displayed estimate
`e.bad.event.Q.estimate`

```
P[ not Q(m,n,z) ]
  <= exp( - c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+} )
     + exp( - exp( c E^{-2} gamma^{-1} ) ) .
```

This module supplies a conditional local result for the coarse-ellipticity
branch **case `n >= m`** and the umbrella on the same branch, both
**conditionally** on the exact coarse-ellipticity conclusion.  The frozen
coarse theorem is now proved, but this local A retains that conclusion as the
disclosed `hcg` binder until a downstream assembly discharges it together with
the separate transport obligation.

## The two disclosed conditional binders

The frozen `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is proved.
This conditional helper still carries its conclusion as an explicit A
hypothesis, in the *exact* shape of its specialization at the cube scale `n`,
`sigma = 1/2`, `s = 1/8`, `q = 2`; a downstream assembly may now discharge that
hypothesis from the frozen export.  This module does not itself perform that
assembly or confer graph status:

* `hcg` is the first conjunct of
  `(coarse_ellipticity_bounds d).choose_spec.2 M n E hS (1/2) hsigma hE hEgamma
  exponentTwo (1/8) hsWindow`, verbatim.  The discharge of `hcg` from the proved
  frozen theorem is exactly that term.
* The needed lemma, in the exact form the branch consumes, is
  ```
  lambda^{-1}_{1/8,2}(z + square_m; a_n) <= lambda^{-1}_{1/8,2}(square_n; a_n)
  ```
  for `m <= n`, pointwise in the sample.  At an off-centre cube it also absorbs
  the manuscript's `z = 0` stationarity reduction, since the frozen observable
  lives at the centered cube; at the centered cube of scale `m` it is exactly
  the manuscript's unstated step.  It is a *different* statement from the
  exponent monotonicity `e.ellipticities.monotone.ordered`.

Two further gates are disclosed:

* `hCcg : 1 <= Ccg` normalizes the frozen constant `C_{(e.cg.ellip.lower)}`.  It
  is what turns the tail level `Ccg exp(Ccg^{-1} E^{-2} gamma^{-1})` into the
  manuscript's `exp(c E^{-2} gamma^{-1})`, and it would be discharged by
  the frozen theorem's own choice of constant.
* `hgamma : gamma <= 1/8` makes the frozen deterministic profile
  `lowerEllipticityProfile Ccg gamma (1/8) 2 = Ccg / (8 (1/4 - gamma))` at most
  `Ccg`, which is what the manuscript's threshold `2 C_{(e.cg.ellip.lower)}`
  needs.  It is **not** an addition: `gamma_le_one_eighth_of_admissible` derives
  it from the manuscript's own admissibility `e.bad.event.admissibility` at the
  dimension-only constant `badEventOscAdmissibleConst`.

## What is *not* here

The case `n < m` is not realized.  It reduces `lambda^{-1}_{1/8,2}(square_m;
a_n)` to a maximum over the `3^{d(m-n)}` cubes `z + square_n` by
`e.subadda.nosymm`, then applies `p.cg.ellipticity.bounds` at *each translate*
and `l.maximums.Gamma.s`.

## Main results

* `lowerEllipticityProfile_exponentTwo_le`: the frozen profile at `s = 1/8`,
  `q = 2` is below `Ccg` when `gamma <= 1/8`.
* `gamma_le_one_eighth_of_admissible`.
* `measureReal_coarseEllipticityFailure_le_of_coarseBounds`: the branch
  `n >= m` of the coarse-ellipticity half, with the displayed
  double-exponential bound.

## References

* ABK26, `l.bad.event.lemma`; `e.bad.event.Q.estimate`; the case `n >= m`.
* ABK26, `p.cg.ellipticity.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The frozen deterministic profile at `s = 1/8`, `q = 2` -/

/-- The frozen lower profile at the parameters of `e.good.local.events`:
`lowerEllipticityProfile Ccg gamma (1/8) 2 = Ccg (1/8) (1/4 - gamma)^{-1}`. -/
theorem lowerEllipticityProfile_exponentTwo (Ccg gamma : ℝ) :
    Algsuperdiff.Section3.lowerEllipticityProfile Ccg gamma (1 / 8) exponentTwo =
      Ccg * (1 / 8) * (2 * (1 / 8) - gamma)⁻¹ := by
  simp only [Algsuperdiff.Section3.lowerEllipticityProfile, exponentTwo,
    Algsuperdiff.Section3.CoarseEllipticityExponent.finite]
  norm_num

/-- At `gamma <= 1/8` the frozen deterministic profile is below the frozen
constant itself, which is what the manuscript's threshold
`2 C_{(e.cg.ellip.lower)}` needs. -/
theorem lowerEllipticityProfile_exponentTwo_le {Ccg gamma : ℝ} (hCcg : 0 < Ccg)
    (hgamma : gamma ≤ 1 / 8) :
    Algsuperdiff.Section3.lowerEllipticityProfile Ccg gamma (1 / 8) exponentTwo ≤
      Ccg := by
  have hgap : (0 : ℝ) < 2 * (1 / 8 : ℝ) - gamma := by linarith
  have heighth : (1 / 8 : ℝ) ≤ 2 * (1 / 8 : ℝ) - gamma := by linarith
  have hinv : (2 * (1 / 8 : ℝ) - gamma)⁻¹ ≤ (1 / 8 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) heighth
  rw [lowerEllipticityProfile_exponentTwo]
  have h8 : ((1 : ℝ) / 8)⁻¹ = 8 := by norm_num
  rw [h8] at hinv
  nlinarith [hinv, hCcg, inv_pos.2 hgap]

/-- The manuscript's own admissibility `e.bad.event.admissibility`, at the
dimension-only constant `badEventOscAdmissibleConst`, implies `gamma <= 1/8`
(indeed `gamma <= 1/32`). -/
theorem gamma_le_one_eighth_of_admissible (M : ABKModel d) {Ccg E : ℝ}
    (hadm : badEventOscAdmissibleConst d Ccg ≤
      E * Algsuperdiff.Section3.Disorder.cstar M)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) : M.gamma ≤ 1 / 8 := by
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hchalf : Algsuperdiff.Section3.Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have h3 : (3 : ℝ) ≤ E * Algsuperdiff.Section3.Disorder.cstar M :=
    le_trans (le_max_left _ _) hadm
  have hE2 : (2 : ℝ) ≤ E := by
    by_contra hlt
    push Not at hlt
    have hmul : E * Algsuperdiff.Section3.Disorder.cstar M <
        2 * Algsuperdiff.Section3.Disorder.cstar M :=
      mul_lt_mul_of_pos_right hlt hc
    linarith
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hsq : (4 : ℝ) ≤ E ^ 2 := by nlinarith
  have hquart : (16 : ℝ) ≤ E ^ 4 := by nlinarith
  have h32 : (32 : ℝ) ≤ E ^ (5 : ℕ) := by nlinarith
  have hle : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
    rw [← hEpow]
    exact hgammaE
  have hinv : (E ^ (5 : ℕ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h32
  have h132 : ((32 : ℝ))⁻¹ ≤ 1 / 8 := by norm_num
  linarith

/-! ## The coarse-ellipticity branch, case `n >= m` -/

/-- **The case `n >= m` of the coarse-ellipticity branch** (ABK26):

```
P[ lambda^{-1}_{1/8,2}(z+square_m; a_n) sigmabar_{n-1}
     > 2 . 3^{(1/4)(n-m)_+} C_{(e.cg.ellip.lower)} ]
  <= exp( - exp( c E^{-2} gamma^{-1} ) ) ,   c = Ccg^{-1}/4 .
``` -/
theorem measureReal_coarseEllipticityFailure_le_of_coarseBounds (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n : ℤ} {E : ℝ}
    (hgamma : M.gamma ≤ 1 / 8)
    (hmono : ∀ omega : CutoffSample d,
      cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
        (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
          Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
            (by norm_num) exponentTwo omega)
    (hcg : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
      (fun L : ℤ => fun omega =>
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n L (1 / 8)
            (by norm_num) exponentTwo omega *
          (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
      (n - 1)
      (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 8)
        exponentTwo)
      (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)))) :
    (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M Ccg Q n) ≤
      Real.exp (-Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨Y, hY⟩ := hcg
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M (n - 1)).1
  have hXnn : (0 : ℝ) ≤ Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹ := by
    have h1 : (0 : ℝ) ≤ Ccg⁻¹ := (inv_pos.2 hCcg0).le
    have h2 : (0 : ℝ) ≤ (E⁻¹) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.2 hg).le
    positivity
  have hApos : (0 : ℝ) < Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hAle : Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  -- the deterministic profile is below the frozen constant
  have hb : Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 8)
      exponentTwo ≤ Ccg :=
    lowerEllipticityProfile_exponentTwo_le hCcg0 hgamma
  -- the failure event forces the weak-Orlicz witness above the frozen constant
  have hsub : coarseEllipticityFailure M Ccg Q n ⊆
      HCPolySupport.IndependentSums.upperTailEvent Y Ccg := by
    intro omega homega
    have hfail : 2 * (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) * Ccg <
        cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := homega
    have hgap : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) := by
      refine Real.one_le_rpow (by norm_num) ?_
      have := scaleGapPos_nonneg Q.scale n
      linarith
    have hW : (0 : ℝ) < (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) :=
      lt_of_lt_of_le one_pos hgap
    have hstep : cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo
          omega * ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) ≤
        (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
          (Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
              (by norm_num) exponentTwo omega *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by
      have h := mul_le_mul_of_nonneg_right (hmono omega) hsig.le
      calc cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
          ≤ ((3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
              Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
                (by norm_num) exponentTwo omega) *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := h
        _ = (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
            (Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
                (by norm_num) exponentTwo omega *
              ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) := by ring
    have hdom := hY.dominates omega n (by omega)
    have h2Ccg : 2 * Ccg <
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
            (by norm_num) exponentTwo omega *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by
      have hchain := lt_of_lt_of_le hfail hstep
      nlinarith [hchain, hW, hCcg0]
    change Ccg < Y omega
    nlinarith [h2Ccg, hdom, hb, hCcg0]
  -- the weak-Orlicz tail at the level `Ccg`
  have ht1 : (1 : ℝ) ≤ Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) :=
    (one_le_div hApos).2 (le_trans hAle hCcg)
  have htail := hY.tail ht1
  have hlevel : Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) *
      (Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) = Ccg := by
    field_simp
  rw [hlevel] at htail
  refine le_trans (le_trans (measureReal_mono hsub) htail) ?_
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  -- the tail level is at least the manuscript's double exponential
  have hquotient : Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) =
      Ccg * Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) := by
    rw [Real.exp_neg]
    field_simp
  have hge : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ≤
      Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) := by
    rw [hquotient]
    nlinarith [Real.exp_pos (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹), hCcg]
  have hquarter : ((1 : ℝ) - 1 / 2) / 2 = 1 / 4 := by norm_num
  rw [hquarter]
  have hrpow : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ^ ((1 : ℝ) / 4) ≤
      (Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (Real.exp_pos _).le hge (by norm_num)
  have hexpid : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ^ ((1 : ℝ) / 4) =
      Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hexpid] at hrpow
  exact hrpow

end

end Algsuperdiff.Section3.Provider.BadEvents
