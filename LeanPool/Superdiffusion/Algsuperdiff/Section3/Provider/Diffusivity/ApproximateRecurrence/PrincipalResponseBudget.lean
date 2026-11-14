/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Bounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseBudgetDescent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseBudgetMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseBudgetScales

/-!
# PrincipalResponseBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the budget `delta <=^2 |log gamma|^2 gamma`

This module assembles the budget printed in ABK26, inside the proof of
`e.use.also.for.the.upper.bound`, for the annealed defect

```
  delta = 2 E[ bfJ(cu_n, bfAhom_L^{-1/2} e, bfAhom_L^{1/2} e; a_L) ]
```

proved as `cubeAnnealedProbeDefect` in
`...ApproximateRecurrence.PrincipalResponseSwitch`, at the cutoff index `L`
(the manuscript's `m - h`).

The manuscript's own chain is

```
  delta <= C 3^{t(m-h-n)} E[ mathcalE_{t,infinity,2}(cu_{m-h}; a_{m-h}, shom_{m-h})^2 ]
        <= C E^2 |log gamma|^2 gamma ,        t := |log gamma|^{-1} .
```

Its three legs are supplied by the three sibling modules and combined here:

* the deterministic leg (`e.mathcalE.monotone.ordered` squared, then
  `e.bound.one.cube.by.mathcalE`) is
  `...PrincipalResponseBudgetDescent.doubledResponseJ_annealedProbe_originCube_le`;
* the Orlicz-to-moment leg -- the only consumption of the induction state
  `d.mathcalS.def` -- is
  `...PrincipalResponseBudgetMoment.integral_sq_le_of_isTwoTermBigOWith_gammaSigma`;
* the domination of the heavy `Gamma_{1/2}` scale by the light `Gamma_2` scale is
  `...PrincipalResponseBudgetScales.exp_leg_le_window_gaussian_leg`.

What this module adds is the carrier bookkeeping: the defect is an integral
against the pushforward `Cutoff.coefficientCutoffLaw M L`, whereas the induction
state lives on the cutoff-sample law, so the integral is transported by
`integral_map` and the integrand identified, cube by cube, with the Chapter 2
doubled response of the literal cutoff coefficient family.

## The regime, stated honestly

`l.approximate.recurrence.formula` assumes `e.lower.bound.cgamma.cond.again.0`:
`E >= C cstar^{-1}` and `gamma <= E^{-5}`, with `C = C(d)` free until
`e.cgamma.constraints`.  Two hypotheses below encode it: `hgamE` is literally
`gamma <= E^{-5}`, and `h: 6 <= E` is a numerical floor on that free constant.
The floor is what `E >= C cstar^{-1}` delivers once `cstar <= 1`; that last
inequality is a separately tracked development gap and is **not** invoked, the
floor being carried as an explicit hypothesis instead.

The window `hsw : s in [8 gamma, 1]` is the window of `e.new.induction.for.shom`
itself.  The manuscript's `t := |log gamma|^{-1}` is the instance
`s = |log gamma|^{-1}`, and `cubeAnnealedProbeDefect_le_logSq_budget` is that
instance, with `s^{-2}` become the printed `|log gamma|^2`; the hypothesis that
`|log gamma|^{-1}` lies in the window is then explicit, as it must be.

## What is *not* here

The cube is the origin cube `cu_n`, not the translate `z + cu_n` printed in the
display of `e.use.also.for.the.upper.bound`; the transfer by real-translation
stationarity is the one step a consumer at a translated cube still owes,
exactly as recorded in `...PrincipalResponseSwitch`.  The manuscript's own
random vector `G_{-(h)_{z+cu_n}} P_z` is still absent, `P_z` having no
definition in this repository.  Consequently nothing below claims
`e.use.also.for.the.upper.bound` itself, nor any source node, nor any fraction
of one: what is established is the budget for the proved defect
`cubeAnnealedProbeDefect`, which is the input the proved switch
`...PrincipalResponseSwitch.annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic`
consumes.

## Main results

* `integral_blockJObservable_coefficientCutoffLaw_eq_integral_cutoffSampleLaw`,
  `blockJObservableCubeSetBlockVec_coefficientCutoff_eq_doubledResponseJ`: the
  carrier transfer.
* `cubeAnnealedProbeDefect_le_rpow_mul_orliczScales`: the defect against the two
  scales of `e.new.induction.for.shom`.
* `principalResponseBudgetConst`: the absolute constant, and its positivity.
* `cubeAnnealedProbeDefect_le_budget`: **the budget**, at a free window
  exponent `s`.
* `cubeAnnealedProbeDefect_le_budget_of_gap`: the same with the scale gap behind
  an explicit gate.
* `cubeAnnealedProbeDefect_le_logSq_budget`: the manuscript's own instance `s =
  |log gamma|^{-1}`, i.e. `delta <=^{2K} E^2 |log gamma|^2 gamma`.

## References

* ABK26, `d.mathcalS.def`, `e.new.induction.for.shom`.
* ABK26, the labels `l.approximate.recurrence.formula`,
  `e.lower.bound.cgamma.cond.again.0`, `e.cgamma.constraints`,
  `e.recurrence.params`, `d.mathcalS.def`, `e.new.induction.for.shom`,
  `e.mathcalE.monotone.ordered`, `e.bound.one.cube.by.mathcalE`,
  `e.use.also.for.the.upper.bound`.
* ABK26, (`e.use.also.for.the.upper.bound` and its proof; the chain is the
  `align*` display, its third line and its final bound).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Carrier transfer -/

/-- The annealed integral defining the defect, transported from the pushforward
coefficient law to the cutoff-sample carrier on which the induction state
lives.  The integrand is almost-everywhere measurable by CoarseGraining's
Chapter 4 local random-variable representative of the block response. -/
theorem integral_blockJObservable_coefficientCutoffLaw_eq_integral_cutoffSampleLaw
    (M : ABKModel d) (L n : ℤ) (P Qv : BlockVec d) :
    ∫ a, Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv a
        ∂(Cutoff.coefficientCutoffLaw M L) =
      ∫ omega, Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv
          (Cutoff.coefficientCutoff M.nu L omega)
        ∂((Cutoff.cutoffSampleLaw M).toMeasure) := by
  have hcar := Cutoff.coefficientCutoffLaw_lawCarrier M L
  have haem :
      AEMeasurable (Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv)
        (Cutoff.coefficientCutoffLaw M L) :=
    Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hcar (originCube d n) P Qv
  rw [Cutoff.coefficientCutoffLaw_eq_map] at haem ⊢
  exact integral_map (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable
    haem.aestronglyMeasurable

/-- The Chapter 4 carrier block response at a genuine cutoff realization is the
Chapter 2 doubled response of the literal cutoff coefficient family on the same
cube.  The two triadic families differ only in their ellipticity witnesses, so
they are Chapter 2 a.e. equal and the doubled response is unchanged. -/
theorem blockJObservableCubeSetBlockVec_coefficientCutoff_eq_doubledResponseJ
    (M : ABKModel d) (L n : ℤ) (P Qv : BlockVec d)
    (omega : Cutoff.CutoffSample d) :
    Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv
        (Cutoff.coefficientCutoff M.nu L omega) =
      Ch02.doubledResponseJ (Ch02.cubeDomain (originCube d n))
        ((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d n))
        P Qv := by
  have hell := Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  have h1 :=
    Ch04.doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
      hell (originCube d n) P Qv
  have h2 := Ch02.doubledResponseJ_eq_ofAEEq
    (Cutoff.coefficientCutoff_canonicalFamily_aeeq M L omega (originCube d n)) P Qv
  rw [← h1, h2]

/-! ## The defect against the two Orlicz scales of `e.new.induction.for.shom` -/

theorem cubeAnnealedProbeDefect_le_rpow_mul_orliczScales (M : ABKModel d)
    {m0 L n : ℤ} {Ec : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec)
    (hL : L ≤ m0) (hn : n ≤ L) {s : ℝ} (hsw : s ∈ Set.Icc (8 * M.gamma) 1)
    {Ev : BlockVec d} (hE : blockVecDot Ev Ev = 1) :
    cubeAnnealedProbeDefect M L n Ev ≤
      2 * ((3 : ℝ) ^ (2 * s * ((Int.toNat (L - n) : ℕ) : ℝ)) *
        (orliczSecondMomentConst 2 *
            ((Ec : ℝ) * s⁻¹ * Real.sqrt M.gamma) ^ 2 +
          orliczSecondMomentConst (1 / 2) *
            ((s⁻¹) ^ 2 *
              Real.exp (-(((Ec : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2)) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hs : 0 < s := (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma).trans_le hsw.1
  set sp : {s : ℝ // 0 < s} := ⟨s, hs⟩ with hsp
  set fac : ℝ := (3 : ℝ) ^ (2 * s * ((Int.toNat (L - n) : ℕ) : ℝ)) with hfac
  have hfac0 : 0 ≤ fac := Real.rpow_nonneg (by norm_num) _
  have htail := hS.2 L hL s hsw
  have hptwise : ∀ omega : Cutoff.CutoffSample d,
      Ch04.blockJObservableCubeSetBlockVec (originCube d n)
          (annealedProbePotential (Annealed.sigmaBar M L) Ev)
          (annealedProbeFlux (Annealed.sigmaBar M L) Ev)
          (Cutoff.coefficientCutoff M.nu L omega) ≤
        fac * Ch02.HomogenizationErrorOnCube (originCube d L) s .infinity (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) ^ 2 := by
    intro omega
    rw [blockJObservableCubeSetBlockVec_coefficientCutoff_eq_doubledResponseJ]
    exact doubledResponseJ_annealedProbe_originCube_le
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Annealed.sigmaBar M L) hE hs hn
  have hae := Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M L sp
  have hmajor : ∀ᵐ omega ∂((Cutoff.cutoffSampleLaw M).toMeasure),
      Ch04.blockJObservableCubeSetBlockVec (originCube d n)
          (annealedProbePotential (Annealed.sigmaBar M L) Ev)
          (annealedProbeFlux (Annealed.sigmaBar M L) Ev)
          (Cutoff.coefficientCutoff M.nu L omega) ≤
        fac * Observable.cutoffHomogenizationError M L sp omega ^ 2 := by
    filter_upwards [hae] with omega hom
    rw [hom]
    exact hptwise omega
  have hnonneg2 := Observable.cutoffHomogenizationError_nonneg M L sp
  have hint : Integrable
      (fun omega => Observable.cutoffHomogenizationError M L sp omega ^ 2)
      ((Cutoff.cutoffSampleLaw M).toMeasure) :=
    integrable_sq_of_isTwoTermBigOWith_gammaSigma (by norm_num) (by norm_num)
      hnonneg2 htail
  have hmom := integral_sq_le_of_isTwoTermBigOWith_gammaSigma
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 2) hnonneg2 htail
  have hchain : ∫ omega, Ch04.blockJObservableCubeSetBlockVec (originCube d n)
        (annealedProbePotential (Annealed.sigmaBar M L) Ev)
        (annealedProbeFlux (Annealed.sigmaBar M L) Ev)
        (Cutoff.coefficientCutoff M.nu L omega) ∂((Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ∫ omega, fac * Observable.cutoffHomogenizationError M L sp omega ^ 2
        ∂((Cutoff.cutoffSampleLaw M).toMeasure) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega =>
        Ch04.blockJObservableCubeSetBlockVec_nonneg _ _ _ _)
      (hint.const_mul fac) hmajor
  rw [integral_const_mul] at hchain
  rw [cubeAnnealedProbeDefect_eq_two_mul_integral_blockJ,
    integral_blockJObservable_coefficientCutoffLaw_eq_integral_cutoffSampleLaw]
  have hfin : fac * ∫ omega, Observable.cutoffHomogenizationError M L sp omega ^ 2
        ∂((Cutoff.cutoffSampleLaw M).toMeasure) ≤
      fac * (orliczSecondMomentConst 2 * ((Ec : ℝ) * s⁻¹ * Real.sqrt M.gamma) ^ 2 +
        orliczSecondMomentConst (1 / 2) *
          ((s⁻¹) ^ 2 * Real.exp (-(((Ec : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2) :=
    mul_le_mul_of_nonneg_left hmom hfac0
  have hcomb := le_trans hchain hfin
  linarith

/-! ## The budget -/

/-- The absolute constant of the budget: twice the sum of the two class
second-moment constants of `orliczSecondMomentConst`.  It depends on nothing --
not on the dimension, the model, the parameters, or the scales. -/
def principalResponseBudgetConst : ℝ :=
  2 * (orliczSecondMomentConst 2 + orliczSecondMomentConst (1 / 2))

theorem principalResponseBudgetConst_pos : 0 < principalResponseBudgetConst := by
  have h1 := orliczSecondMomentConst_pos (by norm_num : (0 : ℝ) < 2)
  have h2 := orliczSecondMomentConst_pos (by norm_num : (0 : ℝ) < 1 / 2)
  unfold principalResponseBudgetConst
  linarith

/-- **The budget of ABK26, at a free window exponent.**

At the cutoff index `L`, every cube scale `n <= L` and every window exponent
`s in [8 gamma, 1]`, the annealed defect of `e.use.also.for.the.upper.bound`
obeys

```
  delta  <=  C 3^{2 s (L-n)} E^2 s^{-2} gamma ,
```

with `C = principalResponseBudgetConst` absolute.  The manuscript's own display
is the instance `s = |log gamma|^{-1}`, where `s^{-2}` is `|log gamma|^2`; see
`cubeAnnealedProbeDefect_le_logSq_budget`.

This does not claim `e.use.also.for.the.upper.bound`, whose printed display is
at the translated cube and at the random vector `G_{-(h)_{z+cu_n}} P_z`; see the
module header. -/
theorem cubeAnnealedProbeDefect_le_budget (M : ABKModel d)
    {m0 L n : ℤ} {Ec : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec)
    (hL : L ≤ m0) (hn : n ≤ L) (hE6 : 6 ≤ (Ec : ℝ))
    (hgamE : M.gamma ≤ ((Ec : ℝ) ^ 5)⁻¹)
    {s : ℝ} (hsw : s ∈ Set.Icc (8 * M.gamma) 1)
    {Ev : BlockVec d} (hE : blockVecDot Ev Ev = 1) :
    cubeAnnealedProbeDefect M L n Ev ≤
      principalResponseBudgetConst *
        (3 : ℝ) ^ (2 * s * ((Int.toNat (L - n) : ℕ) : ℝ)) *
        ((Ec : ℝ) ^ 2 * (s⁻¹) ^ 2 * M.gamma) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hstep := cubeAnnealedProbeDefect_le_rpow_mul_orliczScales M hS hL hn hsw hE
  set A1 : ℝ := (Ec : ℝ) * s⁻¹ * Real.sqrt M.gamma with hA1
  set A2 : ℝ := (s⁻¹) ^ 2 * Real.exp (-(((Ec : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) with hA2
  set fac : ℝ := (3 : ℝ) ^ (2 * s * ((Int.toNat (L - n) : ℕ) : ℝ)) with hfac
  have hfac0 : (0 : ℝ) ≤ fac := Real.rpow_nonneg (by norm_num) _
  have hc2 : (0 : ℝ) ≤ orliczSecondMomentConst (1 / 2) :=
    (orliczSecondMomentConst_pos (by norm_num)).le
  have hA2nn : (0 : ℝ) ≤ A2 := by rw [hA2]; positivity
  have hle : A2 ≤ A1 := by
    rw [hA1, hA2]
    exact exp_leg_le_window_gaussian_leg hE6 hgamma hgamE hsw.1
  have hsq : A2 ^ 2 ≤ A1 ^ 2 := pow_le_pow_left₀ hA2nn hle 2
  have hA1sq : A1 ^ 2 = (Ec : ℝ) ^ 2 * (s⁻¹) ^ 2 * M.gamma := by
    rw [hA1, mul_pow, mul_pow, Real.sq_sqrt hgamma.le]
  have h1 : orliczSecondMomentConst 2 * A1 ^ 2 +
        orliczSecondMomentConst (1 / 2) * A2 ^ 2 ≤
      (orliczSecondMomentConst 2 + orliczSecondMomentConst (1 / 2)) * A1 ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hc2
    linarith
  have h2 : 2 * (fac * (orliczSecondMomentConst 2 * A1 ^ 2 +
        orliczSecondMomentConst (1 / 2) * A2 ^ 2)) ≤
      2 * (fac * ((orliczSecondMomentConst 2 + orliczSecondMomentConst (1 / 2)) *
        A1 ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hfac0) (by norm_num)
  have h3 : 2 * (fac * ((orliczSecondMomentConst 2 +
        orliczSecondMomentConst (1 / 2)) * A1 ^ 2)) =
      principalResponseBudgetConst * fac *
        ((Ec : ℝ) ^ 2 * (s⁻¹) ^ 2 * M.gamma) := by
    rw [← hA1sq, principalResponseBudgetConst]
    ring
  linarith [hstep, h2, h3.le, h3.ge]

/-- A consumer that fixes any buffer -- the printed `16 ceil|log_3 gamma|` of
`e.recurrence.params` or a corrected larger one -- discharges `hgap` and reads
off `delta <=^{2K} E^2 s^{-2} gamma`. -/
theorem cubeAnnealedProbeDefect_le_budget_of_gap (M : ABKModel d)
    {m0 L n : ℤ} {Ec : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec)
    (hL : L ≤ m0) (hn : n ≤ L) (hE6 : 6 ≤ (Ec : ℝ))
    (hgamE : M.gamma ≤ ((Ec : ℝ) ^ 5)⁻¹)
    {s : ℝ} (hsw : s ∈ Set.Icc (8 * M.gamma) 1)
    {Ev : BlockVec d} (hE : blockVecDot Ev Ev = 1)
    {K : ℝ} (hgap : s * ((Int.toNat (L - n) : ℕ) : ℝ) ≤ K) :
    cubeAnnealedProbeDefect M L n Ev ≤
      principalResponseBudgetConst * (3 : ℝ) ^ (2 * K) *
        ((Ec : ℝ) ^ 2 * (s⁻¹) ^ 2 * M.gamma) := by
  have hb := cubeAnnealedProbeDefect_le_budget M hS hL hn hE6 hgamE hsw hE
  have hmono : (3 : ℝ) ^ (2 * s * ((Int.toNat (L - n) : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (2 * K) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hrhs : (0 : ℝ) ≤ (Ec : ℝ) ^ 2 * (s⁻¹) ^ 2 * M.gamma := by
    have : 0 < M.gamma := M.shellPrefix.gamma_pos
    positivity
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmono principalResponseBudgetConst_pos.le) hrhs

/-- **The manuscript's own instance, `t = |log gamma|^{-1}`** (ABK26 and the
budget):

```
  delta  <=  C 3^{2K} E^2 |log gamma|^2 gamma .
```

Both are conditions on the parameters alone. -/
theorem cubeAnnealedProbeDefect_le_logSq_budget (M : ABKModel d)
    {m0 L n : ℤ} {Ec : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec)
    (hL : L ≤ m0) (hn : n ≤ L) (hE6 : 6 ≤ (Ec : ℝ))
    (hgamE : M.gamma ≤ ((Ec : ℝ) ^ 5)⁻¹)
    (hsw : |Real.log M.gamma|⁻¹ ∈ Set.Icc (8 * M.gamma) 1)
    {Ev : BlockVec d} (hE : blockVecDot Ev Ev = 1)
    {K : ℝ} (hgap : |Real.log M.gamma|⁻¹ * ((Int.toNat (L - n) : ℕ) : ℝ) ≤ K) :
    cubeAnnealedProbeDefect M L n Ev ≤
      principalResponseBudgetConst * (3 : ℝ) ^ (2 * K) *
        ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by
  have h := cubeAnnealedProbeDefect_le_budget_of_gap M hS hL hn hE6 hgamE hsw hE hgap
  rwa [inv_inv, sq_abs] at h

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
