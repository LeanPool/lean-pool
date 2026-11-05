/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# ObservableTranslate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-observable translation identities of the Section 4.2 lattice maxima

`Provider/GoodEvents/Translate.lean` supplies the *law-level* half of the
translation calculus and states explicitly that the remaining half — the
per-observable pointwise identities `observable(z+□)(ω) =
observable(□)(translate z ω)` — is supplied by the individual Section 4 modules.
This module discharges that half for the three observables the §4.2 lattice
maxima read, and packages the compositions with the proved measure
preservation.

## What the frozen displays actually contain

Throughout, the *sample* is translated, never the cube: the
manuscript's `𝓔(z+□_m)`, `λ_{γ,2}^{-1}(z+□_{k−2})` and
`𝒢(m, y; s, ε)` are rendered as compositions with
`Cutoff.translateCutoffSample`.  Consequently

* the public flux observables `Support.fluxCorrectedErrorObservableSup` /
  `…SqSup` are hard-wired to the origin cube (`originCube d m` throughout
  `fluxCorrectedErrorRepresentative`), and **no public Section 4 observable
  exposes a cube parameter**, so there is no second, cube-indexed observable
  that a translation identity could compare them to.  (The atom layer beneath
  them is cube-indexed — `Support.fluxCorrectedCoeffFamily M L m Q omega` takes
  `Q : TriadicCube d` — so a literal `𝓔(z+□_m)` could in principle be written
  at the triadic cube of scale `m` and index `v`; no frozen §4 statement does.)
  For these two observables the frozen composition *is* the rendering, so the
  identities below are the definitional ones a proof actually needs: the
  translation passes inside the `L`-supremum, the translations compose
  additively, and `y = 0` is the identity;

**Not required by any frozen statement.**  The lift of that
coefficient covariance *through* the Ch02 error functional — i.e. a theorem
"the `(∞,2)` error on `y+□_m` at `a(ω)` equals the error on `□_m` at
`a(translate y ω)`" — is **not proved** and is **not** proved here.  No frozen
§4 statement needs it: every one of them composes with `translateCutoffSample`.
Any future statement that wants to read the composition as a literal cube
translation must prove that lemma first.

## Consumers

* `mul_sum_indicator_goodEventAt_comp_translate` and
  `measure_lt_mul_sum_indicator_goodEventAt` are what the centre-union step
  reads: the two clauses of `Frozen.Section4.minimal_scale_separation` at the
  centre `Support.triadicLatticePoint (n-1) z` have the same law as at the
  origin.
* `measure_lt_comp_translateCutoffSample` is the law-transport estimate used by
  the tail step.

## References

* ABK26, `d.good.event.for.lambda`, (the translate convention).
* ABK26, `p.minimal.scale.separation.sec4`.
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The flux-corrected error observables at a translated sample

The two public observables of `p.mathcalE.annular.decomp` are the ones the
frozen `minimal_scale_separation` composes with
`Cutoff.translateCutoffSample`.  All four identities per observable are
definitional (`rfl`, or `congrArg` over the proved group action). -/

/-- **The indicator-composition identity.**  Verifies and uses the
preimage shape of the frozen definition (`Api.goodEventAt_eq_preimage`). -/
theorem indicator_goodEventAt_comp_translate {beta : Type*} [Zero beta]
    (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (f : Cutoff.CutoffSample d → beta)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)
        (fun omega' => f (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep) f
        (Cutoff.translateCutoffSample y omega) := by
  by_cases h : Cutoff.translateCutoffSample y omega ∈
      Support.goodEventBase M Ccg m s ep
  · have h' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep := h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
  · have h' : omega ∉ Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep := h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- The identity at the observable of `minimal_scale_separation`'s first
conclusion: the `k`-th summand at centre `y` is the origin summand at the
`y`-translated sample. -/
theorem indicator_goodEventAt_fluxCorrectedErrorObservableSup (M : ABKModel d)
    (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)
        (fun omega' =>
          Support.fluxCorrectedErrorObservableSup M m s
            (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)
        (Support.fluxCorrectedErrorObservableSup M m s)
        (Cutoff.translateCutoffSample y omega) :=
  indicator_goodEventAt_comp_translate M Ccg m y s ep
    (Support.fluxCorrectedErrorObservableSup M m s) omega

/-- The indicator-composition identity on the *bad* event. -/
theorem indicator_compl_goodEventAt_comp_translate {beta : Type*} [Zero beta]
    (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (f : Cutoff.CutoffSample d → beta)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ
        (fun omega' => f (Cutoff.translateCutoffSample y omega')) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)ᶜ f
        (Cutoff.translateCutoffSample y omega) := by
  by_cases h : Cutoff.translateCutoffSample y omega ∈
      (Support.goodEventBase M Ccg m s ep)ᶜ
  · have h' : omega ∈ (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ := h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
  · have h' : omega ∉ (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ := h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- The identity at the constant `1` of `minimal_scale_separation`'s second
conclusion: the bad-event count at centre `y` is the origin bad-event count at
the `y`-translated sample. -/
theorem indicator_compl_goodEventAt_one (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep)ᶜ
        (fun _ => (1 : ℝ≥0∞)) omega =
      Set.indicator (Support.goodEventBase M Ccg m s ep)ᶜ
        (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  indicator_compl_goodEventAt_comp_translate M Ccg m y s ep
    (fun _ => (1 : ℝ≥0∞)) omega

/-- **The level sets of an observable at a translated sample carry the origin
mass.**  The general form; the two threshold specializations follow. -/
theorem measure_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) {B : Set ℝ≥0∞}
    (hB : MeasurableSet B) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | f (Cutoff.translateCutoffSample y omega) ∈ B} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | f omega ∈ B} :=
  measure_preimage_translateCutoffSample M y (hf hB)

/-- The `t < ·` level set transfers: the shape a union bound over centres
consumes: the `Z₁` tail and the `Z₂` centre union. -/
theorem measure_lt_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f : Cutoff.CutoffSample d → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < f (Cutoff.translateCutoffSample y omega)} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < f omega} :=
  measure_comp_translateCutoffSample M y hf measurableSet_Ioi

/-- **The transport wrapper.**  If `f` is pointwise the origin observable `g`
read at the translated sample, its `t < ·` set carries the origin mass.  The
hypotheses are discharged by §2's indicator identities and by the
measurability lemmas below. -/
theorem measure_lt_of_eq_comp_translateCutoffSample (M : ABKModel d) (y : Vec d)
    {f g : Cutoff.CutoffSample d → ℝ≥0∞} (hg : Measurable g)
    (hfg : ∀ omega, f omega = g (Cutoff.translateCutoffSample y omega))
    (t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < f omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | t < g omega} := by
  have hset : {omega | t < f omega} =
      {omega | t < g (Cutoff.translateCutoffSample y omega)} :=
    Set.ext fun omega => by rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hfg omega]
  rw [hset]
  exact measure_lt_comp_translateCutoffSample M y hg t

/-! ### The two clauses of `minimal_scale_separation` at a centre -/

/-- The window sum of `minimal_scale_separation`'s first conclusion at
centre `y` is the origin window sum at the `y`-translated sample. -/
theorem sum_indicator_goodEventAt_comp_translate (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
          (fun omega' =>
            Support.fluxCorrectedErrorObservableSup M k s
              (Cutoff.translateCutoffSample y omega')) omega) =
      ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s)
          (Cutoff.translateCutoffSample y omega) :=
  Finset.sum_congr rfl fun k _ =>
    indicator_goodEventAt_fluxCorrectedErrorObservableSup M Ccg k y s ep omega

/-- The Cesàro-normalized form, with the frozen prefactor left free. -/
theorem mul_sum_indicator_goodEventAt_comp_translate (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞)
    (omega : Cutoff.CutoffSample d) :
    c * (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
          (fun omega' =>
            Support.fluxCorrectedErrorObservableSup M k s
              (Cutoff.translateCutoffSample y omega')) omega) =
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s)
          (Cutoff.translateCutoffSample y omega) :=
  congrArg (fun x => c * x)
    (sum_indicator_goodEventAt_comp_translate M Ccg y s ep n m omega)

/-- The bad-event count of the second conclusion at centre `y` is the origin
count at the `y`-translated sample. -/
theorem sum_indicator_compl_goodEventAt_comp_translate (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega) =
      ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  Finset.sum_congr rfl fun k _ =>
    indicator_compl_goodEventAt_one M Ccg k y s ep omega

/-- The Cesàro-normalized bad-event count. -/
theorem mul_sum_indicator_compl_goodEventAt_comp_translate (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞)
    (omega : Cutoff.CutoffSample d) :
    c * (∑ k ∈ Finset.Icc n m,
        Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega) =
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) (Cutoff.translateCutoffSample y omega) :=
  congrArg (fun x => c * x)
    (sum_indicator_compl_goodEventAt_comp_translate M Ccg y s ep n m omega)

/-- The origin window average is measurable. -/
theorem measurable_mul_sum_indicator_goodEventBase (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)
          (Support.fluxCorrectedErrorObservableSup M k s) omega := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact (Support.measurable_fluxCorrectedErrorObservableSup M k s).indicator
    (Support.measurableSet_goodEventBase M Ccg k s ep)

/-- The origin bad-event count is measurable. -/
theorem measurable_mul_sum_indicator_compl_goodEventBase (M : ABKModel d)
    (Ccg : ℝ) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c : ℝ≥0∞) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
          (fun _ => (1 : ℝ≥0∞)) omega := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact measurable_const.indicator
    (Support.measurableSet_goodEventBase M Ccg k s ep).compl

/-- **The `Z₂` centre union, first clause.**  The bad set of the window average at
centre `y` has exactly the mass of the bad set at the origin — the per-centre
input of the union bound over `z ∈ 3^{n-1}ℤ^d ∩ □_m`. -/
theorem measure_lt_mul_sum_indicator_goodEventAt (M : ABKModel d) (Ccg : ℝ)
    (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ) (c t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)
            (fun omega' =>
              Support.fluxCorrectedErrorObservableSup M k s
                (Cutoff.translateCutoffSample y omega')) omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Support.goodEventBase M Ccg k s ep)
            (Support.fluxCorrectedErrorObservableSup M k s) omega} :=
  measure_lt_of_eq_comp_translateCutoffSample M y
    (measurable_mul_sum_indicator_goodEventBase M Ccg s ep n m c)
    (fun omega =>
      mul_sum_indicator_goodEventAt_comp_translate M Ccg y s ep n m c omega) t

/-- **The `Z₂` centre union, second clause.**  The same transfer for the
bad-event count. -/
theorem measure_lt_mul_sum_indicator_compl_goodEventAt (M : ABKModel d)
    (Ccg : ℝ) (y : Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) (n m : ℤ)
    (c t : ℝ≥0∞) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator
            (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg k y s ep)ᶜ
            (fun _ => (1 : ℝ≥0∞)) omega} =
      (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | t < c * ∑ k ∈ Finset.Icc n m,
          Set.indicator (Support.goodEventBase M Ccg k s ep)ᶜ
            (fun _ => (1 : ℝ≥0∞)) omega} :=
  measure_lt_of_eq_comp_translateCutoffSample M y
    (measurable_mul_sum_indicator_compl_goodEventBase M Ccg s ep n m c)
    (fun omega =>
      mul_sum_indicator_compl_goodEventAt_comp_translate M Ccg y s ep n m c
        omega) t

end

end Algsuperdiff.Section4.Provider.GoodEvents
