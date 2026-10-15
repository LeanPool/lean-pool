/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ErrorTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability

/-!
# MajorantMeasurability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Measurability of the `L`-free majorant: `hGmeas` at its honest strength

## What this module does

`MajorantTransport.lean`'s transport carries a side condition `hGmeas`: the
per-scale descendant average of `G^{p/2}` must be measurable in the sample.  At
the `L`-free majorant `lFreeStep3Majorant` that average has five ingredients,
and they do NOT all have the same strength:

* the two shell-built slots `lFreeGradSlot`, `lFreeValueSlot` are genuinely
  measurable
  (finite layer sums, `Cutoff.localCubeControl` of a stream increment, plus the
  caller's tail gauge -- and the canonical gauge `tailSeriesGauge` is itself
  measurable, a countable sum of measurable nonnegative layer terms);
* the multiscale ellipticity gauge enters only through its inverse `λ_{2γ,2}^{-1}`,
  which is genuinely measurable: the transfer
  `BadEvents.unitCubeLambda_unitRescaledCutoffCoeff` identifies it with Section
  3's literal `cubeLowerEllipticityInvLiteral`, whose measurability is the
  proved literal-measurability engine;
* the `(2,2)` homogenization error `𝓔_{s,2,2}` is only almost everywhere
  measurable.  As in Section 3, the literal `(p,q)` error functional is not
  measurable by composition; the route used here is
  `Annular.unitCubeHomogenizationError22_unitRescaledCutoffCoeff_ae_eq_annularErrorObservable`,
  the a.e. identification with the measurable `𝒢₂` observable
  `Support.annularErrorObservable` read at the translated sample.

Consequently `hGmeas` is dischargeable at `AEMeasurable`, not at `Measurable`.
That is not a loss: the transport's own proof uses `hGmeas` in exactly one
place, `MeasureTheory.lintegral_tsum`, which asks for `AEMeasurable`.  This
module proves the `AEMeasurable` form of the side condition at the `L`-free
majorant
(`aemeasurable_finsetAverageReal_rpow_lFreeStep3Majorant`); the matching
weakening of the transport, and the composition with `TailSummability`'s
discharged `hTae`, are `AeMeasurableTransport.lean`.

The negated leg costs nothing: `Cutoff.negateCutoffSample` is measurable and
preserves the cutoff-sample law
(`Cutoff.map_negateCutoffSample_cutoffSampleLaw`), so it is quasi measure
preserving and a.e. measurability composes through it.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 2), (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The shell-built slots are genuinely measurable -/

/-- Each `ℤ`-indexed layer term is measurable in the sample. -/
theorem measurable_tailLayerTerm (m k : ℤ) (v : Fin d → ℤ) (i : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => tailLayerTerm m k v omega i := by
  by_cases h : m < i
  · have hfun : (fun omega : Cutoff.CutoffSample d => tailLayerTerm m k v omega i) =
        fun omega : Cutoff.CutoffSample d =>
          Support.shellW1InfGradNorm k
            (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 i)) := by
      funext omega
      rw [tailLayerTerm, ite_eq_left h]
    rw [hfun]
    exact ((Support.measurable_shellW1InfGradNorm k).comp
      (ShellField.measurable_translate (Support.triadicLatticePoint k v))).comp
      ((measurable_pi_apply i).comp measurable_subtype_coe)
  · have hfun : (fun omega : Cutoff.CutoffSample d => tailLayerTerm m k v omega i) =
        fun _ : Cutoff.CutoffSample d => (0 : ℝ) := by
      funext omega
      rw [tailLayerTerm, ite_eq_right h]
    rw [hfun]
    exact measurable_const

/-- **The canonical tail gauge is measurable.** -/
theorem measurable_tailSeriesGauge (m k : ℤ) (v : Fin d → ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => tailSeriesGauge m k v omega :=
  Measurable.tsum (L := SummationFilter.unconditional ℤ)
    (fun i => measurable_tailLayerTerm m k v i)

/-- The `L`-free head block is measurable. -/
theorem measurable_headLayerSum (m k : ℤ) (v : Fin d → ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => headLayerSum m k v omega := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((Support.measurable_shellW1InfGradNorm k).comp
    (ShellField.measurable_translate (Support.triadicLatticePoint k v))).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- The `L`-free gradient slot is measurable whenever the tail gauge is. -/
theorem measurable_lFreeGradSlot (m : ℤ) (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (hT : ∀ (k : ℤ) (v : Fin d → ℤ), Measurable (T k v)) (R : TriadicCube d) :
    Measurable fun omega : Cutoff.CutoffSample d => lFreeGradSlot m T R omega :=
  ((measurable_headLayerSum m R.scale R.index).add (hT R.scale R.index)).const_mul _

/-- The `L`-free value slot is measurable whenever the tail gauge is. -/
theorem measurable_lFreeValueSlot (m : ℤ) (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (hT : ∀ (k : ℤ) (v : Fin d → ℤ), Measurable (T k v)) (R : TriadicCube d) :
    Measurable fun omega : Cutoff.CutoffSample d => lFreeValueSlot m T R omega := by
  refine Measurable.add ?_ (((hT m (0 : Fin d → ℤ)).const_mul _).const_mul _)
  exact (Cutoff.measurable_localCubeControl R.scale).comp
    ((ShellField.measurable_translate (Support.triadicLatticePoint R.scale R.index)).comp
      (measurable_shellIncrement_cutoffSample (R.scale - 2) m))

/-! ## 2. The two unit-cube gauges -/

/-- The admissible finite exponent `q = 2` of Section 3's ellipticity carrier,
spelled so that its underlying multiscale exponent is literally `.finite 2`. -/
def exponentTwoAdm : Algsuperdiff.Section3.CoarseEllipticityExponent :=
  Algsuperdiff.Section3.CoarseEllipticityExponent.finite ⟨2, by norm_num⟩

/-- **The multiscale ellipticity gauge enters only through its inverse, and the
inverse is genuinely measurable.**

`BadEvents.unitCubeLambda_unitRescaledCutoffCoeff` identifies
`λ_{t,2}(unitRescaledCutoffCoeff M R (R.scale−2) ω)` with Section 3's
`Ch02.lambdaSq` at the cube `R`, i.e. with the inverse of the literal
`cubeLowerEllipticityInvLiteral`; the latter is measurable by the proved
literal-measurability engine. -/
theorem measurable_unitCubeLambda_inv_unitRescaledCutoffCoeff [NeZero d] (M : ABKModel d)
    (R : TriadicCube d) {t : ℝ} (ht : 0 < t) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      (Algsuperdiff.Frozen.Section24.unitCubeLambda t (.finite 2)
        (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ := by
  have hkey : ∀ omega : Cutoff.CutoffSample d,
      (Algsuperdiff.Frozen.Section24.unitCubeLambda t (.finite 2)
          (unitRescaledCutoffCoeff M R (R.scale - 2) omega))⁻¹ =
        cubeLowerEllipticityInvLiteral M R (R.scale - 2) t exponentTwoAdm omega := by
    intro omega
    have h1 := unitCubeLambda_unitRescaledCutoffCoeff M R (R.scale - 2) t (.finite 2) omega
    have h2 : (cubeLowerEllipticityInvLiteral M R (R.scale - 2) t exponentTwoAdm omega)⁻¹ =
        Ch02.lambdaSq R t (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M (R.scale - 2) omega) :=
      cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq M R (R.scale - 2) t exponentTwoAdm omega
    rw [h1, ← h2, inv_inv]
  rw [funext hkey]
  exact measurable_cubeLowerEllipticityInvLiteral M R (R.scale - 2) ht exponentTwoAdm

/-- **The `(2,2)` homogenization error gauge is almost everywhere measurable.**

This is the exact strength available -- as in Section 3, no
everywhere-measurable realization of the literal `(p,q)` error exists by
composition. -/
theorem aemeasurable_unitCubeHomogenizationError22_unitRescaledCutoffCoeff
    (M : ABKModel d) (R : TriadicCube d) (s : {s : ℝ // 0 < s}) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError (s : ℝ)
          (.finite 2) (.finite 2) (unitRescaledCutoffCoeff M R (R.scale - 2) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M (R.scale - 2))))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hobs : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      Support.annularErrorObservable M R.scale s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint R.scale R.index) omega))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((Support.measurable_annularErrorObservable M R.scale s).comp
      (Cutoff.measurable_translateCutoffSample _)).aemeasurable
  exact hobs.congr
    (unitCubeHomogenizationError22_unitRescaledCutoffCoeff_ae_eq_annularErrorObservable
      M R.scale R.index s).symm

/-! ## 3. The display, and the majorant -/

/-- The gapped-gauge exponents of Step 3's display are nonnegative in the
anchor's own ranges.  (Re-derivation of the `private` helper of
`MajorantSlots.lean`.) -/
private theorem step3_exponents_nonneg' {gam s : ℝ} (hgam0 : 0 < gam) (hgam : gam ≤ 1 / 8)
    (hs : 0 < s) : 0 ≤ 2 * s / (1 - 4 * gam) ∧ 0 ≤ 4 * gam / (1 - 4 * gam) := by
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam]
  exact ⟨div_nonneg (by linarith only [hs]) hden.le,
    div_nonneg (by linarith only [hgam0]) hden.le⟩

/-- The abstract-real measurability core of Step 3's display: the two `Real.rpow`
atoms are moved only by continuity in the base (nonnegative exponents), and the
rest is arithmetic. -/
private theorem aemeasurable_displayAt_core {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {C sm sj e1 e2 : ℝ} (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    {lam err grad val : Omega → ℝ} (hlam : AEMeasurable lam mu)
    (herr : AEMeasurable err mu) (hgrad : AEMeasurable grad mu)
    (hval : AEMeasurable val mu) :
    AEMeasurable (fun w =>
      C * (sm⁻¹ * sj) * Real.rpow (1 + grad w * lam w) e1 * err w ^ 2 +
        C * (sm⁻¹ * sj ^ 2) * lam w * Real.rpow (1 + grad w * lam w) e2 *
          (sj⁻¹ ^ 2 * val w ^ 2 + (sm * sj⁻¹ - 1) ^ 2) +
        C * ((sm⁻¹ + lam w) * grad w) ^ 2) mu := by
  have hbase : AEMeasurable (fun w => 1 + grad w * lam w) mu := (hgrad.mul hlam).const_add 1
  have hr1 : AEMeasurable (fun w => Real.rpow (1 + grad w * lam w) e1) mu :=
    (Real.continuous_rpow_const he1).measurable.comp_aemeasurable hbase
  have hr2 : AEMeasurable (fun w => Real.rpow (1 + grad w * lam w) e2) mu :=
    (Real.continuous_rpow_const he2).measurable.comp_aemeasurable hbase
  have h1 : AEMeasurable (fun w =>
      C * (sm⁻¹ * sj) * Real.rpow (1 + grad w * lam w) e1 * err w ^ 2) mu :=
    (hr1.const_mul _).mul (herr.pow_const 2)
  have h2 : AEMeasurable (fun w =>
      C * (sm⁻¹ * sj ^ 2) * lam w * Real.rpow (1 + grad w * lam w) e2 *
        (sj⁻¹ ^ 2 * val w ^ 2 + (sm * sj⁻¹ - 1) ^ 2)) mu :=
    ((hlam.const_mul _).mul hr2).mul (((hval.pow_const 2).const_mul _).add_const _)
  have h3 : AEMeasurable (fun w => C * ((sm⁻¹ + lam w) * grad w) ^ 2) mu :=
    (((hlam.const_add _).mul hgrad).pow_const 2).const_mul _
  exact (h1.add h2).add h3

/-- **Step 3's display at the two `L`-free slots is a.e. measurable.** -/
theorem aemeasurable_step3DisplayAt [NeZero d] (M : ABKModel d) (C : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (hgam : M.gamma ≤ 1 / 8)
    (GB VB : TriadicCube d → Cutoff.CutoffSample d → ℝ) (R : TriadicCube d)
    (hGB : Measurable fun omega : Cutoff.CutoffSample d => GB R omega)
    (hVB : Measurable fun omega : Cutoff.CutoffSample d => VB R omega) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        step3DisplayAt C M m R omega (s : ℝ) (GB R omega) (VB R omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hgam0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨he1, he2⟩ := step3_exponents_nonneg' hgam0 hgam s.2
  have hlam := (measurable_unitCubeLambda_inv_unitRescaledCutoffCoeff M R
    (t := 2 * M.gamma) (by linarith only [hgam0])).aemeasurable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
  exact aemeasurable_displayAt_core he1 he2 hlam
    (aemeasurable_unitCubeHomogenizationError22_unitRescaledCutoffCoeff M R s)
    hGB.aemeasurable hVB.aemeasurable

/-- Whole-sequence negation is quasi measure preserving for the cutoff-sample
law: it is measurable and preserves the law exactly. -/
theorem quasiMeasurePreserving_negateCutoffSample (M : ABKModel d) :
    Measure.QuasiMeasurePreserving (Cutoff.negateCutoffSample (d := d))
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  refine ⟨Cutoff.measurable_negateCutoffSample, ?_⟩
  rw [Cutoff.map_negateCutoffSample_cutoffSampleLaw]

/-- **The `L`-free majorant is a.e. measurable.**  Its two legs are the display
at the sample and the display at the negated sample; the second composes through
the law-preserving negation. -/
theorem aemeasurable_lFreeStep3Majorant [NeZero d] (M : ABKModel d) (C : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (hgam : M.gamma ≤ 1 / 8)
    (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
    (hT : ∀ (k : ℤ) (v : Fin d → ℤ), Measurable (T k v)) (R : TriadicCube d) :
    AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T) (lFreeValueSlot m T) R omega)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hbase := aemeasurable_step3DisplayAt M C m s hgam (lFreeGradSlot m T)
    (lFreeValueSlot m T) R (measurable_lFreeGradSlot m T hT R)
    (measurable_lFreeValueSlot m T hT R)
  exact hbase.add (hbase.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_negateCutoffSample M))

end

end Algsuperdiff.Section4.Provider.BoundsEaL
