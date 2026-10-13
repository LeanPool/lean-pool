/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MinkowskiLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeFirstThird

/-!
# PerCubeSixWay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube six-way Minkowski, and the negation factor two

## What is here

`MinkowskiProviderFinal.lean` reduces the anchor to ONE per-cube
`L^{p/2}`-moment obligation at the `L`-free Step-3 majorant

```
Maj(ω) = step3DisplayAt(ω) + step3DisplayAt(Nω) ,
    step3DisplayAt = step3FirstTerm + step3SecondTerm + step3ThirdTerm .
```

This module performs the SIX-WAY Minkowski that splits that obligation into the
three summands, at the sample and at the negated sample, and cancels the second
triple against the first: the negation map preserves the cutoff sample law
(`Cutoff.map_negateCutoffSample_cutoffSampleLaw`), so
the negated leg has the SAME `L^{p/2}` moment as the untouched one and the
whole split costs an absolute factor `2`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, `e.apply.sensitivity.J.aL`, Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The negation leg has the same moment -/

/-- **The J3 negation invariance, at the `lintegral`.**  Composition with
`negateCutoffSample` does not change a lower integral against the cutoff sample
law. -/
theorem lintegral_comp_negateCutoffSample (M : ABKModel d)
    {F : Cutoff.CutoffSample d → ℝ≥0∞}
    (hF : AEMeasurable F (Cutoff.cutoffSampleLaw M).toMeasure) :
    (∫⁻ omega, F (Cutoff.negateCutoffSample omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫⁻ omega, F omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmap := Cutoff.map_negateCutoffSample_cutoffSampleLaw M
  have hF' : AEMeasurable F
      (Measure.map (Cutoff.negateCutoffSample (d := d))
        (Cutoff.cutoffSampleLaw M).toMeasure) := by
    rw [hmap]
    exact hF
  have h := MeasureTheory.lintegral_map' (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (f := F) (g := Cutoff.negateCutoffSample) hF'
    Cutoff.measurable_negateCutoffSample.aemeasurable
  rw [← h, hmap]

/-! ## 2. Two `L^q`-norm helpers -/

/-- The development normal form, after the `q`-th root. -/
private theorem rootLe_of_moment {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F : Omega → ℝ≥0∞} {Rv q : ℝ} (hq0 : 0 < q)
    (h : (∫⁻ omega, F omega ^ q ∂mu) ≤ ENNReal.ofReal Rv ^ q) :
    (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal Rv := by
  refine le_trans (ENNReal.rpow_le_rpow h (one_div_nonneg.mpr hq0.le)) (le_of_eq ?_)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]

/-- The two-function Minkowski of `MinkowskiLp`, in applied form. -/
private theorem rootAdd {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {q : ℝ} (hq : 1 ≤ q) {F G : Omega → ℝ≥0∞} (hF : AEMeasurable F mu)
    (hG : AEMeasurable G mu) :
    (∫⁻ omega, (F omega + G omega) ^ q ∂mu) ^ (1 / q) ≤
      (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) + (∫⁻ omega, G omega ^ q ∂mu) ^ (1 / q) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := mu) (f := F) (g := G) hF hG hq
  simp only [Pi.add_apply] at h
  exact h

/-! ## 3. The six-way split, abstractly -/

/-- **The abstract six-way Minkowski.**  Three real summands, read at a sample
and at an involution `N` whose composition leaves lower integrals unchanged. -/
private theorem lintegral_rpow_sixWay {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {q : ℝ} (hq : 1 ≤ q) (T1 T2 T3 : Omega → ℝ) (N : Omega → Omega)
    (hN : ∀ F : Omega → ℝ≥0∞, AEMeasurable F mu →
      (∫⁻ omega, F (N omega) ∂mu) = ∫⁻ omega, F omega ∂mu)
    (hNq : Measure.QuasiMeasurePreserving N mu mu)
    (hm1 : AEMeasurable T1 mu) (hm2 : AEMeasurable T2 mu) (hm3 : AEMeasurable T3 mu)
    {R1 R2 R3 : ℝ} (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (h1 : (∫⁻ omega, ENNReal.ofReal (T1 omega) ^ q ∂mu) ≤ ENNReal.ofReal R1 ^ q)
    (h2 : (∫⁻ omega, ENNReal.ofReal (T2 omega) ^ q ∂mu) ≤ ENNReal.ofReal R2 ^ q)
    (h3 : (∫⁻ omega, ENNReal.ofReal (T3 omega) ^ q ∂mu) ≤ ENNReal.ofReal R3 ^ q) :
    (∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega +
        (T1 (N omega) + T2 (N omega) + T3 (N omega))) ^ q ∂mu) ≤
      ENNReal.ofReal (2 * (R1 + R2 + R3)) ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hDm : AEMeasurable
      (fun omega => ENNReal.ofReal (T1 omega + T2 omega + T3 omega)) mu :=
    ((hm1.add hm2).add hm3).ennreal_ofReal
  have hMm : AEMeasurable
      (fun omega => ENNReal.ofReal (T1 (N omega) + T2 (N omega) + T3 (N omega))) mu :=
    hDm.comp_quasiMeasurePreserving hNq
  -- the display's own three-way split
  have hrootD : (∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega) ^ q ∂mu) ^
      (1 / q) ≤ ENNReal.ofReal R1 + ENNReal.ofReal R2 + ENNReal.ofReal R3 := by
    have hpt : ∀ omega : Omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega) ≤
        ENNReal.ofReal (T1 omega) + ENNReal.ofReal (T2 omega) +
          ENNReal.ofReal (T3 omega) := fun omega =>
      le_trans ENNReal.ofReal_add_le (add_le_add ENNReal.ofReal_add_le le_rfl)
    have hmono : (∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega) ^ q ∂mu) ≤
        ∫⁻ omega, (ENNReal.ofReal (T1 omega) + ENNReal.ofReal (T2 omega) +
          ENNReal.ofReal (T3 omega)) ^ q ∂mu :=
      lintegral_mono fun omega => ENNReal.rpow_le_rpow (hpt omega) hq0.le
    refine le_trans (ENNReal.rpow_le_rpow hmono (one_div_nonneg.mpr hq0.le)) ?_
    refine le_trans (rootAdd hq (hm1.ennreal_ofReal.add hm2.ennreal_ofReal)
      hm3.ennreal_ofReal) ?_
    refine add_le_add ?_ (rootLe_of_moment hq0 h3)
    exact le_trans (rootAdd hq hm1.ennreal_ofReal hm2.ennreal_ofReal)
      (add_le_add (rootLe_of_moment hq0 h1) (rootLe_of_moment hq0 h2))
  -- the negated leg carries the same moment
  have hnegint : (∫⁻ omega,
        ENNReal.ofReal (T1 (N omega) + T2 (N omega) + T3 (N omega)) ^ q ∂mu) =
      ∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega) ^ q ∂mu :=
    hN (fun omega => ENNReal.ofReal (T1 omega + T2 omega + T3 omega) ^ q)
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hDm)
  have hptM : ∀ omega : Omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega +
      (T1 (N omega) + T2 (N omega) + T3 (N omega))) ≤
      ENNReal.ofReal (T1 omega + T2 omega + T3 omega) +
        ENNReal.ofReal (T1 (N omega) + T2 (N omega) + T3 (N omega)) := fun _ =>
    ENNReal.ofReal_add_le
  have hmonoM : (∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega +
        (T1 (N omega) + T2 (N omega) + T3 (N omega))) ^ q ∂mu) ≤
      ∫⁻ omega, (ENNReal.ofReal (T1 omega + T2 omega + T3 omega) +
        ENNReal.ofReal (T1 (N omega) + T2 (N omega) + T3 (N omega))) ^ q ∂mu :=
    lintegral_mono fun omega => ENNReal.rpow_le_rpow (hptM omega) hq0.le
  have hsum : ENNReal.ofReal R1 + ENNReal.ofReal R2 + ENNReal.ofReal R3 +
      (ENNReal.ofReal R1 + ENNReal.ofReal R2 + ENNReal.ofReal R3) =
      ENNReal.ofReal (2 * (R1 + R2 + R3)) := by
    rw [← ENNReal.ofReal_add hR1 hR2,
      ← ENNReal.ofReal_add (by linarith only [hR1, hR2]) hR3,
      ← ENNReal.ofReal_add (by linarith only [hR1, hR2, hR3])
        (by linarith only [hR1, hR2, hR3])]
    congr 1
    ring
  have hrootM : (∫⁻ omega, ENNReal.ofReal (T1 omega + T2 omega + T3 omega +
        (T1 (N omega) + T2 (N omega) + T3 (N omega))) ^ q ∂mu) ^ (1 / q) ≤
      ENNReal.ofReal (2 * (R1 + R2 + R3)) := by
    refine le_trans (ENNReal.rpow_le_rpow hmonoM (one_div_nonneg.mpr hq0.le)) ?_
    refine le_trans (rootAdd hq hDm hMm) ?_
    rw [hnegint, ← hsum]
    exact add_le_add hrootD hrootD
  have hraise := ENNReal.rpow_le_rpow hrootM hq0.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one] at hraise

/-! ## 4. The six-way split at Step 3's display -/

/-- **The per-cube obligation, split into its three summands.**

If the three named summands of Step 3's display obey the development normal
form at exponent `q ≥ 1` with majorants `R₁, R₂, R₃`, then the `L`-free Step-3
majorant obeys it with majorant `2(R₁+R₂+R₃)`.

The factor `2` is the negated leg, priced by the proved negation invariance of
the cutoff sample law; no other constant is spent.  The three moment inputs and
the three `AEMeasurable` side conditions are conditional API obligations,
carried as hypotheses rather than instantiated, so that each proved bullet
keeps its own constant. -/
theorem lintegral_rpow_lFreeStep3Majorant_le_of_summands [NeZero d] (M : ABKModel d)
    (C : ℝ) (m : ℤ) (R : TriadicCube d) (s : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (GB VB : TriadicCube d → Cutoff.CutoffSample d → ℝ) {R1 R2 R3 : ℝ}
    (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (hm1 : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      step3FirstTerm C M m R omega s (GB R omega)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (hm2 : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      step3SecondTerm C M m R omega (GB R omega) (VB R omega))
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hm3 : AEMeasurable (fun omega : Cutoff.CutoffSample d =>
      step3ThirdTerm C M m R omega (GB R omega)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (h1 : (∫⁻ omega, ENNReal.ofReal (step3FirstTerm C M m R omega s (GB R omega)) ^ q
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R1 ^ q)
    (h2 : (∫⁻ omega,
        ENNReal.ofReal (step3SecondTerm C M m R omega (GB R omega) (VB R omega)) ^ q
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R2 ^ q)
    (h3 : (∫⁻ omega, ENNReal.ofReal (step3ThirdTerm C M m R omega (GB R omega)) ^ q
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R3 ^ q) :
    (∫⁻ omega, ENNReal.ofReal (lFreeStep3Majorant C M m s GB VB R omega) ^ q
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (2 * (R1 + R2 + R3)) ^ q := by
  exact lintegral_rpow_sixWay hq
    (fun omega => step3FirstTerm C M m R omega s (GB R omega))
    (fun omega => step3SecondTerm C M m R omega (GB R omega) (VB R omega))
    (fun omega => step3ThirdTerm C M m R omega (GB R omega))
    Cutoff.negateCutoffSample
    (fun F hF => lintegral_comp_negateCutoffSample M hF)
    (quasiMeasurePreserving_negateCutoffSample M) hm1 hm2 hm3 hR1 hR2 hR3 h1 h2 h3

end

end Algsuperdiff.Section4.Provider.BoundsEaL
