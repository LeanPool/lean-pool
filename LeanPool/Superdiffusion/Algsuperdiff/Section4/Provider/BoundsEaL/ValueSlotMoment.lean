/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.GradSlotMoment

/-!
# ValueSlotMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# B6, second half: the mean-value tail of the `L`-free value slot

Nothing here imports that file, and nothing here claims the anchor.

## What this module does

`ShellSlotBounds.lFreeValueSlot m T R ω` has exactly two summands:

```
‖k_m − k_{j−2}‖_{L∞(3^j v + □_j)}                                     (the L∞ leg)
  +  centeringConst d · 3^{2m} · T m 0 ω                             (the mean-value tail)
```

with `j = R.scale`.  Consequently

```
centeringConst d · 3^{2m} · tailSeriesGauge m m 0
    = 𝒪_{Γ₂}( centeringConst d · gammaTriangleConst 2 · (1 − 3^{γ−1})^{-1} · 3^{γ m} ) ,
```

which is the Step-4 target shape `𝒪_{Γ₂}(^{γ m})` for this summand, with an
explicit constant and no exponent moved.

The domination `tailSeriesGauge m m 0 ≤ deepGradSeries m 0` is proved sample,
not almost surely: the two `ℤ`-indexed families differ by the single layer `i =
m`, so they are summable together, and on the non-summable set both real
`tsum`s are `0`.  No a.e. hypothesis is therefore needed, which is what lets
the conclusion be a genuine `IsBigOWith` (a statement about the whole measure).

## References

* ABK26, (`e.km.kn.Linfty`, `e.km.kn.Linfty.smallcube`),
  (`e.k.ell.upscales.infty`), (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## 1. The mean-value tail is a sub-block of the deep block -/

/-- Termwise: at the origin cube of scale `m` every `(m, ∞)` layer term is a deep
layer term. -/
private theorem tailLayerTerm_le_deepGradTerm (m : ℤ) (omega : Cutoff.CutoffSample d)
    (i : ℤ) :
    tailLayerTerm m m (0 : Fin d → ℤ) omega i ≤ deepGradTerm m (0 : Fin d → ℤ) omega i := by
  rcases lt_or_ge m i with hmi | hmi
  · rw [tailLayerTerm, ite_eq_left hmi, deepGradTerm, ite_eq_left (by omega : m ≤ i),
    gradLayerGauge]
  · rw [tailLayerTerm, ite_eq_right (by omega : ¬ m < i)]
    exact deepGradTerm_nonneg _ _ _ _

/-- The two `ℤ`-indexed families differ by the single layer `i = m`, hence are
summable together. -/
private theorem summable_deepGradTerm_iff (m : ℤ) (omega : Cutoff.CutoffSample d) :
    Summable (deepGradTerm m (0 : Fin d → ℤ) omega) ↔
      Summable (tailLayerTerm m m (0 : Fin d → ℤ) omega) := by
  have hmid : Summable fun i : ℤ =>
      (if m ≤ i ∧ i ≤ m then gradLayerGauge m (0 : Fin d → ℤ) omega i else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc m m) fun i hi => ?_
    rw [ite_eq_right (fun h => hi (Finset.mem_Icc.mpr h))]
  have hsplit := deepGradTerm_eq_add m m (0 : Fin d → ℤ) omega le_rfl
  constructor
  · intro hdeep
    have hsub : Summable fun i : ℤ =>
        deepGradTerm m (0 : Fin d → ℤ) omega i -
          (if m ≤ i ∧ i ≤ m then gradLayerGauge m (0 : Fin d → ℤ) omega i else 0) :=
      hdeep.sub hmid
    refine hsub.congr fun i => ?_
    rw [hsplit i]
    ring
  · intro htail
    exact (htail.add hmid).congr fun i => (hsplit i).symm

/-- **The mean-value tail is dominated by the deep block sample.** -/
theorem tailSeriesGauge_le_deepGradSeries (m : ℤ) (omega : Cutoff.CutoffSample d) :
    tailSeriesGauge m m (0 : Fin d → ℤ) omega ≤
      deepGradSeries m (0 : Fin d → ℤ) omega := by
  by_cases htail : Summable (tailLayerTerm m m (0 : Fin d → ℤ) omega)
  · exact Summable.tsum_le_tsum (tailLayerTerm_le_deepGradTerm m omega) htail
      ((summable_deepGradTerm_iff m omega).2 htail)
  · have hdeep : ¬ Summable (deepGradTerm m (0 : Fin d → ℤ) omega) := fun h =>
      htail ((summable_deepGradTerm_iff m omega).1 h)
    rw [tailSeriesGauge, tsum_eq_zero_of_not_summable htail, deepGradSeries,
      tsum_eq_zero_of_not_summable hdeep]

/-! ## 2. The `Γ₂` display of the mean-value tail -/

/-- The cube weight of the value slot, in `Real.rpow` form. -/
private theorem zpow_two_mul_eq_rpow (m : ℤ) :
    (3 : ℝ) ^ (2 * m) = Real.rpow 3 (2 * (m : ℝ)) := by
  rw [← Real.rpow_intCast 3 (2 * m)]
  congr 1
  push_cast
  ring

theorem centeringConst_nonneg (d : ℕ) : (0 : ℝ) ≤ centeringConst d := by
  rw [centeringConst]
  positivity

/-- **B6, second half (the settled summand): the mean-value tail of the value
slot has the Step-4 target shape.**

`centeringConst d · 3^{2m} · tailSeriesGauge m m 0 = 𝒪_{Γ₂}(^{γ m})` with the
explicit constant `C = centeringConst d · gammaTriangleConst 2 · (1 −
3^{γ−1})^{-1}`.  No exponent is moved. -/
theorem isBigOWith_gammaSigma_valueSlotMeanValueTail (M : ABKModel d) (m : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        centeringConst d * ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega))
      (centeringConst d * (deepGradConst M * Real.rpow 3 (M.gamma * (m : ℝ)))) := by
  have hdeep := IsBigOWith.const_mul (centeringConst_nonneg d)
    (isBigOWith_gammaSigma_deepGradSeries M m (0 : Fin d → ℤ))
  refine hdeep.of_le fun omega => ?_
  refine mul_le_mul_of_nonneg_left ?_ (centeringConst_nonneg d)
  rw [zpow_two_mul_eq_rpow]
  exact mul_le_mul_of_nonneg_left (tailSeriesGauge_le_deepGradSeries m omega)
    (Real.rpow_nonneg (by norm_num) _)

/-- The value slot, split into its `L∞` leg and its mean-value tail. -/
theorem lFreeValueSlot_eq_linfty_add_meanValueTail (m : ℤ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    lFreeValueSlot m (tailSeriesGauge m) R omega =
      Cutoff.localCubeControl R.scale
          (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
            (shellIncrement omega.1 (R.scale - 2) m)) +
        centeringConst d *
          ((3 : ℝ) ^ (2 * m) * tailSeriesGauge m m (0 : Fin d → ℤ) omega) :=
  rfl

end

end Algsuperdiff.Section4.Provider.BoundsEaL
