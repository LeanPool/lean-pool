/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# OscillationMeanSquare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Mean-square oscillation algebra for `e.nablaw.oscillations`

The quantity compared in `e.nablaw.oscillations` is the normalized mean-square
gradient oscillation on a cube.  CoarseGraining already defines its squared
carrier,

```
  meanSquareDeviationOn V u c    = avg_V (u - c)^2 ,
  meanSquareDeviationVecOn V h c = sum_k meanSquareDeviationOn V (h . k) (c k) ,
  meanSquareOscillationVecOn V h = meanSquareDeviationVecOn V h (avg_V h) ,
```

in `Homogenization.Book.Ch01` (`MeanSquareDeviation.lean`), but supplies **no
lemma at all** about `meanSquareOscillationVecOn`: a repository sweep of
CoarseGraining finds the definition and no consumer.  The three facts proved
here are the ones the nested-recentring route consumes at every scale.

* Nonnegativity, needed to feed any of the accumulation arithmetic.
* The **weighted splitting inequality** `|a + b|^2 <= (1 + 1/k)|a|^2 +
  (1 + k)|b|^2`.  With `k` chosen as the number of telescope pieces this is what
  turns a finite sum of harmonic increments into a bound that grows *linearly*,
  not geometrically, in the number of scales -- the squared-form counterpart of
  the cancellation in `OscillationTelescope`.  Using the crude `k = 1` form
  instead would produce a factor `2^N` and destroy the estimate.
* The **volume-ratio comparison**: restricting a mean-square deviation from a
  cube to a subcube costs exactly the volume ratio.  For one triadic step that
  ratio is `3^d` (see `OscillationCubeFamily`), and it is the factor `rho` of
  `OscillationTelescope.sum_zpow_neg_mul_le_nsmul_of_triadic_bound`.

## References

* ABK26, `e.nablaw.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

theorem meanSquareDeviationOn_nonneg (V : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) :
    0 ≤ Book.Ch01.meanSquareDeviationOn V u c := by
  refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  exact integral_nonneg fun x => sq_nonneg _

theorem meanSquareDeviationVecOn_nonneg (V : Set (Vec d)) (h : Vec d → Vec d)
    (c : Vec d) : 0 ≤ Book.Ch01.meanSquareDeviationVecOn V h c :=
  Finset.sum_nonneg fun k _ => meanSquareDeviationOn_nonneg V (fun y => h y k) (c k)

theorem meanSquareOscillationVecOn_nonneg (V : Set (Vec d)) (h : Vec d → Vec d) :
    0 ≤ Book.Ch01.meanSquareOscillationVecOn V h :=
  meanSquareDeviationVecOn_nonneg V h (volumeAverageVec V h)

/-- **The scalar volume-ratio comparison.**

Restricting a mean-square deviation from `U` to a measurable subset `V` costs
exactly the volume ratio `|U| / |V|`.  Note the hypothesis is integrability on
the *larger* set only. -/
theorem meanSquareDeviationOn_le_volume_ratio_mul {V U : Set (Vec d)}
    (hVU : V ⊆ U) (hvolV : 0 < (volume V).toReal) (hvolU : 0 < (volume U).toReal)
    {u : Vec d → ℝ} {c : ℝ}
    (hint : IntegrableOn (fun y => (u y - c) ^ 2) U) :
    Book.Ch01.meanSquareDeviationOn V u c ≤
      ((volume U).toReal / (volume V).toReal) *
        Book.Ch01.meanSquareDeviationOn U u c := by
  have hmono : ∫ x in V, (u x - c) ^ 2 ≤ ∫ x in U, (u x - c) ^ 2 :=
    setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun x => sq_nonneg (u x - c))
      (Filter.Eventually.of_forall fun x hx => hVU hx)
  have hscaled : (volume V).toReal⁻¹ * ∫ x in V, (u x - c) ^ 2 ≤
      (volume V).toReal⁻¹ * ∫ x in U, (u x - c) ^ 2 :=
    mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hrewrite : ((volume U).toReal / (volume V).toReal) *
        ((volume U).toReal⁻¹ * ∫ x in U, (u x - c) ^ 2) =
      (volume V).toReal⁻¹ * ∫ x in U, (u x - c) ^ 2 := by
    field_simp
  change (volume V).toReal⁻¹ * ∫ x in V, (u x - c) ^ 2 ≤
    ((volume U).toReal / (volume V).toReal) *
      ((volume U).toReal⁻¹ * ∫ x in U, (u x - c) ^ 2)
  rw [hrewrite]
  exact hscaled

/-- **The vector volume-ratio comparison.**

The form actually consumed: passing the mean-square gradient deviation from the
cube `U` to a subcube `V` costs the volume ratio.  For one triadic step of the
concentric family this ratio is `3^d`, whose square root is the factor `rho`
weighting the `E (j+1)` term in `OscillationTelescope`. -/
theorem meanSquareDeviationVecOn_le_volume_ratio_mul {V U : Set (Vec d)}
    (hVU : V ⊆ U) (hvolV : 0 < (volume V).toReal) (hvolU : 0 < (volume U).toReal)
    {h : Vec d → Vec d} {c : Vec d}
    (hint : ∀ k : Fin d, IntegrableOn (fun y => (h y k - c k) ^ 2) U) :
    Book.Ch01.meanSquareDeviationVecOn V h c ≤
      ((volume U).toReal / (volume V).toReal) *
        Book.Ch01.meanSquareDeviationVecOn U h c := by
  change ∑ k : Fin d, Book.Ch01.meanSquareDeviationOn V (fun y => h y k) (c k) ≤
    ((volume U).toReal / (volume V).toReal) *
      ∑ k : Fin d, Book.Ch01.meanSquareDeviationOn U (fun y => h y k) (c k)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    meanSquareDeviationOn_le_volume_ratio_mul hVU hvolV hvolU (hint k)

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
