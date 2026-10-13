/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.BallAverageHolder
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DatumIntegralContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DensePoints
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionMeasurable

/-!
# LocalizedGaugeMeasurable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# At a fixed forcing field the two ball-average gauges are measurable in the sample

For one forcing field the ball-average supremum norm and the ball-average
`1/2`-Hölder seminorm of the solution are suprema of countably many ball
averages, by density, and each ball average is a measurable function of the
sample.  Both gauges are therefore measurable functions of the sample, and
neither asks for a continuous representative.

The comparator enters the supremum norm as a fixed function: the comparator
background does not depend on the sample, so only the rough-field solution
varies.

## Main results

* `measurable_ballAverageHolderOn_solution`,
  `measurable_ballAverageSupNormOn_solution_sub` — the ball-average gauges,
  which need no representative at all.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Countable suprema indexed by points -/

private theorem measurable_biSup_of_countable {alpha : Type*} [MeasurableSpace alpha]
    {P : Set (Vec d)} (hP : P.Countable) {F : Vec d → alpha → ℝ≥0∞}
    (hF : ∀ x ∈ P, Measurable (F x)) :
    Measurable fun w => ⨆ x ∈ P, F x w := by
  have := hP.to_subtype
  have hrw : (fun w => ⨆ x ∈ P, F x w) = fun w => ⨆ x : ↥P, F (x : Vec d) w := by
    funext w
    exact iSup_subtype'
  rw [hrw]
  exact Measurable.iSup fun x => hF (x : Vec d) x.2

/-! ## 2. The ball-average gauges -/

private theorem measurable_iSup_prop {alpha : Type*} [MeasurableSpace alpha] (p : Prop)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) : Measurable fun w => ⨆ _ : p, f w := by
  by_cases hp : p
  · simpa only [iSup_pos hp] using hf
  · simpa only [iSup_neg hp] using (measurable_const : Measurable fun _ : alpha => (⊥ : ℝ≥0∞))

private theorem measurable_setAverage_ball_solution (M : ABKModel d) (m n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {p : Vec d} {r : ℝ} (hB : Metric.ball p r ⊆ cubeSetAt y n) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      ⨍ z in Metric.ball p r, (solutionAt M m n y omega hg).toFun z ∂volume := by
  have hrw : (fun omega : Cutoff.CutoffSample d =>
      ⨍ z in Metric.ball p r, (solutionAt M m n y omega hg).toFun z ∂volume) =
      fun omega : Cutoff.CutoffSample d => (volume.real (Metric.ball p r))⁻¹ *
        ∫ z in Metric.ball p r, (solutionAt M m n y omega hg).toFun z ∂volume := by
    funext omega
    rw [setAverage_eq, smul_eq_mul]
  rw [hrw]
  exact (measurable_setIntegral_solutionAt M m n y hKg hg hB).const_mul _

/-- **The ball-average Hölder gauge of the solution is a measurable function of
the sample.**  No continuous representative is involved. -/
theorem measurable_ballAverageHolderOn_solution (M : ABKModel d) (m n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {D : Set (Vec d)} (hD : D.Countable) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      ballAverageHolderOn (cubeSetAt y n) D (solutionAt M m n y omega hg).toFun := by
  refine measurable_biSup_of_countable hD fun x _hx => ?_
  refine measurable_biSup_of_countable hD fun z _hz => ?_
  refine measurable_iSup_prop _ ?_
  refine Measurable.iSup fun k => ?_
  by_cases hbx : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
  · by_cases hbz : Metric.ball z (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
    · simp only [iSup_pos hbx, iSup_pos hbz]
      exact ENNReal.measurable_ofReal.comp
        (((measurable_setAverage_ball_solution M m n y hKg hg hbx).sub
          (measurable_setAverage_ball_solution M m n y hKg hg hbz)).abs.div_const _)
    · simp only [iSup_pos hbx, iSup_neg hbz]
      exact measurable_const
  · simp only [iSup_neg hbx]
    exact measurable_const

/-- **The ball-average supremum gauge of the difference between the solution and
a fixed function is a measurable function of the sample.** -/
theorem measurable_ballAverageSupNormOn_solution_sub (M : ABKModel d) (m n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} {Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g)
    {D : Set (Vec d)} (hD : D.Countable) (v : H1Function (cubeSetAt y n)) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      ballAverageSupNormOn (cubeSetAt y n) D
        fun z => (solutionAt M m n y omega hg).toFun z - v.toFun z := by
  refine measurable_biSup_of_countable hD fun x _hx => ?_
  refine Measurable.iSup fun k => ?_
  by_cases hbx : Metric.ball x (1 / (k + 1 : ℝ)) ⊆ cubeSetAt y n
  · simp only [iSup_pos hbx]
    have hrw : (fun omega : Cutoff.CutoffSample d => ENNReal.ofReal
        |⨍ z in Metric.ball x (1 / (k + 1 : ℝ)),
          ((solutionAt M m n y omega hg).toFun z - v.toFun z) ∂volume|) =
        fun omega : Cutoff.CutoffSample d => ENNReal.ofReal
          |(⨍ z in Metric.ball x (1 / (k + 1 : ℝ)),
              (solutionAt M m n y omega hg).toFun z ∂volume) -
            ⨍ z in Metric.ball x (1 / (k + 1 : ℝ)), v.toFun z ∂volume| := by
      funext omega
      rw [setAverage_ball_sub_of_h1 _ v hbx]
    rw [hrw]
    exact ENNReal.measurable_ofReal.comp
      (((measurable_setAverage_ball_solution M m n y hKg hg hbx).sub
        measurable_const).abs)
  · simp only [iSup_neg hbx]
    exact measurable_const

end

end Algsuperdiff.Section5.Support
