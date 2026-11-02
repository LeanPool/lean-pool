/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJCommonRepresentative

/-!
# CutoffResponseJ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Section 3 cutoff response observable

This module defines the source-facing Section 3.5 response observable using
the genuine running diffusivity `sigmaBar` at the coefficient-cutoff scale.
It evaluates the single measurable representative of the entire coarse block,
so every direction shares one probability-one event.

The final common-event theorem identifies this measurable observable with the
literal manuscript expression
`J(square_m, sigmaBar_L^(-1/2)e, sigmaBar_L^(1/2)e; a_L)` simultaneously for
every direction `e`.  No direction-dependent measurable modification and no
fallback comparator enters the definition.

## References

* ABK26, (2.4), definition of `J(U,p,q;a)`.
* ABK26, Section 3.5, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Observable

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch04

noncomputable section

/-- The measurable Section 3.5 response at cube scale `m`, coefficient-cutoff
scale `L`, and direction `e`, with the comparator fixed to the genuine running
diffusivity `sigmaBar_L`.  It is evaluated from the one common full coarse-block
representative. -/
noncomputable def cutoffResponseJ {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) (e : Vec d) :
    Cutoff.CutoffSample d → ℝ :=
  cutoffResponseJWithComparatorFromCommonCoarseBlock M cubeScale
    coefficientScale (Annealed.sigmaBar M coefficientScale) e

/-- For each direction, the source-facing cutoff response is measurable under
the genuine cutoff-sample law. -/
theorem measurable_cutoffResponseJ {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) (e : Vec d) :
    Measurable (cutoffResponseJ M cubeScale coefficientScale e) :=
  measurable_cutoffResponseJWithComparatorFromCommonCoarseBlock M cubeScale
    coefficientScale (Annealed.sigmaBar M coefficientScale) e

/-- On one probability-one event, simultaneously for every direction, the
measurable source-facing response is exactly the literal manuscript quantity
`J(square_m, sigmaBar_L^(-1/2)e, sigmaBar_L^(1/2)e; a_L)`. -/
theorem ae_forall_cutoffResponseJ_eq_literal {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ e : Vec d,
        cutoffResponseJ M cubeScale coefficientScale e omega =
          ResponseJ (cubeSet (originCube d cubeScale))
            (inverseSqrtLoad (Annealed.sigmaBar M coefficientScale) e)
            (sqrtLoad (Annealed.sigmaBar M coefficientScale) e)
            (Cutoff.coefficientCutoff M.nu coefficientScale omega).toFun := by
  filter_upwards
    [ae_forall_cutoffResponseJWithComparator_eq_fromCommonCoarseBlock M
      cubeScale coefficientScale] with omega homega
  intro e
  simpa only [cutoffResponseJ, cutoffResponseJWithComparator_apply] using
    (homega (Annealed.sigmaBar M coefficientScale) e).symm

/-- At each fixed cube scale, one probability-one event identifies the entire
integer-indexed family of source-facing responses with the literal manuscript
family, simultaneously for every coefficient-cutoff scale `L` and every
direction `e`.  Countability is used only for the intersection over `L`; the
uncountable direction quantifier was already placed inside each fixed-`L`
event by the common full-block representative. -/
theorem ae_forall_coefficientScale_cutoffResponseJ_eq_literal {d : ℕ}
    (M : ABKModel d) (cubeScale : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (coefficientScale : ℤ) (e : Vec d),
        cutoffResponseJ M cubeScale coefficientScale e omega =
          ResponseJ (cubeSet (originCube d cubeScale))
            (inverseSqrtLoad (Annealed.sigmaBar M coefficientScale) e)
            (sqrtLoad (Annealed.sigmaBar M coefficientScale) e)
            (Cutoff.coefficientCutoff M.nu coefficientScale omega).toFun := by
  exact MeasureTheory.ae_all_iff.2 fun coefficientScale =>
    ae_forall_cutoffResponseJ_eq_literal M cubeScale coefficientScale

/-- The source-facing response is nonnegative simultaneously in every
direction on one probability-one event.  Pointwise nonnegativity off that
event is neither asserted nor needed for the measurable representative. -/
theorem ae_forall_cutoffResponseJ_nonneg {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ e : Vec d, 0 ≤ cutoffResponseJ M cubeScale coefficientScale e omega := by
  filter_upwards [ae_forall_cutoffResponseJ_eq_literal M cubeScale
    coefficientScale] with omega homega
  intro e
  rw [homega e]
  simpa only [cutoffResponseJWithComparator_apply] using
    cutoffResponseJWithComparator_nonneg M cubeScale coefficientScale
      (Annealed.sigmaBar M coefficientScale) e omega

end

end Algsuperdiff.Section3.Observable
