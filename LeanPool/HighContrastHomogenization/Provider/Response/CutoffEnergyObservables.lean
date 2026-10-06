/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.OptimizerEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseCarriers

/-!
# High-contrast homogenization: Provider.Response.CutoffEnergyObservables

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-weighted terminal optimizer energy

The terminal cutoff energy of the weak-norm estimate for the optimizer state is
the localized optimizer energy of the adapted parent cell at the pre-Young cutoff
weight, minus the response functional of the same cell.  The cutoff is smooth and bounded, so both
terms are measurable functions of the sample, in the primal and in the adjoint
orientation.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The cutoff is a bounded smooth weight -/

theorem measurable_adaptedPreYoungCutoff [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    Measurable (Response.adaptedPreYoungCutoff q hq t) :=
  ((Response.adaptedPreYoungCutoff_smooth hq t).continuous).measurable

theorem abs_adaptedPreYoungCutoff_le_two [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (x : Vec d) : |Response.adaptedPreYoungCutoff q hq t x| ≤ 2 := by
  rw [abs_of_nonneg (Response.adaptedPreYoungCutoff_nonneg hq t x)]
  exact Response.adaptedPreYoungCutoff_le_two hq t x

/-! ## The cutoff-energy defect of the adapted parent cell -/

/-- **The cutoff-weighted terminal optimizer energy defect is measurable on the
coefficient space.** -/
theorem measurable_cutoffOptimizerEnergyDefect [NeZero d] {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (p r : Vec d) :
    Measurable fun b : CoeffSpace d =>
      weightedOptimizerEnergy (Response.adaptedDomain hq t) (b.coeffOn (Response.adaptedDomain hq t))
          p r (Response.adaptedPreYoungCutoff q hq t) -
        Book.Ch02.responseJ (Response.adaptedDomain hq t)
          (b.coeffOn (Response.adaptedDomain hq t)) p r :=
  Measurable.sub
    (measurable_weightedOptimizerEnergy_coeffSpace
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
      (Recurrence.toReal_volume_adaptedCell_pos hq t) p r
      (measurable_adaptedPreYoungCutoff hq t) (by norm_num)
      (abs_adaptedPreYoungCutoff_le_two hq t))
    (measurable_responseJ_coeffSpace
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
      (Recurrence.toReal_volume_adaptedCell_pos hq t) p r)

/-- **The measurability half of the primal cutoff-energy binder**, in the shape
the terminal component consumes. -/
theorem aestronglyMeasurable_affineSubSkewCutoffEnergyDefect [NeZero d] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      Book.Ch02.average (Response.adaptedDomain hq t) (fun x =>
        Response.adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).coeffOn
              (Response.adaptedDomain hq t)).toCoeffField x)
              ((Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        Book.Ch02.responseJ (Response.adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (Response.adaptedDomain hq t)) p r) P :=
  ((measurable_cutoffOptimizerEnergyDefect hq t p r).comp
    (measurable_subSkew g hg)).aestronglyMeasurable

/-- **The measurability half of the adjoint cutoff-energy binder**, in the shape
the transposed terminal component consumes. -/
theorem aestronglyMeasurable_affineAdjointSubSkewCutoffEnergyDefect [NeZero d] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g)
    (p r : Vec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      Book.Ch02.average (Response.adaptedDomain hq t) (fun x =>
        Response.adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (Response.adaptedDomain hq t)).toCoeffField x)
              ((Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        Book.Ch02.responseJ (Response.adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (Response.adaptedDomain hq t)) p r) P :=
  (((measurable_cutoffOptimizerEnergyDefect hq t p r).comp measurable_transpose).comp
    (measurable_subSkew g hg)).aestronglyMeasurable

end

end Selection
end HighContrast
end HCPolySupport
