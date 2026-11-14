/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Law

/-!
# Law

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The actual coefficient-cutoff law

For a fixed scale, the law used by the annealed Section 3 objects is not an
extra datum.  It is the pushforward of the canonical probability law on the
public lower-tail convergence carrier along the genuine coefficient cutoff
`a_m = nu I + k_m`.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory
open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- The actual probability law of the coefficient cutoff `a_m`.  Both the
source carrier and the coefficient map are genuine measurable objects, so this
definition has no default-value or a.e.-map branch. -/
noncomputable def coefficientCutoffProbabilityLaw (M : ABKModel d) (m : ℤ) :
    ProbabilityMeasure (RegCoeffField d) :=
  (cutoffSampleLaw M).map (coefficientCutoff M.nu m)

/-- The actual Chapter 4 coefficient law of `a_m`, forgetting only the
probability-measure packaging. -/
noncomputable def coefficientCutoffLaw (M : ABKModel d) (m : ℤ) :
    Book.Ch04.RestrictionCoeffLaw d :=
  (coefficientCutoffProbabilityLaw M m).toMeasure

/-- The cutoff coefficient law is a probability measure because it is the
measurable pushforward of the induced canonical cutoff-sample law. -/
noncomputable instance coefficientCutoffLaw_isProbability (M : ABKModel d)
    (m : ℤ) : IsProbabilityMeasure (coefficientCutoffLaw M m) := by
  change IsProbabilityMeasure
    ((cutoffSampleLaw M).map (coefficientCutoff M.nu m)).toMeasure
  infer_instance

@[simp]
theorem coefficientCutoffLaw_eq_map (M : ABKModel d) (m : ℤ) :
    coefficientCutoffLaw M m =
      Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure := by
  rfl

end

end Algsuperdiff.Section3.Cutoff
