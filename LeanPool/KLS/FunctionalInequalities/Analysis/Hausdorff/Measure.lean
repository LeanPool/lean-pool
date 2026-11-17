/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Normalized Hausdorff and codimension-one measures

Mathlib uses the diameter gauge. These definitions rescale it by `ω_d / 2^d` and fix the
codimension-one measure with natural subtraction in dimension zero. The existing KLS namespace
is retained as a public interface; the definitions have no log-concavity or smooth-domain input.
The top-dimensional convention check is in `Analysis/Hausdorff/Volume.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

universe u

section Normalization

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- The volume `ω_d = π^{d/2} / Γ(d/2 + 1)` of the unit ball of `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The standard `d`-dimensional Hausdorff measure `(ω_d / 2^d) • μH[d]`: Mathlib's `μH[d]` uses the
gauge `diam ^ d`, the classical definition uses `ω_d (diam / 2)^d`. -/
def hausdorffNormalized (d : ℕ) : Measure V :=
  ENNReal.ofReal (unitBallVolume d / 2 ^ d) • (μH[(d : ℝ)] : Measure V)

/-- The surface measure `ℋ^{n-1}` of the Blueprint, `n = finrank ℝ V`, in the standard
normalization.  For `n = 0` the natural subtraction gives `ℋ^0`, which only meets the empty
frontier of a smooth domain in a one-point space. -/
def surfaceMeasure : Measure V := hausdorffNormalized V (Module.finrank ℝ V - 1)

end Normalization

end FunctionalInequalities.KLS

end
