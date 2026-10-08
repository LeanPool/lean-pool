/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.WeakOrlicz

/-!
# High-contrast homogenization: Provider.Quenched.ScaledMaximumTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Tail bound for a deterministically scaled maximum

This file records the union-bound step that combines the finite-range mixing
scale and the restored microscopic source scale.  The common deterministic
factor cancels before either tail estimate is applied, so it does not enter the
source gauge.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

variable {Ω : Type*}

section Measurable

variable [MeasurableSpace Ω]

/-- The normalized scaled maximum used by the source is measurable. -/
theorem measurable_scaled_max_one {Rmix Ssrc : Ω → ℝ}
    (hRmix : Measurable Rmix) (hSsrc : Measurable Ssrc) (L : ℝ) :
    Measurable fun ω => L * max 1 (max (Rmix ω) (Ssrc ω)) :=
  measurable_const.mul (measurable_const.max <| hRmix.max hSsrc)

end Measurable

/-- The source-normalized scaled maximum is pointwise at least one as soon as
its deterministic factor is. -/
theorem one_le_scaled_max_one {Rmix Ssrc : Ω → ℝ} {L : ℝ}
    (hL : 1 ≤ L) :
    ∀ ω, 1 ≤ L * max 1 (max (Rmix ω) (Ssrc ω)) := by
  intro ω
  exact one_le_mul_of_one_le_of_one_le hL (le_max_left _ _)

end Quenched
end HighContrast
end HCPolySupport
