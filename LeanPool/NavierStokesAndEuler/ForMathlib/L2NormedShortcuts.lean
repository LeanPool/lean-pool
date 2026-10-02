/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.NavierStokesAndEuler.ForMathlib.NormedSpaceShortcuts
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Shortcut instances for the normed structure of `L²` spaces

`MeasureTheory.Lp E 2 μ` is an additive subgroup of the almost-everywhere function classes, so a
query such as `AddCommMonoid (Lp E 2 μ)` or `Module ℝ (Lp E 2 μ)` explores the instances of every
kind of subobject, each of which re-derives structures on `E`, before it succeeds. The shortcuts
below record the instances found.

They apply to every abbreviation of an `L²` space, in particular to the lifted, spatial and time
`L²` spaces of this development.
-/

public section

noncomputable section

namespace NavierStokesAndEuler

open MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

normed_group_shortcut_instances L2Shortcut : Lp E 2 μ

variable [NormedSpace ℝ E]

normed_space_shortcut_instances L2Shortcut : Lp E 2 μ

end NavierStokesAndEuler

end

end
