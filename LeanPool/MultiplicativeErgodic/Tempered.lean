/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Tempered functions along an orbit

A real function is *tempered* along a map `σ` if it grows subexponentially along almost every
forward orbit: `f(σⁿω)/n → 0`. The notion involves only the map and the measure. Invertibility
and ergodicity enter only in theorems *about* temperedness, never in the definition, and
nothing about a cocycle or an operator enters at all. `Cocycle.IsTempered` is this notion
applied to `ω ↦ log‖P ω‖`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Topology

/-- **Temperedness.** `f` grows subexponentially along almost every forward `σ`-orbit:
`f(σⁿω)/n → 0` for `μ`-a.e. `ω`. -/
def Tempered {Ω : Type*} [MeasurableSpace Ω] (σ : Ω → Ω) (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (σ^[n] ω) / n) atTop (𝓝 0)

end MultiplicativeErgodic
