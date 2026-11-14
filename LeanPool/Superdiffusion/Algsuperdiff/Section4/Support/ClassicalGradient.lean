/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# ClassicalGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The classical `C¹` carrier, Support-layer home

The queued cleanup is DONE: the provider's duplicate copies were deleted and
`AffineSplitLift.lean` now imports this module, so `slope, `slope and
`HasGradientOn` have exactly one home and no `Iff.rfl` conversion is needed
anywhere.
-/

open HCPolySupport

namespace Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The continuous linear functional `v ↦ A · v` attached to a slope `A`. -/
def slopeCLM (A : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, A i • ContinuousLinearMap.proj i

@[simp] theorem slopeCLM_apply (A v : Vec d) : slopeCLM A v = vecDot A v := by
  simp only [slopeCLM, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, vecDot]

/-- **`f` is differentiable on `W` with gradient field `G`.**  This is the
classical `C¹` half of the source hypothesis `h ∈ C^{1,1/2}(□_m)`, written
against `Vec d`'s sup-norm through `slopeCLM`. -/
def HasGradientOn (W : Set (Vec d)) (f : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  ∀ y ∈ W, HasFDerivWithinAt f (slopeCLM (G y)) W y

/-- `HasGradientOn` is antitone in the window: the Fréchet derivative within a set
restricts to any subset.  Consolidated here  from the two identically named
provider copies in `Provider/ExcessDecay/OneStepAssembly.lean` and
`Provider/ExcessDecay/BoundaryAssemblyTransport.lean`, so that dot notation
`h.mono_set hsub` keeps working on the single Support-layer carrier. -/
theorem HasGradientOn.mono_set {U V : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : HasGradientOn U f G) (hVU : V ⊆ U) : HasGradientOn V f G :=
  fun y hy => (hf y (hVU hy)).mono hVU

end

end Algsuperdiff.Section4.Support
