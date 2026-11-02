/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.GoodLocalEventAt
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ObservableSwapPayoff

/-!
# GoodLocalEventAtBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The centred presentation of the good local event

The frozen event `goodLocalEventAt M Ccg m n z` is the pullback of the centred
good local event at scale `m` by translation of the cutoff sample through `z`.
For a triadic cube `Q`, taking `m = Q.scale` and
`z = triadicCubeShift Q` recovers exactly the existing cube-indexed event
`goodLocalEvent M Ccg Q n`.

The sign is positive on the sample translation: `translateCutoffSample z`
evaluates each shell at `x + z`, which turns the centred cube into the cube
whose base point is `z`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

private theorem shellIncrement_translateCutoffSample (z : Vec d)
    (omega : CutoffSample d) (n L : ℤ) :
    shellIncrement (translateCutoffSample z omega).1 n L =
      ShellField.translate z (shellIncrement omega.1 n L) := by
  rw [translateCutoffSample_val]
  unfold shellIncrement
  rw [ShellField.translate_sum]
  rfl

private theorem incrementOscGauge₂_originCube_translateCutoffSample
    (Q : TriadicCube d) (n L : ℤ) (omega : CutoffSample d) :
    incrementOscGauge₂ (originCube d Q.scale) n L
        (translateCutoffSample (triadicCubeShift Q) omega) =
      incrementOscGauge₂ Q n L omega := by
  have hbase : cubeBasePoint (originCube d Q.scale) = (0 : Vec d) := by
    funext i
    simp [cubeBasePoint, originCube]
  have hfield :
      ShellField.translate (cubeBasePoint (originCube d Q.scale))
          (ShellField.translate (triadicCubeShift Q)
            (shellIncrement omega.1 n L)) =
        ShellField.translate (cubeBasePoint Q) (shellIncrement omega.1 n L) := by
    rw [hbase, cubeBasePoint_eq_triadicCubeShift]
    apply ShellField.ext
    intro x
    simp only [ShellField.translate_apply, add_zero]
  unfold incrementOscGauge₂ cubeOscGauge
  rw [shellIncrement_translateCutoffSample, hfield]
  rfl

private theorem cubeLowerEllipticity_originCube_translateCutoffSample
    (M : ABKModel d) (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (hs : 0 < s) (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    cubeLowerEllipticity M (originCube d Q.scale) cutoffScale s hs q
        (translateCutoffSample (triadicCubeShift Q) omega) =
      cubeLowerEllipticity M Q cutoffScale s hs q omega := by
  unfold cubeLowerEllipticity
  apply congrArg (fun x : ℝ => x⁻¹)
  exact
    (cubeLowerEllipticityInv_translateCutoffSample M Q cutoffScale s hs q omega).symm

/-- Pulling the centred good local event back by the positive base-point
translation gives the cube-indexed good local event exactly. -/
theorem goodLocalEventAt_triadicCubeShift (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg Q.scale n
        (triadicCubeShift Q) =
      goodLocalEvent M Ccg Q n := by
  ext omega
  change translateCutoffSample (triadicCubeShift Q) omega ∈
      goodLocalEvent M Ccg (originCube d Q.scale) n ↔
    omega ∈ goodLocalEvent M Ccg Q n
  rw [mem_goodLocalEvent_iff, mem_goodLocalEvent_iff]
  have hscale : (originCube d Q.scale).scale = Q.scale := rfl
  simp only [incrementOscGauge₂_originCube_translateCutoffSample,
    cubeLowerEllipticity_originCube_translateCutoffSample, hscale]

end

end Algsuperdiff.Section3.Provider.BadEvents
