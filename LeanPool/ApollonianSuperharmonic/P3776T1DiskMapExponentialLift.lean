/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.Lifting

-- [TABLET NODE: P3776T1DiskMapExponentialLift]

/-!
# P3776T1DiskMapExponentialLift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3776T1DiskMapExponentialLift (z : Real × Real) (R : Real)
    (hR : 0 ≤ R) (g : C(Metric.closedBall z R, Complex))
    (hg : ∀ x, g x ≠ 0) :
    ∃ F : C(Metric.closedBall z R, Complex), ∀ x, Complex.exp (F x) = g x := by
-- BODY
  let D : Set (Real × Real) := Metric.closedBall z R
  let : ContractibleSpace D := Metric.contractibleSpace_closedBall hR
  let : LocallyPathConnectedSpace D :=
    (convex_closedBall z R).locallyPathConnectedSpace
  let x0 : D := ⟨z, by change dist z z ≤ R; simpa using hR⟩
  have he0 : Complex.exp (Complex.log (g x0)) = g x0 := Complex.exp_log (hg x0)
  obtain ⟨F, hF, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    g (a₀ := x0) (e₀ := Complex.log (g x0)) he0 (fun x => by simpa using hg x)
  exact ⟨F, fun x => congrFun hF.2 x⟩

end ApollonianSuperharmonic

end
