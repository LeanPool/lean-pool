/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TopologicalDisk
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.Lifting

/-!
# TopologicalDiskExponentialLift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: TopologicalDiskExponentialLift]
theorem TopologicalDiskExponentialLift
    (S : Set (Real × Real)) (hS : TopologicalDisk S)
    (q : Real × Real) (hq : q ∉ S) :
    ∃ F : S → ℂ, Continuous F ∧
      ∀ x : S, Complex.exp (F x) =
        (⟨x.1.1 - q.1, x.1.2 - q.2⟩ : ℂ) := by
-- BODY
  rcases hS with ⟨e⟩
  let D : Set (Real × Real) := Metric.closedBall 0 1
  let : ContractibleSpace D := Metric.contractibleSpace_closedBall (by norm_num)
  let : LocallyPathConnectedSpace D :=
    (convex_closedBall (0 : Real × Real) 1).locallyPathConnectedSpace
  let : ContractibleSpace S := e.symm.contractibleSpace
  let : LocallyPathConnectedSpace S := e.isQuotientMap.locallyPathConnectedSpace
  let g : S → ℂ := fun x ↦
    ((x.1.1 - q.1 : Real) : ℂ) + ((x.1.2 - q.2 : Real) : ℂ) * Complex.I
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  let x0 : S := Classical.choice (inferInstance : Nonempty S)
  have hg0 (x : S) : g x ≠ 0 := by
    intro hx
    apply hq
    have hre := congrArg Complex.re hx
    have him := congrArg Complex.im hx
    have hxq : (x.1 : Real × Real) = q := by
      apply Prod.ext <;> simp [g] at hre him <;> linarith
    exact hxq ▸ x.2
  let e0 : ℂ := Complex.log (g x0)
  have he0 : Complex.exp e0 = g x0 := by
    exact Complex.exp_log (hg0 x0)
  rcases Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨g, hg⟩ (a₀ := x0) (e₀ := e0) he0 (fun x ↦ by simpa using hg0 x) with
    ⟨F, hF, _⟩
  refine ⟨F, F.continuous, ?_⟩
  intro x
  have hx := congrFun hF.2 x
  apply Complex.ext
  · simpa [Function.comp_apply, g] using congrArg Complex.re hx
  · simpa [Function.comp_apply, g] using congrArg Complex.im hx

end

end ApollonianSuperharmonic

end
