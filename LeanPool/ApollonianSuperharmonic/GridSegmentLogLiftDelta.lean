/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Order.Support
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Lifting

/-!
# GridSegmentLogLiftDelta

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: GridSegmentLogLiftDelta]
theorem GridSegmentLogLiftDelta
    (z0 z1 : ℂ)
    (hz : ∀ t : Set.Icc (0 : Real) 1,
      (1 - (t : Real)) * z0 + (t : Real) * z1 ∈ Complex.slitPlane)
    (L : Set.Icc (0 : Real) 1 → ℂ) (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) =
      (1 - (t : Real)) * z0 + (t : Real) * z1) :
    L ⟨1, by norm_num⟩ - L ⟨0, by norm_num⟩ =
      Complex.log z1 - Complex.log z0 := by
-- BODY
  let : ContractibleSpace (Set.Icc (0 : Real) 1) :=
    (convex_Icc 0 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace (Set.Icc (0 : Real) 1) :=
    (convex_Icc 0 1).locallyPathConnectedSpace
  let z : Set.Icc (0 : Real) 1 → ℂ := fun t ↦
    (1 - (t : Real)) * z0 + (t : Real) * z1
  have hzcont : Continuous z := by
    dsimp [z]
    fun_prop
  have hz0 : z0 ≠ 0 :=
    Complex.slitPlane_ne_zero (by simpa [z] using hz ⟨0, by norm_num⟩)
  let c : ℂ := L ⟨0, by norm_num⟩ - Complex.log z0
  have hexpc : Complex.exp c = 1 := by
    rw [Complex.exp_sub, hexp ⟨0, by norm_num⟩]
    rw [show (1 - ((⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1) : Real)) * z0 +
        ((⟨0, by norm_num⟩ : Set.Icc (0 : Real) 1) : Real) * z1 = z0 by norm_num,
      Complex.exp_log hz0]
    exact div_self hz0
  let K : Set.Icc (0 : Real) 1 → ℂ := fun t ↦ Complex.log (z t) + c
  have hK : Continuous K := by
    dsimp [K]
    have hlog : Continuous (fun t ↦ Complex.log (z t)) := hzcont.clog hz
    exact hlog.add continuous_const
  have hK0 : K ⟨0, by norm_num⟩ = L ⟨0, by norm_num⟩ := by
    simp [K, c, z]
  have hKexp : ∀ t, Complex.exp (K t) = z t := by
    intro t
    rw [show K t = Complex.log (z t) + c by rfl, Complex.exp_add,
      Complex.exp_log (Complex.slitPlane_ne_zero (hz t)), hexpc, mul_one]
  have hLK : L = K := by
    rcases Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
        ⟨z, hzcont⟩ (a₀ := ⟨0, by norm_num⟩)
        (e₀ := L ⟨0, by norm_num⟩) (by simp [hexp, z])
        (fun t ↦ by simpa using Complex.slitPlane_ne_zero (hz t)) with
      ⟨_, _, hunique⟩
    have hLu := hunique ⟨L, hL⟩ ⟨rfl, by ext t; exact hexp t⟩
    have hKu := hunique ⟨K, hK⟩ ⟨hK0, by ext t; exact hKexp t⟩
    exact congrArg DFunLike.coe (hLu.trans hKu.symm)
  rw [hLK]
  simp [K, c, z]
  ring

end

end ApollonianSuperharmonic

end
