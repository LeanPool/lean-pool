/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.Ring.Real

-- [TABLET NODE: P4715T1PlaneMap]

/-!
# P4715T1PlaneMap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1PlaneMap (u v : GaussianInt)
    (hinj : Function.Injective (fun mn : Int × Int =>
      (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v)) :
    (u.re : Real) * (v.im : Real) - (u.im : Real) * (v.re : Real) ≠ 0 ∧
    ∃ E : (Real × Real) ≃L[Real] (Real × Real),
      ∀ p, E p = p.1 • GaussianRealPoint u + p.2 • GaussianRealPoint v := by
-- BODY
  have hZ : u.re * v.im - u.im * v.re ≠ 0 := by
    intro h
    have h1 : ((v.re, -u.re) : Int × Int) = (0, 0) := by
      apply hinj
      ext <;> simp <;> nlinarith
    have h2 : ((v.im, -u.im) : Int × Int) = (0, 0) := by
      apply hinj
      ext <;> simp <;> nlinarith
    have hur : u.re = 0 := by simpa using congrArg Prod.snd h1
    have hui : u.im = 0 := by simpa using congrArg Prod.snd h2
    have hu : u = 0 := by ext <;> assumption
    have bad : ((1, 0) : Int × Int) = (0, 0) := hinj (by simp [hu])
    norm_num at bad
  have hD : (u.re : Real) * (v.im : Real) - (u.im : Real) * (v.re : Real) ≠ 0 := by
    exact_mod_cast hZ
  let e : (Real × Real) ≃ₗ[Real] (Real × Real) := {
    toFun := fun p => ((u.re : Real) * p.1 + (v.re : Real) * p.2,
      (u.im : Real) * p.1 + (v.im : Real) * p.2)
    invFun := fun p =>
      (((v.im : Real) * p.1 - (v.re : Real) * p.2) /
        ((u.re : Real) * (v.im : Real) - (u.im : Real) * (v.re : Real)),
      (-(u.im : Real) * p.1 + (u.re : Real) * p.2) /
        ((u.re : Real) * (v.im : Real) - (u.im : Real) * (v.re : Real)))
    left_inv := by
      intro p
      ext <;> dsimp <;> apply (div_eq_iff hD).2 <;> ring
    right_inv := by
      intro p
      ext <;> dsimp <;> rw [← mul_div_assoc, ← mul_div_assoc, ← add_div] <;>
        apply (div_eq_iff hD).2 <;> ring
    map_add' := by intro p q; ext <;> simp <;> ring
    map_smul' := by intro s p; ext <;> simp <;> ring }
  let E : (Real × Real) ≃L[Real] (Real × Real) := {
    e with
    continuous_toFun := by dsimp [e]; fun_prop
    continuous_invFun := by dsimp [e]; fun_prop }
  refine ⟨hD, E, ?_⟩
  intro p
  ext <;> simp [E, e, GaussianRealPoint, mul_comm]

end ApollonianSuperharmonic

end
