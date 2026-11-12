/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P4715T1LatticeCoordinates]

/-!
# P4715T1LatticeCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1LatticeCoordinates (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (hu : u ∈ L) (hv : v ∈ L)
    (hcoords : ∀ w : L, ∃! mn : Int × Int,
      (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v = w) :
    Function.Injective (fun mn : Int × Int =>
      (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) ∧
    ∃ c : L →+ Int × Int,
      (∀ w, ((c w).1 : GaussianInt) * u + ((c w).2 : GaussianInt) * v = w) ∧
      Function.Surjective c := by
-- BODY
  classical
  let F : (Int × Int) →+ GaussianInt := {
    toFun := fun mn => (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v
    map_zero' := by simp
    map_add' := by intros; simp [add_mul]; ring }
  have hz (mn : Int × Int) (h : F mn = 0) : mn = 0 := by
    obtain ⟨k, _, hk⟩ := hcoords 0
    exact (hk mn h).trans (hk 0 (by simp [])).symm
  have hinj : Function.Injective F := by
    intro a b hab
    have h := hz (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp h
  let c0 : L → Int × Int := fun w => Classical.choose (hcoords w)
  have hc (w : L) : F (c0 w) = w := (Classical.choose_spec (hcoords w)).1
  let c : L →+ Int × Int := {
    toFun := c0
    map_zero' := hinj (by rw [hc]; simp)
    map_add' := by
      intro a b
      apply hinj
      rw [hc, map_add, hc, hc]
      rfl }
  refine ⟨hinj, c, hc, ?_⟩
  intro mn
  have hm : F mn ∈ L := by
    change (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v ∈ L
    simpa only [← zsmul_eq_mul] using
      L.add_mem (L.zsmul_mem hu mn.1) (L.zsmul_mem hv mn.2)
  refine ⟨⟨F mn, hm⟩, ?_⟩
  exact hinj (hc ⟨F mn, hm⟩)

end ApollonianSuperharmonic

end
