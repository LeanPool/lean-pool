/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Logic.Relation

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence

-- [TABLET NODE: P3161T1BlockTreeReachability]

/-!
# P3161T1BlockTreeReachability

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T1BlockTreeReachability
    (S : Int × Int → Prop) (m n : Int) (h : S (m, n))
    (a b : SixSubtileLabel) :
    Relation.ReflTransGen
      (fun x y : PeriodicSubtileIndex ↦
        AllowedSubtileIncidence x y ∧ S (x.first, x.second) ∧
          S (y.first, y.second)) ⟨a, m, n⟩ ⟨b, m, n⟩ := by
-- BODY
  let r := fun x y : PeriodicSubtileIndex ↦
    AllowedSubtileIncidence x y ∧ S (x.first, x.second) ∧ S (y.first, y.second)
  have rev {x y} (hxy : Relation.ReflTransGen r x y) :
      Relation.ReflTransGen r y x := by
    induction hxy with
    | refl => exact .refl
    | tail h e ih => exact (Relation.ReflTransGen.single
        ⟨e.1.symm, e.2.2, e.2.1⟩).trans ih
  have toA (c : SixSubtileLabel) :
      Relation.ReflTransGen r ⟨c, m, n⟩ ⟨.A, m, n⟩ := by
    cases c with
    | A => exact .refl
    | B => exact .single ⟨(AllowedSubtileIncidence.AB m n).symm, h, h⟩
    | C => exact .single ⟨(AllowedSubtileIncidence.AC m n).symm, h, h⟩
    | D => exact .single ⟨(AllowedSubtileIncidence.AD m n).symm, h, h⟩
    | E =>
      exact (Relation.ReflTransGen.single
        ⟨(AllowedSubtileIncidence.BE m n).symm, h, h⟩).trans
        (.single ⟨(AllowedSubtileIncidence.AB m n).symm, h, h⟩)
    | F => exact .single ⟨(AllowedSubtileIncidence.AF m n).symm, h, h⟩
  exact (toA a).trans (rev (toA b))

end ApollonianSuperharmonic

end
