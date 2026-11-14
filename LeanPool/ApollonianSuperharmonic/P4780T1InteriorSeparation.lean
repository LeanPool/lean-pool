/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4780T1OverlapBound
public import LeanPool.ApollonianSuperharmonic.P4780T1StrictInterior

-- [TABLET NODE: P4780T1InteriorSeparation]

/-!
# P4780T1InteriorSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1InteriorSeparation :
    Pairwise fun k l : Int × Int => Disjoint
      (interior ((fun p : Real × Real => p + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon))
      (interior ((fun p : Real × Real => p + ((l.1 : Real), (l.2 : Real))) ''
        P4715T1Hexagon)) := by
-- BODY
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hp hq
  have ht (c : Real × Real) :
      interior ((fun p : Real × Real => p + c) '' P4715T1Hexagon) =
        (fun p : Real × Real => p + c) '' interior P4715T1Hexagon := by
    simpa using ((Homeomorph.addRight c).image_interior P4715T1Hexagon).symm
  rw [ht] at hp hq
  rcases hp with ⟨a, ha, hap⟩
  rcases hq with ⟨b, hb, hbp⟩
  let d := l - k
  have hab : a = b + ((d.1 : Real), (d.2 : Real)) := by
    have h1 := congrArg Prod.fst (hap.trans hbp.symm)
    have h2 := congrArg Prod.snd (hap.trans hbp.symm)
    ext <;> simp [d, Int.cast_sub] at * <;> linarith
  have hd := P4780T1OverlapBound d a b (interior_subset ha) (interior_subset hb) hab
  have hne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hkl)
  rw [P4780T1StrictInterior] at ha hb
  rcases ha with ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
  rcases hb with ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
  rcases d with ⟨x, y⟩
  rcases hd with ⟨hx0, hx1, hy0, hy1⟩
  have he1 := congrArg Prod.fst hab
  have he2 := congrArg Prod.snd hab
  simp only [Prod.fst_add, Prod.snd_add] at he1 he2
  interval_cases x <;> interval_cases y <;> norm_num at he1 he2 hne <;> linarith

end ApollonianSuperharmonic

end
