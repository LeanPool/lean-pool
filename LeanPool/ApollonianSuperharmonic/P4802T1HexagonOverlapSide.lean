/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1CoefficientTranslation
public import LeanPool.ApollonianSuperharmonic.P4780T1NeighborFacets
public import LeanPool.ApollonianSuperharmonic.P4780T1OverlapBound
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.IntervalCases

-- [TABLET NODE: P4802T1HexagonOverlapSide]

/-!
# P4802T1HexagonOverlapSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4802T1HexagonOverlapSide (k l : Int × Int) (hkl : k ≠ l)
    (p : Real × Real)
    (hp : p ∈ ((fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
      P4715T1Hexagon) ∩
      ((fun x : Real × Real => x + ((l.1 : Real), (l.2 : Real))) ''
      P4715T1Hexagon)) :
    ∃ r : Fin 6,
      ((fun x : Real × Real => x + ((k.1 : Real), (k.2 : Real))) ''
        P4715T1Hexagon) ∩
      ((fun x : Real × Real => x + ((l.1 : Real), (l.2 : Real))) ''
        P4715T1Hexagon) =
      P4715T1Arc (P4715T1VertexShift k (P4715T1BoundaryCycle r))
        (P4715T1VertexShift k (P4715T1BoundaryCycle (r+1))) := by
-- BODY
  obtain ⟨⟨a, ha, hap⟩, ⟨b, hb, hbp⟩⟩ := hp
  let d := l-k
  have hab : a = b + ((d.1 : Real), (d.2 : Real)) := by
    have hx := congrArg Prod.fst (hap.trans hbp.symm)
    have hy := congrArg Prod.snd (hap.trans hbp.symm)
    ext <;> simp [d, Int.cast_sub] at hx hy ⊢ <;> linarith
  have hd := P4780T1OverlapBound d a b ha hb hab
  have hne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hkl)
  have hdiag : d = (1,-1) ∨ d = (-1,1) → False := by
    intro hh
    rw [P4780T1HullHalfspaces] at ha hb
    rcases ha with ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
    rcases hb with ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
    rcases hh with hh | hh <;> rw [hh] at hab
    all_goals
      have hx := congrArg Prod.fst hab
      have hy := congrArg Prod.snd hab
      norm_num at hx hy
      linarith
  have hn : ∃ r : Fin 6,
      d = (![(1,0),(0,-1),(-1,-1),(-1,0),(0,1),(1,1)] r : Int × Int) := by
    rcases d with ⟨x,y⟩
    rcases hd with ⟨hx0,hx1,hy0,hy1⟩
    interval_cases x <;> interval_cases y
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact (hdiag (Or.inr rfl)).elim
    · exact ⟨1,rfl⟩
    · exact (hne rfl).elim
    · exact ⟨4,rfl⟩
    · exact (hdiag (Or.inl rfl)).elim
    · exact ⟨0,rfl⟩
    · exact ⟨5,rfl⟩
  obtain ⟨r,hr⟩ := hn
  refine ⟨r, ?_⟩
  rw [(P4715T1CoefficientTranslation k).2.1]
  ext z
  constructor
  · rintro ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
    refine ⟨x, ?_, hxz⟩
    rw [← P4780T1NeighborFacets r]
    refine ⟨hx,y,hy,?_⟩
    have h1 := congrArg Prod.fst (hxz.trans hyz.symm)
    have h2 := congrArg Prod.snd (hxz.trans hyz.symm)
    rw [← hr]
    ext <;> simp [d, Int.cast_sub] at h1 h2 ⊢ <;> linarith
  · rintro ⟨x,hx,rfl⟩
    rw [← P4780T1NeighborFacets r] at hx
    obtain ⟨hx,y,hy,hyx⟩ := hx
    refine ⟨⟨x,hx,rfl⟩,⟨y,hy,?_⟩⟩
    rw [← hr] at hyx
    have h1 := congrArg Prod.fst hyx
    have h2 := congrArg Prod.snd hyx
    ext <;> simp [d, Int.cast_sub] at h1 h2 ⊢ <;> linarith

end ApollonianSuperharmonic

end
