/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4780T1HullHalfspaces
public import LeanPool.ApollonianSuperharmonic.P4715T1Arc

-- [TABLET NODE: P4780T1ActiveFacets]

/-!
# P4780T1ActiveFacets

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1ActiveFacets (j : Fin 6) :
    P4715T1Arc (P4715T1BoundaryCycle j)
      (P4715T1BoundaryCycle (j + 1)) =
    P4715T1Hexagon ∩ {p : Real × Real |
      ![2*p.1-p.2=0, p.1-2*p.2=1, p.1+p.2 = -2,
        2*p.1-p.2 = -2, p.1-2*p.2 = -1, p.1+p.2=0] j} := by
-- BODY
  rw [P4780T1HullHalfspaces]
  ext p
  constructor
  · intro hp
    fin_cases j
    all_goals
      simp? [P4715T1Arc, P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets] at hp ⊢
      rw [segment_eq_image] at hp
      rcases hp with ⟨θ, ⟨hθ0, hθ1⟩, hp⟩
      have hfst := congrArg Prod.fst hp
      have hsnd := congrArg Prod.snd hp
      norm_num at hfst hsnd
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> linarith
  · intro hp
    fin_cases j
    all_goals
      simp? [P4715T1Arc, P4715T1Position, P4715T1BoundaryCycle,
        P4715T1Offsets] at hp ⊢
      rcases hp with ⟨⟨hx0, hx1, hy0, hy1, hz0, hz1⟩, heq⟩
      rw [segment_eq_image]
    · refine ⟨-3*p.1, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith
    · refine ⟨(-3*p.1-1)/2, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith
    · refine ⟨-3*p.1-3, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith
    · refine ⟨3*p.1+4, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith
    · refine ⟨(3*p.1+3)/2, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith
    · refine ⟨3*p.1+1, ⟨by linarith, by linarith⟩, ?_⟩
      ext <;> simp <;> linarith

end ApollonianSuperharmonic

end
