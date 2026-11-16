/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: TouchingTriplePermutations]

/-!
# TouchingTriplePermutations

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TouchingTriplePermutations : ∀ T U V : ProtoTile,
    TouchingTriple T U V ↔
      TouchingTriple T V U ∧ TouchingTriple U T V ∧
      TouchingTriple U V T ∧ TouchingTriple V T U ∧
      TouchingTriple V U T := by
-- BODY
  intro T U V
  have touching_swap : ∀ A B : ProtoTile, TileTouching A B ↔ TileTouching B A := by
    intro A B
    unfold TileTouching
    constructor
    · intro h
      rcases h with h | h | h
      · left
        rcases h with ⟨ha, hb, hab, hp⟩
        exact ⟨hb, ha, hab.symm, by simpa [Set.inter_comm] using hp⟩
      · right
        right
        exact h
      · right
        left
        exact h
    · intro h
      rcases h with h | h | h
      · left
        rcases h with ⟨hb, ha, hba, hp⟩
        exact ⟨ha, hb, hba.symm, by simpa [Set.inter_comm] using hp⟩
      · right
        right
        exact h
      · right
        left
        exact h
  have triple_swap : ∀ A B C : ProtoTile,
      TouchingTriple A B C ↔ TouchingTriple A C B := by
    intro A B C
    constructor
    · intro h
      rcases h with ⟨hAB, hBC, hCA, x, hx, hxuniq⟩
      refine ⟨(touching_swap C A).mp hCA, (touching_swap B C).mp hBC,
        (touching_swap A B).mp hAB, x, ?_, ?_⟩
      · exact ⟨hx.1, hx.2.2, hx.2.1⟩
      · intro y hy
        exact hxuniq y ⟨hy.1, hy.2.2, hy.2.1⟩
    · intro h
      rcases h with ⟨hAC, hCB, hBA, x, hx, hxuniq⟩
      refine ⟨(touching_swap B A).mp hBA, (touching_swap C B).mp hCB,
        (touching_swap A C).mp hAC, x, ?_, ?_⟩
      · exact ⟨hx.1, hx.2.2, hx.2.1⟩
      · intro y hy
        exact hxuniq y ⟨hy.1, hy.2.2, hy.2.1⟩
  have triple_cycle : ∀ A B C : ProtoTile,
      TouchingTriple A B C ↔ TouchingTriple B C A := by
    intro A B C
    constructor
    · intro h
      rcases h with ⟨hAB, hBC, hCA, x, hx, hxuniq⟩
      refine ⟨hBC, hCA, hAB, x, ?_, ?_⟩
      · exact ⟨hx.2.1, hx.2.2, hx.1⟩
      · intro y hy
        exact hxuniq y ⟨hy.2.2, hy.1, hy.2.1⟩
    · intro h
      rcases h with ⟨hBC, hCA, hAB, x, hx, hxuniq⟩
      refine ⟨hAB, hBC, hCA, x, ?_, ?_⟩
      · exact ⟨hx.2.2, hx.1, hx.2.1⟩
      · intro y hy
        exact hxuniq y ⟨hy.2.1, hy.2.2, hy.1⟩
  have hswap : TouchingTriple T U V ↔ TouchingTriple T V U := triple_swap T U V
  have hcycle : TouchingTriple T U V ↔ TouchingTriple U V T := triple_cycle T U V
  have hcycle2 : TouchingTriple T U V ↔ TouchingTriple V T U :=
    hcycle.trans (triple_cycle U V T)
  have hlast : TouchingTriple T U V ↔ TouchingTriple V U T :=
    hswap.trans (triple_cycle T V U)
  constructor
  · intro h
    exact ⟨hswap.mp h, (hcycle.trans (triple_swap U V T)).mp h,
      hcycle.mp h, hcycle2.mp h, hlast.mp h⟩
  · intro h
    exact hswap.mpr h.1

end ApollonianSuperharmonic

end
