/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5157T1StaircasePoint
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange

-- [TABLET NODE: P5157T1AlternatingStaircase]

/-!
# P5157T1AlternatingStaircase

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5157T1AlternatingStaircase (z : GaussianInt) (h : Bool)
    (s : Int) (hs : s = 1 ∨ s = -1) (N : Nat) (hN : 0 < N) :
    let p := P5157T1StaircasePoint z h s
    Function.Injective p ∧
    SimpleGridPath {v | ∃ j ≤ N, v = p j}
      {e | ∃ j < N, e = {p j, p (j + 1)}} := by
-- BODY
  dsimp only
  let p := P5157T1StaircasePoint z h s
  have inj : Function.Injective p := by
    intro a b hab
    have hr := congrArg Zsqrtd.re hab
    have hi := congrArg Zsqrtd.im hab
    rcases hs with rfl | rfl <;> cases h <;>
      simp [p, P5157T1StaircasePoint] at hr hi <;> omega
  have step (j : Nat) :
      p (j + 1) = p j + 1 ∨ p (j + 1) = p j - 1 ∨
      p (j + 1) = p j + ⟨0, 1⟩ ∨ p (j + 1) = p j - ⟨0, 1⟩ := by
    rcases hs with rfl | rfl <;> cases h <;>
      simp [p, P5157T1StaircasePoint, Zsqrtd.ext_iff] <;> omega
  let l := List.ofFn (fun j : Fin (N + 1) => p j)
  have hl : l.length = N + 1 := List.length_ofFn
  have chain : l.IsChain (fun a b => ∃ j < N, a = p j ∧ b = p (j + 1)) := by
    apply List.isChain_ofFn.mpr
    intro j hj
    exact ⟨j, by omega, rfl, rfl⟩
  have consecutive (a b : GaussianInt) (l₁ l₂ : List GaussianInt)
      (heq : l = l₁ ++ a :: b :: l₂) :
      ∃ j < N, a = p j ∧ b = p (j + 1) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp chain heq
  refine ⟨inj, l, List.nodup_ofFn.mpr ?_, by omega, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.ext (inj hab)
  · ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, l, List.mem_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by omega, rfl⟩
  · intro a b l₁ l₂ heq
    obtain ⟨j, _, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
    exact step j
  · intro e
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjl : j < l.length := by omega
      have hjl' : j + 1 < l.length := by omega
      refine ⟨p j, p (j + 1), l.take j, l.drop (j + 2), ?_, rfl⟩
      have hd := List.getElem_cons_drop hjl
      have hd' := List.getElem_cons_drop hjl'
      have heq : l = l.take j ++ l[j] :: l[j + 1] :: l.drop (j + 2) := by
        rw [show j + 2 = j + 1 + 1 by omega, hd', hd, List.take_append_drop]
      simpa only [l, List.getElem_ofFn] using heq
    · rintro ⟨a, b, l₁, l₂, heq, rfl⟩
      obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
      exact ⟨j, hj, rfl⟩

end ApollonianSuperharmonic

end
