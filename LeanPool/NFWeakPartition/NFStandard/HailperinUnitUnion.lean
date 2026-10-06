/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.HailperinCylinder

/-! NF weak partition development: NFStandard.HailperinUnitUnion. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore

section Coding

variable {S : Fol.Structure LNF} (hH : Fol.allRealizeSentence S LiteralHailperinNF)

/-! `typeLower` turns a relation-like object `R` into the set of `z` for which
every pair `⟨w,{z}⟩` belongs to `R`.  Taking `R = V × (V \ A)` and then a
complement therefore removes exactly one singleton level from the membership
test.
-/


/-- Remove one singleton level from the elements tested against `A`. -/
@[expose]
noncomputable def unitUnionObj (A : S) : S :=
  complement hH (typeLower hH (xp hH (complement hH A)))

/-- Exact semantic law for one level of singleton lowering. -/
@[simp]
theorem mem_unitUnionObj (A z : S) :
    Mem S z (unitUnionObj hH A) ↔ Mem S (singleton hH z) A :=
  by
  rw [unitUnionObj, mem_complement, mem_typeLower]
  constructor
  · intro h
    by_contra hz
    apply h
    intro w
    rw [mem_xp_kPair, mem_complement]
    exact hz
  · intro hz hall
    have hw := hall (oneC hH)
    rw [mem_xp_kPair, mem_complement] at hw
    exact hw hz

/-- Iterate singleton lowering `m` times. -/
@[expose]
noncomputable def unitUnionIter : Nat → S → S
  | 0, A => A
  | m + 1, A => unitUnionIter m (unitUnionObj hH A)

@[simp]
theorem unitUnionIter_zero (A : S) : unitUnionIter hH 0 A = A :=
  rfl

@[simp]
theorem unitUnionIter_succ (m : Nat) (A : S) :
    unitUnionIter hH (m + 1) A = unitUnionIter hH m (unitUnionObj hH A) :=
  rfl

/-- Iterated lowering is inverse, at the membership level, to `raise`. -/
@[simp]
theorem mem_unitUnionIter (m : Nat) (A z : S) :
    Mem S z (unitUnionIter hH m A) ↔ Mem S (raise hH m z) A := by
  induction m generalizing A z with
  | zero => rfl
  | succ m ih => rw [unitUnionIter_succ, ih, mem_unitUnionObj, raise_succ]


end Coding

end NFChoice.Foundation.NFStandard
