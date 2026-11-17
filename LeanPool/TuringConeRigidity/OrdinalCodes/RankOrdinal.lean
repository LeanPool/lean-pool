/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/RankOrdinal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.SetTheory.ZFC.Ordinal
public import LeanPool.TuringConeRigidity.OrdinalCodes.RankRecursion

/-!
# Rank Ordinal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

theorem rankSet_eq_ordinal (x : ZFSet.{u}) : rankSet x = x.rank.toZFSet := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [mem_rankSet]
    constructor
    · rintro ⟨y,hy,rfl|hz⟩
      · rw [ih y hy]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (ZFSet.rank_lt_of_mem hy)
      · rw [ih y hy] at hz
        exact Ordinal.toZFSet_monotone (ZFSet.rank_lt_of_mem hy).le hz
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨y,hy,hay⟩ := ZFSet.lt_rank_iff.mp ha
      refine ⟨y,hy,?_⟩
      rw [ih y hy]
      rcases lt_or_eq_of_le hay with hay|rfl
      · exact Or.inr (Ordinal.toZFSet_mem_toZFSet_iff.mpr hay)
      · exact Or.inl rfl

theorem rankSet_isOrdinal (x : ZFSet.{u}) : (rankSet x).IsOrdinal := by
  rw [rankSet_eq_ordinal]
  exact ZFSet.isOrdinal_toZFSet _

theorem rankSet_lt_iff (x y : ZFSet.{u}) : rankSet x ∈ rankSet y ↔ x.rank < y.rank := by
  rw [rankSet_eq_ordinal,rankSet_eq_ordinal,Ordinal.toZFSet_mem_toZFSet_iff]

theorem rankSet_le_iff (x y : ZFSet.{u}) : rankSet x ⊆ rankSet y ↔ x.rank ≤ y.rank := by
  rw [rankSet_eq_ordinal,rankSet_eq_ordinal,Ordinal.toZFSet_subset_toZFSet_iff]

end TuringRigidity.InternalRank

end OAI
