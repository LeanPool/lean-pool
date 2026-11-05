/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Approximable
public import LeanPool.DomainTheory.Neighborhood.Example12
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SetLike

/-!
# Exercise 4.12 (Scott 1981, PRG-19, Lecture IV)

*Need an approximable `f : 𝒟 → 𝒟` have a **maximum** fixed point? Give an example
where there are
many fixed points.*

**No.** The identity map `I_𝒟` has *every* element as a fixed point. Taking `𝒟` to
be Scott's
Example 1.2 (the fork `T` with `⊥ ⊏ {0}-total`, `⊥ ⊏ {1}-total` and the two total
elements
incomparable), `I_T` has three fixed points `⊥`, `elemZero`, `elemOne`; the two
total ones are
maximal and incomparable, so there is **no greatest fixed point**
(`no_greatest_fixedPoint`) — in
particular no maximum. This is the simplest counterexample to "a least fixed point
is a maximum
fixed point".

Uses `Classical.choice` only through Example 1.2's finite `fin_cases`/`simp`
classification, exactly
as that file does.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem

/-- Abbreviation for Example 1.2's domain `T`. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- `{1} ≠ {0}` as tokens. -/
private theorem one_ne_zero : (Example12.one) ≠ Example12.zero := by
  intro h
  rw [Example12.one, Example12.zero, Set.ext_iff] at h
  simp_all only [Fin.isValue, Set.mem_singleton_iff, eq_iff_eq_cancel_left, Fin.one_eq_zero_iff,
    Nat.succ_ne_self]

/-- `{1} ≠ Δ` as tokens. -/
private theorem one_ne_master : (Example12.one) ≠ Example12.master := by
  intro h
  rw [Example12.one, Example12.master, Set.ext_iff] at h
  simp_all only [Fin.isValue, Set.mem_singleton_iff, Set.mem_univ, iff_true, Fin.forall_fin_two,
    Fin.zero_eq_one_iff, Nat.succ_ne_self, and_true]

/-- `{0} ≠ Δ` as tokens. -/
private theorem zero_ne_master : (Example12.zero) ≠ Example12.master := by
  intro h
  rw [Example12.zero, Example12.master, Set.ext_iff] at h
  simp_all only [Fin.isValue, Set.mem_singleton_iff, Set.mem_univ, iff_true, Fin.forall_fin_two,
    Fin.one_eq_zero_iff, Nat.succ_ne_self, and_false]

/-- The two total elements are incomparable: `elemOne ⋢ elemZero`. -/
theorem elemOne_not_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h Example12.one (Or.inr rfl) with hm | hz
  · exact one_ne_master hm
  · exact one_ne_zero hz

/-- The two total elements are incomparable: `elemZero ⋢ elemOne`. -/
theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h Example12.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm

/-- **Exercise 4.12 (Scott 1981, PRG-19).** Every element is a fixed point of the
identity map
(so `I_T` has *many* fixed points: `⊥`, `elemZero`, `elemOne`). -/
theorem idMap_fixed (x : T.Element) : (idMap T).toElementMap x = x := toElementMap_idMap x

/-- **Exercise 4.12 (Scott 1981, PRG-19).** `I_T` has no *greatest* (hence no
maximum) fixed point:
the two total elements `elemZero`, `elemOne` are both fixed points, are
incomparable, and no element
dominates both. -/
theorem no_greatest_fixedPoint :
    ¬ ∃ z : T.Element, (idMap T).toElementMap z = z ∧
      ∀ x, (idMap T).toElementMap x = x → x ≤ z := by
  rintro ⟨z, _, hz⟩
  have h0 : elemZero ≤ z := hz elemZero (idMap_fixed elemZero)
  have h1 : elemOne ≤ z := hz elemOne (idMap_fixed elemOne)
  rcases element_classification z with rfl | rfl | rfl
  · exact (bot_lt_elemZero).2 h0
  · exact elemOne_not_le_elemZero h1
  · exact elemZero_not_le_elemOne h0

end Domain.Neighborhood.Exercise412
