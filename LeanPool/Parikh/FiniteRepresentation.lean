/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Activation
import LeanPool.Parikh.InsertionSequences

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Turning the tree description into a finite union

Decomposition and activation describe the grammar image using simple bases and
bounded cycle contexts. To conclude semilinearity, we must show that only
finitely many choices occur.

`bases_finite` and `bounded_cycles_finite` specialize the bounded-tree theorem.
There are then finitely many context subsets for each base, and each activatable
choice contributes a linear set. `treeRepresentation_isSemilinearSet` combines
these facts using Mathlib's finite-union results. This is semantic finiteness;
an algorithm that enumerates the families is a separate task.

Source: `lem:finite`, `thm:main`.
-/
namespace Parikh
variable {T : Type*}

/-- Simple complete start trees form a finite family over arbitrary nonterminals. -/
theorem bases_finite [Finite T] (g : ContextFreeGrammar T) :
    {B : ParseTree T g.NT | IsBase g B}.Finite := by
  apply (bounded_open_finite g (activeNonterminals g).card).subset
  rintro B ⟨hB, _, hsimple⟩
  exact ⟨⟨hB.1, by simp [hB.2]⟩, simple_height g B hB hsimple⟩

/-- A cycle's unique hole is active because its matching root is a production
label. Thus the bounded-cycle family is finite even with infinite nonterminals. -/
theorem bounded_cycles_finite [Finite T] (g : ContextFreeGrammar T) :
    {C : ParseTree T g.NT | IsBoundedCycle g C}.Finite := by
  apply (bounded_open_finite g ((activeNonterminals g).card + 1)).subset
  rintro C ⟨⟨A, hcycle⟩, hheight⟩
  refine ⟨⟨hcycle.1.1, ?_⟩, hheight⟩
  intro B hB
  have hBA : B = A := by
    simpa only [hcycle.1.2, List.mem_singleton] using hB
  subst B
  exact hcycle.1.1.support_active hcycle.root_mem_support

/-- The tree representation is a finite union of the existing linear components.
Filtering the finite powerset keeps exactly the activatable context subsets. -/
theorem treeRepresentation_isSemilinearSet [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (treeRepresentation g) := by
  classical
  let bases := (bases_finite g).toFinset
  let cycles := (bounded_cycles_finite g).toFinset
  have hunion : treeRepresentation g =
      ⋃ B ∈ bases, ⋃ D ∈ cycles.powerset.filter (ContextsActivatable g B),
        (contextComponent B D).denotation := by
    ext v
    simp only [treeRepresentation, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨B, D, hB, hD, hactive, hv⟩
      refine ⟨B, (bases_finite g).mem_toFinset.mpr hB, D, ⟨?_, hactive⟩, hv⟩
      intro C hC
      exact (bounded_cycles_finite g).mem_toFinset.mpr (hD C hC)
    · rintro ⟨B, hB, D, ⟨hD, hactive⟩, hv⟩
      exact ⟨B, D, (bases_finite g).mem_toFinset.mp hB,
        fun C hC => (bounded_cycles_finite g).mem_toFinset.mp (hD hC), hactive, hv⟩
  rw [hunion]
  exact IsSemilinearSet.biUnion_finset fun B _ =>
    IsSemilinearSet.biUnion_finset fun D _ =>
      (component_isLinearSet (contextComponent B D)).isSemilinearSet

end Parikh
