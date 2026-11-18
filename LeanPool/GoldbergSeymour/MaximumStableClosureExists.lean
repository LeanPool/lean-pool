/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import Mathlib.Data.Fintype.Card

/-!
# Maximum Stable Closure Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MaximumStableClosureExists
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (T seed : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k)
    (hnonempty : exists (pi : PartialEdgeColoring E k)
        (candidate : TreeSequence G e0),
      IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
        StableColoring T C phi pi ∧ TashkinovClosure pi seed candidate) :
    exists (pi : PartialEdgeColoring E k) (candidate : TreeSequence G e0),
      IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
        StableColoring T C phi pi ∧ TashkinovClosure pi seed candidate ∧
        forall (rho : PartialEdgeColoring E k) (other : TreeSequence G e0),
          IsProperEdgeColoring G rho → IsOneEdgeUncolored rho e0 →
          StableColoring T C phi rho → TashkinovClosure rho seed other →
          (TreeSequenceVertexSet other).card ≤
            (TreeSequenceVertexSet candidate).card := by
  classical
  have card_bound : forall S : TreeSequence G e0,
      (TreeSequenceVertexSet S).card ≤ Fintype.card V := by
    intro S
    exact Finset.card_le_card (Finset.subset_univ _)
  let sizes : Finset Nat :=
    (Finset.range (Fintype.card V + 1)).filter (fun n =>
      exists (pi : PartialEdgeColoring E k) (candidate : TreeSequence G e0),
        IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
          StableColoring T C phi pi ∧ TashkinovClosure pi seed candidate ∧
          (TreeSequenceVertexSet candidate).card = n)
  have sizes_nonempty : sizes.Nonempty := by
    obtain ⟨pi, candidate, hproper, hone, hstable, hclosure⟩ := hnonempty
    refine ⟨(TreeSequenceVertexSet candidate).card, ?_⟩
    simp only [sizes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (card_bound candidate),
      ⟨pi, candidate, hproper, hone, hstable, hclosure, rfl⟩⟩
  let largest : Nat := sizes.max' sizes_nonempty
  have largest_mem : largest ∈ sizes :=
    Finset.max'_mem sizes sizes_nonempty
  obtain ⟨pi, candidate, hproper, hone, hstable, hclosure, hcard⟩ :=
    (Finset.mem_filter.mp largest_mem).2
  refine ⟨pi, candidate, hproper, hone, hstable, hclosure, ?_⟩
  intro rho other hrhoProper hrhoOne hrhoStable hotherClosure
  have other_mem : (TreeSequenceVertexSet other).card ∈ sizes := by
    simp only [sizes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (card_bound other),
      ⟨rho, other, hrhoProper, hrhoOne, hrhoStable, hotherClosure, rfl⟩⟩
  rw [hcard]
  exact Finset.le_max' sizes _ other_mem

end GoldbergSeymour

end
