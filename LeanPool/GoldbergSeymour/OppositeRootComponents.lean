/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.TreeInterchangeable

/-!
# P2668_T2_Opposite Root Components

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2668_T2_OppositeRootComponents
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : Nat}
        {e0 : E}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (X Y U : TreeSequence G e0)
    (hunion : Nonempty (OrderedTreeUnion X Y U))
    (hproper : IsProperEdgeColoring G phi)
    (hX : TreeInterchangeable G X phi alpha beta)
    (hY : TreeInterchangeable G Y phi alpha beta)
    (u v : V) (hu : u ∈ TreeSequenceVertexSet X)
    (hv : v ∈ TreeSequenceVertexSet Y)
    (hua : alpha ∈ MissingColors G phi u)
    (hvb : beta ∈ MissingColors G phi v)
    (hnot : ¬ TreeInterchangeable G U phi alpha beta) :
    alpha ≠ beta ∧ u ∉ TreeSequenceVertexSet Y ∧
      v ∉ TreeSequenceVertexSet X ∧
      (∀ x ∈ TreeSequenceVertexSet X,
        Sum.inl x ∉ TwoColorComponent G phi alpha beta (Sum.inl v)) ∧
      (∀ x ∈ TreeSequenceVertexSet Y,
        Sum.inl x ∉ TwoColorComponent G phi alpha beta (Sum.inl u)) := by
  classical
  obtain ⟨ord⟩ := hunion
  have hab : alpha ≠ beta := by
    intro heq
    apply hnot
    intro z w hz
    exact (hz.1 heq).elim
  let H := TwoColorIncidenceGraph G phi alpha beta
  have self (x : V) : Sum.inl x ∈
      TwoColorComponent G phi alpha beta (Sum.inl x) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have leaf (x : V)
      (hm : alpha ∈ MissingColors G phi x ∨ beta ∈ MissingColors G phi x) :
      Set.Subsingleton (H.neighborSet (Sum.inl x)) := by
    exact TwoColorMissingVertexNeighborsSubsingleton G phi hproper alpha beta x hm
  have pu : TwoColorPathComponent G phi alpha beta (Sum.inl u) :=
    ⟨hab, Sum.inl u, self u, leaf u (Or.inl hua)⟩
  have pv : TwoColorPathComponent G phi alpha beta (Sum.inl v) :=
    ⟨hab, Sum.inl v, self v, leaf v (Or.inr hvb)⟩
  have distinct : TwoColorComponent G phi alpha beta (Sum.inl u) ≠
      TwoColorComponent G phi alpha beta (Sum.inl v) := by
    intro heq
    apply hnot
    have rooted (z : Sum V E) (pz : TwoColorPathComponent G phi alpha beta z)
        (hz : ∃ x ∈ TreeSequenceVertexSet U,
          Sum.inl x ∈ TwoColorComponent G phi alpha beta z) :
        TwoColorComponent G phi alpha beta z =
          TwoColorComponent G phi alpha beta (Sum.inl u) := by
      obtain ⟨x, hx, hxc⟩ := hz
      rw [ord.vertexSet] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hX z _ pz pu ⟨x, hx, hxc⟩ ⟨u, hu, self u⟩
      · exact (hY z _ pz pv ⟨x, hx, hxc⟩ ⟨v, hv, self v⟩).trans heq.symm
    intro z w pz pw hz hw
    exact (rooted z pz hz).trans (rooted w pw hw).symm
  have avoidX : ∀ x ∈ TreeSequenceVertexSet X,
      Sum.inl x ∉ TwoColorComponent G phi alpha beta (Sum.inl v) := by
    intro x hx hxc
    exact distinct (hX _ _ pu pv ⟨u, hu, self u⟩ ⟨x, hx, hxc⟩)
  have avoidY : ∀ x ∈ TreeSequenceVertexSet Y,
      Sum.inl x ∉ TwoColorComponent G phi alpha beta (Sum.inl u) := by
    intro x hx hxc
    exact distinct (hY _ _ pu pv ⟨x, hx, hxc⟩ ⟨v, hv, self v⟩)
  exact ⟨hab, (fun h => avoidY u h (self u)),
    (fun h => avoidX v h (self v)), avoidX, avoidY⟩

end GoldbergSeymour

end
