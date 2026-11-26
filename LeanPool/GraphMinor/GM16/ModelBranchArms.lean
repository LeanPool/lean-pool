/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ConnectedBranchArms
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Branch arms in a subcubic minor model

For a vertex of the wall in XVI (4.2), page 54, choose the end of
each incident model edge in its branch set. There are at most three
such occurrences. Construct arms to them in the connected branch
graph supplied by the model. The arms use none of the chosen model
edges, and two arms at the same branch centre meet only there, even
when two chosen edges have the same attachment vertex.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph GraphMinor.Surface GraphMinor.GM09
universe u v w

/-- The branch-set step in replacing the wall minor by a subdivision,
XVI (4.2), page 54. The graph containing the arms avoids all chosen
model edges. -/
theorem model_vertex_arms {α : Type u} {β : Type v} {ν : Type w}
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe) (v : ν)
    (hFin : (H.neighborSet v).Finite) (hDeg : (H.neighborSet v).ncard ≤ 3) :
    ∃ (K : Graph α β), K ≤ G.deleteEdges (ηe '' H.edgeSet) ∧ V(K) = ηv v ∧
      ∃ (m : α) (attach : H.neighborSet v → α) (P : H.neighborSet v → Graph α β),
        m ∈ V(K) ∧
        (∀ i, attach i ∈ V(K) ∧ G.Inc (ηe s(v,i.val)) (attach i)) ∧
        (∀ i, IsGraphPathWithEnds K (P i) m (attach i)) ∧
        ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {m} := by
  classical
  obtain ⟨K, hK, hVK, hConn⟩ := h.connected v (mem_univ _)
  have hAttach (i : H.neighborSet v) :
      ∃ x ∈ ηv v, G.Inc (ηe s(v,i.val)) x := by
    have he : s(v,i.val) ∈ E(Graph.ofSimpleGraph H) := i.property
    have hi : (Graph.ofSimpleGraph H).Inc s(v,i.val) v := ⟨i.val, rfl, he⟩
    exact (h.inc_iff v (mem_univ _) s(v,i.val) he).mp hi
  let attach : H.neighborSet v → α := fun i => (hAttach i).choose
  have hInK : ∀ i, attach i ∈ V(K) := fun i => hVK.symm ▸ (hAttach i).choose_spec.1
  let : Finite (H.neighborSet v) := hFin.to_subtype
  obtain ⟨m, P, hm, hPath, hInter⟩ :=
    exists_connected_indexed_arms hConn hDeg attach hInK
  exact ⟨K, hK, hVK, m, attach, P, hm,
    fun i => ⟨hInK i, (hAttach i).choose_spec.2⟩, hPath, hInter⟩

end GraphMinor.GM16
