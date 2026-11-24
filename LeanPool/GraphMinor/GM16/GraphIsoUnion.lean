/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
import LeanPool.GraphMinor.GM16.EquivUnion
import LeanPool.GraphMinor.GM16.GraphIsoEdgeEnds

/-!
# Gluing graph isomorphisms on unions

Glue the vertex and edge equivalences, using compatibility of
both their forward and inverse maps. Every edge belongs to a
piece, where its ends are preserved. The resulting equivalences
therefore form an isomorphism of the whole graphs. This joins
the individual path drawings of the subdivision in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph
universe u v u' v' w

/-- Compatible isomorphisms on covering subgraphs glue to a graph
isomorphism whose vertex and edge maps restrict to the given maps. -/
theorem exists_iso_of_subgraph_unions
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {ι : Type w}
    {G : Graph α β} {H : Graph α' β'} (P : ι → Graph α β) (Q : ι → Graph α' β')
    (hP : ∀ i, P i ≤ G) (hQ : ∀ i, Q i ≤ H) (φ : ∀ i, Iso (P i) (Q i))
    (hVG : V(G) = ⋃ i, V(P i)) (hEG : E(G) = ⋃ i, E(P i))
    (hVH : V(H) = ⋃ i, V(Q i)) (hEH : E(H) = ⋃ i, E(Q i))
    (hvF : ∀ i j x (hi : x ∈ V(P i)) (hj : x ∈ V(P j)),
      ((φ i).vertexEquiv ⟨x, hi⟩).val = ((φ j).vertexEquiv ⟨x, hj⟩).val)
    (hvB : ∀ i j y (hi : y ∈ V(Q i)) (hj : y ∈ V(Q j)),
      ((φ i).vertexEquiv.symm ⟨y, hi⟩).val = ((φ j).vertexEquiv.symm ⟨y, hj⟩).val)
    (heF : ∀ i j e (hi : e ∈ E(P i)) (hj : e ∈ E(P j)),
      ((φ i).edgeEquiv ⟨e, hi⟩).val = ((φ j).edgeEquiv ⟨e, hj⟩).val)
    (heB : ∀ i j e (hi : e ∈ E(Q i)) (hj : e ∈ E(Q j)),
      ((φ i).edgeEquiv.symm ⟨e, hi⟩).val = ((φ j).edgeEquiv.symm ⟨e, hj⟩).val) :
    ∃ Φ : Iso G H,
      (∀ i (x : V(P i)), (Φ.vertexEquiv ⟨x.val,(hP i).vertexSet_mono x.property⟩).val =
        ((φ i).vertexEquiv x).val) ∧
      (∀ i (e : E(P i)), (Φ.edgeEquiv ⟨e.val,(hP i).edgeSet_mono e.property⟩).val =
        ((φ i).edgeEquiv e).val) := by
  obtain ⟨vUnion,hvUnion⟩ := exists_equiv_iUnion (fun i => V(P i)) (fun i => V(Q i))
    (fun i => (φ i).vertexEquiv) hvF hvB
  obtain ⟨eUnion,heUnion⟩ := exists_equiv_iUnion (fun i => E(P i)) (fun i => E(Q i))
    (fun i => (φ i).edgeEquiv) heF heB
  let fv : V(G) ≃ V(H) := (Set.equivOfEq hVG).trans (vUnion.trans (Set.equivOfEq hVH.symm))
  let fe : E(G) ≃ E(H) := (Set.equivOfEq hEG).trans (eUnion.trans (Set.equivOfEq hEH.symm))
  have hVR (i : ι) (x : V(P i)) :
      (fv ⟨x.val,(hP i).vertexSet_mono x.property⟩).val = ((φ i).vertexEquiv x).val := by
    change (vUnion ⟨x.val,mem_iUnion_of_mem i x.property⟩).val = _
    exact hvUnion i x
  have hER (i : ι) (e : E(P i)) :
      (fe ⟨e.val,(hP i).edgeSet_mono e.property⟩).val = ((φ i).edgeEquiv e).val := by
    change (eUnion ⟨e.val,mem_iUnion_of_mem i e.property⟩).val = _
    exact heUnion i e
  have hEnds (e : E(G)) : ∃ x y : V(G), G.IsLink e.val x.val y.val ∧
      H.IsLink (fe e).val (fv x).val (fv y).val := by
    have heU : e.val ∈ ⋃ i, E(P i) := (congrArg (fun A : Set β => e.val ∈ A) hEG).mp e.property
    obtain ⟨i,hei⟩ := mem_iUnion.mp heU
    obtain ⟨x,y,hLink⟩ := (P i).exists_isLink_of_mem_edgeSet hei
    let xi : V(P i) := ⟨x,hLink.left_mem⟩
    let yi : V(P i) := ⟨y,hLink.right_mem⟩
    let ei : E(P i) := ⟨e.val,hei⟩
    refine ⟨⟨x,(hP i).vertexSet_mono hLink.left_mem⟩,
      ⟨y,(hP i).vertexSet_mono hLink.right_mem⟩,(hP i).isLink_mono hLink,?_⟩
    rw [hER i ei,hVR i xi,hVR i yi]
    exact (hQ i).isLink_mono (((φ i).isLink_iff ei xi yi).mp hLink)
  exact ⟨⟨fv,fe,isLink_iff_of_edge_ends fv fe hEnds⟩,hVR,hER⟩

end GraphMinor.GM16
