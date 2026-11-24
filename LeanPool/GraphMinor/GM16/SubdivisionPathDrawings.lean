/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.SimpleDrawingVertices
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM16.PathDrawingOnLine
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Drawing all replacing paths of a subdivision

Draw each path on the closure of the corresponding original edge.
Its two ends map to the original edge ends. The path-system
intersection condition identifies every branch centre on that
path with one of those ends, so all centre maps agree. Distinct
path supports meet only at original drawing vertices. These are
the gluing data for the subdivision in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM09 GM11
universe u v w t

/-- The replacing paths have drawings on the original edge lines,
with compatible maps at every centre and at every support intersection. -/
theorem exists_subdivision_path_drawings
    {α : Type u} {β : Type v} {ν : Type w} {S : Type t}
    [TopologicalSpace S] [T2Space S] {N : Graph α β} {H : SimpleGraph ν}
    (c : ν → α) (hc : Function.Injective c) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val=s(a,b) ∧ H.Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) :
    ∃ D : ∀ e : H.edgeSet, GraphDrawing (P e) S,
      (∀ e, (D e).drawing.U=closure (Γ.iso.edgeEquiv e).val) ∧
      (∀ e v (x : V(P e)), x.val=c v → ((D e).iso.vertexEquiv x).val=simpleDrawingVertex Γ v) ∧
      (∀ e, (D e).drawing.U ∩ Γ.drawing.V ⊆ (D e).drawing.V) ∧
      (∀ e f, e ≠ f → (D e).drawing.U ∩ (D f).drawing.U ⊆ Γ.drawing.V) := by
  classical
  choose a b he hAdj hPath hRange using hPaths
  have hLink (e : H.edgeSet) : Γ.drawing.toGraph.IsLink (Γ.iso.edgeEquiv e).val
      (simpleDrawingVertex Γ (a e)) (simpleDrawingVertex Γ (b e)) :=
    (Γ.iso.isLink_iff e ⟨a e,mem_univ _⟩ ⟨b e,mem_univ _⟩).mp ⟨he e,e.property⟩
  have hNe (e : H.edgeSet) : simpleDrawingVertex Γ (a e) ≠ simpleDrawingVertex Γ (b e) :=
    (simpleDrawingVertex_injective Γ).ne (hAdj e).ne
  have hL (e : H.edgeSet) : IsLineWithEnds (closure (Γ.iso.edgeEquiv e).val)
      (simpleDrawingVertex Γ (a e)) (simpleDrawingVertex Γ (b e)) :=
    isLine_closure (Γ.iso.edgeEquiv e).property (hNe e) (hLink e).2.2.2
  choose D hDU hLeft hRight using fun e => exists_path_drawing_on_line
    (hPath e) (hc.ne (hAdj e).ne) (hL e) (hNe e)
  refine ⟨D,hDU,?_,?_,?_⟩
  · intro e v x hxc
    have hxRange : c v ∈ V(P e) ∩ range c := ⟨hxc ▸ x.property,mem_range_self v⟩
    have hxPair : c v ∈ ({c (a e),c (b e)} : Set α) := hRange e ▸ hxRange
    rcases hxPair with hx | hx
    · have hv : v=a e := hc hx
      subst v
      exact hLeft e x hxc
    · rw [mem_singleton_iff] at hx
      have hv : v=b e := hc hx
      subst v
      exact hRight e x hxc
  · intro e y hy
    have hyEnds : y ∈ ({simpleDrawingVertex Γ (a e),simpleDrawingVertex Γ (b e)} : Set S) :=
      (hLink e).2.2.2 ▸ (show y ∈ closure (Γ.iso.edgeEquiv e).val ∩ Γ.drawing.V from ⟨hDU e ▸
        hy.1,hy.2⟩)
    rcases hyEnds with hyA | hyB
    · have hPoint : simpleDrawingVertex Γ (a e) ∈ (D e).drawing.V :=
        hLeft e ⟨c (a e),(hPath e).left_mem⟩ rfl ▸
          ((D e).iso.vertexEquiv ⟨c (a e),(hPath e).left_mem⟩).property
      exact hyA.symm ▸ hPoint
    · rw [mem_singleton_iff] at hyB
      have hPoint : simpleDrawingVertex Γ (b e) ∈ (D e).drawing.V :=
        hRight e ⟨c (b e),(hPath e).right_mem⟩ rfl ▸
          ((D e).iso.vertexEquiv ⟨c (b e),(hPath e).right_mem⟩).property
      exact hyB.symm ▸ hPoint
  · intro e f hne
    rw [hDU e,hDU f]
    exact closure_inter_subset_V (Γ.iso.edgeEquiv e).property (Γ.iso.edgeEquiv f).property
      (fun h => hne (Γ.iso.edgeEquiv.injective (Subtype.ext h)))

/-- A centre point on a replacing path's support comes from a vertex
of that abstract path. -/
theorem source_centre_mem_of_path_drawing_support
    {α : Type u} {β : Type v} {ν : Type w} {S : Type t}
    [TopologicalSpace S] {N : Graph α β} {H : SimpleGraph ν}
    (c : ν → α) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val=s(a,b) ∧ H.Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b))
    (Γ : GraphDrawing (Graph.ofSimpleGraph H) S)
    (D : ∀ e : H.edgeSet, GraphDrawing (P e) S)
    (hDU : ∀ e, (D e).drawing.U=closure (Γ.iso.edgeEquiv e).val)
    (e : H.edgeSet) (v : ν) (hv : simpleDrawingVertex Γ v ∈ (D e).drawing.U) : c v ∈ V(P e) := by
  obtain ⟨a,b,he,_,hPath⟩ := hPaths e
  have hLink := (Γ.iso.isLink_iff e ⟨a,mem_univ _⟩ ⟨b,mem_univ _⟩).mp ⟨he,e.property⟩
  have hvBase : simpleDrawingVertex Γ v ∈ Γ.drawing.V := (Γ.iso.vertexEquiv ⟨v,mem_univ _⟩).property
  have hvPair : simpleDrawingVertex Γ v ∈ ({simpleDrawingVertex Γ a,simpleDrawingVertex Γ b} : Set
    S) :=
    hLink.2.2.2 ▸ ⟨hDU e ▸ hv,hvBase⟩
  rcases hvPair with hvA | hvB
  · have hEq : v=a := simpleDrawingVertex_injective Γ hvA
    exact hEq.symm ▸ hPath.left_mem
  · rw [mem_singleton_iff] at hvB
    have hEq : v=b := simpleDrawingVertex_injective Γ hvB
    exact hEq.symm ▸ hPath.right_mem

end GraphMinor.GM16
