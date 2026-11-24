/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.SimpleDrawingVertices
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM16.SubdivisionPathDrawings
import LeanPool.GraphMinor.GM16.SubdivisionCentreCover
import LeanPool.GraphMinor.GM16.FiniteDrawingUnion
import LeanPool.GraphMinor.GM16.DrawingFamilyCompatibility
import LeanPool.GraphMinor.GM16.GraphIsoUnion
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM09.Basic

/-!
# Drawing a subdivision on the original support

Draw the replacing paths on the original edge closures and glue
them at their common centre points. The source paths and target
drawings have compatible vertex maps and inverse maps, and their
edge sets are disjoint. Glue their graph isomorphisms. Since the
original graph has no isolated vertices, the paths cover all
centres. Their drawing has exactly the original support. This
supplies the drawing step in the final paragraph of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM09 GM11
universe u v w t

/-- A subdivision path system for a finite simple graph without isolated
vertices can be drawn on the original drawing's support, preserving centres. -/
theorem exists_subdivision_drawing
    {α : Type u} {β : Type v} {ν : Type w} [Finite ν] {S : Type t}
    [TopologicalSpace S] [T2Space S] {N : Graph α β} {H : SimpleGraph ν}
    (c : ν → α) (hc : Function.Injective c) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val=s(a,b) ∧ H.Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f, e ≠ f → Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c)
    (hVN : V(N)=range c ∪ ⋃ e, V(P e)) (hEN : E(N)=⋃ e, E(P e))
    (hNoIsolated : ∀ v, ∃ w, H.Adj v w)
    (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) :
    ∃ Γ' : GraphDrawing N S, Γ'.drawing.U=Γ.drawing.U ∧
      ∀ v (x : V(N)), x.val=c v → (Γ'.iso.vertexEquiv x).val=simpleDrawingVertex Γ v := by
  classical
  obtain ⟨D,hDU,hCentre,hZMeet,hMeet⟩ := exists_subdivision_path_drawings c hc P hPaths Γ
  have hPathOnly (e : H.edgeSet) : ∃ a b, e.val=s(a,b) ∧ IsGraphPathWithEnds N (P e) (c a) (c b)
    := by
    obtain ⟨a,b,he,_,hPath,_⟩ := hPaths e
    exact ⟨a,b,he,hPath⟩
  have hCover := subdivision_centres_subset_path_union c P hPathOnly hNoIsolated
  have hVN' : V(N)=⋃ e, V(P e) := hVN.trans (union_eq_self_of_subset_left hCover)
  have hBaseCover : Γ.drawing.V ⊆ ⋃ e, (D e).drawing.V := by
    intro x hx
    obtain ⟨v,rfl⟩ := range_simpleDrawingVertex Γ ▸ hx
    obtain ⟨e,hv⟩ := mem_iUnion.mp (hCover (mem_range_self v))
    have hPoint : simpleDrawingVertex Γ v ∈ (D e).drawing.V :=
      hCentre e v ⟨c v,hv⟩ rfl ▸ ((D e).iso.vertexEquiv ⟨c v,hv⟩).property
    exact mem_iUnion_of_mem e hPoint
  obtain ⟨J,hJU,hJV,hJE⟩ := exists_drawing_of_finite_drawings
    (Set.toFinite (univ : Set H.edgeSet)) Γ.drawing.finite_V (fun e => (D e).drawing)
    (fun e _ => hZMeet e) (fun e _ f _ hne => hMeet e f hne)
  simp only [mem_univ,iUnion_true] at hJU hJV hJE
  have hJV' : J.V=⋃ e, (D e).drawing.V := hJV.trans (union_eq_self_of_subset_left hBaseCover)
  have hSub (e : H.edgeSet) : (D e).drawing.IsSubdrawing J := by
    constructor
    · intro x hx
      exact hJV'.symm ▸ mem_iUnion_of_mem e hx
    · intro f hf
      exact hJE.symm ▸ mem_iUnion_of_mem e hf
  have hQ (e : H.edgeSet) : (D e).drawing.toGraph ≤ J.toGraph := toGraph_le_of_isSubdrawing (hSub e)
  have hP (e : H.edgeSet) : P e ≤ N := by
    obtain ⟨_,_,_,_,hp,_⟩ := hPaths e
    exact hp.le
  have hTarget (e f : H.edgeSet) (hne : e ≠ f) :
      (D e).drawing.U ∩ (D f).drawing.U ⊆ range (simpleDrawingVertex Γ) := by
    rw [range_simpleDrawingVertex]
    exact hMeet e f hne
  have hPointSource (e : H.edgeSet) (v : ν) (hv : simpleDrawingVertex Γ v ∈
    (D e).drawing.U) : c v ∈ V(P e) :=
    source_centre_mem_of_path_drawing_support c P
      (fun e => by obtain ⟨a,b,he,ha,hp,_⟩ := hPaths e; exact ⟨a,b,he,ha,hp⟩) Γ D hDU e v hv
  obtain ⟨hvF,hvB⟩ := drawing_family_vertex_maps_compatible P D c (simpleDrawingVertex Γ)
    (fun e f hne => (hInter e f hne).2) hTarget hPointSource hCentre
  have heF (i j : H.edgeSet) (e : β) (hi : e ∈ E(P i)) (hj : e ∈ E(P j)) :
      ((D i).iso.edgeEquiv ⟨e,hi⟩).val=((D j).iso.edgeEquiv ⟨e,hj⟩).val := by
    by_cases hij : i=j
    · subst j
      rfl
    exact ((disjoint_left.mp (hInter i j hij).1) hi hj).elim
  have heB (i j : H.edgeSet) (e : Set S) (hi : e ∈ (D i).drawing.E) (hj : e ∈ (D j).drawing.E) :
      ((D i).iso.edgeEquiv.symm ⟨e,hi⟩).val=((D j).iso.edgeEquiv.symm ⟨e,hj⟩).val := by
    by_cases hij : i=j
    · subst j
      rfl
    have hDisj := drawing_family_edges_disjoint (fun e => (D e).drawing) Γ.drawing.V hZMeet hMeet
      hij
    exact ((disjoint_left.mp hDisj) hi hj).elim
  obtain ⟨φ,hφV,_⟩ := exists_iso_of_subgraph_unions P (fun e => (D e).drawing.toGraph) hP hQ
    (fun e => (D e).iso) hVN' hEN hJV' hJE hvF hvB heF heB
  have hJU' : J.U=Γ.drawing.U := by
    rw [hJU,Γ.drawing.U_eq]
    apply congrArg (fun X : Set S => Γ.drawing.V ∪ X)
    ext x
    constructor
    · intro hx
      obtain ⟨e,hxe⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨(Γ.iso.edgeEquiv e).val,(Γ.iso.edgeEquiv e).property,hDU e ▸ hxe⟩
    · intro hx
      obtain ⟨e,he,hxe⟩ := mem_iUnion₂.mp hx
      let e₀ := Γ.iso.edgeEquiv.symm ⟨e,he⟩
      apply mem_iUnion_of_mem e₀
      rw [hDU e₀]
      have hMap : (Γ.iso.edgeEquiv e₀).val=e := congrArg Subtype.val
        (Γ.iso.edgeEquiv.apply_symm_apply ⟨e,he⟩)
      exact hMap.symm ▸ hxe
  refine ⟨⟨J,φ⟩,hJU',?_⟩
  intro v x hx
  obtain ⟨e,hv⟩ := mem_iUnion.mp (hCover (mem_range_self v))
  have hxEq : x=⟨c v,(hP e).vertexSet_mono hv⟩ := Subtype.ext hx
  rw [hxEq]
  exact (hφV e ⟨c v,hv⟩).trans (hCentre e v ⟨c v,hv⟩ rfl)

end GraphMinor.GM16
