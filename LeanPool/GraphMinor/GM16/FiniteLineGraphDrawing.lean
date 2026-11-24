/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.FiniteLineDrawing
public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The graph carried by a finite family of lines

The finite-line construction produces a topological drawing. Its
vertices are in bijection with the original graph vertices, and each
open line gives one edge. The endpoint conditions identify the ends
of these edges. This supplies an explicit graph isomorphism for the
wall and subdivision drawings in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology GraphMinor.Surface GraphMinor.GM11
universe u v w

/-- Draw a finite loopless graph from prescribed lines. The returned
isomorphism has the prescribed vertex map and edge closures. -/
theorem exists_graphDrawing_of_finite_lines
    {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (f : α → S) (hf : InjOn f V(G)) (L : β → Set S)
    (hNoLoop : ∀ e v, ¬ G.IsLoopAt e v)
    (hLine : ∀ e ∈ E(G), ∀ a b, G.IsLink e a b → IsLineWithEnds (L e) (f a) (f b))
    (hVertex : ∀ e ∈ E(G), ∀ v ∈ V(G), f v ∈ L e → G.Inc e v)
    (hMeet : ∀ e ∈ E(G), ∀ d ∈ E(G), e ≠ d → L e ∩ L d ⊆ f '' V(G)) :
    ∃ Γ : GraphDrawing G S,
      Γ.drawing.V = f '' V(G) ∧
      (∀ v : V(G), (Γ.iso.vertexEquiv v).val = f v.val) ∧
      (∀ e : E(G), closure (Γ.iso.edgeEquiv e).val = L e.val) := by
  classical
  let : Finite E(G) := hEG.to_subtype
  have hEndsExists (e : E(G)) : ∃ a b, G.IsLink e.val a b :=
    G.exists_isLink_of_mem_edgeSet e.property
  choose a b hlink using hEndsExists
  have hLe (e : E(G)) : IsLineWithEnds (L e.val) (f (a e)) (f (b e)) :=
    hLine e.val e.property (a e) (b e) (hlink e)
  have hNe (e : E(G)) : f (a e) ≠ f (b e) := by
    intro heq
    have hab := hf (hlink e).left_mem (hlink e).right_mem heq
    exact hNoLoop e.val (b e) (hab ▸ hlink e)
  have hEnds (e : E(G)) : L e.val ∩ (f '' V(G)) = {f (a e),f (b e)} := by
    apply Subset.antisymm
    · rintro x ⟨hxL,v,hv,rfl⟩
      rcases (hVertex e.val e.property v hv hxL).eq_or_eq_of_isLink (hlink e) with heq | heq
      · exact Or.inl (congrArg f heq)
      · exact Or.inr (congrArg f heq)
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨(hLe e).left_mem, mem_image_of_mem f (hlink e).left_mem⟩
      · rw [mem_singleton_iff] at hx
        subst x
        exact ⟨(hLe e).right_mem, mem_image_of_mem f (hlink e).right_mem⟩
  obtain ⟨D,hDU,hDV,hDE⟩ := exists_drawing_of_finite_lines
    (Set.finite_univ : (Set.univ : Set E(G)).Finite) (hVG.image f)
    (fun e : E(G) => f (a e)) (fun e : E(G) => f (b e)) (fun e : E(G) => L e.val)
    (fun e _ => hLe e) (fun e _ => hNe e) (fun e _ => hEnds e)
    (fun e _ d _ hne => hMeet e.val e.property d.val d.property (fun heq => hne (Subtype.ext heq)))
  let openEdge : E(G) → Set S := fun e => L e.val \ {f (a e),f (b e)}
  have hOpenInj : Function.Injective openEdge := by
    intro e d heq
    by_contra hne
    obtain ⟨x,hx⟩ := (isPathConnected_sdiff_pair (hLe e)).nonempty
    have hxd : x ∈ openEdge d := heq ▸ hx
    have hxZ := hMeet e.val e.property d.val d.property
      (fun heq => hne (Subtype.ext heq)) ⟨hx.1,hxd.1⟩
    exact hx.2 ((hEnds e) ▸ (show x ∈ L e.val ∩ f '' V(G) from ⟨hx.1,hxZ⟩))
  have hRange : D.E = range openEdge := by simpa only [image_univ] using hDE
  let ev : V(G) ≃ D.V := (Equiv.Set.imageOfInjOn f V(G) hf).trans (Set.equivOfEq hDV.symm)
  let ee : E(G) ≃ D.E := (Equiv.ofInjective openEdge hOpenInj).trans (Set.equivOfEq hRange.symm)
  have hEV (v : V(G)) : (ev v).val = f v.val := rfl
  have hEE (e : E(G)) : (ee e).val = openEdge e := rfl
  have hCl (e : E(G)) : closure (openEdge e) = L e.val := closure_sdiff_pair (hLe e)
  have hIso (e : E(G)) (u v : V(G)) :
      G.IsLink e.val u.val v.val ↔ D.toGraph.IsLink (ee e).val (ev u).val (ev v).val := by
    change G.IsLink e.val u.val v.val ↔
      (openEdge e ∈ D.E ∧ f u.val ∈ D.V ∧ f v.val ∈ D.V ∧
        closure (openEdge e) ∩ D.V = {f u.val,f v.val})
    have heD : openEdge e ∈ D.E := (ee e).property
    have huD : f u.val ∈ D.V := (ev u).property
    have hvD : f v.val ∈ D.V := (ev v).property
    simp only [heD,huD,hvD,true_and]
    rw [hCl,hDV,hEnds]
    rw [(hlink e).isLink_iff, Set.pair_eq_pair_iff]
    constructor
    · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
      · exact Or.inl ⟨congrArg f hu,congrArg f hv⟩
      · exact Or.inr ⟨congrArg f hv,congrArg f hu⟩
    · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
      · exact Or.inl ⟨hf (hlink e).left_mem u.property hu,hf (hlink e).right_mem v.property hv⟩
      · exact Or.inr ⟨hf (hlink e).left_mem v.property hv,hf (hlink e).right_mem u.property hu⟩
  exact ⟨⟨D,⟨ev,ee,hIso⟩⟩,hDV,hEV,fun e => hCl e⟩

end GraphMinor.GM16
