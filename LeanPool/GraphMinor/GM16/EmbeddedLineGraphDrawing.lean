/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.FiniteLineGraphDrawing
import LeanPool.GraphMinor.GM16.LineImageEmbedding

/-!
# Finite line drawings after an embedding

Compose the vertex map with the embedding and replace every line by
its image. Injectivity preserves all incidence and intersection
conditions. The finite-line graph-drawing theorem then constructs the
drawing in the new space with the same prescribed maps. This moves
the wall's coordinate drawing into the sphere in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology GraphMinor.Surface
universe u v w w'

/-- Carry prescribed lines into another space before constructing the
graph drawing. The source and target spaces may have different universes. -/
theorem exists_graphDrawing_of_embedded_lines
    {α : Type u} {β : Type v} {S : Type w} {T : Type w'}
    [TopologicalSpace S] [TopologicalSpace T] [T2Space T]
    (G : Graph α β) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (f : α → S) (hf : InjOn f V(G)) (L : β → Set S)
    (hNoLoop : ∀ e v, ¬ G.IsLoopAt e v)
    (hLine : ∀ e ∈ E(G), ∀ a b, G.IsLink e a b → IsLineWithEnds (L e) (f a) (f b))
    (hVertex : ∀ e ∈ E(G), ∀ v ∈ V(G), f v ∈ L e → G.Inc e v)
    (hMeet : ∀ e ∈ E(G), ∀ d ∈ E(G), e ≠ d → L e ∩ L d ⊆ f '' V(G))
    (j : S → T) (hj : IsEmbedding j) :
    ∃ Γ : GraphDrawing G T,
      Γ.drawing.V = (j ∘ f) '' V(G) ∧
      (∀ v : V(G), (Γ.iso.vertexEquiv v).val = j (f v.val)) ∧
      (∀ e : E(G), closure (Γ.iso.edgeEquiv e).val = j '' L e.val) := by
  apply exists_graphDrawing_of_finite_lines G hVG hEG (j ∘ f)
    (fun x hx y hy heq => hf hx hy (hj.injective heq)) (fun e => j '' L e) hNoLoop
  · intro e he a b hLink
    exact isLineWithEnds_image_embedding hj (hLine e he a b hLink)
  · intro e he v hv hPoint
    obtain ⟨x,hx,heq⟩ := hPoint
    have hxf : x = f v := hj.injective heq
    exact hVertex e he v hv (hxf ▸ hx)
  · intro e he d hd hne x hx
    obtain ⟨y,hy,hyx⟩ := hx.1
    obtain ⟨z,hz,hzx⟩ := hx.2
    have hyz : y = z := hj.injective (hyx.trans hzx.symm)
    have hOld := hMeet e he d hd hne ⟨hy,hyz.symm ▸ hz⟩
    obtain ⟨v,hv,hfy⟩ := hOld
    exact ⟨v,hv,(congrArg j hfy).trans hyx⟩

end GraphMinor.GM16
