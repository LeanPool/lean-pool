/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.DrawingOps
import Mathlib.Logic.Equiv.Set

/-!
# Transporting a drawing as a graph drawing

An injective continuous map on the point set of a drawing preserves
vertices, edges, and their ends. This lets us use a disc chart to view
the annulus in XVI (8.1), Claim (11), as a drawing in the plane.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11
universe u v
variable {S : Type u} {T : Type v}
variable [TopologicalSpace S] [T2Space S] [CompactSpace S] [Nonempty S]
variable [TopologicalSpace T] [T2Space T]

omit [T2Space S] in
/-- Transport preserves the abstract graph as well as its point set. -/
theorem exists_graphDrawing_transport (D : Drawing S) {f : S → T}
    (hf : Continuous f) (hi : InjOn f D.U) :
    ∃ Γ : GraphDrawing D.toGraph T,
      Γ.drawing.U = f '' D.U ∧ Γ.drawing.V = f '' D.V ∧
      (∀ x : D.toGraph.vertexSet, (Γ.iso.vertexEquiv x).val = f x.val) ∧
      (∀ e : D.toGraph.edgeSet, (Γ.iso.edgeEquiv e).val = f '' e.val) := by
  classical
  obtain ⟨D', hU, hV, hE, hcl⟩ := exists_transport D hf hi
  have hiE : InjOn (image f) D.E := by
    intro e he e' he' heq
    have heU : e ⊆ D.U := subset_trans subset_closure (D.closure_subset_U he)
    have he'U : e' ⊆ D.U := subset_trans subset_closure (D.closure_subset_U he')
    apply subset_antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := heq ▸ (mem_image_of_mem f hx)
      exact hi (he'U hy) (heU hx) hxy ▸ hy
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := heq.symm ▸ (mem_image_of_mem f hx)
      exact hi (heU hy) (he'U hx) hxy ▸ hy
  let ev : D.V ≃ D'.V :=
    (Equiv.Set.imageOfInjOn f D.V (hi.mono D.V_subset_U)).trans
      (Set.equivOfEq hV.symm)
  let ee : D.E ≃ D'.E :=
    (Equiv.Set.imageOfInjOn (image f) D.E hiE).trans (Set.equivOfEq hE.symm)
  have hv (x : D.V) : (ev x).val = f x.val := rfl
  have he (e : D.E) : (ee e).val = f '' e.val := rfl
  have hlink (e : D.toGraph.edgeSet) (x y : D.toGraph.vertexSet) :
      D.toGraph.IsLink e x y ↔ D'.toGraph.IsLink (ee e) (ev x) (ev y) := by
    change (e.val ∈ D.E ∧ x.val ∈ D.V ∧ y.val ∈ D.V ∧
      closure e.val ∩ D.V = {x.val, y.val}) ↔
      ((f '' e.val) ∈ D'.E ∧ f x.val ∈ D'.V ∧ f y.val ∈ D'.V ∧
      closure (f '' e.val) ∩ D'.V = {f x.val, f y.val})
    have heD : e.val ∈ D.E := e.prop
    have hxD : x.val ∈ D.V := x.prop
    have hyD : y.val ∈ D.V := y.prop
    have heD' : f '' e.val ∈ D'.E := (ee e).prop
    have hxD' : f x.val ∈ D'.V := (ev x).prop
    have hyD' : f y.val ∈ D'.V := (ev y).prop
    simp only [heD, hxD, hyD, heD', hxD', hyD', true_and]
    rw [hV, hcl e.val heD]
    rw [← hi.image_inter (D.closure_subset_U e.prop) D.V_subset_U,
      ← image_pair f x.val y.val]
    exact (hi.image_eq_image_iff (s₁ := closure e.val ∩ D.V)
      (s₂ := {x.val, y.val})
      (inter_subset_right.trans D.V_subset_U)
      (by intro z hz; rcases hz with hz | hz
          · exact hz ▸ D.V_subset_U x.prop
          · exact hz ▸ D.V_subset_U y.prop)).symm
  exact ⟨⟨D', ⟨ev, ee, hlink⟩⟩, hU, hV, hv, he⟩

end GraphMinor.GM16
