/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.EvenCircuit
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# A walk in a connected drawing

For the base case of XII (7.4), pages 262--263, the old two-cell
drawing has a connected point set. Any two of its vertices are
therefore joined by a graph walk. Otherwise the reachable vertices
and their edge closures, and the remaining vertices and their edge
closures, form two disjoint closed pieces of the point set. This
supplies a non-loop edge at the vertex when another vertex exists.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Topological connectedness of a finite drawing gives graph
walks between its vertices. -/
theorem exists_walk_of_isPreconnected_U
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hconn : IsPreconnected Γ.U) {a b : S} (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) :
    Nonempty (GraphWalk Γ.toGraph a b) := by
  classical
  let : Nonempty S := ⟨a⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  by_contra hno
  let A : Set S := {x | Nonempty (GraphWalk Γ.toGraph a x)}
  have haA : a ∈ A := ⟨.nil ha⟩
  have hbA : b ∉ A := hno
  have hAV : A ⊆ Γ.V := by
    rintro x ⟨W⟩
    exact mem_V_of_mem_support W W.end_mem_support
  have hstep : ∀ f ∈ Γ.E, ∀ c, γ f (endOf c) ∈ A → γ f (endOf (!c)) ∈ A := by
    rintro f hf c ⟨W⟩
    have hl := isLink_ends hγ (Drawing.IsSubdrawing.refl Γ) hf c
    exact ⟨W.append (.cons hl (.nil hl.2.2.1))⟩
  let side : Set S → Prop := fun f => γ f (endOf false) ∈ A
  have hside : ∀ f ∈ Γ.E, ∀ x ∈ closure f, x ∈ Γ.V → (side f ↔ x ∈ A) := by
    intro f hf x hxf hxV
    obtain ⟨c, rfl⟩ := exists_end_eq hγ hf hxV hxf
    cases c with
    | false => exact Iff.rfl
    | true => exact ⟨hstep f hf false, hstep f hf true⟩
  let X := A ∪ ⋃ f ∈ {f | f ∈ Γ.E ∧ side f}, closure f
  let Y := (Γ.V \ A) ∪ ⋃ f ∈ {f | f ∈ Γ.E ∧ ¬ side f}, closure f
  have hfin : ∀ P : Set S → Prop, {f | f ∈ Γ.E ∧ P f}.Finite :=
    fun P => Γ.finite_edges.subset fun _ h => h.1
  have hXc : IsClosed X := (Γ.finite_V.subset hAV).isClosed.union
    ((hfin _).isClosed_biUnion fun _ _ => isClosed_closure)
  have hYc : IsClosed Y := (Γ.finite_V.subset sdiff_subset).isClosed.union
    ((hfin _).isClosed_biUnion fun _ _ => isClosed_closure)
  have hdis : Disjoint X Y := by
    apply disjoint_left.mpr
    rintro x (hx₁ | hx₁) (hx₂ | hx₂)
    · exact hx₂.2 hx₁
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₂
      exact hf.2 ((hside f hf.1 x hxf (hAV hx₁)).mpr hx₁)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₁
      exact hx₂.2 ((hside f hf.1 x hxf hx₂.1).mp hf.2)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₁
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx₂
      have hfg : f ≠ g := fun h => hg.2 (h ▸ hf.2)
      have hxV : x ∈ Γ.V := closure_inter_subset_V hf.1 hg.1 hfg ⟨hxf, hxg⟩
      exact hg.2 ((hside g hg.1 x hxg hxV).mpr ((hside f hf.1 x hxf hxV).mp hf.2))
  have hcover : Γ.U ⊆ X ∪ Y := by
    intro x hx
    rw [Γ.U_eq] at hx
    rcases hx with hxV | hxE
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr (Or.inl ⟨hxV, hxA⟩)
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxE
      by_cases hfside : side f
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfside⟩, hxf⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfside⟩, hxf⟩))
  obtain ⟨x, _, hxX, hxY⟩ := isPreconnected_closed_iff.mp hconn X Y hXc hYc hcover
    ⟨a, Γ.V_subset_U ha, Or.inl haA⟩ ⟨b, Γ.V_subset_U hb, Or.inl ⟨hb, hbA⟩⟩
  exact disjoint_left.mp hdis hxX hxY

end GraphMinor.GM12
