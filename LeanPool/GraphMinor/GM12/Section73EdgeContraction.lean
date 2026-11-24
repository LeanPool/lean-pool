/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ContractDrawing
public import LeanPool.GraphMinor.GM12.Section73ArcCollapse
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Contracting an edge with no parallel mate

In XII (7.3), page 261, each edge of the radial star has distinct
ends and no parallel mate. These conditions imply that every other
edge meets its closure in at most one point. Contract its interval
parameterization, then assemble the image edges into a drawing.
A prescribed closed set disjoint from the edge closure stays fixed.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Distinct edges meet a nonparallel edge in at most one point.
This supplies the intersection condition for the radial contractions
in XII (7.3), page 261. -/
theorem closure_inter_subsingleton_of_unique_link
    {S : Type*} [TopologicalSpace S] {K : Drawing S} {e : Set S} {v u : S}
    (hel : K.toGraph.IsLink e v u) (hvu : v ≠ u)
    (hlines : ∀ g ∈ K.E, ∃ a b : S, IsLineWithEnds (closure g) a b ∧
      closure g ∩ K.V = {a, b})
    (hunique : ∀ g ∈ K.E, K.toGraph.IsLink g v u → g = e) :
    ∀ g ∈ K.E, g ≠ e → (closure g ∩ closure e).Subsingleton := by
  intro g hg hge
  have hnotboth : ¬ (v ∈ closure g ∧ u ∈ closure g) := by
    rintro ⟨hvg, hug⟩
    obtain ⟨a, b, _, hcap⟩ := hlines g hg
    have hva : v = a ∨ v = b := hcap.subset ⟨hvg, hel.2.1⟩
    have hua : u = a ∨ u = b := hcap.subset ⟨hug, hel.2.2.1⟩
    have hcap' : closure g ∩ K.V = {v, u} := by
      rcases hva with rfl | rfl <;> rcases hua with h | h
      · exact False.elim (hvu h.symm)
      · simpa only [h] using hcap
      · simpa only [h, pair_comm] using hcap
      · exact False.elim (hvu h.symm)
    exact hge (hunique g hg ⟨hg, hel.2.1, hel.2.2.1, hcap'⟩)
  intro x hx y hy
  have hxV := closure_inter_subset_V hg hel.1 hge hx
  have hyV := closure_inter_subset_V hg hel.1 hge hy
  rcases hel.2.2.2.subset ⟨hx.2, hxV⟩ with rfl | rfl <;>
    rcases hel.2.2.2.subset ⟨hy.2, hyV⟩ with rfl | rfl
  · rfl
  · exact False.elim (hnotboth ⟨hx.1, hy.1⟩)
  · exact False.elim (hnotboth ⟨hy.1, hx.1⟩)
  · rfl

/-- Realize one radial-star contraction by a continuous surjection
and an image drawing. Only the chosen edge closure is identified.
This is one edge of the contraction in XII (7.3), page 261. -/
theorem exists_edge_contraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {e : Set S} {v u : S}
    (hel : K.toGraph.IsLink e v u) (hvu : v ≠ u)
    (hlines : ∀ g ∈ K.E, ∃ a b : S, IsLineWithEnds (closure g) a b ∧
      closure g ∩ K.V = {a, b})
    (hunique : ∀ g ∈ K.E, K.toGraph.IsLink g v u → g = e)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (closure e) F) :
    ∃ (f : C(S, S)) (H : Drawing S),
      Function.Surjective f ∧ (∀ x ∈ F, f x = x) ∧
      (∀ x ∈ closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ closure e ∧ y ∈ closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' (K.E \ {e}) := by
  obtain ⟨p, hp0, hp1⟩ := isLine_closure hel.1 hvu hel.2.2.2
  let a : unitInterval → S := fun t => (p t).val
  have ha : IsArcMap a := ⟨continuous_subtype_val.comp p.continuous,
    fun _ _ h => p.injective (Subtype.ext h)⟩
  have hrange : range a = closure e := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (p t).property
    · intro hx
      exact ⟨p.symm ⟨x, hx⟩, congrArg Subtype.val (p.apply_symm_apply ⟨x, hx⟩)⟩
  obtain ⟨f, hsurj, hfix, hconst, hfibre⟩ := exists_arc_collapse hS ha hF (hrange ▸ havoid)
  have hcollapse : ∀ x ∈ closure e, f x = v := by
    intro x hx
    exact (hconst x (hrange.symm ▸ hx)).trans hp0
  have hfibre' : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ closure e ∧ y ∈ closure e) := by
    simpa only [hrange] using hfibre
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_drawing_of_edge_collapse hel.1 hel.2.1
    (hel.2.2.2.superset (Or.inl rfl)).1 hlines
    (closure_inter_subsingleton_of_unique_link hel hvu hlines hunique) f hcollapse hfibre'
  exact ⟨f, H, hsurj, hfix, hcollapse, hfibre', hHU, hHV, hHE⟩

end GraphMinor.GM12
