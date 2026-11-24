/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.Surface.CutParallel
public import LeanPool.GraphMinor.GM19.CutMap

/-!
# Cutting in stages

The surface `Σ'` in the proof of Graph Minors VII, (4.6) (page 225) is got by cutting along a
forest. We do this one edge at a time. `IsCutAlongSet F θ` lists what a cut along `F` must satisfy,
and
`IsCutAlongSet.comp` says that two cuts in a row make a cut along the union.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

variable {S S₁ S₂ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] [TopologicalSpace S₂]

/-- `θ` cuts `S` along `F`, as in `IsCutAlongGraph` but for a set: `θ` is a quotient map with finite
fibers, the boundary of the cut surface lies over `bd S ∪ F`, and `θ` is injective off that
boundary. -/
structure IsCutAlongSet (F : Set S) (θ : S₁ → S) : Prop where
  isSurface : IsSurface S₁
  quotientMap : Topology.IsQuotientMap θ
  preimage_bd : θ ⁻¹' (bd S ∪ F) = bd S₁
  interior_inj : ∀ x ∈ (bd S₁)ᶜ, ∀ y : S₁, θ x = θ y → x = y
  finite_fiber : ∀ x, (θ ⁻¹' {x}).Finite

/-- A cut along `F₁`, followed by a cut along the preimage of `F₂`, is a cut along `F₁ ∪ F₂`. -/
theorem IsCutAlongSet.comp {F₁ F₂ : Set S} {θ₁ : S₁ → S} {θ₂ : S₂ → S₁} (h₁ : IsCutAlongSet F₁ θ₁)
  (h₂ : IsCutAlongSet (θ₁ ⁻¹' F₂) θ₂) :
    IsCutAlongSet (F₁ ∪ F₂) (θ₁ ∘ θ₂) := by
  have hbd : (θ₁ ∘ θ₂) ⁻¹' (bd S ∪ (F₁ ∪ F₂)) = bd S₂ := by
    rw [← h₂.preimage_bd, ← h₁.preimage_bd, ← preimage_union, preimage_comp, union_assoc]
  refine ⟨h₂.isSurface, h₁.quotientMap.comp h₂.quotientMap, hbd, fun x hx y hxy => ?_, fun x => ?_⟩
  · have hx₁ : θ₂ x ∉ bd S₁ := fun h => hx (by
      rw [← h₂.preimage_bd]
      exact Or.inl h)
    exact h₂.interior_inj x hx y (h₁.interior_inj _ hx₁ _ hxy)
  · have : (θ₁ ∘ θ₂) ⁻¹' {x} = ⋃ y ∈ θ₁ ⁻¹' {x}, θ₂ ⁻¹' {y} := by
      ext z
      simp
    rw [this]
    exact (h₁.finite_fiber x).biUnion fun y _ => h₂.finite_fiber y

/-- A cut along a set is a cut along a graph with that set as its points, when the graph is proper
and has no isolated vertices. -/
theorem IsCutAlongSet.isCutAlongGraph {J : Drawing S} {θ : S₁ → S} (h : IsCutAlongSet J.U θ)
  (hp : J.IsProper) (hn : HasNoIsolatedVertices J) :
    IsCutAlongGraph J S₁ θ :=
  ⟨hp, hn, h.isSurface, h.quotientMap, h.preimage_bd, h.interior_inj, h.finite_fiber⟩

/-- The cut along an edge built by `exists_cut` is a cut along the closure of the edge. -/
theorem IsCutAlongSet.of_cutAlongEdge {G : Drawing S} {e : Set S} {a b c : ℕ} {θ : S₁
  → S} {G' : Drawing S₁} (hc : IsCutAlongEdge G e a b c S₁ θ G') : IsCutAlongSet (closure e) θ := by
  refine ⟨hc.isSurface, hc.quotientMap, hc.bd_eq.symm, fun x hx y hxy => ?_, hc.finite_fiber⟩
  refine (hc.inj x y hxy).resolve_right fun h => hx ?_
  rw [hc.bd_eq]
  exact Or.inr (subset_closure h)

/-- A cutting map of a compact surface along a closed set, such as the one given by `cutIArc`, is a
cut along that set. -/
theorem IsCutAlongSet.of_isCutting (hS₁ : IsSurface S₁) (hS : IsSurface S) {F : Set S}
  (hF : IsClosed F) {θ : S₁ → S} (hc : IsCutting θ F) : IsCutAlongSet F θ := by
  have : CompactSpace S₁ := hS₁.1
  have : T2Space S₁ := hS₁.2.1
  have : T2Space S := hS.2.1
  refine ⟨hS₁, hc.1.isClosedMap.isQuotientMap hc.1 hc.2.1, ?_, fun x hx y hxy => ?_,
    (GM19.IsCutting.isCutMap hc).2.2.2.1⟩
  · ext y
    constructor
    · rintro (h | h)
      · by_cases hyF : θ y ∈ F
        · exact hc.2.2.2.2 hyF
        · exact bd_lift hc hF h hyF
      · exact hc.2.2.2.2 h
    · intro hy
      by_cases hyF : θ y ∈ F
      · exact Or.inr hyF
      · exact Or.inl (bd_of_bd hc hF hy hyF)
  · have hxF : θ x ∉ F := fun h => hx (hc.2.2.2.2 h)
    exact hc.2.2.1 hxF (show θ y ∈ Fᶜ from hxy ▸ hxF) hxy

end GraphMinor.GM07
