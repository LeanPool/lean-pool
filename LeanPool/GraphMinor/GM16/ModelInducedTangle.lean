/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphSupportedTangle
public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM16.ModelContractionMaps
import LeanPool.GraphMinor.GM16.GraphIsoImage
import LeanPool.GraphMinor.GM10.Section6

/-!
# Inducing a tangle through a specified minor model

The tangle construction in XVI (4.2), pages 53–54, must retain the
chosen edge names. Realise the model by contraction with those maps,
relabel the tangle of the minor, and apply X (6.1). Injectivity is
required only on actual vertices and edges, so unused names cause
no extra assumption.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10 GM15
universe u v u' v'

/-- The branch-set map of a minor model is injective on its vertices. -/
theorem minorModel_vertexMap_injOn {α : Type u} {β : Type v} {ν : Type u'} {ε : Type v'}
    {H : Graph ν ε} {G : Graph α β} {ηv : ν → Set α} {ηe : ε → β}
    (h : IsMinorModel H G ηv ηe) : InjOn ηv V(H) := by
  intro a ha b hb heq
  by_contra hne
  obtain ⟨x,hx⟩ := h.vertex_nonempty a ha
  exact (disjoint_left.mp (h.vertex_disjoint a ha b hb hne)) hx (heq ▸ hx)

/-- Induce a tangle through a minor model, preserving its specified
vertex and edge maps, as in XVI (4.2), pages 53–54. -/
theorem exists_model_induced_tangle {α : Type u} {β : Type v} {ν : Type u'} {ε : Type v'}
    {H : Graph ν ε} {G : Graph α β} {ηv : ν → Set α} {ηe : ε → β}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (h : IsMinorModel H G ηv ηe) {θ : ℕ} (hθ : 2 ≤ θ)
    {T : Set (Hypergraph ν ε × Hypergraph ν ε)}
    (hT : IsTangle (Hypergraph.ofGraph H hVH hEH) θ T) :
    ∃ (K : Graph (Set α) β) (hVK : V(K).Finite) (hEK : E(K).Finite),
      IsMinor K G ∧
      Hypergraph.ofGraph K hVK hEK = imageHypergraph ηv ηe (Hypergraph.ofGraph H hVH hEH) ∧
      IsTangle (Hypergraph.ofGraph K hVK hEK) θ (imageHypergraphTangle ηv ηe T) ∧
      IsTangle (Hypergraph.ofGraph G hVG hEG) θ
        (inducedTangle (Hypergraph.ofGraph G hVG hEG) (Hypergraph.ofGraph K hVK hEK)
          (imageHypergraphTangle ηv ηe T) θ) := by
  obtain ⟨G', hG', C, hC, φ, hv, he⟩ := exists_contraction_realizing_model h
  let K := contract G' C
  have hVK : V(K).Finite := by
    let : Finite (V(H)) := hVH.to_subtype
    let : Finite (V(K)) := Finite.of_equiv _ φ.vertexEquiv
    exact Set.toFinite _
  have hEK : E(K).Finite := by
    let : Finite (E(H)) := hEH.to_subtype
    let : Finite (E(K)) := Finite.of_equiv _ φ.edgeEquiv
    exact Set.toFinite _
  have hMinor : IsMinor K G := ⟨G', hG', C, hC, rfl⟩
  have hImage : Hypergraph.ofGraph K hVK hEK = imageHypergraph ηv ηe (Hypergraph.ofGraph H hVH hEH)
    :=
    (imageHypergraph_of_iso hVH hEH hVK hEK φ ηv ηe hv he).symm
  have hTK : IsTangle (Hypergraph.ofGraph K hVK hEK) θ (imageHypergraphTangle ηv ηe T) := by
    rw [hImage]
    exact isTangle_imageHypergraphTangle_on ηv ηe (minorModel_vertexMap_injOn h) h.edge_injOn hT
  exact ⟨K, hVK, hEK, hMinor, hImage, hTK,
    GM10.theorem_6_1_proof hVG hEG hVK hEK hMinor hθ hTK⟩

end GraphMinor.GM16
