/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4Claim1
public import LeanPool.GraphMinor.GM16.ModelInducedTangle
import LeanPool.GraphMinor.GM16.Section4GridMinor
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# The wall-induced tangle is contained in the original tangle

This proves the paragraph following Step (2) in XVI (4.2), page 53.
The large side of every induced separation contains the images of a
whole wall row. Its reverse therefore cannot belong to the original
tangle, by Step (2). The first tangle axiom places the separation itself
in that tangle. The wall tangle and the controlled wall minor are both
constructed by the proved earlier steps.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10 GM15
universe u v

private theorem induced_wall_subset {θ : ℕ} {α : Type u} {β : Type v}
    {G : Graph α β} {θG : ℕ} {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsGraphTangle G θG Tstar) (hθG : θ ≤ θG)
    {ηv : Fin (2 * θ + 1) × Fin θ → Set α}
    {ηe : Sym2 (Fin (2 * θ + 1) × Fin θ) → β}
    (hModel : IsMinorModel (sphereWallGraph θ) G ηv ηe)
    (hNoRow : ∀ A B : Hypergraph α β, (A,B) ∈ Tstar → separationOrder A B ≤ 2 * θ →
      ∀ j : Fin θ, ¬ ηe '' E(sphereWallRow θ j) ⊆ A.edgeSet)
    {K : Graph (Set α) β} (hVK : V(K).Finite) (hEK : E(K).Finite)
    (hImage : Hypergraph.ofGraph K hVK hEK = imageHypergraph ηv ηe
      (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _))) :
    inducedTangle (Hypergraph.ofGraph G hT.finite_V hT.finite_E)
      (Hypergraph.ofGraph K hVK hEK) (imageHypergraphTangle ηv ηe (sphereWallTangle θ)) θ ⊆ Tstar
        := by
  rintro ⟨A,B⟩ hAB
  obtain ⟨p, hp, hEdge⟩ := hAB.2.2
  obtain ⟨⟨A₀,B₀⟩, hSrc, hPair⟩ := hp
  have hA := congrArg Prod.fst hPair
  have hAE : ηe '' A₀.edgeSet = A.edgeSet ∩ E(K) :=
    (congrArg Hypergraph.edgeSet hA).trans hEdge
  have hEN : E(K) = ηe '' E(sphereWallGraph θ) := congrArg Hypergraph.edgeSet hImage
  obtain ⟨j, hj⟩ := hSrc.2.2
  have hBig : ηe '' E(sphereWallRow θ j) ⊆ B.edgeSet := by
    rintro _ ⟨e, heRow, rfl⟩
    have heWall := (sphereWallRow_le θ j).edgeSet_mono heRow
    have heG := hModel.edge_mem e heWall
    have heK : ηe e ∈ E(K) := hEN.symm ▸ mem_image_of_mem ηe heWall
    have heNotA : ηe e ∉ A.edgeSet := by
      intro heA
      obtain ⟨e₀, he₀, hEq⟩ := hAE.symm ▸ (show ηe e ∈ A.edgeSet ∩ E(K) from ⟨heA,heK⟩)
      have he₀Wall := hSrc.1.left_le.edgeSet_subset he₀
      have hEq' : e₀ = e := hModel.edge_injOn he₀Wall heWall hEq
      have heA₀ : e ∈ A₀.edgeSet := hEq' ▸ he₀
      exact hSrc.1.notMem_edgeSet_left (hj heRow) heA₀
    have heAB : ηe e ∈ A.edgeSet ∪ B.edgeSet := hAB.1.edgeSet_union.symm ▸ heG
    exact heAB.resolve_left heNotA
  have hOrd : separationOrder A B < θG := hAB.2.1.trans_le hθG
  rcases hT.isTangle.axiom1 hAB.1 hOrd with hm | hm
  · exact hm
  · have hOrdSwap : separationOrder B A ≤ 2 * θ := by
      rw [separationOrder_comm]
      have hθOrd : separationOrder A B < θ := hAB.2.1
      omega
    exact (hNoRow B A hm hOrdSwap j hBig).elim

/-- The wall minor and its conformal induced tangle in XVI (4.2),
page 53. All graph and tangle steps are proved, with no statement
hypotheses. -/
theorem exists_conformal_wall_minor (θ : ℕ) (hθ : 2 ≤ θ) :
    ∃ θstar : ℕ, 1 ≤ θstar ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θG : ℕ)
        (Tstar : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θG Tstar),
        θstar ≤ θG →
        ∃ (ηv : Fin (2 * θ + 1) × Fin θ → Set α)
          (ηe : Sym2 (Fin (2 * θ + 1) × Fin θ) → β),
          IsMinorModel (sphereWallGraph θ) G ηv ηe ∧
          ∃ (K : Graph (Set α) β) (hVK : V(K).Finite) (hEK : E(K).Finite),
            IsMinor K G ∧
            Hypergraph.ofGraph K hVK hEK = imageHypergraph ηv ηe
              (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)) ∧
            IsTangle (Hypergraph.ofGraph K hVK hEK) θ (imageHypergraphTangle ηv ηe
              (sphereWallTangle θ)) ∧
            IsTangle (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ
              (inducedTangle (Hypergraph.ofGraph G hT.finite_V hT.finite_E)
                (Hypergraph.ofGraph K hVK hEK) (imageHypergraphTangle ηv ηe
                  (sphereWallTangle θ)) θ) ∧
            inducedTangle (Hypergraph.ofGraph G hT.finite_V hT.finite_E)
              (Hypergraph.ofGraph K hVK hEK) (imageHypergraphTangle ηv ηe
                (sphereWallTangle θ)) θ ⊆ Tstar := by
  obtain ⟨θ₀, hθ₀, hWall⟩ := exists_wall_minor_no_small_row θ (by omega)
  refine ⟨θ₀ + θ, by omega, ?_⟩
  intro α β G θG Tstar hT hOrd
  obtain ⟨ηv, ηe, hModel, hNoRow⟩ := hWall G θG Tstar hT (by omega)
  obtain ⟨K, hVK, hEK, hMinor, hImage, hTK, hTG⟩ := exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hT.finite_V hT.finite_E hModel hθ (theorem_4_2_claim_1 hθ)
  exact ⟨ηv, ηe, hModel, K, hVK, hEK, hMinor, hImage, hTK, hTG,
    induced_wall_subset hT (by omega) hModel hNoRow hVK hEK hImage⟩

end GraphMinor.GM16
