/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentOrient
public import LeanPool.GraphMinor.Surface.CutOArc
public import LeanPool.GraphMinor.Surface.Epstein

/-!
# Cutting a closed surface along a non-null-homotopic `O`-arc

Each piece of a closed connected surface, cut along an `O`-arc that is not null-homotopic, is
simpler than the surface
(`exists_cut_simpler`). The surface `cutOArc` leaves three cases. A piece that is a copy of the
surface would have no boundary, while
each piece has boundary. A piece that is a closed disc would give a closed disc that holds the
`O`-arc, and then the `O`-arc is
null-homotopic by `epstein`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

theorem exists_cut_simpler (hT : IsClosedSurface T) {F : Set T} (hF : IsOArc F)
  (hn : ¬ IsNullHomotopicOArc F) :
    ∃ (S' : Type) (_ : TopologicalSpace S') (ψ : S' → T), IsSurface S' ∧ IsCutting ψ F ∧
      ∀ C ∈ spaceComponents S', IsSimplerThan C T := by
  classical
  have hb : bd T = ∅ := eq_empty_of_forall_notMem fun x hx ↦ hx (hT.2.2 x)
  obtain ⟨S', tS', ψ, hS', hcut, hcase, harcs⟩ := cutOArc T F hT.isSurface inferInstance hF
    (by rw [hb]; exact disjoint_empty _)
  refine ⟨S', tS', ψ, hS', hcut, ?_⟩
  have hψ : IsCutMap ψ F := IsCutting.isCutMap hcut
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have : LocallyConnectedSpace S' := hS'.locallyConnected
  have : CompactSpace T := hT.1
  have hFne : F.Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨_, (φ 1).2⟩
  have hmeet : ∀ x : S', (connectedComponent x ∩ ψ ⁻¹' F).Nonempty := by
    intro x
    by_contra hne
    have hsub : connectedComponent x ⊆ ψ ⁻¹' Fᶜ := fun w hw hwF ↦ hne ⟨w, hw, hwF⟩
    have hop : IsOpen (ψ '' connectedComponent x) := isOpen_image_of_isCutMap hψ hsub
      isOpen_connectedComponent
    have hcl : IsClosed (ψ '' connectedComponent x) := (isClosed_connectedComponent.isCompact.image
      hψ.1).isClosed
    have huniv : ψ '' connectedComponent x = univ := IsClopen.eq_univ ⟨hcl, hop⟩ ⟨_,
      mem_image_of_mem _ mem_connectedComponent⟩
    obtain ⟨f, hf⟩ := hFne
    obtain ⟨w, hw, rfl⟩ := huniv.ge (mem_univ f)
    exact hsub hw hf
  have hmemC : ∀ {C}, C ∈ spaceComponents S' → ∃ x, C = connectedComponent x ∧ IsOpen C
    := fun {C} hC ↦ by
    rw [spaceComponents_eq] at hC
    obtain ⟨x, rfl⟩ := hC
    exact ⟨x, rfl, isOpen_connectedComponent⟩
  have hbS : ψ ⁻¹' F ⊆ bd S' := hψ.2.2.2.2
  rcases hcase with h | ⟨C₁, C₂, hne, hc, -, ⟨e⟩⟩ | ⟨C₁, C₂, hne, hc, hd⟩
  · exact h.2
  · exfalso
    have hC₂ : C₂ ∈ spaceComponents S' := by
      rw [hc]
      exact mem_insert_of_mem _ rfl
    obtain ⟨x, rfl, hop⟩ := hmemC hC₂
    obtain ⟨w, hw, hwF⟩ := hmeet x
    have hbw : (⟨w, hw⟩ : connectedComponent x) ∈ bd (connectedComponent x) := (mem_bd_sub hop).2
      (hbS hwF)
    have := (isInteriorPoint_homeomorph_iff e ⟨w, hw⟩).1 (hT.2.2 _)
    exact hbw this
  · exfalso
    have hm₁ : C₁ ∈ spaceComponents S' := by rw [hc]; exact mem_insert _ _
    have hm₂ : C₂ ∈ spaceComponents S' := by rw [hc]; exact mem_insert_of_mem _ rfl
    obtain ⟨x₁, rfl, -⟩ := hmemC hm₁
    obtain ⟨x₂, rfl, -⟩ := hmemC hm₂
    have hdisj : Disjoint (connectedComponent x₁) (connectedComponent x₂) :=
      connectedComponent_disjoint hne
    have hin : ∀ {Z : Set S'} {x : S'}, IsPreconnected Z → (connectedComponent x ∩ Z).Nonempty
      → Z ⊆ connectedComponent x := by
      rintro Z x hZ ⟨w, hw, hwZ⟩
      rw [connectedComponent_eq hw]
      exact hZ.subset_connectedComponent hwZ
    rcases harcs with ⟨X, Z, hXZ, hun, hX, hZ, hbX, hbZ⟩ | hO
    · have key : ∀ {A B : Set S'}, IsOArc A → BijOn ψ A F → A ⊆ connectedComponent x₁
      → B ⊆ connectedComponent x₂ → A ∪ B = ψ ⁻¹' F → False := by
        intro A B hA hbA hA₁ hB₂ hAB
        have hinj : InjOn ψ (connectedComponent x₁) := by
          intro a ha b hb he
          by_cases hf : ψ a ∈ F
          · have hmem : ∀ {z}, z ∈ connectedComponent x₁ → ψ z ∈ F → z ∈ A := fun {z} hz hzF ↦ by
              have : z ∈ A ∪ B := hAB ▸ hzF
              exact this.resolve_right fun h ↦ disjoint_left.1 hdisj hz (hB₂ h)
            exact hbA.injOn (hmem ha hf) (hmem hb (he ▸ hf)) he
          · exact hψ.2.2.1 hf (fun h ↦ hf (he ▸ h)) he
        have hdisc := (isClosedDisc_image_injOn hd hψ.1.continuousOn hinj).1
        have hFsub : F ⊆ ψ '' connectedComponent x₁ := fun f hf ↦ by
          obtain ⟨a, ha, rfl⟩ := hbA.surjOn hf
          exact mem_image_of_mem _ (hA₁ ha)
        exact hn ((epstein T univ F hT.isSurface inferInstance hF (subset_univ _)
          (by rw [hb]; exact disjoint_empty _)).2.1
          ⟨_, subset_univ _, hdisc, hFsub⟩)
      obtain ⟨w₁, hw₁, hF₁⟩ := hmeet x₁
      obtain ⟨w₂, hw₂, hF₂⟩ := hmeet x₂
      rw [← hun] at hF₁ hF₂
      rcases hF₁ with h₁ | h₁ <;> rcases hF₂ with h₂ | h₂
      · have := hin hX.isPreconnected ⟨w₁, hw₁, h₁⟩
        exact disjoint_left.1 hdisj (this h₂) hw₂
      · exact key hX hbX (hin hX.isPreconnected ⟨w₁, hw₁, h₁⟩) (hin hZ.isPreconnected ⟨w₂, hw₂,
          h₂⟩) hun
      · exact key hZ hbZ (hin hZ.isPreconnected ⟨w₁, hw₁, h₁⟩) (hin hX.isPreconnected ⟨w₂, hw₂,
          h₂⟩) (by rw [union_comm]; exact hun)
      · have := hin hZ.isPreconnected ⟨w₁, hw₁, h₁⟩
        exact disjoint_left.1 hdisj (this h₂) hw₂
    · obtain ⟨w₁, hw₁, hF₁⟩ := hmeet x₁
      obtain ⟨w₂, hw₂, hF₂⟩ := hmeet x₂
      have := hin hO.isPreconnected ⟨w₁, hw₁, hF₁⟩
      exact disjoint_left.1 hdisj (this hF₂) hw₂

end GraphMinor.GM19
