/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Nice73

/-!
# Graph Minors XI, (7.9)

`theorem_7_9` is (7.9) of the paper, for closed sets, by way of `nice_73`. The paper says that at
most
one disc in `Σ` bounded by an `O`-arc misses a given point, since `Σ` is connected. This is
`disc_unique`. Two
discs with the same boundary either have the same interior, or their union is open as well as
closed, by the
two sides of the `O`-arc.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [ConnectedSpace S]

/-- At most one disc bounded by an `O`-arc misses a given point. -/
theorem disc_unique (hS : IsClosedSurface S) {F Δ₁ Δ₂ : Set S} (hF : IsOArc F)
  (h₁ : IsClosedDisc Δ₁)
    (h₂ : IsClosedDisc Δ₂) (hb₁ : discBd Δ₁ = F) (hb₂ : discBd Δ₂ = F) {z : S} (hz₁ : z ∉ Δ₁)
      (hz₂ : z ∉ Δ₂) :
    Δ₁ = Δ₂ := by
  classical
  have hT2 : T2Space S := hS.2.1
  have hi₁ : IsOpen (Δ₁ \ F) := by
    have := interior_eq_sdiff_discBd hS h₁
    rw [hb₁] at this
    exact this ▸ isOpen_interior
  have hi₂ : IsOpen (Δ₂ \ F) := by
    have := interior_eq_sdiff_discBd hS h₂
    rw [hb₂] at this
    exact this ▸ isOpen_interior
  have hp₁ : IsPreconnected (Δ₁ \ F) := by
    have := (isOpenDisc_interior hS h₁).isPathConnected.isConnected.isPreconnected
    rwa [hb₁] at this
  have hp₂ : IsPreconnected (Δ₂ \ F) := by
    have := (isOpenDisc_interior hS h₂).isPathConnected.isConnected.isPreconnected
    rwa [hb₂] at this
  have hF₁ : F ⊆ Δ₁ := hb₁ ▸ discBd_subset Δ₁
  have hF₂ : F ⊆ Δ₂ := hb₂ ▸ discBd_subset Δ₂
  have hc₁ := h₁.isCompact.isClosed
  have hc₂ := h₂.isCompact.isClosed
  -- A preconnected set that misses `F` and meets the inside of a disc lies in it.
  have hin : ∀ {Δ A : Set S}, IsClosed Δ → IsOpen (Δ \ F) → IsPreconnected A → Disjoint A F →
      (A ∩ (Δ \ F)).Nonempty → A ⊆ Δ \ F := by
    intro Δ A hc hi hA hdis hne
    refine hA.subset_left_of_subset_union hi hc.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' hx.1) (fun x hx => ?_) hne
    by_cases hxΔ : x ∈ Δ
    · exact Or.inl ⟨hxΔ, disjoint_left.mp hdis hx⟩
    · exact Or.inr hxΔ
  by_cases hmeet : ((Δ₁ \ F) ∩ (Δ₂ \ F)).Nonempty
  · have hs₁ := hin hc₂ hi₂ hp₁ (disjoint_left.mpr fun x hx => hx.2) hmeet
    have hs₂ := hin hc₁ hi₁ hp₂ (disjoint_left.mpr fun x hx => hx.2) (by rwa [inter_comm])
    apply subset_antisymm
    · intro x hx
      by_cases hxF : x ∈ F
      · exact hF₂ hxF
      · exact (hs₁ ⟨hx, hxF⟩).1
    · intro x hx
      by_cases hxF : x ∈ F
      · exact hF₁ hxF
      · exact (hs₂ ⟨hx, hxF⟩).1
  exfalso
  have hlcl : ∀ {Δ y}, IsClosedDisc Δ → discBd Δ = F → y ∈ F → y ∈ closure (Δ \ F) := by
    intro Δ y hd hb hy
    have := discBd_subset_closure hd (hb ▸ hy)
    rwa [hb] at this
  have hopen : IsOpen (Δ₁ ∪ Δ₂) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    by_cases hyF : y ∈ F
    · obtain ⟨a, haF, hay⟩ : ∃ a ∈ F, a ≠ y :=
        ((infinite_of_isOArc hF).sdiff (finite_singleton y)).nonempty.imp fun _ h => ⟨h.1, h.2⟩
      obtain ⟨D, hDU, hDV⟩ := exists_loop_drawing hF haF
      have hyV : y ∉ D.V := by
        rw [hDV]
        exact fun h => hay h.symm
      obtain ⟨e, he, hye⟩ := D.exists_edge_of_mem (hDU ▸ hyF) hyV
      obtain ⟨W, A₁, A₂, -, -, hWo, hyW, -, hcov, hA₁, hA₂, hdis₁, hdis₂, -⟩ :=
        exists_edge_sides_split hS D he hye
      rw [hDU] at hcov hdis₁ hdis₂
      have hside : ∀ {Δ : Set S}, IsClosed Δ → IsOpen (Δ \ F) → y ∈ closure (Δ \ F) →
          (A₁ ⊆ Δ \ F ∧ (A₁ ∩ (Δ \ F)).Nonempty) ∨ (A₂ ⊆ Δ \ F ∧ (A₂ ∩ (Δ \ F)).Nonempty) := by
        intro Δ hc hi hcl
        obtain ⟨q, hqW, hqi⟩ := mem_closure_iff.mp hcl W hWo hyW
        rcases hcov ⟨hqW, hqi.2⟩ with hq | hq
        · exact Or.inl ⟨hin hc hi hA₁ hdis₁ ⟨q, hq, hqi⟩, q, hq, hqi⟩
        · exact Or.inr ⟨hin hc hi hA₂ hdis₂ ⟨q, hq, hqi⟩, q, hq, hqi⟩
      have hsub : W ⊆ Δ₁ ∪ Δ₂ := by
        intro x hx
        by_cases hxF : x ∈ F
        · exact Or.inl (hF₁ hxF)
        · rcases hside hc₁ hi₁ (hlcl h₁ hb₁ hyF) with ⟨s₁, n₁⟩ | ⟨s₁, n₁⟩ <;>
            rcases hside hc₂ hi₂ (hlcl h₂ hb₂ hyF) with ⟨s₂, n₂⟩ | ⟨s₂, n₂⟩
          · obtain ⟨z, hz, _⟩ := n₁
            exact (hmeet ⟨z, s₁ hz, s₂ hz⟩).elim
          · rcases hcov ⟨hx, hxF⟩ with h' | h'
            · exact Or.inl (s₁ h').1
            · exact Or.inr (s₂ h').1
          · rcases hcov ⟨hx, hxF⟩ with h' | h'
            · exact Or.inr (s₂ h').1
            · exact Or.inl (s₁ h').1
          · obtain ⟨z, hz, _⟩ := n₁
            exact (hmeet ⟨z, s₁ hz, s₂ hz⟩).elim
      exact Filter.mem_of_superset (hWo.mem_nhds hyW) hsub
    · rcases hy with hy | hy
      · exact Filter.mem_of_superset (hi₁.mem_nhds ⟨hy, hyF⟩) fun x hx => Or.inl hx.1
      · exact Filter.mem_of_superset (hi₂.mem_nhds ⟨hy, hyF⟩) fun x hx => Or.inr hx.1
  have hclopen : IsClopen (Δ₁ ∪ Δ₂) := ⟨hc₁.union hc₂, hopen⟩
  have hne : (Δ₁ ∪ Δ₂).Nonempty := by
    obtain ⟨y, hy⟩ := (infinite_of_isOArc hF).nonempty
    exact ⟨y, Or.inl (hF₁ hy)⟩
  have := hclopen.eq_univ hne
  have hzm : z ∈ Δ₁ ∪ Δ₂ := this ▸ mem_univ z
  exact hzm.elim hz₁ hz₂

/-- **(7.9)** of Graph Minors XI (page 95): "If $\Sigma$ is connected, $X, Y \subseteq \Sigma$ are
simply-connected, and $X \cap Y \ne
\emptyset$ is arc-wise connected and nice, and $X \cup Y \ne \Sigma$, then $X \cap Y$ is
simply-connected." We ask that
`X ∩ Y` be closed, for `nice_73`. -/
theorem theorem_7_9_proof (hS : IsClosedSurface S)
    {Γ : Drawing S} {X Y : Set S} (hXs : IsSimplyConnectedSet X) (hYs : IsSimplyConnectedSet Y)
    (hc : IsClosed (X ∩ Y)) (hn : IsGammaNice Γ (X ∩ Y)) (hp : IsPathConnected (X ∩ Y))
    (hu : X ∪ Y ≠ univ) : IsSimplyConnectedSet (X ∩ Y) := by
  have hT2 : T2Space S := hS.2.1
  refine ⟨hp, fun φ hφ => ?_⟩
  by_contra hnot
  obtain ⟨F, hF, hFφ, hFn⟩ := nice_73 S hS Γ _ hc hn φ hφ hnot
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).mp hu
  have hbounded : ∀ {T : Set S}, IsSimplyConnectedSet T → F ⊆ T → ∃ Δ : Set S, Δ ⊆ T
    ∧ IsClosedDisc Δ ∧
      discBd Δ = F := by
    intro T hT hFT
    have hnull : IsNullHomotopicOArcIn T F := by
      obtain ⟨ψ⟩ := id hF
      refine ⟨ψ, hT.2 _ ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hFT (ψ x).2
    obtain ⟨Δ, hΔ, hd, hb⟩ := theorem_7_2_proof hS hF hFT hnull
    refine ⟨Δ, hΔ, hd, ?_⟩
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hd] at hb
    exact hb
  obtain ⟨Δ₁, h₁, hd₁, hb₁⟩ := hbounded hXs ((hFφ.trans hφ).trans inter_subset_left)
  obtain ⟨Δ₂, h₂, hd₂, hb₂⟩ := hbounded hYs ((hFφ.trans hφ).trans inter_subset_right)
  have heq := disc_unique hS hF hd₁ hd₂ hb₁ hb₂ (fun h => hz (Or.inl (h₁ h))) fun h => hz (Or.inr
    (h₂ h))
  exact hFn (isNullHomotopicOArcIn_of_subset_disc hF (subset_inter h₁ (heq ▸ h₂)) hd₁
    (hb₁ ▸ discBd_subset Δ₁))

end GraphMinor.GM11
