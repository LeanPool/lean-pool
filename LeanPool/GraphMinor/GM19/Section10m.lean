/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10l
public import LeanPool.GraphMinor.GM19.Section5r

/-!
# The first bullet of the distance flaw

A short circuit around two poles gives the data of the first shape of a distance flaw.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] in
/-- The two sides of a short circuit are its inside and its outside. -/
theorem sides_ins (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) :
    IsSidesOf C (D.ins C) (closure (D.ins C)ᶜ) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hC hlt
  have h : Sided C (discInt (D.ins C)) (D.ins C)ᶜ := ⟨D.ins C, hi.2.2.1, hi.2.2.2.1, Or.inl ⟨rfl,
    rfl⟩⟩
  have := h.isSidesOf hT
  rwa [closure_discInt hi.2.2.1] at this

omit [T2Space S] [T2Space Shat] in
/-- Linked discs with small order, each in the outside of the others, form a linked family. -/
theorem family_of_discs {θ : ℕ} {𝓓 : Set (Set Shat)} (hf : 𝓓.Finite)
    (hlink : ∀ Δ ∈ 𝓓, GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ Δ)
      (partIn cap D.P.Γ (closure Δᶜ)))
    (hord : ∀ Δ ∈ 𝓓, Hypergraph.separationOrder (partIn cap D.P.Γ Δ) (partIn cap D.P.Γ
      (closure Δᶜ)) < θ)
    (hdis : ∀ Δ ∈ 𝓓, ∀ Δ' ∈ 𝓓, Δ ≠ Δ' → Δ ⊆ closure Δ'ᶜ) : IsLinkedFamily D θ (discPairs cap 𝓓)
      := by
  refine ⟨hf.image _, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨Δ, hΔ, rfl⟩
    exact hlink Δ hΔ
  · rintro _ ⟨Δ, hΔ, rfl⟩
    exact hord Δ hΔ
  · rintro _ ⟨Δ, hΔ, rfl⟩ _ ⟨Δ', hΔ', rfl⟩ hne
    have hne' : Δ ≠ Δ' := fun h ↦ hne (by rw [h])
    refine (le_iff_of_le (D.P.Γ.restrict_le _) (D.P.Γ.restrict_le _)).2 ⟨?_, ?_⟩
    · exact fun v hv ↦ ⟨hv.1, hdis Δ hΔ Δ' hΔ' hne' hv.2⟩
    · exact fun c hc ↦ ⟨hc.1, fun x hx ↦ hdis Δ hΔ Δ' hΔ' hne' (hc.2.1 hx),
        fun v hv ↦ hdis Δ hΔ Δ' hΔ' hne' (hc.2.2 hv)⟩
  · rintro _ ⟨Δ, -, rfl⟩
    exact isClosed_closure.preimage cap.isEmbedding.continuous

variable (hS : IsSurface S)
include hS

omit [T2Space S] [T2Space Shat] in
/-- A pole does not lie in `Σ`. -/
theorem pole_notMem_range (D : TangleDatum cap χ) {r : Shat} (hr : r ∈ D.rad.poles) : r ∉ range
  cap.emb := by
  obtain ⟨Θ, hΘ, -, hd⟩ := D.rad.pole_cases hS hr
  exact fun h ↦ cap.notMem_range hΘ hd h

omit [T2Space S] [T2Space Shat] in
/-- Distinct poles belong to distinct cuffs. -/
theorem pole_cuffs_ne (D : TangleDatum cap χ) {r₁ r₂ : Shat} (h₁ : r₁ ∈ D.rad.poles)
  (h₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂) :
    ∃ Θ₁ ∈ cuffs S, ∃ Θ₂ ∈ cuffs S, Θ₁ ≠ Θ₂ ∧ r₁ ∈ cap.cuffDisc Θ₁ ∧ r₂ ∈ cap.cuffDisc Θ₂ := by
  obtain ⟨Θ₁, hΘ₁, hreg₁, hd₁⟩ := D.rad.pole_cases hS h₁
  obtain ⟨Θ₂, hΘ₂, hreg₂, hd₂⟩ := D.rad.pole_cases hS h₂
  refine ⟨Θ₁, hΘ₁, Θ₂, hΘ₂, ?_, hd₁, hd₂⟩
  rintro rfl
  obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
  have m₁ := D.rad.regionOf_mem h₁.1
  have m₂ := D.rad.regionOf_mem h₂.1
  exact hne ((hG3 _ m₁.1).unique ⟨m₁.2, h₁.1.1⟩ ⟨(hreg₁.trans hreg₂.symm) ▸ m₂.2, h₂.1.1⟩)

omit [T2Space S] in
/-- A circuit with a pole in its inside is not the edge of a disc of `Σ` that misses the vertices of
`Γ` off the circuit. -/
theorem no_empty_disc (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
  (hlt : F.E.ncard < 2 * D.rep) {r : Shat}
    (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins F) {Δ : Set Shat} (hd : IsClosedDisc Δ)
      (hsub : Δ ⊆ range cap.emb) (hbd : discBd Δ = F.U)
    (hV : ∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ F.U) : False := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hF hlt
  rcases isSidesOf_cases hT hd hbd (D.sides_ins hF hlt) with ⟨e₁, -⟩ | ⟨e₁, e₂⟩
  · exact D.pole_notMem_range hS hr (hsub (e₁ ▸ hri))
  · have hm := hi.2.2.2.2
    refine D.isTangle.axiom3 hm ?_
    refine subset_antisymm inter_subset_left fun v hv ↦ ⟨hv, ?_⟩
    change cap.emb v ∈ D.ins F
    by_cases hvΔ : cap.emb v ∈ Δ
    · exact D.U_subset_ins hF hlt (hV v hv hvΔ)
    · rw [e₁]
      exact subset_closure hvΔ

omit [TopologicalSpace S] [T2Space S] hS in
/-- The bound `dist(Γ) > ½n + 1` excludes the third outcome of the second assertion of (10.1). -/
theorem not_dist_le {d : ℕ∞} {n m : ℕ} (hd : ((n + 2 : ℕ) : ℕ∞) < 2 * d) (hm : m ≤ 2 * n)
  (h : d * 4 ≤ ((m + 4 : ℕ) : ℕ∞)) : False := by
  induction d using ENat.recTopCoe with
  | top => simp at h
  | coe k =>
    have h₁ : n + 2 < 2 * k := by exact_mod_cast hd
    have h₂ : k * 4 ≤ m + 4 := by exact_mod_cast h
    omega

variable (h3 : D.P.Γ.IsInternallyThreeConnected)
include h3

/-- **The first shape.** -/
theorem exists_outer_of_pair [Nonempty S] {n : ℕ} (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (h : ∃ C, D.IsPairCircuit n C) : ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨F₀, hF₀, hmin₀⟩ := exists_least_pair h
  have hlt₀ : F₀.E.ncard < 2 * D.rep := by have := hF₀.2.1; omega
  -- The linked circuit from (8.7) is again least.
  obtain ⟨F, hFc, hle, hw, hsub, hlink⟩ := exists_linked hS h3 hF₀.1 hlt₀
  have hc₀ := hF₀.2.1
  obtain ⟨-, -, p₀, hp₀, q₀, hq₀, hne₀, hi₀, hi₀'⟩ := hF₀
  have hle₂ : F.E.ncard ≤ 2 * n := by omega
  have hlF : D.IsPairCircuit n F := ⟨hFc, hle₂, p₀, hp₀, q₀, hq₀, hne₀, hsub hi₀, hsub hi₀'⟩
  have heq : F.E.ncard = F₀.E.ncard := le_antisymm hle (hmin₀ F hlF).1
  have hminF : ∀ C, D.IsPairCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard
    → D.tb.weightSub F ≤ D.tb.weightSub C) := fun C hC ↦ by
    obtain ⟨h₁, h₂⟩ := hmin₀ C hC
    exact ⟨heq.le.trans h₁, fun h₃ ↦ (hw heq).trans (h₂ (heq.symm.trans h₃))⟩
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hθ : ThetaFree D F := thetaFree_of_least hn hlF hminF
  have hform : ((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
    ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) := by
    rcases second_of_thetaFree hS h3 hFc hθ with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (not_dist_le hd hle₂ h).elim
  obtain ⟨K, hK, htwo⟩ := exists_part_of_form hS h3 hFc hform fun Δ h₁ h₂ h₃ h₄ ↦
    D.no_empty_disc hS hFc hlt hp₀ (hsub hi₀) h₁ h₂ h₃ h₄
  have hi := D.ins_spec hFc hlt
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  obtain ⟨Θ₁, hΘ₁, Θ₂, hΘ₂, hΘ, hd₁, hd₂⟩ := D.pole_cuffs_ne hS hp₀ hq₀ hne₀
  have hKF : cap.emb '' K.U ⊆ F.U := by
    rcases hK.form with ⟨h, -⟩ | ⟨s, t, Θ, -, -, -, -, -, -, h, -⟩
    · exact h.symm.subset
    · exact h
  have hfrontier : frontier (D.ins F) = F.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hbd]
  refine ⟨{D.ins F}, K, Or.inl ⟨D.ins F, rfl, hi.2.2.1, hbd ▸ hK.form, Θ₁, hΘ₁, Θ₂, hΘ₂, hΘ, ⟨p₀,
    hd₁, hsub hi₀⟩, ⟨q₀, hd₂, hsub hi₀'⟩⟩,
    finite_singleton _, by simp, ?_, hK.feature, hK.inter, hK.lines, ?_, ?_, ?_, ?_, ?_⟩
  · refine family_of_discs (finite_singleton _) (by rintro _ rfl; exact hlink) ?_ ?_
    · rintro _ rfl
      have := disc_order hS h3 D.rad hFc hi.2.2.1 hbd
      omega
    · rintro _ rfl _ rfl h
      exact (h rfl).elim
  · have h₁ := hK.V_le
    have h₂ := hK.E_le
    have h₃ := IsCircuit.ncard_V hFc.2
    omega
  · rcases hK.form with ⟨-, hO, -⟩ | ⟨s, t, Θ, -, hst, -, -, hbds, hl, -⟩
    · exact ⟨{K.U}, ∅, finite_singleton _, finite_empty, by rintro _ rfl; exact hO, by simp, by
        simp⟩
    · refine ⟨∅, {K.U}, finite_empty, finite_singleton _, by simp, ?_, by simp⟩
      rintro _ rfl
      have hs : s ∈ K.U ∩ bd S := hbds ▸ mem_insert _ _
      have ht : t ∈ K.U ∩ bd S := hbds ▸ mem_insert_of_mem _ rfl
      exact ⟨s, t, hst, hl, Or.inl hs.2, Or.inl ht.2⟩
  · rintro _ rfl v hv h₁ h₂
    have hvF : cap.emb v ∈ F.U := by
      rw [← hfrontier, frontier_eq_closure_inter_closure]
      exact ⟨subset_closure h₁, h₂⟩
    rcases hK.form with ⟨h, -⟩ | ⟨s, t, Θ, hΘ', -, -, -, -, -, -, h⟩
    · rw [h] at hvF
      obtain ⟨u, hu, hvu⟩ := hvF
      rwa [← cap.isEmbedding.injective hvu]
    · by_contra hn'
      exact cap.notMem_range hΘ' (h ⟨hvF, fun ⟨u, hu, hvu⟩ ↦ hn' (cap.isEmbedding.injective hvu ▸
        hu)⟩) ⟨v, rfl⟩
  · rintro v hv _ rfl
    have : cap.emb v ∈ frontier (D.ins F) := hfrontier ▸ hKF (mem_image_of_mem _ hv)
    rw [frontier_eq_closure_inter_closure] at this
    exact this.2
  · exact isAnchored_of_form hK.form hK.inter htwo

end TangleDatum

end GraphMinor.GM19
