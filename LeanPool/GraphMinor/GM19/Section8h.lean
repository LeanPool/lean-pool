/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8g

/-!
# Graph Minors XIX, (8.6) and (8.7)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [ConnectedSpace Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
  {ord : ℕ} {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- **Both edges of the pair of an edge `e` of `Γ*` lie on the side of `e`.** The two edges `c₁, c₂`
of `Γ` next to `e` share a region of `sk(Γ) ∪ G₃` with `e`, by `pair_side`. -/
theorem pair_in_side (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) {K : Drawing Shat} (hK : K.IsSubdrawing rad.G) {Ω : Set Shat}
    (hΩ : IsSide Ω K) {e : Set Shat} {c₁ c₂ : Set S} (he : e ∈ rad.G.E) (hp : rad.PairOf e c₁ c₂)
    (heΩ : e ⊆ Ω) : cap.emb '' c₁ ⊆ Ω ∧ cap.emb '' c₂ ⊆ Ω := by
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  obtain ⟨v₀, w, hv₀, hw, hsetG, f₁, f₂, hne, h₁, h₂, ht₁, ht₂, hfr₁, hfr₂⟩ := hp
  have heG := hsub.2 he
  obtain ⟨v', hv', r, hr, w', hw', hw'G, hset', her⟩ := spoke_ends hrad hT heG
  have hvhat : cap.emb v₀ ∈ D.V := by
    rw [hD.hV]
    exact mem_image_of_mem _ hv₀
  have hwD : w ∉ D.V := fun h ↦ hw.2 (by rwa [hD.hV] at h)
  have hwc : w ∈ closure e ∩ G₃.V := by
    have : w ∈ closure e ∩ rad.G.V := by rw [hsetG]; exact Or.inr rfl
    exact ⟨this.1, hsub.1 this.2⟩
  have hvc : cap.emb v₀ ∈ closure e ∩ G₃.V := by
    have : cap.emb v₀ ∈ closure e ∩ rad.G.V := by rw [hsetG]; exact Or.inl rfl
    exact ⟨this.1, hsub.1 this.2⟩
  rw [hset'] at hwc hvc
  have hww : w = w' := by
    rcases hwc with h | h
    · exact absurd (h ▸ hv') hwD
    · exact h
  subst hww
  have hvv : cap.emb v₀ = v' := by
    rcases hvc with h | h
    · exact h
    · exact absurd (D.V_subset_U hvhat) (h ▸ region_subset hr hw')
  subst hvv
  obtain ⟨hrO, hwO⟩ := rad.regionOf_mem hw
  have hrr : rad.regionOf w = r := region_eq_of_mem (hD.hatRegion_mem_R hS hrO) hr hwO hw'
  rw [hrr] at hrO hfr₁ hfr₂
  have key : ∀ {f c : Set S} , Γ.IsSkEdgeIn f c → v₀ ∈ tilde f →
      cap.emb '' f ⊆ frontier r → cap.emb '' c ⊆ Ω := by
    intro f c hfc htf hfr
    obtain ⟨p, hp, hep, hfp⟩ := pair_side hS hD h3 hrad hmax hfc.mem hv₀ htf hrO hfr heG her hw'
      hw'G hset'
    obtain ⟨y, hye⟩ := heG.1
    obtain ⟨z, hzΩ, hzp⟩ := mem_closure_iff.mp (hep hye) _ hΩ.isOpen (heΩ hye)
    have hconn : IsPreconnected p := by
      obtain ⟨q, hq, rfl⟩ := id hp
      exact isPreconnected_connectedComponentIn
    have hpΩ : p ⊆ Ω := hΩ.subset hconn (disjoint_left.mpr fun a ha haK ↦
      region_subset hp ha (Or.inr (hsub.U_subset (hK.U_subset haK)))) ⟨z, hzp, hzΩ⟩
    obtain ⟨x, hx⟩ := hfc.mem.1
    have hxi : cap.emb x ∈ cap.emb '' c := mem_image_of_mem _ (hfc.subset hx)
    have hxΩ : cap.emb x ∈ Ω := hΩ.mem_of_closure (closure_mono hpΩ (hfp (mem_image_of_mem _ hx)))
      (disjoint_left.mp (disc_edge_disjoint rad hK hfc.1) hxi)
    exact side_edge rad hK hΩ hfc.1 ⟨_, hxi, hxΩ⟩
  exact ⟨key h₁ ht₁ hfr₁, key h₂ ht₂ hfr₂⟩

variable {F₁ F₂ : Drawing Shat} {Δ₁ Δ₂ : Set Shat}

/-- Every edge of a circuit bounding `Δ₁` has an edge of `Γ ∩ Δ₁` next to it. -/
theorem exists_pair_in (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) (hF₁ : F₁.IsCircuitOf rad.G) (hΔ₁ : IsClosedDisc Δ₁)
    (hbd₁ : discBd Δ₁ = F₁.U) {e : Set Shat} (he : e ∈ F₁.E) :
    ∃ c₁ c₂, rad.PairOf e c₁ c₂ ∧ c₁ ∈ (partIn cap Γ Δ₁).edgeSet := by
  obtain ⟨c₁, c₂, hp, h | h⟩ := rad.splits_iff.mp (disc_split hS h3 rad hF₁ hΔ₁ hbd₁ he)
  · exact ⟨c₁, c₂, hp, h.1⟩
  · refine ⟨c₂, c₁, ?_, h.2⟩
    obtain ⟨v, w, hv, hw, hs, f₁, f₂, hne, a, b, c, d, x, y⟩ := hp
    exact ⟨v, w, hv, hw, hs, f₂, f₁, hne.symm, b, a, d, c, y, x⟩

omit [T2Space Shat] [ConnectedSpace Shat] in
theorem U_of_edges (hF : F₁.IsCircuit) {X : Set Shat} (hX : IsClosed X) (h : ∀ e ∈ F₁.E, e ⊆ X) :
    F₁.U ⊆ X := by
  intro x hx
  by_cases hxV : x ∈ F₁.V
  · obtain ⟨g, hg, hxg⟩ := exists_edge_at_vertex hF hxV
    exact closure_minimal (h g hg) hX hxg
  · obtain ⟨g, hg, hxg⟩ := F₁.exists_edge_of_mem hx hxV
    exact h g hg hxg

/-- A circuit edge outside `Δ₂` has its pair outside `Δ₂`. So if `Γ ∩ Δ₁ ⊆ Γ ∩ Δ₂` then `Δ₁ ⊆ Δ₂`.
-/
theorem nest_of_le (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) (hins₁ : IsInsOf rad ord 𝒯 F₁ Δ₁)
    (hins₂ : IsInsOf rad ord 𝒯 F₂ Δ₂) (hle : partIn cap Γ Δ₁ ≤ partIn cap Γ Δ₂) : Δ₁ ⊆ Δ₂ := by
  have hT := cap.isClosedSurface
  obtain ⟨hF₁, -, hΔ₁, hbd₁, hm₁⟩ := hins₁
  obtain ⟨hF₂, -, hΔ₂, hbd₂, hm₂⟩ := hins₂
  have hout := isSide_out hT hΔ₂ hbd₂
  have hO₁ := isSide_int hT hΔ₁ hbd₁
  have hO₂ := isSide_int hT hΔ₂ hbd₂
  have hedge : ∀ e ∈ F₁.E, e ⊆ Δ₂ := by
    intro e he
    by_contra hn
    obtain ⟨y, hy, hyn⟩ := not_subset.mp hn
    have heG := hF₁.1.2 he
    have heF : e ∉ F₂.E := fun h ↦ hn fun z hz ↦
      Surface.discBd_subset _ (hbd₂ ▸ F₂.closure_subset_U h (subset_closure hz))
    have hd := edge_disjoint_U hF₂.1 heG heF
    have heO : e ⊆ Δ₂ᶜ := hout.subset heG.2.2.1.isConnected.isPreconnected hd ⟨y, hy, hyn⟩
    obtain ⟨c₁, c₂, hp, hc⟩ := exists_pair_in hS h3 rad hF₁ hΔ₁ hbd₁ he
    have hcO := (pair_in_side hS h3 rad hF₂.1 hout heG hp heO).1
    obtain ⟨x, hx⟩ := hc.1.1
    exact hcO (mem_image_of_mem _ hx) ((hle.edgeSet_subset hc).2.1 hx)
  have hUsub : F₁.U ⊆ Δ₂ := U_of_edges hF₁.2 hΔ₂.isClosed hedge
  have hnot : ¬ Δ₂ᶜ ⊆ discInt Δ₁ := fun hsub ↦ by
    have hc := part_cover rad hF₂.1 hF₁.1 hF₁.1 hO₂ hO₁ hO₁ fun x ↦ by
      rw [closure_discInt hΔ₁, closure_discInt hΔ₂]
      by_cases hx : x ∈ Δ₂
      · exact Or.inl hx
      · exact Or.inr (Or.inl (discInt_subset _ (hsub hx)))
    rw [closure_discInt hΔ₁, closure_discInt hΔ₂] at hc
    exact h𝒯.axiom2 hm₂ hm₁ hm₁ hc
  have hd := disjoint_disc hT hout hΔ₁ hbd₁
    (disjoint_left.mpr fun x hx hxU ↦ hx (hUsub hxU)) hnot
  exact fun x hx ↦ by
    by_contra hn
    exact disjoint_left.mp hd hn hx

/-- If `Γ ∩ Δ₁ ⊆ Γ ∩ out(Δ₂)` then `U(F₁)` misses the inside of `Δ₂`. -/
theorem apart_of_le (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (hins₁ : IsInsOf rad ord 𝒯 F₁ Δ₁) (hins₂ : IsInsOf rad ord 𝒯 F₂ Δ₂)
    (hle : partIn cap Γ Δ₁ ≤ partIn cap Γ (closure Δ₂ᶜ)) : Disjoint (discInt Δ₂) F₁.U := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  obtain ⟨hF₁, -, hΔ₁, hbd₁, hm₁⟩ := hins₁
  obtain ⟨hF₂, -, hΔ₂, hbd₂, hm₂⟩ := hins₂
  have hO₂ := isSide_int hT hΔ₂ hbd₂
  have hedge : ∀ e ∈ F₁.E, e ⊆ (discInt Δ₂)ᶜ := by
    intro e he
    by_contra hn
    obtain ⟨y, hy, hyn⟩ := not_subset.mp hn
    have hyI : y ∈ discInt Δ₂ := not_not.mp hyn
    have heG := hF₁.1.2 he
    have heF : e ∉ F₂.E := fun h ↦ disjoint_left.mp hO₂.disjoint_U hyI
      (F₂.closure_subset_U h (subset_closure hy))
    have hd := edge_disjoint_U hF₂.1 heG heF
    have heI : e ⊆ discInt Δ₂ := hO₂.subset heG.2.2.1.isConnected.isPreconnected hd ⟨y, hy, hyI⟩
    obtain ⟨c₁, c₂, hp, hc⟩ := exists_pair_in hS h3 rad hF₁ hΔ₁ hbd₁ he
    have hcI := (pair_in_side hS h3 rad hF₂.1 hO₂ heG hp heI).1
    obtain ⟨x, hx⟩ := hc.1.1
    have h₂ := (hle.edgeSet_subset hc).2.1 hx
    exact disjoint_left.mp (disjoint_discInt_closure hman hΔ₂) (hcI (mem_image_of_mem _ hx)) h₂
  have := U_of_edges hF₁.2 (hO₂.isOpen.isClosed_compl) hedge
  exact disjoint_left.mpr fun x hx hxU ↦ this hxU hx

/-- **Graph Minors XIX, (8.6).** "Let $\mathscr{T}$ be a tangle in $\Gamma$, and let $F_1, F_2$ be
$\mathscr{T}$-enclaves.
Then either $ins(F_1) \subseteq ins(F_2)$, or $ins(F_2) \subseteq ins(F_1)$, or $ins(F_1)
\cap ins(F_2) = U(F_1) \cap U(F_2)$." -/
theorem theorem_8_6_proof (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (tb : TieBreaker rad)
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) {ord₁ ord₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯₁ : IsTangle Γ.toHypergraph ord₁ 𝒯₁) (h𝒯₂ : IsTangle Γ.toHypergraph ord₂ 𝒯₂)
    (hins₁ : IsInsOf rad ord 𝒯 F₁ Δ₁) (hins₂ : IsInsOf rad ord 𝒯 F₂ Δ₂)
    (hd₁ : IsDistinction tb.lambdaOrder 𝒯 𝒯₁ (partIn cap Γ Δ₁) (partIn cap Γ (closure Δ₁ᶜ)))
    (hd₂ : IsDistinction tb.lambdaOrder 𝒯 𝒯₂ (partIn cap Γ Δ₂) (partIn cap Γ (closure Δ₂ᶜ))) :
    Δ₁ ⊆ Δ₂ ∨ Δ₂ ⊆ Δ₁ ∨ Δ₁ ∩ Δ₂ = F₁.U ∩ F₂.U := by
  have hT := cap.isClosedSurface
  have htie := tb.isTieBreaker hS h3
  have hr₁ := GraphMinor.GM10.theorem_10_2_proof _ _ _ _ _ _ _ _ htie h𝒯 h𝒯₁ hd₁
  have hr₂ := GraphMinor.GM10.theorem_10_2_proof _ _ _ _ _ _ _ _ htie h𝒯 h𝒯₂ hd₂
  have hnc := GraphMinor.GM10.theorem_9_4_proof htie hr₁ hr₂
  rw [SeparationsCross, not_not] at hnc
  have hs₂ := h𝒯.isSeparation hd₂.1.1
  obtain ⟨hF₁, -, hΔ₁, hbd₁, hm₁⟩ := id hins₁
  obtain ⟨hF₂, -, hΔ₂, hbd₂, hm₂⟩ := id hins₂
  rcases hnc with ⟨h, -⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨-, h⟩
  · exact Or.inl (nest_of_le hS h3 h𝒯 hins₁ hins₂ h)
  · have a₁ := apart_of_le hS h3 hins₁ hins₂ h
    have a₂ := apart_of_le hS h3 hins₂ hins₁ h'
    have hO₁ := isSide_int hT hΔ₁ hbd₁
    have hO₂ := isSide_int hT hΔ₂ hbd₂
    by_cases hm : (discInt Δ₁ ∩ discInt Δ₂).Nonempty
    · refine Or.inl ?_
      have hsub := hO₂.subset hO₁.conn a₂ hm
      exact hΔ₁.subset_closure_discInt.trans
        (closure_minimal (hsub.trans (discInt_subset _)) hΔ₂.isClosed)
    · refine Or.inr (Or.inr ?_)
      have hdis : Disjoint (discInt Δ₁) (discInt Δ₂) :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hm)
      apply Subset.antisymm
      · rintro x ⟨hx₁, hx₂⟩
        refine ⟨?_, ?_⟩
        · by_contra hn
          have hxI : x ∈ discInt Δ₁ := ⟨hx₁, fun hb ↦ hn (hbd₁ ▸ hb)⟩
          obtain ⟨z, hzO, hzI⟩ := mem_closure_iff.mp (hΔ₂.subset_closure_discInt hx₂) _ hO₁.isOpen
            hxI
          exact disjoint_left.mp hdis hzO hzI
        · by_contra hn
          have hxI : x ∈ discInt Δ₂ := ⟨hx₂, fun hb ↦ hn (hbd₂ ▸ hb)⟩
          obtain ⟨z, hzO, hzI⟩ := mem_closure_iff.mp (hΔ₁.subset_closure_discInt hx₁) _ hO₂.isOpen
            hxI
          exact disjoint_left.mp hdis hzI hzO
      · rintro x ⟨hx₁, hx₂⟩
        exact ⟨Surface.discBd_subset _ (hbd₁ ▸ hx₁), Surface.discBd_subset _ (hbd₂ ▸ hx₂)⟩
  · exfalso
    refine h𝒯.axiom2 hd₂.1.1 hd₁.1.1 hd₂.1.1 ?_
    have l₂ := hs₂.left_le
    have l₁ := (h𝒯.isSeparation hd₁.1.1).left_le
    have l₃ := GM10.union_le l₂ l₁
    exact eq_of_cover hs₂ (le_trans (GM10.le_union_left l₂ l₁) (GM10.le_union_left l₃ l₂))
      (le_trans h' (le_trans (GM10.le_union_right l₂ l₁) (GM10.le_union_left l₃ l₂)))
      (GM10.union_le l₃ l₂)
  · exact Or.inr (Or.inl (nest_of_le hS h3 h𝒯 hins₂ hins₁ h))

end GraphMinor.GM19
