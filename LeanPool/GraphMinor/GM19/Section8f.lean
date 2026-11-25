/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Section8e
public import LeanPool.GraphMinor.GM19.Section8d

/-!
# Graph Minors XIX, (8.4)

The part of the proof of (8.4) that uses only tangles is `distinction_cases`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

section Abstract

variable {α β Λ : Type*} [LinearOrder Λ] {G A B H H' : Hypergraph α β}
  {lam : Hypergraph α β × Hypergraph α β → Λ} {θ θ' : ℕ}
  {𝒯 𝒯' : Set (Hypergraph α β × Hypergraph α β)}

theorem eq_of_cover (hHH' : G.IsSeparation H H') {X : Hypergraph α β} (h₁ : H ≤ X) (h₂ : H' ≤ X)
    (hX : X ≤ G) : X = G :=
  le_antisymm hX (hHH'.union_eq ▸ GM10.union_le h₁ h₂)

theorem cover_three (hAB : G.IsSeparation A B) (hHH' : G.IsSeparation H H') :
    H ∪ B ∪ (A ∩ H') = G := by
  have hle : H ∪ B ∪ (A ∩ H') ≤ G := GM10.union_le (GM10.union_le hHH'.left_le hAB.right_le)
    (GM10.inter_le hAB.left_le hHH'.right_le)
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_
  · apply Subset.antisymm hle.vertexSet_subset
    intro v hv
    have h₁ : v ∈ (H ∪ H').vertexSet := hHH'.union_eq ▸ hv
    have h₂ : v ∈ (A ∪ B).vertexSet := hAB.union_eq ▸ hv
    rcases h₁ with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · rcases h₂ with h₂ | h₂
      · exact Or.inr ⟨h₂, h₁⟩
      · exact Or.inl (Or.inr h₂)
  · apply Subset.antisymm hle.edgeSet_subset
    intro v hv
    have h₁ : v ∈ (H ∪ H').edgeSet := hHH'.union_eq ▸ hv
    have h₂ : v ∈ (A ∪ B).edgeSet := hAB.union_eq ▸ hv
    rcases h₁ with h₁ | h₁
    · exact Or.inl (Or.inl h₁)
    · rcases h₂ with h₂ | h₂
      · exact Or.inr ⟨h₂, h₁⟩
      · exact Or.inl (Or.inr h₂)

/-- The tangle argument of the proof of (8.4). Let `(A, B)` be the `(𝒯, 𝒯')`-distinction, and let
`(H, H')` be a separation with `E(H) ≠ ∅` and `H ⊆ A` or `H ⊆ B`, such that `(H, H')`,
`(A ∩ H', B ∪ H)`, `(A ∪ H, B ∩ H')` all have `λ`-order at most that of `(A, B)`. Then `(H, H')` is
`(A, B)`, or it is `(B, A)` and it is not in `𝒯`. -/
theorem distinction_cases (hlam : IsTieBreaker G lam) (h𝒯 : IsTangle G θ 𝒯)
    (h𝒯' : IsTangle G θ' 𝒯') (hd : IsDistinction lam 𝒯 𝒯' A B) (hHH' : G.IsSeparation H H')
    (hle₁ : lam (H, H') ≤ lam (A, B)) (hle₂ : lam (A ∩ H', B ∪ H) ≤ lam (A, B))
    (hle₃ : lam (A ∪ H, B ∩ H') ≤ lam (A, B)) (hsub : H ≤ A ∨ H ≤ B)
    (hne : H.edgeSet.Nonempty) :
    (H = A ∧ H' = B) ∨ (H = B ∧ H' = A ∧ (H, H') ∉ 𝒯) := by
  obtain ⟨⟨hABT, hBAT⟩, hmin⟩ := hd
  have hAB := h𝒯.isSeparation hABT
  have hs₂ : G.IsSeparation (A ∩ H') (B ∪ H) := (hAB.symm.union_inter hHH').symm
  have hs₃ : G.IsSeparation (A ∪ H) (B ∩ H') := hAB.union_inter hHH'
  have hord : ∀ {P Q}, G.IsSeparation P Q → lam (P, Q) ≤ lam (A, B) →
      Hypergraph.separationOrder P Q ≤ Hypergraph.separationOrder A B := by
    intro P Q hPQ hle
    by_contra hn
    exact absurd (hlam.axiom3 hAB hPQ (not_le.mp hn)) (not_lt.mpr hle)
  have hlt : Hypergraph.separationOrder A B < θ := h𝒯.order_lt hABT
  have hlt' : Hypergraph.separationOrder A B < θ' := by
    have h := h𝒯'.order_lt hBAT
    have e : Hypergraph.separationOrder B A = Hypergraph.separationOrder A B := by
      simp only [Hypergraph.separationOrder, GM10.inter_comm B A]
    omega
  have hnotboth : (B, A) ∉ 𝒯 := fun h ↦ by
    refine h𝒯.axiom2 hABT h hABT ?_
    exact eq_of_cover hAB (le_trans (GM10.le_union_left hAB.left_le hAB.right_le)
      (GM10.le_union_left (GM10.union_le hAB.left_le hAB.right_le) hAB.left_le))
      (le_trans (GM10.le_union_right hAB.left_le hAB.right_le)
      (GM10.le_union_left (GM10.union_le hAB.left_le hAB.right_le) hAB.left_le))
      (GM10.union_le (GM10.union_le hAB.left_le hAB.right_le) hAB.left_le)
  have heq : ∀ {P Q}, G.IsSeparation P Q → Distinguishes 𝒯 𝒯' P Q → lam (P, Q) ≤ lam (A, B) →
      P = A ∧ Q = B := by
    intro P Q hPQ hdis hle
    have he : lam (P, Q) = lam (A, B) := le_antisymm hle (hmin hdis)
    rcases (hlam.axiom1 hPQ hAB).mp he with h | ⟨rfl, rfl⟩
    · exact h
    · exact absurd hdis.1 hnotboth
  have hcomm : lam (H', H) = lam (H, H') := (hlam.axiom1 hHH'.symm hHH').mpr (Or.inr ⟨rfl, rfl⟩)
  have hordH := hord hHH' hle₁
  have hmem : (H, H') ∈ 𝒯 ∨ (H, H') ∈ 𝒯' := by
    rcases hsub with h | h
    · left
      refine (h𝒯.axiom1 hHH' (hordH.trans_lt hlt)).resolve_right fun hc ↦ ?_
      refine h𝒯.axiom2 hABT hc hABT (eq_of_cover hHH' ?_ ?_ ?_)
      · exact h.trans (le_trans (GM10.le_union_left hAB.left_le hHH'.right_le)
          (GM10.le_union_left (GM10.union_le hAB.left_le hHH'.right_le) hAB.left_le))
      · exact le_trans (GM10.le_union_right hAB.left_le hHH'.right_le)
          (GM10.le_union_left (GM10.union_le hAB.left_le hHH'.right_le) hAB.left_le)
      · exact GM10.union_le (GM10.union_le hAB.left_le hHH'.right_le) hAB.left_le
    · right
      refine (h𝒯'.axiom1 hHH' (hordH.trans_lt hlt')).resolve_right fun hc ↦ ?_
      refine h𝒯'.axiom2 hBAT hc hBAT (eq_of_cover hHH' ?_ ?_ ?_)
      · exact h.trans (le_trans (GM10.le_union_left hAB.right_le hHH'.right_le)
          (GM10.le_union_left (GM10.union_le hAB.right_le hHH'.right_le) hAB.right_le))
      · exact le_trans (GM10.le_union_right hAB.right_le hHH'.right_le)
          (GM10.le_union_left (GM10.union_le hAB.right_le hHH'.right_le) hAB.right_le)
      · exact GM10.union_le (GM10.union_le hAB.right_le hHH'.right_le) hAB.right_le
  have hnb : ¬ ((H, H') ∈ 𝒯 ∧ (H, H') ∈ 𝒯') := by
    rintro ⟨h₁, h₂⟩
    have hn₂ : (A ∩ H', B ∪ H) ∉ 𝒯' := fun hc ↦ h𝒯'.axiom2 h₂ hBAT hc (cover_three hAB hHH')
    have hm₂ : (B ∪ H, A ∩ H') ∈ 𝒯' :=
      (h𝒯'.axiom1 hs₂ ((hord hs₂ hle₂).trans_lt hlt')).resolve_left hn₂
    have hT₂ : (A ∩ H', B ∪ H) ∈ 𝒯 := GraphMinor.GM10.theorem_2_9_proof h𝒯 hABT hs₂
      ((hord hs₂ hle₂).trans_lt hlt)
      (Or.inr (Or.inl inter_subset_left))
    obtain ⟨-, hB⟩ := heq hs₂ ⟨hT₂, hm₂⟩ hle₂
    have hn₃ : (B ∩ H', A ∪ H) ∉ 𝒯 := fun hc ↦ h𝒯.axiom2 h₁ hABT hc (cover_three hAB.symm hHH')
    have hs₃' := hs₃.symm
    have hcomm₃ : Hypergraph.separationOrder (B ∩ H') (A ∪ H) =
        Hypergraph.separationOrder (A ∪ H) (B ∩ H') := by
      simp only [Hypergraph.separationOrder, GM10.inter_comm (B ∩ H') (A ∪ H)]
    have hlt₃ := hord hs₃ hle₃
    have hm₃ : (A ∪ H, B ∩ H') ∈ 𝒯 :=
      (h𝒯.axiom1 hs₃' (by omega)).resolve_left hn₃
    have hT₃ : (B ∩ H', A ∪ H) ∈ 𝒯' := GraphMinor.GM10.theorem_2_9_proof h𝒯' hBAT hs₃' (by omega)
      (Or.inr (Or.inl inter_subset_left))
    obtain ⟨hA, -⟩ := heq hs₃ ⟨hm₃, hT₃⟩ hle₃
    obtain ⟨c, hc⟩ := hne
    have hcA : c ∈ A.edgeSet := hA ▸ Or.inr hc
    have hcB : c ∈ B.edgeSet := hB ▸ Or.inr hc
    have : c ∈ (A ∩ B).edgeSet := ⟨hcA, hcB⟩
    rw [hAB.edgeSet_inter_eq] at this
    exact this
  rcases hmem with h | h
  · have hn : (H, H') ∉ 𝒯' := fun hc ↦ hnb ⟨h, hc⟩
    have hm := (h𝒯'.axiom1 hHH' (hordH.trans_lt hlt')).resolve_left hn
    exact Or.inl (heq hHH' ⟨h, hm⟩ hle₁)
  · have hn : (H, H') ∉ 𝒯 := fun hc ↦ hnb ⟨hc, h⟩
    have hm := (h𝒯.axiom1 hHH' (hordH.trans_lt hlt)).resolve_left hn
    obtain ⟨h₁, h₂⟩ := heq hHH'.symm ⟨hm, h⟩ (hcomm ▸ hle₁)
    exact Or.inr ⟨h₂, h₁, hn⟩

end Abstract

section Geometry

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D G₃ : Drawing Shat}

/-- Two edges of `G₃` with the same ends, in a region of `Γ`, are equal. -/
theorem spoke_unique (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected)
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃) {e₁ e₂ r : Set Shat} (he₁ : e₁ ∈ G₃.E)
    (he₂ : e₂ ∈ G₃.E) (hr : r ∈ Γ.hatRegions cap) (h₁r : e₁ ⊆ r) (h₂r : e₂ ⊆ r) {v₀ : S}
    (hv₀ : v₀ ∈ Γ.V) {w : Shat} (hw : w ∈ r) (hwG : w ∈ G₃.V)
    (h₁ : closure e₁ ∩ G₃.V = {cap.emb v₀, w}) (h₂ : closure e₂ ∩ G₃.V = {cap.emb v₀, w}) :
    e₁ = e₂ := by
  by_contra hne
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hrD := hD.hatRegion_mem_R hr
  have hdis : Disjoint r D.U := by
    refine disjoint_left.mpr fun x hx hxU ↦ region_subset hrD hx hxU
  have hvne : cap.emb v₀ ≠ w := fun h ↦ disjoint_left.mp hdis hw
    (D.V_subset_U (by rw [hD.hV]; exact h ▸ mem_image_of_mem _ hv₀))
  have hL₁ : IsLineWithEnds (closure e₁) (cap.emb v₀) w := isLine_closure he₁ hvne h₁
  have hL₂ : IsLineWithEnds (closure e₂) (cap.emb v₀) w := isLine_closure he₂ hvne h₂
  have hcl : ∀ {e}, e ∈ G₃.E → closure e ∩ G₃.V = {cap.emb v₀, w} → closure e ⊆ e ∪ {cap.emb v₀, w}
    := by
    intro e he hset x hx
    rcases closure_edge_subset he hx with h | h
    · exact Or.inl h
    · exact Or.inr (hset ▸ ⟨hx, h⟩)
  have hcap : closure e₁ ∩ closure e₂ ⊆ {cap.emb v₀, w} := by
    rintro x ⟨hx₁, hx₂⟩
    rcases hcl he₁ h₁ hx₁ with h | h
    · rcases hcl he₂ h₂ hx₂ with h' | h'
      · exact absurd (arcComp_eq_of_mem he₁ he₂ h h') hne
      · exact h'
    · exact h
  have hO := isOArc_union hL₁ hL₂ hcap
  have hsubr : (closure e₁ ∪ closure e₂) \ {cap.emb v₀} ⊆ r := by
    have hc : ∀ {e}, e ∈ G₃.E → e ⊆ r → closure e ∩ G₃.V = {cap.emb v₀, w} →
        closure e \ {cap.emb v₀} ⊆ r := by
      intro e he her hset x hx
      rcases hcl he hset hx.1 with h | h | h
      · exact her h
      · exact absurd h hx.2
      · exact h ▸ hw
    rintro x ⟨hx | hx, hxn⟩
    · exact hc he₁ h₁r h₁ ⟨hx, hxn⟩
    · exact hc he₂ h₂r h₂ ⟨hx, hxn⟩
  have hvm : cap.emb v₀ ∈ closure e₁ := by
    have : cap.emb v₀ ∈ closure e₁ ∩ G₃.V := by rw [h₁]; exact Or.inl rfl
    exact this.1
  have hclv : cap.emb v₀ ∈ closure ((closure e₁ ∪ closure e₂) \ {cap.emb v₀}) := by
    have : e₁ ⊆ (closure e₁ ∪ closure e₂) \ {cap.emb v₀} := fun x hx ↦
      ⟨Or.inl (subset_closure hx), fun h ↦ hdis.le_bot ⟨h₁r hx, D.V_subset_U (by
        rw [hD.hV, mem_singleton_iff.mp h]
        exact mem_image_of_mem _ hv₀)⟩⟩
    exact closure_mono this hvm
  obtain ⟨Δ, hΔ, hbd, hΔU⟩ := pinch hS hD h3 hr hv₀ hO (Or.inl hvm) hclv hsubr
  have hsubΔ : Δ ⊆ r ∪ {cap.emb v₀} := by
    have hopen := hΔ.isOpen_discInt hman
    obtain ⟨x, hx⟩ := he₁.1
    have hxb : x ∈ discBd Δ := by rw [hbd]; exact Or.inl (subset_closure hx)
    have hxΔ : x ∈ closure (discInt Δ) := hΔ.subset_closure_discInt (Surface.discBd_subset _ hxb)
    obtain ⟨y, hyr, hyi⟩ := mem_closure_iff.mp hxΔ r (region_isOpen hrD) (h₁r hx)
    have hdI : Disjoint (discInt Δ) D.U := by
      refine disjoint_left.mpr fun z hz hzU ↦ ?_
      have hzv : z = cap.emb v₀ := hΔU ⟨hz.1, hzU⟩
      apply hz.2
      rw [hbd, hzv]
      exact Or.inl hvm
    have hIr := subset_region hrD hΔ.isPreconnected_discInt hdI hyi hyr
    intro z hz
    by_cases hzb : z ∈ discBd Δ
    · rw [hbd] at hzb
      by_cases hzv : z = cap.emb v₀
      · exact Or.inr hzv
      · exact Or.inl (hsubr ⟨hzb, hzv⟩)
    · exact Or.inl (hIr ⟨hz, hzb⟩)
  refine hrad.2.2.2.2.2.2 e₁ he₁ e₂ he₂ hne (cap.emb v₀) ?_ r hrD w ⟨hw, hwG⟩ h₁ h₂
    ⟨Δ, hΔ, hsubΔ, ?_⟩
  · change cap.emb v₀ ∈ D.V
    rw [hD.hV]
    exact mem_image_of_mem _ hv₀
  · rw [← hbd, ← subBd_eq_frontier', IsClosedDisc.frontier_eq_discBd hT hΔ]

/-- **The two sides of a spoke.** An edge `f` of `sk(Γ)` on the boundary of a region `r` at `v` and
the
spoke from `v` into `r` lie on the boundary of one region of `H = sk(Γ) ∪ G₃`. -/
theorem pair_side [ConnectedSpace Shat] (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) {f : Set S}
    (hf : f ∈ arcComponentsIn (Γ.skU \ Γ.V)) {v₀ : S} (hv₀ : v₀ ∈ Γ.V) (hvf : v₀ ∈ tilde f)
    {r : Set Shat} (hr : r ∈ Γ.hatRegions cap) (hfr : cap.emb '' f ⊆ frontier r)
    {e : Set Shat} (he : e ∈ G₃.E) (her : e ⊆ r) {w : Shat} (hw : w ∈ r) (hwG : w ∈ G₃.V)
    (hset : closure e ∩ G₃.V = {cap.emb v₀, w}) :
    ∃ p ∈ (radialUnion hrad).R, e ⊆ closure p ∧ cap.emb '' f ⊆ closure p := by
  classical
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hrD := hD.hatRegion_mem_R hr
  have hDE : D.E.Nonempty := hD.E_nonempty h3.1
  have hg : cap.emb '' f ∈ D.E := hD.edge_iff.mpr ⟨f, hf, rfl⟩
  have : Nonempty Shat := ⟨w⟩
  let H := radialUnion hrad
  have hE : H.E = D.E ∪ G₃.E := radialUnion_E hrad
  have hV : H.V = G₃.V := radialUnion_V hrad
  have hvD : cap.emb v₀ ∈ D.V := by
    rw [hD.hV]
    exact mem_image_of_mem _ hv₀
  have hvG : cap.emb v₀ ∈ G₃.V := hrad.2.2.1 hvD
  have hvH : cap.emb v₀ ∈ H.V := hV ▸ hvG
  obtain ⟨γ, hγ⟩ := exists_edgePar H
  have hgH : cap.emb '' f ∈ H.E := hE ▸ Or.inl hg
  have hcl : cap.emb v₀ ∈ closure (cap.emb '' f) :=
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hvf.1)
  obtain ⟨b, hb⟩ := exists_end_eq hγ hgH hvH hcl
  let j : halfEdges H γ (cap.emb v₀) := ⟨(cap.emb '' f, b), hgH, hb⟩
  have hfin : Finite (halfEdges H γ (cap.emb v₀)) := (finite_halfEdges H γ _).to_subtype
  obtain ⟨next, ρ, P, W, Q, τ, hsec, -, -⟩ := exists_sectors' hT H hγ hvH
    (two_half_edges hrad hT hmax hDE hγ hvD)
  have hsurj : Function.Surjective next := Finite.injective_iff_surjective.mp hsec.corners.inj
  obtain ⟨k, hk⟩ := hsurj j
  -- A region of `H` inside `r` with `f` on its boundary.
  obtain ⟨x, hxf⟩ := hg.1
  have hxr : x ∈ closure r := frontier_subset_closure (hfr hxf)
  have hRfin : H.R.Finite := finite_R hT H
  have hHsub : ∀ p ∈ H.R, (p ∩ r).Nonempty → p ⊆ r := by
    intro p hp ⟨z, hzp, hzr⟩
    obtain ⟨y, hy, rfl⟩ := id hp
    refine subset_region hrD isPreconnected_connectedComponentIn ?_ hzp hzr
    refine disjoint_left.mpr fun a ha haD ↦ ?_
    exact (connectedComponentIn_subset _ _ ha).2 (Or.inl haD)
  have hxdense : x ∈ closure (⋃ p ∈ {p ∈ H.R | p ⊆ r}, p) := by
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨y, hyO, hyr⟩ := mem_closure_iff.mp hxr O hO hxO
    obtain ⟨z, ⟨hzO, hzr⟩, hzU⟩ := exists_notMem_U (Γ := H) hT
      (hO.inter (region_isOpen hrD)) ⟨y, hyO, hyr⟩
    obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
    exact ⟨z, hzO, mem_biUnion (x := p) ⟨hp, hHsub p hp ⟨z, hzp, hzr⟩⟩ hzp⟩
  have hfinite : {p ∈ H.R | p ⊆ r}.Finite := hRfin.subset fun _ hp => hp.1
  rw [hfinite.closure_biUnion] at hxdense
  obtain ⟨p, ⟨hp, hpr⟩, hxp⟩ := mem_iUnion₂.mp hxdense
  have hfp : cap.emb '' f ⊆ closure p :=
    edge_subset_closure_of_incident hT hgH hp ⟨x, hxf, hxp⟩
  refine ⟨p, hp, ?_, hfp⟩
  have hjp : (next k).1.1 ⊆ closure p := by rw [hk]; exact hfp
  -- The half-edge on the other side of the corner.
  obtain ⟨i, hine, hip⟩ : ∃ i : halfEdges H γ (cap.emb v₀), i ≠ j ∧ i.1.1 ⊆ closure p := by
    rcases hsec.corners.sides k p hp hjp with rfl | rfl
    · obtain ⟨k', hk'⟩ := hsurj k
      refine ⟨k, ?_, ?_⟩
      · rw [← hk]
        exact (hsec.next_ne k).symm
      · have := hsec.corners.right k'
        rwa [hk'] at this
    · refine ⟨next (next k), ?_, hsec.corners.left (next k)⟩
      rw [← hk]
      exact hsec.next_ne (next k)
  have hiE : i.1.1 ∈ H.E := i.2.1
  have hidisj : i.1.1 ∉ D.E := by
    intro hiD
    obtain ⟨e', -, -, huniq, -⟩ := face_edge hrad hT hmax hDE hp
    have h₁ : i.1.1 = cap.emb '' f := (huniq _ hiD hip).trans (huniq _ hg hfp).symm
    have hbne : i.1.2 ≠ b := by
      intro hbb
      exact hine (Subtype.ext (Prod.ext h₁ hbb))
    have hend : γ (cap.emb '' f) (endOf i.1.2) = cap.emb v₀ := by
      have := i.2.2
      rwa [h₁] at this
    obtain ⟨u, u', huu, hset'⟩ := hD.no_loops hS _ hg
    have hforall : ∀ c : Bool, γ (cap.emb '' f) (endOf c) = cap.emb v₀ := by
      intro c
      by_cases hc : c = b
      · rw [hc]; exact hb
      · have : c = i.1.2 := by cases c <;> cases b <;> cases hi : i.1.2 <;> simp_all
        rw [this]; exact hend
    have hm : ∀ {y}, y ∈ closure (cap.emb '' f) ∩ D.V → y = cap.emb v₀ := by
      rintro y ⟨hy, hyD⟩
      obtain ⟨c, hc⟩ := exists_end_eq hγ hgH (hV ▸ hrad.2.2.1 hyD) hy
      rw [← hc, hforall]
    have h₁' : u ∈ closure (cap.emb '' f) ∩ D.V := by rw [hset']; exact Or.inl rfl
    have h₂' : u' ∈ closure (cap.emb '' f) ∩ D.V := by rw [hset']; exact Or.inr rfl
    exact huu ((hm h₁').trans (hm h₂').symm)
  have hiG : i.1.1 ∈ G₃.E := by
    have := hiE
    rw [hE] at this
    exact this.resolve_left hidisj
  obtain ⟨v', hv', r', hr', w', hw', hw'G, hset', hsubr'⟩ := spoke_ends hrad hT hiG
  have hvi : cap.emb v₀ ∈ closure i.1.1 := by
    have := end_mem_closure hγ hiE i.1.2
    rwa [i.2.2] at this
  obtain ⟨y, hy⟩ := hiG.1
  obtain ⟨z, hzr', hzp⟩ := mem_closure_iff.mp (hip hy) r' (region_isOpen hr') (hsubr' hy)
  have hrr : r' = r := region_eq_of_mem hr' hrD hzr' (hpr hzp)
  subst hrr
  have hww : w' = w := (hrad.2.2.2.1 r' hr').unique ⟨hw', hw'G⟩ ⟨hw, hwG⟩
  subst hww
  have hvv : v' = cap.emb v₀ := by
    have h₁ : cap.emb v₀ ∈ closure i.1.1 ∩ G₃.V := ⟨hvi, hvG⟩
    rw [hset'] at h₁
    rcases h₁ with h₁ | h₁
    · exact h₁.symm
    · exact absurd (D.V_subset_U hvD) (region_subset hr' (h₁ ▸ hw'))
  subst hvv
  have := spoke_unique hS hD h3 hrad hiG he hr hsubr' her hv₀ hw hwG hset' hset
  rw [← this]
  exact hip

/-- Two closed discs with the same boundary, in a surface, are equal or have disjoint insides. -/
theorem discInt_disjoint {T : Type} [TopologicalSpace T] [T2Space T] (hT : IsClosedSurface T)
    {Δ Δ₂ : Set T} (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂) (hbd : discBd Δ = discBd Δ₂)
    (hne : Δ ≠ Δ₂) : Disjoint (discInt Δ) (discInt Δ₂) := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have key : ∀ {X Y : Set T}, IsClosedDisc X → IsClosedDisc Y → discBd X = discBd Y →
      (discInt X ∩ discInt Y).Nonempty → X ⊆ Y := by
    intro X Y hX hY hb hm
    have hsub : discInt X ⊆ discInt Y := by
      refine hX.isPreconnected_discInt.subset_left_of_subset_union (hY.isOpen_discInt hman)
        hY.isClosed.isOpen_compl (disjoint_left.mpr fun w hw hn ↦ hn hw.1) (fun w hw ↦ ?_) hm
      by_cases hwY : w ∈ Y
      · exact Or.inl ⟨hwY, fun h ↦ hw.2 (hb ▸ h)⟩
      · exact Or.inr hwY
    exact hX.subset_closure_discInt.trans
      (closure_minimal (hsub.trans (discInt_subset Y)) hY.isClosed)
  refine disjoint_left.mpr fun y h₁ h₂ ↦ hne (Subset.antisymm ?_ ?_)
  · exact key hΔ hΔ₂ hbd ⟨y, h₁, h₂⟩
  · exact key hΔ₂ hΔ hbd.symm ⟨y, h₂, h₁⟩

omit [T2Space S] [T2Space Shat] in
theorem disc_edge_disjoint (rad : RadialDrawing cap Γ) {F : Drawing Shat}
    (hF : F.IsSubdrawing rad.G) {c : Set S} (hc : c ∈ Γ.E) : Disjoint (cap.emb '' c) F.U := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, hx, rfl⟩ hxF
  have hm : cap.emb x ∈ Γ.hatU cap ∩ rad.G.U :=
    ⟨mem_image_of_mem _ (hc.2.1 hx).1, hF.U_subset hxF⟩
  rw [rad.isPreRadial.1] at hm
  obtain ⟨z, hz, hzx⟩ := hm
  obtain rfl := cap.isEmbedding.injective hzx
  exact (hc.2.1 hx).2 hz

omit [T2Space S] in
/-- An edge of `Γ` lies inside `Δ` or outside `Δ`, when the boundary of `Δ` is a circuit of `Γ*`. -/
theorem disc_edge_side (rad : RadialDrawing cap Γ) {F : Drawing Shat} (hF : F.IsSubdrawing rad.G)
    (hman : ∀ x : Shat, IsManifoldPoint x) {Δ : Set Shat} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) {c : Set S} (hc : c ∈ Γ.E) :
    cap.emb '' c ⊆ discInt Δ ∨ cap.emb '' c ⊆ Δᶜ := by
  have hconn : IsPreconnected (cap.emb '' c) := hc.2.2.1.isConnected.isPreconnected.image _
    cap.isEmbedding.continuous.continuousOn
  refine hconn.subset_or_subset (hΔ.isOpen_discInt hman) hΔ.isClosed.isOpen_compl
    (disjoint_left.mpr fun w hw hn ↦ hn hw.1) fun y hy ↦ ?_
  by_cases hyΔ : y ∈ Δ
  · refine Or.inl ⟨hyΔ, fun hb ↦ disjoint_left.mp (disc_edge_disjoint rad hF hc) hy ?_⟩
    rwa [hbd] at hb
  · exact Or.inr hyΔ

theorem disjoint_discInt_closure {T : Type} [TopologicalSpace T] (hman : ∀ x : T, IsManifoldPoint x)
    {Δ : Set T} (hΔ : IsClosedDisc Δ) : Disjoint (discInt Δ) (closure Δᶜ) := by
  refine disjoint_left.mpr fun y hy hyc ↦ ?_
  obtain ⟨z, hz, hzi⟩ := mem_closure_iff.mp hyc _ (hΔ.isOpen_discInt hman) hy
  exact hzi hz.1

omit [T2Space S] in
theorem restrict_in (_hman : ∀ x : Shat, IsManifoldPoint x) {Δ : Set Shat} (hΔ : IsClosedDisc Δ)
    {c : Set S} (hc : c ∈ Γ.E) (h : cap.emb '' c ⊆ discInt Δ) :
    c ∈ (Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet := by
  refine ⟨hc, fun x hx ↦ (h (mem_image_of_mem _ hx)).1, fun v hv ↦ ?_⟩
  have h₁ : cap.emb v ∈ closure (cap.emb '' c) :=
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hv.1.1)
  exact closure_minimal (h.trans (discInt_subset Δ)) hΔ.isClosed h₁

omit [T2Space S] [T2Space Shat] in
theorem restrict_out {Δ : Set Shat} {c : Set S} (hc : c ∈ Γ.E) (h : cap.emb '' c ⊆ Δᶜ) :
    c ∈ (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)).edgeSet := by
  refine ⟨hc, fun x hx ↦ subset_closure (h (mem_image_of_mem _ hx)), fun v hv ↦ ?_⟩
  exact closure_mono h (image_closure_subset_closure_image cap.isEmbedding.continuous
    (mem_image_of_mem _ hv.1.1))

/-- **What a disc bounded by a circuit of `Γ*` does to `Γ`.** -/
theorem disc_facts (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) {F : Drawing Shat} (hF : F.IsCircuitOf rad.G) {Δ : Set Shat}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) :
    Γ.toHypergraph.IsSeparation (Γ.restrict (cap.emb ⁻¹' Δ)) (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∧
    (∀ v ∈ (Γ.restrict (cap.emb ⁻¹' Δ) ∩ Γ.restrict (cap.emb ⁻¹' closure Δᶜ)).vertexSet,
      cap.emb v ∈ F.U) ∧
    (Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet.Nonempty ∧
    ∀ e ∈ rad.G.E, rad.Splits (Γ.restrict (cap.emb ⁻¹' Δ))
      (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) e → e ∈ F.E := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hFG := hF.1
  have hdd := disjoint_discInt_closure hman hΔ
  have hopen := hΔ.isOpen_discInt hman
  have hmid : ∀ v ∈ (Γ.restrict (cap.emb ⁻¹' Δ) ∩ Γ.restrict (cap.emb ⁻¹' closure Δᶜ)).vertexSet,
      cap.emb v ∈ F.U := by
    rintro v ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    by_contra hn
    exact disjoint_left.mp hdd ⟨h₁, fun hb ↦ hn (hbd ▸ hb)⟩ h₂
  have hinter : ∀ c, c ∈ (Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet →
      c ∈ (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)).edgeSet → False := by
    rintro c ⟨hc, h₁, -⟩ ⟨-, h₂, -⟩
    obtain ⟨x, hx⟩ := hc.1
    refine disjoint_left.mp hdd ⟨h₁ hx, fun hb ↦ ?_⟩ (h₂ hx)
    exact disjoint_left.mp (disc_edge_disjoint rad hFG hc) (mem_image_of_mem _ hx) (hbd ▸ hb)
  have hsep : Γ.toHypergraph.IsSeparation (Γ.restrict (cap.emb ⁻¹' Δ))
      (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) := by
    rw [isSeparation_iff_of_le (Γ.restrict_le _) (Γ.restrict_le _)]
    refine ⟨?_, ?_, ?_⟩
    · apply Subset.antisymm
      · exact union_subset (Γ.restrict_le _).vertexSet_subset (Γ.restrict_le _).vertexSet_subset
      · intro v hv
        by_cases hvΔ : cap.emb v ∈ Δ
        · exact Or.inl ⟨hv, hvΔ⟩
        · exact Or.inr ⟨hv, subset_closure hvΔ⟩
    · apply Subset.antisymm
      · exact union_subset (Γ.restrict_le _).edgeSet_subset (Γ.restrict_le _).edgeSet_subset
      · intro c hc
        rcases disc_edge_side rad hFG hman hΔ hbd hc with h | h
        · exact Or.inl (restrict_in hman hΔ hc h)
        · exact Or.inr (restrict_out hc h)
    · exact eq_empty_of_forall_notMem fun c hc ↦ hinter c hc.1 hc.2
  have hsub' : F.U ⊆ rad.G.U := hFG.U_subset
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  have hDE := hD.E_nonempty h3.1
  have hbU : discBd Δ ⊆ G₃.U := by
    rw [hbd]
    exact hFG.U_subset.trans hsub.U_subset
  refine ⟨hsep, hmid, ?_, ?_⟩
  · obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := G₃) hT hopen
      hΔ.nonempty_discInt
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    have hsI := region_in hT hΔ hbU hs (subset_closure hys) hyO
    obtain ⟨f, c, hfc, hfs⟩ := exists_colour hD hrad hmax hDE hs
    obtain ⟨x, hx⟩ := hfc.mem.1
    refine ⟨c, restrict_in hman hΔ hfc.1 ?_⟩
    rcases disc_edge_side rad hFG hman hΔ hbd hfc.1 with h | h
    · exact h
    · exact absurd (hsI (hfs (mem_image_of_mem _ hx))).1 (h (mem_image_of_mem _ (hfc.subset hx)))
  · intro e he hsp
    by_contra heF
    obtain ⟨c₁, c₂, ⟨v₀, w, hv₀, hw, hsetG, f₁, f₂, hne, h₁, h₂, ht₁, ht₂, hfr₁, hfr₂⟩, hcase⟩ :=
      rad.splits_iff.mp hsp
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
    have hrr : rad.regionOf w = r := region_eq_of_mem (hD.hatRegion_mem_R hrO) hr hwO hw'
    rw [hrr] at hrO hfr₁ hfr₂
    obtain ⟨p₁, hp₁, hep₁, hfp₁⟩ := pair_side hS hD h3 hrad hmax h₁.mem hv₀ ht₁ hrO hfr₁ heG her hw'
      hw'G hset'
    obtain ⟨p₂, hp₂, hep₂, hfp₂⟩ := pair_side hS hD h3 hrad hmax h₂.mem hv₀ ht₂ hrO hfr₂ heG her hw'
      hw'G hset'
    have hedis := edge_disjoint_U hFG he heF
    have hbH : discBd Δ ⊆ (radialUnion hrad).U := fun x hx ↦ Or.inr (hbU hx)
    have heconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    obtain ⟨y, hye⟩ := he.1
    have hcases : e ⊆ discInt Δ ∨ e ⊆ Δᶜ := by
      refine heconn.subset_or_subset hopen hΔ.isClosed.isOpen_compl
        (disjoint_left.mpr fun w hw hn ↦ hn hw.1) fun z hz ↦ ?_
      by_cases hzΔ : z ∈ Δ
      · exact Or.inl ⟨hzΔ, fun hb ↦ disjoint_left.mp hedis hz (hbd ▸ hb)⟩
      · exact Or.inr hzΔ
    rcases hcases with hein | heout
    · have key : ∀ {f c p}, Γ.IsSkEdgeIn f c → p ∈ (radialUnion hrad).R → e ⊆ closure p →
          cap.emb '' f ⊆ closure p → c ∈ (Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet := by
        intro f c p hfc hp hep hfp
        have hpI := region_in hT hΔ hbH hp (hep hye) (hein hye)
        have hcl : closure p ⊆ Δ :=
          closure_minimal (hpI.trans (discInt_subset Δ)) hΔ.isClosed
        obtain ⟨x, hx⟩ := hfc.mem.1
        have hxc := mem_image_of_mem cap.emb (hfc.subset hx)
        refine restrict_in hman hΔ hfc.1 ?_
        rcases disc_edge_side rad hFG hman hΔ hbd hfc.1 with h | h
        · exact h
        · exact absurd (hcl (hfp (mem_image_of_mem _ hx))) (h hxc)
      rcases hcase with ⟨-, hb⟩ | ⟨hb, -⟩
      · exact hinter c₂ (key h₂ hp₂ hep₂ hfp₂) hb
      · exact hinter c₁ (key h₁ hp₁ hep₁ hfp₁) hb
    · have key : ∀ {f c p}, Γ.IsSkEdgeIn f c → p ∈ (radialUnion hrad).R → e ⊆ closure p →
          cap.emb '' f ⊆ closure p → c ∈ (Γ.restrict (cap.emb ⁻¹' closure Δᶜ)).edgeSet := by
        intro f c p hfc hp hep hfp
        have hpO : p ⊆ Δᶜ := by
          obtain ⟨z, hzO, hzp⟩ := mem_closure_iff.mp (hep hye) _ hΔ.isClosed.isOpen_compl
            (heout hye)
          obtain ⟨q, hq, rfl⟩ := id hp
          refine isPreconnected_connectedComponentIn.subset_right_of_subset_union hopen
            hΔ.isClosed.isOpen_compl (disjoint_left.mpr fun w hw hn ↦ hn hw.1) (fun a ha ↦ ?_)
            ⟨z, hzp, hzO⟩
          by_cases haΔ : a ∈ Δ
          · exact Or.inl ⟨haΔ, fun hb ↦ region_subset hp ha (hbH hb)⟩
          · exact Or.inr haΔ
        obtain ⟨x, hx⟩ := hfc.mem.1
        have hxc := mem_image_of_mem cap.emb (hfc.subset hx)
        refine restrict_out hfc.1 ?_
        rcases disc_edge_side rad hFG hman hΔ hbd hfc.1 with h | h
        · exact absurd (closure_mono hpO (hfp (mem_image_of_mem _ hx)))
            (disjoint_left.mp hdd (h hxc))
        · exact h
      rcases hcase with ⟨ha, -⟩ | ⟨-, ha⟩
      · exact hinter c₁ ha (key h₁ hp₁ hep₁ hfp₁)
      · exact hinter c₂ ha (key h₂ hp₂ hep₂ hfp₂)

end Geometry

theorem prop_inter {a₁ a₂ p₁ p₂ q₁ q₂ : Prop} (h₁ : (p₁ ∧ ¬ q₁) ∨ (¬ p₁ ∧ q₁))
    (h₂ : (p₂ ∧ ¬ q₂) ∨ (¬ p₂ ∧ q₂)) (ha : a₁ ↔ a₂) (hp : p₁ ↔ p₂) : (a₁ ∧ q₁) ↔ (a₂ ∧ q₂) := by
  tauto

section Main

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}

open Classical in
omit [T2Space S] [T2Space Shat] in
/-- A separation with a smaller middle and fewer split edges has at most the same `λ`-order. -/
theorem TieBreaker.lambda_le (tb : TieBreaker rad) {P Q A B : Hypergraph S (Set S)}
    (hV : (P ∩ Q).vertexSet ⊆ (A ∩ B).vertexSet)
    (hE : ∀ e ∈ rad.G.E, rad.Splits P Q e → rad.Splits A B e)
    (_hAB : Γ.toHypergraph.IsSeparation A B) :
    tb.lambdaOrder (P, Q) ≤ tb.lambdaOrder (A, B) := by
  have hfAB : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have h₁ : tb.N1 (P, Q) ≤ tb.N1 (A, B) := ncard_le_ncard hV hfAB
  have hEfin : rad.G.E.Finite := rad.G.finite_edges
  have hfs : ∀ A' B' : Hypergraph S (Set S), {e ∈ rad.G.E | rad.Splits A' B' e} ⊆
      ↑hEfin.toFinset := fun _ _ e he ↦ hEfin.mem_toFinset.mpr he.1
  have h₂ : tb.N2 (P, Q) ≤ tb.N2 (A, B) := by
    simp only [TieBreaker.N2, finsum_eq_sum_ite _ (hfs _ _)]
    refine Finset.sum_le_sum fun e he ↦ ?_
    have heE : e ∈ rad.G.E := hEfin.mem_toFinset.mp he
    have hpos := (tb.wtE_pos e heE).le
    by_cases a : rad.Splits P Q e
    · simp [heE, a, hE e heE a]
    · by_cases b : rad.Splits A B e <;> simp [heE, a, b, hpos]
  simp only [TieBreaker.lambdaOrder]
  rw [Prod.Lex.toLex_le_toLex]
  rcases h₁.lt_or_eq with h | h
  · exact Or.inl h
  · have heqV : (P ∩ Q).vertexSet = (A ∩ B).vertexSet :=
      eq_of_subset_of_ncard_le hV h.ge hfAB
    refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.toLex_le_toLex]
    rcases h₂.lt_or_eq with h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨h', le_of_eq ?_⟩
      simp only [TieBreaker.N3, heqV]

open Classical in
omit [T2Space S] [T2Space Shat] in
/-- A separation with a smaller middle that splits only edges split by `(A, B)`, but not all of
them,
has smaller `λ`-order. -/
theorem TieBreaker.lambda_lt (tb : TieBreaker rad) {P Q A B : Hypergraph S (Set S)}
    (hV : (P ∩ Q).vertexSet ⊆ (A ∩ B).vertexSet)
    (hE : ∀ e ∈ rad.G.E, rad.Splits P Q e → rad.Splits A B e) {e₀ : Set Shat} (he₀ : e₀ ∈ rad.G.E)
    (h₁ : rad.Splits A B e₀) (h₂ : ¬ rad.Splits P Q e₀) :
    tb.lambdaOrder (P, Q) < tb.lambdaOrder (A, B) := by
  have hfAB : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hN : tb.N1 (P, Q) ≤ tb.N1 (A, B) := ncard_le_ncard hV hfAB
  have hEfin : rad.G.E.Finite := rad.G.finite_edges
  have hfs : ∀ A' B' : Hypergraph S (Set S), {e ∈ rad.G.E | rad.Splits A' B' e} ⊆
      ↑hEfin.toFinset := fun _ _ e he ↦ hEfin.mem_toFinset.mpr he.1
  have hlt : tb.N2 (P, Q) < tb.N2 (A, B) := by
    simp only [TieBreaker.N2, finsum_eq_sum_ite _ (hfs _ _)]
    refine Finset.sum_lt_sum (fun e he ↦ ?_) ⟨e₀, hEfin.mem_toFinset.mpr he₀, ?_⟩
    · have heE : e ∈ rad.G.E := hEfin.mem_toFinset.mp he
      have hpos := (tb.wtE_pos e heE).le
      by_cases a : rad.Splits P Q e
      · simp [heE, a, hE e heE a]
      · by_cases b : rad.Splits A B e <;> simp [heE, a, b, hpos]
    · simp [he₀, h₁, h₂, tb.wtE_pos e₀ he₀]
  simp only [TieBreaker.lambdaOrder]
  rw [Prod.Lex.toLex_lt_toLex]
  rcases hN.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hlt

omit [T2Space S] in
omit [T2Space Shat] in
theorem tangleRep_spec (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) :
    tangleRep rad ord 𝒯 ≤ ord ∧ ∀ F : Drawing Shat, F.IsCircuitOf rad.G →
      F.E.ncard < 2 * tangleRep rad ord 𝒯 → ∃ Δ : Set Shat, IsClosedDisc Δ ∧ discBd Δ = F.U ∧
        (Γ.restrict (cap.emb ⁻¹' Δ), Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∈ 𝒯 := by
  have hne : {k : ℕ | k ≤ ord ∧ ∀ F : Drawing Shat, F.IsCircuitOf rad.G → F.E.ncard < 2 * k →
      ∃ Δ : Set Shat, IsClosedDisc Δ ∧ discBd Δ = F.U ∧
      (Γ.restrict (cap.emb ⁻¹' Δ), Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∈ 𝒯}.Nonempty :=
    ⟨0, Nat.zero_le _, fun F _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  exact Nat.sSup_mem hne ⟨ord, fun _ h ↦ h.1⟩

omit [T2Space S] in
/-- `rep(𝒯) ≤ rep(Γ)`: a circuit of half-length less than `rep(𝒯)` bounds a disc and is consequently
null-homotopic. -/
theorem tangleRep_le_rep (rad : RadialDrawing cap Γ) (ord : ℕ)
    (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) :
    (tangleRep rad ord 𝒯 : ℕ∞) ≤ Painting.rep rad := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  refine le_sInf ?_
  rintro _ ⟨F, hF, hn, rfl⟩
  by_contra hlt
  have hlt' : F.E.ncard / 2 < tangleRep rad ord 𝒯 := by
    exact_mod_cast not_le.mp hlt
  obtain ⟨Δ, hΔ, hbd, -⟩ := (tangleRep_spec rad ord 𝒯).2 F hF (by omega)
  have hbdS : Disjoint F.U (bd Shat) := disjoint_left.mpr fun x _ hx ↦ hx (hT.2.2 x)
  have hO := GM14.isOArc_of_isCircuit hF.2
  refine hn ((epstein Shat univ F.U (Surface.IsClosedSurface.isSurface hT) inferInstance hO
    (subset_univ _) hbdS).2.1 ⟨Δ, subset_univ _, hΔ, ?_⟩)
  rw [← hbd]
  exact Surface.discBd_subset Δ

omit [T2Space S] in
theorem Painting.restrict_le_of {Y : Hypergraph S (Set S)} {W : Set S}
    (hY : Y ≤ Γ.toHypergraph) (hV : Γ.V ∩ W ⊆ Y.vertexSet)
    (hE : (Γ.restrict W).edgeSet ⊆ Y.edgeSet) : Γ.restrict W ≤ Y := by
  refine ⟨hV, hE, fun e he ↦ ?_⟩
  rw [← hY.ends_eq e (hE he), (Γ.restrict_le _).ends_eq e he]

omit [T2Space Shat] in
theorem eq_of_all_edges (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) {X : Hypergraph S (Set S)} (hX : X ≤ Γ.toHypergraph)
    (hall : ∀ c ∈ Γ.E, c ∈ X.edgeSet) : X = Γ.toHypergraph := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hX le_rfl ?_ ?_
  · apply Subset.antisymm hX.vertexSet_subset
    intro v hv
    obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 rad hv
    have h₁ : v ∈ Γ.toHypergraph.ends c :=
      ⟨hc, hv, hvc, fun h ↦ Γ.disjoint_V hc h hv⟩
    rw [hX.ends_eq c (hall c hc)] at h₁
    exact X.vertex_mem_of_inc h₁
  · exact Subset.antisymm hX.edgeSet_subset hall

omit [TopologicalSpace S] [T2Space S] in
theorem left_ne_of_mem {G : Hypergraph S (Set S)} {θ : ℕ}
    {𝒰 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h𝒰 : IsTangle G θ 𝒰) {P Q}
    (hm : (P, Q) ∈ 𝒰) : P ≠ G := by
  intro heq
  refine h𝒰.axiom2 hm hm hm ?_
  rw [heq]
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.union_le (GM10.union_le le_rfl le_rfl) le_rfl) le_rfl
    (by simp) (by simp)

omit [T2Space Shat] in
/-- If `(P, P')` has its middle in the middle of `(A, B)`, and splits only edges that `(A, B)`
splits,
then the same holds for the two separations obtained by uncrossing. -/
theorem mix_facts (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    {A B P P' : Hypergraph S (Set S)} (hAB : Γ.toHypergraph.IsSeparation A B)
    (hPP : Γ.toHypergraph.IsSeparation P P')
    (hV : ∀ v ∈ (P ∩ P').vertexSet, v ∈ (A ∩ B).vertexSet)
    (hspAB : ∀ e ∈ rad.G.E, rad.Splits P P' e → rad.Splits A B e) :
    ((A ∩ P') ∩ (B ∪ P)).vertexSet ⊆ (A ∩ B).vertexSet ∧
    (∀ e ∈ rad.G.E, rad.Splits (A ∩ P') (B ∪ P) e → rad.Splits A B e) ∧
    ((A ∪ P) ∩ (B ∩ P')).vertexSet ⊆ (A ∩ B).vertexSet ∧
    (∀ e ∈ rad.G.E, rad.Splits (A ∪ P) (B ∩ P') e → rad.Splits A B e) := by
  have hs₂ : Γ.toHypergraph.IsSeparation (A ∩ P') (B ∪ P) := (hAB.symm.union_inter hPP).symm
  have hs₃ : Γ.toHypergraph.IsSeparation (A ∪ P) (B ∩ P') := hAB.union_inter hPP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro v ⟨⟨ha, hp'⟩, hb | hp⟩
    · exact ⟨ha, hb⟩
    · exact hV v ⟨hp, hp'⟩
  · intro e he hsp
    obtain ⟨c₁, c₂, hp, -⟩ := rad.splits_iff.mp hsp
    obtain ⟨hc₁, hc₂⟩ : c₁ ∈ Γ.E ∧ c₂ ∈ Γ.E := by
      obtain ⟨_, _, _, _, _, _, _, _, h₁, h₂, _⟩ := hp
      exact ⟨h₁.1, h₂.1⟩
    have e₁ := splits_of_pair hS h3 hp hs₂
    have e₂ := splits_of_pair hS h3 hp hAB
    have e₃ := splits_of_pair hS h3 hp hPP
    by_contra hn
    have hn' : ¬ rad.Splits P P' e := fun h ↦ hn (hspAB e he h)
    have p₁ := edge_cases hPP hc₁
    have p₂ := edge_cases hPP hc₂
    have ha : c₁ ∈ A.edgeSet ↔ c₂ ∈ A.edgeSet := not_not.mp fun h ↦ hn (e₂.mpr h)
    have hq : c₁ ∈ P.edgeSet ↔ c₂ ∈ P.edgeSet := not_not.mp fun h ↦ hn' (e₃.mpr h)
    exact e₁.mp hsp (prop_inter p₁ p₂ ha hq)
  · rintro v ⟨ha | hp, hb, hp'⟩
    · exact ⟨ha, hb⟩
    · exact hV v ⟨hp, hp'⟩
  · intro e he hsp
    obtain ⟨c₁, c₂, hp, -⟩ := rad.splits_iff.mp hsp
    have e₁ := splits_of_pair hS h3 hp hs₃
    have e₂ := splits_of_pair hS h3 hp hAB
    have e₃ := splits_of_pair hS h3 hp hPP
    by_contra hn
    have hn' : ¬ rad.Splits P P' e := fun h ↦ hn (hspAB e he h)
    have ha : c₁ ∈ A.edgeSet ↔ c₂ ∈ A.edgeSet := not_not.mp fun h ↦ hn (e₂.mpr h)
    have hq : c₁ ∈ P.edgeSet ↔ c₂ ∈ P.edgeSet := not_not.mp fun h ↦ hn' (e₃.mpr h)
    exact e₁.mp hsp (or_congr ha hq)

/-- **Graph Minors XIX, (8.4).** "Let $\mathscr{T}, \mathscr{T}'$ be tangles in $\Gamma$ and let
$(A, B)$ be the
$(\mathscr{T}, \mathscr{T}')$-distinction. Suppose that $|V(A \cap B)| < rep(\mathscr{T})$.
Then there is a circuit $F$ in $\Gamma^*$ such that $A = \Gamma \cap ins(F)$, $B = \Gamma
\cap out(F)$." -/
theorem theorem_8_4_proof (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad) {ord ord' : ℕ}
    {𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯')
    {A B : Hypergraph S (Set S)} (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' A B)
    (hlt : Hypergraph.separationOrder A B < tangleRep rad ord 𝒯) :
    ∃ (F : Drawing Shat) (Δ : Set Shat), IsInsOf rad ord 𝒯 F Δ ∧
      A = Γ.restrict (cap.emb ⁻¹' Δ) ∧ B = Γ.restrict (cap.emb ⁻¹' closure Δᶜ) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have htie := tb.isTieBreaker hS h3
  have hABT := hd.1.1
  have hBAT := hd.1.2
  have hAB := h𝒯.isSeparation hABT
  have hinc : ∀ {X : Hypergraph S (Set S)}, X ≤ Γ.toHypergraph → (∀ c ∈ Γ.E, c ∈ X.edgeSet) →
      X = Γ.toHypergraph := fun hX hall ↦ eq_of_all_edges hS h3 rad hX hall
  have hnotfull : ∀ {θ : ℕ} {𝒰 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))},
      IsTangle Γ.toHypergraph θ 𝒰 → ∀ {P Q}, (P, Q) ∈ 𝒰 → P ≠ Γ.toHypergraph := fun h𝒰 _ _ hm ↦
    left_ne_of_mem h𝒰 hm
  have hA : A.edgeSet.Nonempty := by
    by_contra hn
    refine hnotfull h𝒯' hBAT (hinc hAB.right_le fun c hc ↦ ?_)
    rcases edge_cases hAB hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd ⟨c, h⟩ hn
    · exact h
  have hB : B.edgeSet.Nonempty := by
    by_contra hn
    refine hnotfull h𝒯 hABT (hinc hAB.left_le fun c hc ↦ ?_)
    rcases edge_cases hAB hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd ⟨c, h⟩ hn
  have hlt' : (Hypergraph.separationOrder A B : ℕ∞) < Painting.rep rad :=
    lt_of_lt_of_le (by exact_mod_cast hlt) (tangleRep_le_rep rad ord 𝒯)
  obtain ⟨F, Δ, hF, hsplit, hΔ, hbd, hsub, hcount, hmid⟩ :=
    theorem_8_1' hS h3 rad hAB hlt' hA hB
  have hsmall : F.E.ncard < 2 * tangleRep rad ord 𝒯 := by omega
  have hbound : ∀ {P P' : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation P P' →
      (∀ v ∈ (P ∩ P').vertexSet, cap.emb v ∈ F.U) →
      (∀ e ∈ rad.G.E, rad.Splits P P' e → e ∈ F.E) →
      tb.lambdaOrder (P, P') ≤ tb.lambdaOrder (A, B) ∧
      tb.lambdaOrder (A ∩ P', B ∪ P) ≤ tb.lambdaOrder (A, B) ∧
      tb.lambdaOrder (A ∪ P, B ∩ P') ≤ tb.lambdaOrder (A, B) := by
    intro P P' hPP hmidP hsplP
    have hV : ∀ v ∈ (P ∩ P').vertexSet, v ∈ (A ∩ B).vertexSet := fun v hv ↦
      hmid v (hmidP v hv) (hPP.left_le.vertexSet_subset hv.1)
    have hspAB : ∀ e ∈ rad.G.E, rad.Splits P P' e → rad.Splits A B e := fun e he h ↦
      hsplit e (hsplP e he h)
    obtain ⟨m₁, m₂, m₃, m₄⟩ := mix_facts hS h3 hAB hPP hV hspAB
    exact ⟨tb.lambda_le (fun v hv ↦ hV v hv) hspAB hAB, tb.lambda_le m₁ m₂ hAB,
      tb.lambda_le m₃ m₄ hAB⟩
  obtain ⟨hsep, hmidH, hne, hspl⟩ := disc_facts hS h3 rad hF hΔ hbd
  obtain ⟨b₁, b₂, b₃⟩ := hbound hsep hmidH hspl
  rcases distinction_cases htie h𝒯 h𝒯' hd hsep b₁ b₂ b₃ hsub hne with ⟨h₁, h₂⟩ | ⟨h₁, h₂, hnT⟩
  · refine ⟨F, Δ, ⟨hF, hsmall, hΔ, hbd, ?_⟩, h₁.symm, h₂.symm⟩
    rw [h₁, h₂]
    exact hABT
  · obtain ⟨Δ₂, hΔ₂, hbd₂, hmem⟩ := (tangleRep_spec rad ord 𝒯).2 F hF hsmall
    have hne₂ : Δ ≠ Δ₂ := by
      rintro rfl
      exact hnT hmem
    have hdis := discInt_disjoint hT hΔ hΔ₂ (hbd.trans hbd₂.symm) hne₂
    obtain ⟨hsep₂, hmid₂, hne₂', hspl₂⟩ := disc_facts hS h3 rad hF hΔ₂ hbd₂
    obtain ⟨d₁, d₂, d₃⟩ := hbound hsep₂ hmid₂ hspl₂
    have hle : Γ.restrict (cap.emb ⁻¹' Δ₂) ≤ A := by
      have hA' : A = Γ.restrict (cap.emb ⁻¹' closure Δᶜ) := h₂.symm
      refine Painting.restrict_le_of hAB.left_le ?_ ?_
      · rintro v ⟨hv, hvΔ⟩
        rw [hA']
        refine ⟨hv, ?_⟩
        by_cases hvF : cap.emb v ∈ F.U
        · have hfr : discBd Δ ⊆ frontier Δ := (IsClosedDisc.frontier_eq_discBd hT hΔ).ge
          have := hfr (hbd ▸ hvF)
          rw [frontier_eq_closure_inter_closure] at this
          exact this.2
        · have hvI : cap.emb v ∈ discInt Δ₂ := ⟨hvΔ, fun hb ↦ hvF (hbd₂ ▸ hb)⟩
          refine subset_closure fun hc ↦ ?_
          exact disjoint_left.mp hdis ⟨hc, fun hb ↦ hvF (hbd ▸ hb)⟩ hvI
      · rintro c ⟨hc, hsubc, -⟩
        rw [hA']
        refine restrict_out hc ?_
        rcases disc_edge_side rad hF.1 hman hΔ hbd hc with h | h
        · exfalso
          obtain ⟨x, hx⟩ := hc.1
          have hx₁ := mem_image_of_mem cap.emb hx
          refine disjoint_left.mp hdis (h hx₁) ⟨hsubc hx, fun hb ↦ ?_⟩
          exact disjoint_left.mp (disc_edge_disjoint rad hF.1 hc) hx₁ (hbd₂ ▸ hb)
        · exact h
    rcases distinction_cases htie h𝒯 h𝒯' hd hsep₂ d₁ d₂ d₃ (Or.inl hle) hne₂' with
      ⟨h₃, h₄⟩ | ⟨-, -, hn⟩
    · exact ⟨F, Δ₂, ⟨hF, hsmall, hΔ₂, hbd₂, hmem⟩, h₃.symm, h₄.symm⟩
    · exact absurd hmem hn

end Main

end GraphMinor.GM19
