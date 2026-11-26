/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Sides

/-!
# Graph Minors XIX, (8.5)

A circuit `F` of `Γ*` that bounds a closed disc gives a separation of `Γ`. Its first `λ`-term is
`½|E(F)|`, and it splits exactly the edges of `F` (`disc_split`, `disc_order`). So a shorter or
lighter circuit gives a separation of smaller `λ`-order (`disc_lambda_lt`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}

/-- The part of `Γ` in a subset `X` of `Σ̂`. -/
abbrev partIn (cap : IsCappedSurface S Shat) (Γ : Painting S) (X : Set Shat) : Hypergraph S (Set S)
  :=
  Γ.restrict (cap.emb ⁻¹' X)

omit [T2Space S] [T2Space Shat] in
theorem restrict_side {Ω : Set Shat} {c : Set S} (hc : c ∈ Γ.E) (h : cap.emb '' c ⊆ Ω) :
    c ∈ (partIn cap Γ (closure Ω)).edgeSet := by
  refine ⟨hc, fun x hx ↦ subset_closure (h (mem_image_of_mem _ hx)), fun v hv ↦ ?_⟩
  exact closure_mono h (image_closure_subset_closure_image cap.isEmbedding.continuous
    (mem_image_of_mem _ hv.1.1))

variable [ConnectedSpace Shat]

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
theorem side_edge (rad : RadialDrawing cap Γ) {F : Drawing Shat} (hF : F.IsSubdrawing rad.G)
    {Ω : Set Shat} (hΩ : IsSide Ω F) {c : Set S} (hc : c ∈ Γ.E)
    (hm : (cap.emb '' c ∩ Ω).Nonempty) : cap.emb '' c ⊆ Ω := by
  have hconn : IsPreconnected (cap.emb '' c) := hc.2.2.1.isConnected.isPreconnected.image _
    cap.isEmbedding.continuous.continuousOn
  exact hΩ.subset hconn (disc_edge_disjoint rad hF hc) hm

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
/-- Parts of `Γ` in the closures of three sides that cover `Σ̂` have union `Γ`. -/
theorem part_cover (rad : RadialDrawing cap Γ) {F₁ F₂ F₃ : Drawing Shat} {Ω₁ Ω₂ Ω₃ : Set Shat}
    (h₁ : F₁.IsSubdrawing rad.G) (h₂ : F₂.IsSubdrawing rad.G) (h₃ : F₃.IsSubdrawing rad.G)
    (s₁ : IsSide Ω₁ F₁) (s₂ : IsSide Ω₂ F₂) (s₃ : IsSide Ω₃ F₃)
    (hcov : ∀ x, x ∈ closure Ω₁ ∨ x ∈ closure Ω₂ ∨ x ∈ closure Ω₃) :
    partIn cap Γ (closure Ω₁) ∪ partIn cap Γ (closure Ω₂) ∪ partIn cap Γ (closure Ω₃) =
      Γ.toHypergraph := by
  have hle := GM10.union_le (GM10.union_le (Γ.restrict_le (cap.emb ⁻¹' closure Ω₁))
    (Γ.restrict_le (cap.emb ⁻¹' closure Ω₂))) (Γ.restrict_le (cap.emb ⁻¹' closure Ω₃))
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_
  · refine Subset.antisymm hle.vertexSet_subset fun v hv ↦ ?_
    rcases hcov (cap.emb v) with h | h | h
    · exact Or.inl (Or.inl ⟨hv, h⟩)
    · exact Or.inl (Or.inr ⟨hv, h⟩)
    · exact Or.inr ⟨hv, h⟩
  · refine Subset.antisymm hle.edgeSet_subset fun c hc ↦ ?_
    have hc' : c ∈ Γ.E := hc
    obtain ⟨x, hx⟩ := hc'.1
    have hxi := mem_image_of_mem cap.emb hx
    have key : ∀ {K : Drawing Shat} {Ω : Set Shat}, K.IsSubdrawing rad.G → IsSide Ω K →
        cap.emb x ∈ closure Ω → c ∈ (partIn cap Γ (closure Ω)).edgeSet := by
      intro K Ω hK hΩ hxcl
      have hxΩ : cap.emb x ∈ Ω := hΩ.mem_of_closure hxcl (disjoint_left.mp
        (disc_edge_disjoint rad hK hc') hxi)
      exact restrict_side hc' (side_edge rad hK hΩ hc' ⟨_, hxi, hxΩ⟩)
    rcases hcov (cap.emb x) with h | h | h
    · exact Or.inl (Or.inl (key h₁ s₁ h))
    · exact Or.inl (Or.inr (key h₂ s₂ h))
    · exact Or.inr (key h₃ s₃ h)

variable {F : Drawing Shat} {Δ : Set Shat}

/-- Every edge of a circuit that bounds a closed disc is split by the separation of the disc. -/
theorem disc_split (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) (hF : F.IsCircuitOf rad.G) (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) {e : Set Shat} (he : e ∈ F.E) :
    rad.Splits (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)) e := by
  classical
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  have hDE := hD.E_nonempty h3.1
  have hFG₃ : F.IsSubdrawing G₃ := hF.1.trans hsub
  have hin := isSide_int hT hΔ hbd
  have hout := isSide_out hT hΔ hbd
  have heG := hsub.2 (hF.1.2 he)
  obtain ⟨z, hz⟩ := heG.1
  have hzU : z ∈ F.U := F.closure_subset_U he (subset_closure hz)
  obtain ⟨s, hs, hzs, hm⟩ := exists_region_near hT G₃ hin.isOpen (hin.U_subset_closure hzU)
  obtain ⟨s', hs', hzs', hm'⟩ := exists_region_near hT G₃ hout.isOpen (hout.U_subset_closure hzU)
  have hsI := hin.region_subset hFG₃ hs hm
  have hsO := hout.region_subset hFG₃ hs' hm'
  let t : Set S → Prop := fun c ↦ cap.emb '' c ⊆ discInt Δ
  have hside : ∀ {c}, c ∈ Γ.E → cap.emb '' c ⊆ discInt Δ ∨ cap.emb '' c ⊆ Δᶜ := fun hc ↦
    disc_edge_side rad hF.1 hman hΔ hbd hc
  have hcol : s ∈ colourSet cap Γ G₃ t := by
    obtain ⟨f, c, hfc, hfs⟩ := exists_colour hD hrad hmax hDE hs
    refine ⟨hs, f, c, hfc, hfs, ?_⟩
    obtain ⟨x, hx⟩ := hfc.mem.1
    rcases hside hfc.1 with h | h
    · exact h
    · exact absurd (hsI (hfs (mem_image_of_mem _ hx))).1 (h (mem_image_of_mem _ (hfc.subset hx)))
  have hnot : s' ∉ colourSet cap Γ G₃ t := by
    rintro ⟨-, f, c, hfc, hfs, ht⟩
    obtain ⟨x, hx⟩ := hfc.mem.1
    exact hsO (hfs (mem_image_of_mem _ hx)) (ht (mem_image_of_mem _ (hfc.subset hx))).1
  have hb : e ∈ (boundaryDrawing G₃ (colourSet cap Γ G₃ t)).E :=
    mem_boundaryDrawing_E.mpr ⟨⟨s, hcol, heG, hs, z, hz, hzs⟩, ⟨s', ⟨hs', hnot⟩, heG, hs', z, hz,
      hzs'⟩⟩
  obtain ⟨-, -, -, -, -, -, f₁, f₂, c₁, c₂, hp, h₁, h₂, -, -, hnt⟩ :=
    boundary_split hS hDE rad hD hrad hmax hsub hhat hb
  refine rad.splits_iff.mpr ⟨c₁, c₂, hp, ?_⟩
  have hinside : ∀ {c}, c ∈ Γ.E → t c → c ∈ (partIn cap Γ Δ).edgeSet := fun hc ht ↦
    restrict_in hman hΔ hc ht
  have houtside : ∀ {c}, c ∈ Γ.E → ¬ t c → c ∈ (partIn cap Γ (closure Δᶜ)).edgeSet := fun hc ht ↦
    restrict_out hc ((hside hc).resolve_left ht)
  by_cases ht₁ : t c₁
  · exact Or.inl ⟨hinside h₁.1 ht₁, houtside h₂.1 fun h ↦ hnt ⟨fun _ ↦ h, fun _ ↦ ht₁⟩⟩
  · have ht₂ : t c₂ := by
      by_contra h
      exact hnt ⟨fun h' ↦ absurd h' ht₁, fun h' ↦ absurd h' h⟩
    exact Or.inr ⟨houtside h₁.1 ht₁, hinside h₂.1 ht₂⟩

omit [ConnectedSpace Shat] in
/-- The order of the separation of a disc bounded by a circuit is half the length of the circuit. -/
theorem disc_order (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (rad : RadialDrawing cap Γ) (hF : F.IsCircuitOf rad.G) (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) :
    F.E.ncard = 2 * Hypergraph.separationOrder (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)) := by
  have hT := cap.isClosedSurface
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  have hFG₃ : F.IsSubdrawing G₃ := hF.1.trans hsub
  have hb := IsCircuit.ncard_E_eq hF.2 (P := D.V) fun e x y hl ↦
    bipartite_of_preRadial hrad.2 e x y ((hFG₃.isLink_iff hl.1).mp hl)
  have himage : F.V ∩ D.V = cap.emb '' (partIn cap Γ Δ ∩ partIn cap Γ (closure Δᶜ)).vertexSet := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxD⟩
      rw [hD.hV] at hxD
      obtain ⟨v, hv, rfl⟩ := hxD
      have hxU := F.V_subset_U hx
      have hfr : cap.emb v ∈ frontier Δ := by
        rw [IsClosedDisc.frontier_eq_discBd hT hΔ, hbd]
        exact hxU
      rw [frontier_eq_closure_inter_closure, hΔ.isClosed.closure_eq] at hfr
      exact mem_image_of_mem _ ⟨⟨hv, hfr.1⟩, ⟨hv, hfr.2⟩⟩
    · rintro _ ⟨v, hv, rfl⟩
      have hU := (disc_facts hS h3 rad hF hΔ hbd).2.1 v hv
      refine ⟨mem_V_of_mem_U hF.1 hU (rad.isPreRadial.2.1 (mem_image_of_mem _ hv.1.1)), ?_⟩
      rw [hD.hV]
      exact mem_image_of_mem _ hv.1.1
  rw [hb, himage, ncard_image_of_injective _ cap.isEmbedding.injective]
  rfl

/-- The second term of the `λ`-order of the separation of a disc is the weight of the circuit. -/
theorem disc_N2 (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad)
    (hF : F.IsCircuitOf rad.G) (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) :
    tb.N2 (partIn cap Γ Δ, partIn cap Γ (closure Δᶜ)) = tb.weightSub F := by
  have : {e ∈ rad.G.E | rad.Splits (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)) e} = F.E :=
    Subset.antisymm (fun e he ↦ (disc_facts hS h3 rad hF hΔ hbd).2.2.2 e he.1 he.2)
      fun e he ↦ ⟨hF.1.2 he, disc_split hS h3 rad hF hΔ hbd he⟩
  simp only [TieBreaker.N2, TieBreaker.weightSub]
  rw [this]

/-- A shorter circuit, or a lighter circuit of the same length, gives a smaller `λ`-order. -/
theorem disc_lambda_lt (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad)
    {C : Drawing Shat} {Δ' : Set Shat} (hC : C.IsCircuitOf rad.G) (hΔ' : IsClosedDisc Δ')
    (hbd' : discBd Δ' = C.U) (hF : F.IsCircuitOf rad.G) (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U)
    (h : C.E.ncard < F.E.ncard ∨ (C.E.ncard = F.E.ncard ∧ tb.weightSub C < tb.weightSub F)) :
    tb.lambdaOrder (partIn cap Γ Δ', partIn cap Γ (closure Δ'ᶜ)) <
      tb.lambdaOrder (partIn cap Γ Δ, partIn cap Γ (closure Δᶜ)) := by
  have o₁ := disc_order hS h3 rad hC hΔ' hbd'
  have o₂ := disc_order hS h3 rad hF hΔ hbd
  simp only [TieBreaker.lambdaOrder]
  rw [Prod.Lex.toLex_lt_toLex]
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (by simp only [TieBreaker.N1]; omega)
  · refine Or.inr ⟨by simp only [TieBreaker.N1]; omega, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    left
    rw [disc_N2 hS h3 tb hC hΔ' hbd', disc_N2 hS h3 tb hF hΔ hbd]
    exact h'

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
/-- Two disjoint sets of edges of `Γ*`, the second nonempty, have different weights, because the
weights are rationally independent. -/
theorem TieBreaker.weight_ne (tb : TieBreaker rad) {X Y : Set (Set Shat)} (hX : X ⊆ rad.G.E)
    (hY : Y ⊆ rad.G.E) (hd : Disjoint X Y) (hne : Y.Nonempty) :
    ∑ᶠ e ∈ X, tb.wtE e ≠ ∑ᶠ e ∈ Y, tb.wtE e := by
  classical
  intro heq
  have hfin : rad.G.E.Finite := rad.G.finite_edges
  let t := hfin.toFinset
  have ht : ∀ {Z : Set (Set Shat)}, Z ⊆ rad.G.E → Z ⊆ ↑t := fun hZ _ h ↦ hfin.mem_toFinset.mpr
    (hZ h)
  rw [finsum_eq_sum_ite _ (ht hX), finsum_eq_sum_ite _ (ht hY)] at heq
  let α : Set Shat → ℚ := fun e ↦ (if e ∈ X then 1 else 0) - (if e ∈ Y then 1 else 0)
  have hsum : ∑ᶠ e ∈ rad.G.E, (α e : ℝ) * tb.wtE e = ∑ᶠ v ∈ Γ.V, (((0 : S
    → ℚ) v : ℚ) : ℝ) * tb.wtV v := by
    have hr : ∑ᶠ v ∈ Γ.V, (((0 : S → ℚ) v : ℚ) : ℝ) * tb.wtV v = 0 := by simp
    rw [hr, finsum_eq_sum_ite _ (ht subset_rfl)]
    have hsplit : ∀ e ∈ t, (if e ∈ rad.G.E then (α e : ℝ) * tb.wtE e else 0) =
        (if e ∈ X then tb.wtE e else 0) - (if e ∈ Y then tb.wtE e else 0) := by
      intro e he
      have heE : e ∈ rad.G.E := hfin.mem_toFinset.mp he
      by_cases a : e ∈ X <;> by_cases b : e ∈ Y <;> simp [α, heE, a, b]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, heq, sub_self]
  obtain ⟨e, he⟩ := hne
  have := (tb.rationally_independent α 0 hsum).1 e (hY he)
  simp [α, he, disjoint_right.mp hd he] at this

variable {F₁ F₂ P : Drawing Shat} {u v : Shat} {ord ord' : ℕ}
  {𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
theorem TieBreaker.weightSub_sup (tb : TieBreaker rad) {C X Y : Drawing Shat} (hE : C.E = X.E ∪ Y.E)
    (hd : Disjoint X.E Y.E) : tb.weightSub C = tb.weightSub X + tb.weightSub Y := by
  simp only [TieBreaker.weightSub]
  rw [hE, finsum_mem_union hd X.finite_edges Y.finite_edges]

/-- The first assertion of (8.5), from the bound on `P` against `F₁`. -/
theorem step_8_5 (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad)
    (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯') (hins : IsInsOf rad ord 𝒯 F Δ)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)))
    (ht : TwoPaths rad.G F F₁ F₂ P u v) (hle : P.E.ncard ≤ F₁.E.ncard)
    (heq : P.E.ncard = F₁.E.ncard → tb.weightSub P ≤ tb.weightSub F₁) :
    ∃ Δ₂ : Set Shat, IsInsOf rad ord 𝒯 (rad.G.sup P F₂) Δ₂ ∧
      (partIn cap Γ Δ₂, partIn cap Γ (closure Δ₂ᶜ)) ∈ 𝒯' := by
  obtain ⟨hF, hsmall, hΔ, hbd, -⟩ := hins
  have hC : Drawing.IsCircuitOf (rad.G.sup P F₂) rad.G := ⟨rad.G.sup_isSubdrawing P F₂,
    ht.left_circuit⟩
  have hE : (rad.G.sup P F₂).E = P.E ∪ F₂.E := Drawing.sup_E ht.path.1 ht.sub₂
  have hdis : Disjoint P.E F₂.E := disjoint_left.mpr fun e he he' ↦
    disjoint_left.mp ht.meet_E he (ht.right.1.2 he')
  have hc₁ : (rad.G.sup P F₂).E.ncard = P.E.ncard + F₂.E.ncard := by
    rw [hE, ncard_union_eq hdis P.finite_edges F₂.finite_edges]
  have hc₂ : F.E.ncard = F₁.E.ncard + F₂.E.ncard := by
    rw [ht.union_E, ncard_union_eq ht.disj_E F₁.finite_edges F₂.finite_edges]
  obtain ⟨Δ₂, hΔ₂, hbd₂, hmem⟩ := (tangleRep_spec rad ord 𝒯).2 _ hC (by omega)
  refine ⟨Δ₂, ⟨hC, by omega, hΔ₂, hbd₂, hmem⟩, ?_⟩
  have hlt := disc_lambda_lt hS h3 tb hC hΔ₂ hbd₂ hF hΔ hbd (by
    rcases hle.lt_or_eq with h | h
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      rw [tb.weightSub_sup hE hdis, tb.weightSub_sup ht.union_E ht.disj_E]
      have hne := tb.weight_ne (ht.path.1.2) ht.sub₁.2
        (disjoint_right.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he' (ht.left.1.2 he))
        ht.exists_edge
      have := lt_of_le_of_ne (heq h) hne
      simp only [TieBreaker.weightSub]
      simp only [TieBreaker.weightSub] at this
      linarith)
  have o₁ := disc_order hS h3 rad hC hΔ₂ hbd₂
  have o₂ := disc_order hS h3 rad hF hΔ hbd
  have hBA := h𝒯'.order_lt hd.1.2
  have hcomm : Hypergraph.separationOrder (partIn cap Γ (closure Δᶜ)) (partIn cap Γ Δ) =
      Hypergraph.separationOrder (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)) := by
    simp only [Hypergraph.separationOrder, GM10.inter_comm]
  have hord : Hypergraph.separationOrder (partIn cap Γ Δ₂) (partIn cap Γ (closure Δ₂ᶜ)) < ord' := by
    omega
  rcases h𝒯'.axiom1 (disc_facts hS h3 rad hC hΔ₂ hbd₂).1 hord with h | h
  · exact h
  · exact absurd (hd.2 ⟨hmem, h⟩) (not_le.mpr hlt)

/-- **Graph Minors XIX, (8.5).** "Let $\mathscr{T}$ be a tangle in $\Gamma$, and let $F$ be a
$\mathscr{T}$-enclave around
$\mathscr{T}'$, and let $u, v \in V(F)$ be distinct. Let $F_1, F_2$ be the two paths of $F$
between $u$ and $v$, and let $P$ be a path of $\Gamma^*$ between $u$ and $v$ with no other
vertex or edge in common with $F$. Suppose that $|E(P)| \le |E(F_1)|$, and if equality holds
then $\lambda(P) \le \lambda(F_1)$." -/
theorem theorem_8_5_proof (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (tb : TieBreaker rad)
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯')
    (hins : IsInsOf rad ord 𝒯 F Δ)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)))
    (ht : TwoPaths rad.G F F₁ F₂ P u v) (hle : P.E.ncard ≤ F₁.E.ncard)
    (heq : P.E.ncard = F₁.E.ncard → tb.weightSub P ≤ tb.weightSub F₁) :
    ∃ Δ₂ : Set Shat, IsInsOf rad ord 𝒯 (rad.G.sup P F₂) Δ₂ ∧
      (partIn cap Γ Δ₂, partIn cap Γ (closure Δ₂ᶜ)) ∈ 𝒯' ∧
      (¬ P.U ⊆ Δ → Δ₂ ∩ Δ = F₂.U) ∧
      F₂.E.ncard ≤ P.E.ncard ∧ (P.E.ncard = F₂.E.ncard → tb.weightSub F₂ < tb.weightSub P) := by
  have hT := cap.isClosedSurface
  obtain ⟨Δ₂, hins₂, hmem₂⟩ := step_8_5 hS h3 tb h𝒯' hins hd ht hle heq
  obtain ⟨hF, -, hΔ, hbd, hABT⟩ := id hins
  have hBA := hd.1.2
  have hin := isSide_int hT hΔ hbd
  have hout := isSide_out hT hΔ hbd
  have hdis : Disjoint (discInt Δ) Δᶜ := disjoint_left.mpr fun x hx hx' ↦ hx' hx.1
  have hcov : F.Uᶜ ⊆ discInt Δ ∪ Δᶜ := fun x hx ↦ by
    by_cases hxΔ : x ∈ Δ
    · exact Or.inl ⟨hxΔ, fun hb ↦ hx (hbd ▸ hb)⟩
    · exact Or.inr hxΔ
  have hnotA : ∀ {C : Drawing Shat} {Δ' : Set Shat}, C.IsSubdrawing rad.G → IsClosedDisc Δ' →
      discBd Δ' = C.U → (partIn cap Γ Δ', partIn cap Γ (closure Δ'ᶜ)) ∈ 𝒯' →
      ¬ discInt Δ ⊆ discInt Δ' := by
    intro C Δ' hCs hΔ' hb' hm hsub
    have hO := isSide_int hT hΔ' hb'
    have hc := part_cover rad hF.1 hCs hCs hout hO hO (fun x ↦ by
      by_cases hx : x ∈ Δᶜ
      · exact Or.inl (subset_closure hx)
      · refine Or.inr (Or.inl ?_)
        rw [closure_discInt hΔ']
        have : Δ ⊆ Δ' := hΔ.subset_closure_discInt.trans
          (closure_minimal (hsub.trans (discInt_subset _)) hΔ'.isClosed)
        exact this (not_not.mp hx))
    rw [closure_discInt hΔ'] at hc
    exact h𝒯'.axiom2 hBA hm hm hc
  have hnotB : ∀ {C : Drawing Shat} {Δ' : Set Shat}, C.IsSubdrawing rad.G → IsClosedDisc Δ' →
      discBd Δ' = C.U → (partIn cap Γ Δ', partIn cap Γ (closure Δ'ᶜ)) ∈ 𝒯 →
      ¬ Δᶜ ⊆ discInt Δ' := by
    intro C Δ' hCs hΔ' hb' hm hsub
    have hO := isSide_int hT hΔ' hb'
    have hc := part_cover rad hF.1 hCs hCs hin hO hO (fun x ↦ by
      rw [closure_discInt hΔ, closure_discInt hΔ']
      by_cases hx : x ∈ Δ
      · exact Or.inl hx
      · exact Or.inr (Or.inl (discInt_subset _ (hsub hx))))
    rw [closure_discInt hΔ, closure_discInt hΔ'] at hc
    exact h𝒯.axiom2 hABT hm hm hc
  have hpath := path_side ht.sub hin hout hdis hcov ht.path.1 ht.path.2 ht.ne ht.meet_V ht.meet_E
  have huv := ht.mem_V
  have huvΔ : u ∈ Δ ∧ v ∈ Δ := by
    have : F.V ⊆ Δ := fun x hx ↦ Surface.discBd_subset _ (hbd ▸ F.V_subset_U hx)
    exact ⟨this huv.1, this huv.2⟩
  have hC₂s : (rad.G.sup P F₂).IsSubdrawing rad.G := rad.G.sup_isSubdrawing P F₂
  have hC₁s : (rad.G.sup P F₁).IsSubdrawing rad.G := rad.G.sup_isSubdrawing P F₁
  refine ⟨Δ₂, hins₂, hmem₂, ?_, ?_⟩
  · intro hnP
    have hPo : ∀ x ∈ P.U, x ∈ Δᶜ ∨ x = u ∨ x = v := by
      rcases hpath with h | h
      · exfalso
        refine hnP fun x hx ↦ ?_
        rcases h x hx with h' | rfl | rfl
        · exact h'.1
        · exact huvΔ.1
        · exact huvΔ.2
      · exact h
    obtain ⟨-, -, hΔ₂, hbd₂, -⟩ := hins₂
    have hO₂ := isSide_int hT hΔ₂ hbd₂
    have hd₂ := disjoint_disc hT hin hΔ₂ hbd₂ (ht.side_disjoint hin hdis hPo)
      (hnotA hC₂s hΔ₂ hbd₂ hmem₂)
    have huv₂ := ht.swap.mem_V₁
    apply Subset.antisymm
    · rintro x ⟨hx₂, hx⟩
      by_cases hxF : x ∈ F.U
      · by_contra hxn
        have hxC : x ∉ (rad.G.sup P F₂).U := by
          rw [ht.U_right]
          rintro (hxP | hxP)
          · rcases hPo x hxP with h' | rfl | rfl
            · exact h' hx
            · exact hxn (F₂.V_subset_U huv₂.1)
            · exact hxn (F₂.V_subset_U huv₂.2)
          · exact hxn hxP
        have hxI : x ∈ discInt Δ₂ := ⟨hx₂, fun hb ↦ hxC (hbd₂ ▸ hb)⟩
        obtain ⟨z, hzO, hzI⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt hx) _ hO₂.isOpen hxI
        exact disjoint_left.mp hd₂ hzI (discInt_subset _ hzO)
      · exact absurd hx₂ (disjoint_left.mp hd₂ ⟨hx, fun hb ↦ hxF (hbd ▸ hb)⟩)
    · intro x hx
      refine ⟨Surface.discBd_subset _ (hbd₂ ▸ ht.U_right ▸ Or.inr hx), ?_⟩
      exact Surface.discBd_subset _ (hbd ▸ ht.U_eq ▸ Or.inr hx)
  · by_contra hn
    have hn' : P.E.ncard ≤ F₂.E.ncard ∧
        (P.E.ncard = F₂.E.ncard → tb.weightSub P ≤ tb.weightSub F₂) := by
      by_cases h₁ : F₂.E.ncard ≤ P.E.ncard
      · have h₂ : ¬ (P.E.ncard = F₂.E.ncard → tb.weightSub F₂ < tb.weightSub P) :=
          fun h ↦ hn ⟨h₁, h⟩
        push Not at h₂
        exact ⟨h₂.1.le, fun _ ↦ h₂.2⟩
      · exact ⟨(not_le.mp h₁).le, fun h ↦ by omega⟩
    obtain ⟨Δ₁, hins₁, hmem₁⟩ := step_8_5 hS h3 tb h𝒯' hins hd ht.swap hn'.1 hn'.2
    obtain ⟨-, -, hΔ₂, hbd₂, hT₂⟩ := hins₂
    obtain ⟨-, -, hΔ₁, hbd₁, hT₁⟩ := hins₁
    have hO₁ := isSide_int hT hΔ₁ hbd₁
    have hO₂ := isSide_int hT hΔ₂ hbd₂
    rcases hpath with hPi | hPo
    · have d₁ := disjoint_disc hT hout hΔ₁ hbd₁ (ht.swap.side_disjoint hout hdis.symm hPi)
        (hnotB hC₁s hΔ₁ hbd₁ hT₁)
      have d₂ := disjoint_disc hT hout hΔ₂ hbd₂ (ht.side_disjoint hout hdis.symm hPi)
        (hnotB hC₂s hΔ₂ hbd₂ hT₂)
      have hc := part_cover rad hF.1 hC₁s hC₂s hout hO₁ hO₂ fun x ↦ by
        rw [closure_discInt hΔ₁, closure_discInt hΔ₂]
        exact ht.theta_cover hT hout hΔ₁ hΔ₂ hbd₁ hbd₂ d₁ d₂ x
      rw [closure_discInt hΔ₁, closure_discInt hΔ₂] at hc
      exact h𝒯'.axiom2 hBA hmem₁ hmem₂ hc
    · have d₁ := disjoint_disc hT hin hΔ₁ hbd₁ (ht.swap.side_disjoint hin hdis hPo)
        (hnotA hC₁s hΔ₁ hbd₁ hmem₁)
      have d₂ := disjoint_disc hT hin hΔ₂ hbd₂ (ht.side_disjoint hin hdis hPo)
        (hnotA hC₂s hΔ₂ hbd₂ hmem₂)
      have hc := part_cover rad hF.1 hC₁s hC₂s hin hO₁ hO₂ fun x ↦ by
        rw [closure_discInt hΔ₁, closure_discInt hΔ₂]
        exact ht.theta_cover hT hin hΔ₁ hΔ₂ hbd₁ hbd₂ d₁ d₂ x
      rw [closure_discInt hΔ, closure_discInt hΔ₁, closure_discInt hΔ₂] at hc
      exact h𝒯.axiom2 hABT hT₁ hT₂ hc

end GraphMinor.GM19
