/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13g

/-!
# Graph Minors XIX, Section 13: the first steps of (13.6)

Let `F` be a `𝒯`-enclave around `𝒯'`, let `D_v` be a sector with `(Γ ∩ out(D_v), Γ ∩ ins(D_v)) ∈
𝒯'`. We take the steps of the paper
that do not depend on the wheel. A circuit `C` made of edges of `F` and `D_v`, whose disc contains
both `ins(F)` and `ins(D_v)`, is
no longer than `D_v` (step (5)). The two discs share an edge of `Γ` (step (2)).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
  {ord ord' : ℕ} {𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {F Dv C : Drawing Shat}
    {Δf Δd Δc : Set Shat}

omit [T2Space S] [T2Space Shat] in
/-- The `λ`-order of a separation is at most the `λ`-order of a separation of larger first
component. -/
theorem lambdaOrder_lt_of_N1 (tb : TieBreaker rad) {x y : Hypergraph S (Set S) × Hypergraph S
  (Set S)} (h : tb.N1 x < tb.N1 y) :
    tb.lambdaOrder x ≤ tb.lambdaOrder y := by
  simp only [TieBreaker.lambdaOrder]
  rw [Prod.Lex.toLex_le_toLex]
  exact Or.inl h

omit [T2Space S] [T2Space Shat] in
/-- The sum of the weights of a set of edges of `Γ*` is at most the sum over a larger set. -/
theorem TieBreaker.finsum_le_of_subset (tb : TieBreaker rad) {X Y : Set (Set Shat)}
  (hY : Y ⊆ rad.G.E) (h : X ⊆ Y) :
    ∑ᶠ e ∈ X, tb.wtE e ≤ ∑ᶠ e ∈ Y, tb.wtE e := by
  have hfin : Y.Finite := rad.G.finite_edges.subset hY
  have hX : X.Finite := hfin.subset h
  rw [finsum_mem_eq_finite_toFinset_sum _ hX, finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun e he ↦ hfin.mem_toFinset.mpr (h
    (hX.mem_toFinset.mp he)))
    fun e he _ ↦ (tb.wtE_pos e (hY (hfin.mem_toFinset.mp he))).le

omit [T2Space S] in
omit [T2Space Shat] in
/-- An enclave around `𝒯'` has `λ`-order at most that of any circuit which also separates `𝒯` from
`𝒯'`. -/
theorem enclave_lambda_le (tb : TieBreaker rad)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δf) (partIn cap Γ (closure Δfᶜ)))
    (hDv : IsInsOf rad ord 𝒯 Dv Δd) (hmem : (partIn cap Γ (closure Δdᶜ), partIn cap Γ Δd) ∈ 𝒯') :
    tb.lambdaOrder (partIn cap Γ Δf, partIn cap Γ (closure Δfᶜ)) ≤ tb.lambdaOrder
      (partIn cap Γ Δd, partIn cap Γ (closure Δdᶜ)) :=
  hd.2 ⟨hDv.2.2.2.2, hmem⟩

/-- Step (1) of the proof of (13.6): `|E(F)| ≤ |E(D_v)|`. -/
theorem enclave_card_le (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (tb : TieBreaker rad) (hF : IsInsOf rad ord 𝒯 F Δf)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δf) (partIn cap Γ (closure Δfᶜ)))
    (hDv : IsInsOf rad ord 𝒯 Dv Δd) (hmem : (partIn cap Γ (closure Δdᶜ), partIn cap Γ Δd) ∈ 𝒯') :
    F.E.ncard ≤ Dv.E.ncard := by
  have : ConnectedSpace Shat := cap.connected
  have h := (N1_le_of_lambda_le tb (enclave_lambda_le tb hd hDv hmem)).1
  simp only [TieBreaker.N1] at h
  rw [disc_order hS h3 rad hF.1 hF.2.2.1 hF.2.2.2.1, disc_order hS h3 rad hDv.1 hDv.2.2.1
    hDv.2.2.2.1]
  omega

/-- Step (2) of the proof of (13.6): there is an edge of `Γ` inside both `ins(F)` and `ins(D_v)`. -/
theorem exists_edge_in_both (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯')
    (hF : IsInsOf rad ord 𝒯 F Δf) (hmf : (partIn cap Γ (closure Δfᶜ), partIn cap Γ Δf) ∈ 𝒯')
    (hDv : IsInsOf rad ord 𝒯 Dv Δd) (hmd : (partIn cap Γ (closure Δdᶜ), partIn cap Γ Δd) ∈ 𝒯') :
    ∃ c ∈ Γ.E, cap.emb '' c ⊆ discInt Δf ∧ cap.emb '' c ⊆ discInt Δd := by
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  by_contra hn
  push Not at hn
  have hle : partIn cap Γ (closure Δfᶜ) ∪ partIn cap Γ (closure Δdᶜ) ≤ Γ.toHypergraph :=
    GM10.union_le (Γ.restrict_le _) (Γ.restrict_le _)
  have hall := eq_of_all_edges hS h3 rad hle fun c hc ↦ by
    rcases disc_edge_side rad hF.1.1 hman hF.2.2.1 hF.2.2.2.1 hc with h₁ | h₁
    · rcases disc_edge_side rad hDv.1.1 hman hDv.2.2.1 hDv.2.2.2.1 hc with h₂ | h₂
      · exact absurd h₂ (hn c hc h₁)
      · exact Or.inr (restrict_out hc h₂)
    · exact Or.inl (restrict_out hc h₁)
  refine h𝒯'.axiom2 hmf hmd hmd ?_
  rw [← hall]
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.union_le hle (Γ.restrict_le _)) hle (by
      ext v
      simp only [GM10.union_vertexSet, mem_union]
      tauto) (by
      ext v
      simp only [GM10.union_edgeSet, mem_union]
      tauto)

theorem prop_mix {a₀ a₁ b₀ b₁ p q : Prop} (m₀ : a₀ → p) (m₁ : a₁ → p) (m₂ : b₀ → q) (m₃ : b₁ → q)
  (hc : ¬ (p ↔ q))
    (hs : ¬ (a₀ ↔ b₀) ∨ ¬ (a₁ ↔ b₁)) : ¬ ((a₀ ∨ a₁) ↔ (b₀ ∨ b₁)) := by
  tauto

/-- Step (5) of the proof of (13.6): a circuit `C` of `F ∪ D_v` whose disc includes `ins(F)` and
`ins(D_v)` is no longer than `D_v`,
and if equal it is no heavier. -/
theorem uncross_circuit_le (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (tb : TieBreaker rad) (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯') (hF : IsInsOf rad ord 𝒯 F Δf)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δf) (partIn cap Γ (closure Δfᶜ)))
    (hDv : IsInsOf rad ord 𝒯 Dv Δd) (hmem : (partIn cap Γ (closure Δdᶜ), partIn cap Γ Δd) ∈ 𝒯')
    (hC : C.IsCircuitOf rad.G) (hΔc : IsClosedDisc Δc) (hbd : discBd Δc = C.U) (hfc : Δf ⊆ Δc)
      (hdc : Δd ⊆ Δc)
    (hsub : ∀ e ∈ C.E, e ∈ F.E ∨ e ∈ Dv.E) :
    C.E.ncard ≤ Dv.E.ncard ∧ (C.E.ncard = Dv.E.ncard → tb.weightSub C ≤ tb.weightSub Dv) := by
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  set A₀ := partIn cap Γ Δf with hA₀
  set B₀ := partIn cap Γ (closure Δfᶜ) with hB₀
  set A₁ := partIn cap Γ Δd with hA₁
  set B₁ := partIn cap Γ (closure Δdᶜ) with hB₁
  set Ac := partIn cap Γ Δc with hAc
  set Bc := partIn cap Γ (closure Δcᶜ) with hBc
  have hs₀ : Γ.toHypergraph.IsSeparation A₀ B₀ := (disc_facts hS h3 rad hF.1 hF.2.2.1 hF.2.2.2.1).1
  have hs₁ : Γ.toHypergraph.IsSeparation A₁ B₁ := (disc_facts hS h3 rad hDv.1 hDv.2.2.1
    hDv.2.2.2.1).1
  have hsc : Γ.toHypergraph.IsSeparation Ac Bc := (disc_facts hS h3 rad hC hΔc hbd).1
  have hX : Γ.toHypergraph.IsSeparation (A₀ ∩ A₁) (B₀ ∪ B₁) := (hs₀.symm.union_inter hs₁.symm).symm
  have hY : Γ.toHypergraph.IsSeparation (A₀ ∪ A₁) (B₀ ∩ B₁) := hs₀.union_inter hs₁
  have hsum := separationOrder_add_separationOrder hs₀ hs₁
  have hle₀ : Hypergraph.separationOrder A₀ B₀ ≤ Hypergraph.separationOrder A₁ B₁ := by
    have h := (N1_le_of_lambda_le tb (enclave_lambda_le tb hd hDv hmem)).1
    simpa only [TieBreaker.N1] using h
  have hA1T : (A₁, B₁) ∈ 𝒯 := hDv.2.2.2.2
  have hA0T : (A₀, B₀) ∈ 𝒯 := hd.1.1
  have hlamY : tb.lambdaOrder (A₀ ∪ A₁, B₀ ∩ B₁) ≤ tb.lambdaOrder (A₁, B₁) := by
    by_cases hn : Hypergraph.separationOrder (A₀ ∩ A₁) (B₀ ∪ B₁) ≤ Hypergraph.separationOrder A₁ B₁
    · have hXo : Hypergraph.separationOrder (A₀ ∩ A₁) (B₀ ∪ B₁) < ord := lt_of_le_of_lt hn
        (h𝒯.order_lt hA1T)
      have hcomm : Hypergraph.separationOrder B₁ A₁ = Hypergraph.separationOrder A₁ B₁ := by
        simp only [Hypergraph.separationOrder, GM10.inter_comm]
      have hXo' : Hypergraph.separationOrder (A₀ ∩ A₁) (B₀ ∪ B₁) < ord' :=
        lt_of_le_of_lt (hn.trans_eq hcomm.symm) (h𝒯'.order_lt hmem)
      have l₁ := hs₀.left_le
      have l₂ := hs₀.right_le
      have l₃ := hs₁.left_le
      have l₄ := hs₁.right_le
      have hXT : (A₀ ∩ A₁, B₀ ∪ B₁) ∈ 𝒯 := by
        refine (h𝒯.axiom1 hX hXo).resolve_right fun hr ↦ h𝒯.axiom2 hA0T hr hr ?_
        have l₅ := GM10.union_le l₂ l₄
        have l₆ := GM10.union_le (GM10.union_le l₁ l₅) l₅
        exact eq_of_cover hs₀ (le_trans (GM10.le_union_left l₁ l₅) (GM10.le_union_left
          (GM10.union_le l₁ l₅) l₅))
          (le_trans (le_trans (GM10.le_union_left l₂ l₄) (GM10.le_union_right l₁ l₅))
            (GM10.le_union_left (GM10.union_le l₁ l₅) l₅)) l₆
      have hXT' : (B₀ ∪ B₁, A₀ ∩ A₁) ∈ 𝒯' := by
        have hs' : Hypergraph.separationOrder (B₀ ∪ B₁) (A₀ ∩ A₁) < ord' := by
          have : Hypergraph.separationOrder (B₀ ∪ B₁) (A₀ ∩ A₁) = Hypergraph.separationOrder
            (A₀ ∩ A₁) (B₀ ∪ B₁) := by
            simp only [Hypergraph.separationOrder, GM10.inter_comm]
          omega
        exact (h𝒯'.axiom1 hX.symm hs').resolve_right fun hr ↦ h𝒯'.axiom2 hmem hd.1.2 hr
          (cover_three hs₀ hs₁.symm)
      have hc := hd.2 ⟨hXT, hXT'⟩
      rcases (tb.lambda_sum hS h3 hs₁ hs₀).1 with h | h
      · rwa [GM10.union_comm, GM10.inter_comm] at h
      · rw [GM10.inter_comm, GM10.union_comm] at h
        exact absurd hc (not_le.mpr h)
    · apply lambdaOrder_lt_of_N1
      simp only [TieBreaker.N1]
      omega
  have hUsub : C.U ⊆ F.U ∪ Dv.U := U_of_edges hC.2 (F.isClosed_U.union Dv.isClosed_U) fun e he ↦ by
    rcases hsub e he with h | h
    · exact (subset_closure.trans (F.closure_subset_U h)).trans subset_union_left
    · exact (subset_closure.trans (Dv.closure_subset_U h)).trans subset_union_right
  have hV : (Ac ∩ Bc).vertexSet ⊆ ((A₀ ∪ A₁) ∩ (B₀ ∩ B₁)).vertexSet := by
    intro v hv
    have hvU : cap.emb v ∈ C.U := (disc_facts hS h3 rad hC hΔc hbd).2.1 v hv
    have hvV : v ∈ Γ.V := hv.1.1
    have hfr : C.U ⊆ closure Δcᶜ := by
      intro x hx
      have : x ∈ frontier Δc := by
        rw [IsClosedDisc.frontier_eq_discBd hT hΔc, hbd]
        exact hx
      rw [frontier_eq_closure_inter_closure] at this
      exact this.2
    have hout : ∀ {Δ : Set Shat}, Δ ⊆ Δc → cap.emb v ∈ closure Δᶜ := fun h ↦
      closure_mono (compl_subset_compl.mpr h) (hfr hvU)
    refine ⟨?_, ⟨hvV, hout hfc⟩, ⟨hvV, hout hdc⟩⟩
    rcases hUsub hvU with h | h
    · exact Or.inl ⟨hvV, by
        have : F.U ⊆ Δf := by
          rw [← hF.2.2.2.1]
          exact Surface.discBd_subset _
        exact this h⟩
    · exact Or.inr ⟨hvV, by
        have : Dv.U ⊆ Δd := by
          rw [← hDv.2.2.2.1]
          exact Surface.discBd_subset _
        exact this h⟩
  have hSplit : ∀ e ∈ C.E, rad.Splits (A₀ ∪ A₁) (B₀ ∩ B₁) e := by
    intro e he
    obtain ⟨c₁, c₂, hp, -⟩ := rad.splits_iff.mp (disc_split hS h3 rad hC hΔc hbd he)
    have hc := (splits_of_pair hS h3 hp hsc).mp (disc_split hS h3 rad hC hΔc hbd he)
    have hm₀ : ∀ {c}, c ∈ A₀.edgeSet → c ∈ Ac.edgeSet := fun h ↦ (part_mono hfc).edgeSet_subset h
    have hm₁ : ∀ {c}, c ∈ A₁.edgeSet → c ∈ Ac.edgeSet := fun h ↦ (part_mono hdc).edgeSet_subset h
    have hs₃ : ¬ (c₁ ∈ A₀.edgeSet ↔ c₂ ∈ A₀.edgeSet) ∨ ¬ (c₁ ∈ A₁.edgeSet ↔ c₂ ∈ A₁.edgeSet) := by
      rcases hsub e he with h | h
      · exact Or.inl ((splits_of_pair hS h3 hp hs₀).mp (disc_split hS h3 rad hF.1 hF.2.2.1
          hF.2.2.2.1 h))
      · exact Or.inr ((splits_of_pair hS h3 hp hs₁).mp (disc_split hS h3 rad hDv.1 hDv.2.2.1
          hDv.2.2.2.1 h))
    exact (splits_of_pair hS h3 hp hY).mpr (prop_mix hm₀ hm₁ hm₀ hm₁ hc hs₃)
  have hco : C.E.ncard = 2 * Hypergraph.separationOrder Ac Bc := disc_order hS h3 rad hC hΔc hbd
  have hc₁ : Dv.E.ncard = 2 * Hypergraph.separationOrder A₁ B₁ := disc_order hS h3 rad hDv.1
    hDv.2.2.1 hDv.2.2.2.1
  have hcoY : Hypergraph.separationOrder Ac Bc ≤ Hypergraph.separationOrder (A₀ ∪ A₁) (B₀ ∩ B₁) :=
    ncard_le_ncard hV ((A₀ ∪ A₁) ∩ (B₀ ∩ B₁)).vertexSet_finite
  obtain ⟨hN1, hN2⟩ := N1_le_of_lambda_le tb hlamY
  simp only [TieBreaker.N1] at hN1 hN2
  refine ⟨by omega, fun heq ↦ ?_⟩
  have h₂ := hN2 (by omega)
  rw [disc_N2 hS h3 tb hDv.1 hDv.2.2.1 hDv.2.2.2.1] at h₂
  refine le_trans ?_ h₂
  simp only [TieBreaker.N2, TieBreaker.weightSub]
  exact tb.finsum_le_of_subset (fun e he ↦ he.1) fun e he ↦ ⟨hC.1.2 he, hSplit e he⟩

end GraphMinor.GM19
