/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Section8h

/-!
# Graph Minors XIX, (8.7)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

section Sided

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T] {F : Drawing T}
  {Ω₁ Ω₂ : Set T}

/-- `Ω₁, Ω₂` are the two components of the complement of `U(F)`, for a drawing `F` that bounds a
closed disc. -/
def Sided (F : Drawing T) (Ω₁ Ω₂ : Set T) : Prop :=
  ∃ Δ : Set T, IsClosedDisc Δ ∧ discBd Δ = F.U ∧
    ((Ω₁ = discInt Δ ∧ Ω₂ = Δᶜ) ∨ (Ω₁ = Δᶜ ∧ Ω₂ = discInt Δ))

omit [T2Space T] [ConnectedSpace T] in
theorem Sided.symm (h : Sided F Ω₁ Ω₂) : Sided F Ω₂ Ω₁ := by
  obtain ⟨Δ, hΔ, hbd, h | h⟩ := h
  · exact ⟨Δ, hΔ, hbd, Or.inr h.symm⟩
  · exact ⟨Δ, hΔ, hbd, Or.inl h.symm⟩

theorem Sided.left (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) : IsSide Ω₁ F := by
  obtain ⟨Δ, hΔ, hbd, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := h
  · exact isSide_int hT hΔ hbd
  · exact isSide_out hT hΔ hbd

theorem Sided.right (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) : IsSide Ω₂ F :=
  h.symm.left hT

omit [T2Space T] [ConnectedSpace T] in
theorem Sided.disjoint (h : Sided F Ω₁ Ω₂) : Disjoint Ω₁ Ω₂ := by
  obtain ⟨Δ, hΔ, hbd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact disjoint_left.mpr fun x hx hx' ↦ hx' hx.1
  · exact disjoint_left.mpr fun x hx hx' ↦ hx hx'.1

omit [T2Space T] [ConnectedSpace T] in
theorem Sided.cover (h : Sided F Ω₁ Ω₂) : F.Uᶜ ⊆ Ω₁ ∪ Ω₂ := by
  obtain ⟨Δ, hΔ, hbd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · intro x hx
    by_cases hxΔ : x ∈ Δ
    · exact Or.inl ⟨hxΔ, fun hb ↦ hx (hbd ▸ hb)⟩
    · exact Or.inr hxΔ
  · intro x hx
    by_cases hxΔ : x ∈ Δ
    · exact Or.inr ⟨hxΔ, fun hb ↦ hx (hbd ▸ hb)⟩
    · exact Or.inl hxΔ

theorem Sided.compl_subset (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) : Ω₁ᶜ ⊆ closure Ω₂ := by
  intro x hx
  by_cases hxU : x ∈ F.U
  · exact (h.right hT).U_subset_closure hxU
  · exact subset_closure ((h.cover hxU).resolve_left hx)

theorem isSide_component (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) {y : T} (hy : y ∈ Ω₁) :
    connectedComponentIn F.Uᶜ y = Ω₁ := by
  have hs := h.left hT
  have hsub : Ω₁ ⊆ F.Uᶜ := fun x hx hxU ↦ disjoint_left.mp hs.disjoint_U hx hxU
  refine Subset.antisymm ?_ (hs.conn.subset_connectedComponentIn hy hsub)
  refine hs.subset isPreconnected_connectedComponentIn
    (disjoint_left.mpr fun x hx hxU ↦ connectedComponentIn_subset _ _ hx hxU)
    ⟨y, mem_connectedComponentIn (hsub hy), hy⟩

theorem Sided.components (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) :
    componentsIn F.Uᶜ = {Ω₁, Ω₂} := by
  have h₁ := h.left hT
  have h₂ := h.right hT
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rcases h.cover hy with hy' | hy'
    · exact Or.inl (isSide_component hT h hy')
    · exact Or.inr (isSide_component hT h.symm hy')
  · rintro _ (rfl | rfl)
    · obtain ⟨y, hy⟩ := h₁.nonempty
      exact ⟨y, fun hyU ↦ disjoint_left.mp h₁.disjoint_U hy hyU, isSide_component hT h hy⟩
    · obtain ⟨y, hy⟩ := h₂.nonempty
      exact ⟨y, fun hyU ↦ disjoint_left.mp h₂.disjoint_U hy hyU, isSide_component hT h.symm hy⟩

theorem Sided.isSidesOf (hT : IsClosedSurface T) (h : Sided F Ω₁ Ω₂) :
    IsSidesOf F (closure Ω₁) (closure Ω₂) := by
  refine ⟨Ω₁, Ω₂, ?_, h.components hT, rfl, rfl⟩
  intro heq
  obtain ⟨y, hy⟩ := (h.left hT).nonempty
  exact disjoint_left.mp h.disjoint hy (heq ▸ hy)

/-- The sides of a circuit that bounds a closed disc are the disc and the closure of its
complement. -/
theorem exists_sided_of_isSidesOf (hT : IsClosedSurface T) {Δ S₁ S₂ : Set T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) (hs : IsSidesOf F S₁ S₂) :
    ∃ Ω₁ Ω₂, Sided F Ω₁ Ω₂ ∧ S₁ = closure Ω₁ ∧ S₂ = closure Ω₂ := by
  obtain ⟨C₁, C₂, hne, hset, rfl, rfl⟩ := hs
  have h₀ : Sided F (discInt Δ) Δᶜ := ⟨Δ, hΔ, hbd, Or.inl ⟨rfl, rfl⟩⟩
  have hset' : componentsIn F.Uᶜ = {discInt Δ, Δᶜ} := Sided.components hT h₀
  have hC₁ : C₁ ∈ componentsIn F.Uᶜ := by rw [hset]; exact Or.inl rfl
  have hC₂ : C₂ ∈ componentsIn F.Uᶜ := by rw [hset]; exact Or.inr rfl
  rw [hset'] at hC₁ hC₂
  rcases hC₁ with rfl | rfl
  · rcases hC₂ with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨_, _, h₀, rfl, rfl⟩
  · rcases hC₂ with rfl | rfl
    · exact ⟨_, _, h₀.symm, rfl, rfl⟩
    · exact absurd rfl hne

omit [T2Space T] [ConnectedSpace T] in
theorem IsCircuit.E_nonempty {C : Drawing T} (hC : C.IsCircuit) : C.E.Nonempty := by
  obtain ⟨u, W, -, hpos, -, hE⟩ := hC
  cases W with
  | nil h => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons _ x _ e h r => exact ⟨e, by rw [hE]; simp [GraphWalk.edges]⟩

end Sided

section Main

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [ConnectedSpace Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
  {ord : ℕ} {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {F : Drawing Shat}
  {Ω₁ Ω₂ : Set Shat}

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
theorem part_mono {X Y : Set Shat} (h : X ⊆ Y) : partIn cap Γ X ≤ partIn cap Γ Y := by
  refine (le_iff_of_le (Γ.restrict_le _) (Γ.restrict_le _)).2 ⟨?_, ?_⟩
  · exact fun v hv ↦ ⟨hv.1, h hv.2⟩
  · exact fun c hc ↦ ⟨hc.1, fun x hx ↦ h (hc.2.1 hx), fun v hv ↦ h (hc.2.2 hv)⟩

/-- The facts about the separation of the two sides of a circuit. -/
theorem Sided.facts (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (hF : F.IsCircuitOf rad.G) (h : Sided F Ω₁ Ω₂) :
    Γ.toHypergraph.IsSeparation (partIn cap Γ (closure Ω₁)) (partIn cap Γ (closure Ω₂)) ∧
    (∀ v ∈ (partIn cap Γ (closure Ω₁) ∩ partIn cap Γ (closure Ω₂)).vertexSet, cap.emb v ∈ F.U) ∧
    F.E.ncard = 2 * Hypergraph.separationOrder (partIn cap Γ (closure Ω₁))
      (partIn cap Γ (closure Ω₂)) ∧
    ∀ e ∈ rad.G.E, rad.Splits (partIn cap Γ (closure Ω₁)) (partIn cap Γ (closure Ω₂)) e ↔
      e ∈ F.E := by
  obtain ⟨Δ, hΔ, hbd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · rw [closure_discInt hΔ]
    obtain ⟨h₁, h₂, -, h₄⟩ := disc_facts hS h3 rad hF hΔ hbd
    exact ⟨h₁, h₂, disc_order hS h3 rad hF hΔ hbd, fun e he ↦ ⟨h₄ e he,
      disc_split hS h3 rad hF hΔ hbd⟩⟩
  · rw [closure_discInt hΔ]
    obtain ⟨h₁, h₂, -, h₄⟩ := disc_facts hS h3 rad hF hΔ hbd
    refine ⟨h₁.symm, fun v hv ↦ h₂ v ⟨hv.2, hv.1⟩, ?_, fun e he ↦ ⟨fun hs ↦ h₄ e he
      (splits_comm.mp hs), fun hm ↦ splits_comm.mp (disc_split hS h3 rad hF hΔ hbd hm)⟩⟩
    rw [disc_order hS h3 rad hF hΔ hbd]
    simp only [Hypergraph.separationOrder, GM10.inter_comm]

/-- Each side of a circuit contains an edge of `Γ`. -/
theorem Sided.edge_nonempty (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (hF : F.IsCircuitOf rad.G) (h : Sided F Ω₁ Ω₂) :
    (partIn cap Γ (closure Ω₁)).edgeSet.Nonempty := by
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  have hDE := hD.E_nonempty hS h3.1
  have hs := h.left hT
  obtain ⟨y, hy⟩ := hs.nonempty
  obtain ⟨s, hs₁, -, hm⟩ := exists_region_near hT G₃ hs.isOpen (subset_closure hy)
  have hsΩ := hs.region_subset (hF.1.trans hsub) hs₁ hm
  obtain ⟨f, c, hfc, hfs⟩ := exists_colour hS hD hrad hmax hDE hs₁
  obtain ⟨x, hx⟩ := hfc.mem.1
  have hxc := mem_image_of_mem cap.emb (hfc.subset hx)
  exact ⟨c, restrict_side hfc.1 (side_edge rad hF.1 hs hfc.1 ⟨_, hxc, hsΩ (hfs
    (mem_image_of_mem _ hx))⟩)⟩

omit [T2Space S] in
/-- A circuit shorter than twice `rep(Γ)` bounds a closed disc. -/
theorem exists_disc_of_lt_rep (hF : F.IsCircuitOf rad.G)
    (hlt : (F.E.ncard : ℕ∞) < 2 * Painting.rep rad) : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F.U := by
  have hT := cap.isClosedSurface
  have hnull : IsNullHomotopicOArc F.U := by
    by_contra hn
    have hle : Painting.rep rad ≤ ((F.E.ncard / 2 : ℕ) : ℕ∞) := sInf_le ⟨F, hF, hn, rfl⟩
    have h₂ : 2 * Painting.rep rad ≤ 2 * ((F.E.ncard / 2 : ℕ) : ℕ∞) := by gcongr
    have h₃ : (2 : ℕ∞) * ((F.E.ncard / 2 : ℕ) : ℕ∞) ≤ (F.E.ncard : ℕ∞) := by
      exact_mod_cast Nat.mul_div_le _ _
    exact absurd (lt_of_lt_of_le hlt (h₂.trans h₃)) (lt_irrefl _)
  have hbdS : Disjoint F.U (bd Shat) := disjoint_left.mpr fun x _ hx ↦ hx (hT.2.2 x)
  obtain ⟨Δ, -, hΔ, hbd⟩ := (epstein Shat univ F.U (Surface.IsClosedSurface.isSurface hT)
    inferInstance
    (GM14.isOArc_of_isCircuit hF.2) (subset_univ _) hbdS).1 hnull
  exact ⟨Δ, hΔ, hbd⟩

omit [ConnectedSpace Shat] in
omit [T2Space Shat] in
/-- The contradiction in the proof of (8.7): if the two sides of `F'` could be used to improve
`(A, B)`, then `(A, B)` was not minimal. -/
theorem uncross_absurd (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad)
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) {A B P₁ P₂ Q₁ Q₂ : Hypergraph S (Set S)}
    (hAB : (A, B) ∈ 𝒯) (hQ : (Q₁, Q₂) ∈ 𝒯)
    (hV : ∀ v ∈ (Q₁ ∩ Q₂).vertexSet, v ∈ (A ∩ B).vertexSet)
    (hE : ∀ e ∈ rad.G.E, rad.Splits Q₁ Q₂ e → rad.Splits A B e) {e₀ : Set Shat}
    (he₀ : e₀ ∈ rad.G.E) (hs₀ : rad.Splits Q₁ Q₂ e₀) (hsub : Q₁ ≤ A ∨ Q₁ ≤ B)
    (hP₁A : P₁ ≤ A) (hBP₂ : B ≤ P₂) (hP₁Q₂ : P₁ ≤ Q₂) (hQ₁P₂ : Q₁ ≤ P₂)
    (hmin : ∀ ⦃A' B'⦄, (A', B') ∈ 𝒯 → P₁ ≤ A' → B' ≤ P₂ →
      tb.lambdaOrder (A, B) ≤ tb.lambdaOrder (A', B')) : False := by
  have hsAB := h𝒯.isSeparation hAB
  have hsQ := h𝒯.isSeparation hQ
  have hordAB := h𝒯.order_lt hAB
  obtain ⟨m₁, m₂, m₃, m₄⟩ := mix_facts hS h3 hsAB hsQ hV hE
  have hX : Γ.toHypergraph.IsSeparation (A ∩ Q₂) (B ∪ Q₁) := (hsAB.symm.union_inter hsQ).symm
  have hY : Γ.toHypergraph.IsSeparation (A ∪ Q₁) (B ∩ Q₂) := hsAB.union_inter hsQ
  have hfin := (A ∩ B).vertexSet_finite
  have hXo : Hypergraph.separationOrder (A ∩ Q₂) (B ∪ Q₁) < ord :=
    lt_of_le_of_lt (ncard_le_ncard m₁ hfin) hordAB
  have hYo : Hypergraph.separationOrder (A ∪ Q₁) (B ∩ Q₂) < ord :=
    lt_of_le_of_lt (ncard_le_ncard m₃ hfin) hordAB
  have l₁ := hsAB.left_le
  have l₂ := hsAB.right_le
  have l₃ := hsQ.left_le
  have l₄ := hsQ.right_le
  have hXT : (A ∩ Q₂, B ∪ Q₁) ∈ 𝒯 := by
    refine (h𝒯.axiom1 hX hXo).resolve_right fun hr ↦ h𝒯.axiom2 hAB hQ hr ?_
    have l₅ := GM10.union_le l₂ l₃
    have l₆ := GM10.union_le l₁ l₃
    exact eq_of_cover hsAB (le_trans (GM10.le_union_left l₁ l₃) (GM10.le_union_left l₆ l₅))
      (le_trans (GM10.le_union_left l₂ l₃) (GM10.le_union_right l₆ l₅)) (GM10.union_le l₆ l₅)
  have hYT : (A ∪ Q₁, B ∩ Q₂) ∈ 𝒯 := by
    refine (h𝒯.axiom1 hY hYo).resolve_right fun hr ↦ h𝒯.axiom2 hQ hAB hr ?_
    exact cover_three hsAB.symm hsQ
  have hPΓ : P₁ ≤ Γ.toHypergraph := le_trans hP₁A l₁
  have cX := hmin hXT
    ((le_iff_of_le hPΓ (GM10.inter_le l₁ l₄)).2
      ⟨subset_inter hP₁A.vertexSet_subset hP₁Q₂.vertexSet_subset,
        subset_inter hP₁A.edgeSet_subset hP₁Q₂.edgeSet_subset⟩)
    (GM10.union_le hBP₂ hQ₁P₂)
  have cY := hmin hYT (le_trans hP₁A (GM10.le_union_left l₁ l₃))
    (le_trans (GM10.inter_le_left l₂ l₄) hBP₂)
  have hsp₀ := hE e₀ he₀ hs₀
  obtain ⟨q, q', hp, hq, hq'⟩ : ∃ q q', rad.PairOf e₀ q q' ∧ q ∈ Q₁.edgeSet ∧ q' ∈ Q₂.edgeSet := by
    obtain ⟨c₁, c₂, hp, h | h⟩ := rad.splits_iff.mp hs₀
    · exact ⟨c₁, c₂, hp, h⟩
    · refine ⟨c₂, c₁, ?_, h.2, h.1⟩
      obtain ⟨v, w, hv, hw, hs, f₁, f₂, hne, a, b, c, d, x, y⟩ := hp
      exact ⟨v, w, hv, hw, hs, f₂, f₁, hne.symm, b, a, d, c, y, x⟩
  have hiff := (splits_of_pair hS h3 hp hsAB).mp hsp₀
  have hqΓ : q ∈ Γ.E := l₃.edgeSet_subset hq
  have hqn : q ∉ Q₂.edgeSet := fun h ↦ (edge_cases hsQ hqΓ).elim (fun h' ↦ h'.2 h) fun h' ↦ h'.1 hq
  rcases hsub with hle | hle
  · have hqA : q ∈ A.edgeSet := hle.edgeSet_subset hq
    have hqn' : q' ∉ A.edgeSet := fun h ↦ hiff ⟨fun _ ↦ h, fun _ ↦ hqA⟩
    have hns : ¬ rad.Splits (A ∩ Q₂) (B ∪ Q₁) e₀ := fun h ↦
      (splits_of_pair hS h3 hp hX).mp h ⟨fun h' ↦ absurd h'.2 hqn, fun h' ↦ absurd h'.1 hqn'⟩
    exact absurd cX (not_le.mpr (tb.lambda_lt m₁ m₂ he₀ hsp₀ hns))
  · have hqB : q ∈ B.edgeSet := hle.edgeSet_subset hq
    have hqn₁ : q ∉ A.edgeSet := fun h ↦ (edge_cases hsAB hqΓ).elim (fun h' ↦ h'.2 hqB)
      fun h' ↦ h'.1 h
    have hq'A : q' ∈ A.edgeSet := by
      by_contra h'
      exact hiff ⟨fun h ↦ absurd h hqn₁, fun h ↦ absurd h h'⟩
    have hns : ¬ rad.Splits (A ∪ Q₁) (B ∩ Q₂) e₀ := fun h ↦
      (splits_of_pair hS h3 hp hY).mp h ⟨fun _ ↦ Or.inl hq'A, fun _ ↦ Or.inr hq⟩
    exact absurd cY (not_le.mpr (tb.lambda_lt m₃ m₄ he₀ hsp₀ hns))

omit [T2Space S] [T2Space Shat] [ConnectedSpace Shat] in
theorem N1_le_of_lambda_le (tb : TieBreaker rad) {x y : Hypergraph S (Set S) × Hypergraph S (Set S)}
    (h : tb.lambdaOrder x ≤ tb.lambdaOrder y) :
    tb.N1 x ≤ tb.N1 y ∧ (tb.N1 x = tb.N1 y → tb.N2 x ≤ tb.N2 y) := by
  simp only [TieBreaker.lambdaOrder] at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, h'⟩
  · exact ⟨h.le, fun h'' ↦ absurd h'' h.ne⟩
  · refine ⟨h.le, fun _ ↦ ?_⟩
    rw [Prod.Lex.toLex_le_toLex] at h'
    rcases h' with h' | ⟨h', -⟩
    · exact h'.le
    · exact h'.le

/-- **Graph Minors XIX, (8.7).** "**8.7.** *Let $\mathscr{T}$ be a tangle in $\Gamma$, let $F$ be a
circuit of $\Gamma^*$ with $\frac{1}{2} |E(F)| < \min(ord(\mathscr{T}), rep(\Gamma))$, and let
$\Sigma_1, \Sigma_2$ be the closures of the two components of $\hat{\Sigma} \setminus U(F)$, where
$(\Gamma \cap \Sigma_1, \Gamma \cap \Sigma_2) \in \mathscr{T}$. Then there is a $\lambda$-linked
circuit $F'$ in $\Gamma^*$ such that*
• *$|E(F')| \le |E(F)|$ and if equality holds then $\lambda(F') \le \lambda(F)$,*
• *$\Sigma_1 \subseteq \Sigma'_1$ and $\Sigma'_2 \subseteq \Sigma_2$, where $\Sigma'_1, \Sigma'_2$
  are the closures of the two components of $\hat{\Sigma} \setminus U(F')$ and
  $(\Gamma \cap \Sigma'_1, \Gamma \cap \Sigma'_2) \in \mathscr{T}$.*" -/
theorem theorem_8_7_proof (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad) (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    (hF : F.IsCircuitOf rad.G) (hlt : (F.E.ncard : ℕ∞) < 2 * min (ord : ℕ∞) (Painting.rep rad))
    {S₁ S₂ : Set Shat} (hs : IsSidesOf F S₁ S₂) (hm : (partIn cap Γ S₁, partIn cap Γ S₂) ∈ 𝒯) :
    ∃ (F' : Drawing Shat) (S₁' S₂' : Set Shat), IsLambdaLinkedCircuit tb ord 𝒯 F' ∧
      IsSidesOf F' S₁' S₂' ∧
      GM18.IsLambdaLinkedTo tb.lambdaOrder 𝒯 (partIn cap Γ S₁') (partIn cap Γ S₂') ∧
      F'.E.ncard ≤ F.E.ncard ∧ (F'.E.ncard = F.E.ncard → tb.weightSub F' ≤ tb.weightSub F) ∧
      S₁ ⊆ S₁' ∧ S₂' ⊆ S₂ := by
  classical
  have hT := cap.isClosedSurface
  have hlord : (F.E.ncard : ℕ∞) < 2 * (ord : ℕ∞) :=
    lt_of_lt_of_le hlt (by gcongr; exact min_le_left _ _)
  have hlrep : (F.E.ncard : ℕ∞) < 2 * Painting.rep rad :=
    lt_of_lt_of_le hlt (by gcongr; exact min_le_right _ _)
  have hlord' : F.E.ncard < 2 * ord := by exact_mod_cast hlord
  obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hF hlrep
  obtain ⟨Ω₁, Ω₂, hsd, rfl, rfl⟩ := exists_sided_of_isSidesOf hT hΔ hbd hs
  obtain ⟨hPs, hPm, hPo, hPe⟩ := hsd.facts hS h3 hF
  let P₁ := partIn cap Γ (closure Ω₁)
  let P₂ := partIn cap Γ (closure Ω₂)
  -- Choose `(A, B)` of minimum `λ`-order.
  let C : Set (Hypergraph S (Set S) × Hypergraph S (Set S)) := {p | p ∈ 𝒯 ∧ P₁ ≤ p.1 ∧ p.2 ≤ P₂}
  have hCfin : C.Finite := finite_of_forall_isSeparation fun p hp ↦ h𝒯.isSeparation hp.1
  have hCne : hCfin.toFinset.Nonempty :=
    ⟨(P₁, P₂), hCfin.mem_toFinset.2 ⟨hm, le_rfl, le_rfl⟩⟩
  obtain ⟨⟨A, B⟩, hmem, hmin'⟩ := hCfin.toFinset.exists_min_image tb.lambdaOrder hCne
  obtain ⟨hABT, hP₁A, hBP₂⟩ := hCfin.mem_toFinset.1 hmem
  change P₁ ≤ A at hP₁A
  change B ≤ P₂ at hBP₂
  have hmin : ∀ ⦃A' B'⦄, (A', B') ∈ 𝒯 → P₁ ≤ A' → B' ≤ P₂ →
      tb.lambdaOrder (A, B) ≤ tb.lambdaOrder (A', B') := fun A' B' h₁ h₂ h₃ ↦
    hmin' (A', B') (hCfin.mem_toFinset.2 ⟨h₁, h₂, h₃⟩)
  have hsAB := h𝒯.isSeparation hABT
  have hleP := hmin hm le_rfl le_rfl
  obtain ⟨hNP, -⟩ := N1_le_of_lambda_le tb hleP
  have hP₁ne := hsd.edge_nonempty hS h3 hF
  have hA : A.edgeSet.Nonempty := hP₁ne.mono hP₁A.edgeSet_subset
  have hB : B.edgeSet.Nonempty := by
    by_contra hn
    refine left_ne_of_mem h𝒯 hABT (eq_of_all_edges hS h3 rad hsAB.left_le fun c hc ↦ ?_)
    rcases edge_cases hsAB hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd ⟨c, h⟩ hn
  have hordAB : 2 * Hypergraph.separationOrder A B ≤ F.E.ncard := by
    have : Hypergraph.separationOrder A B ≤ Hypergraph.separationOrder P₁ P₂ := hNP
    rw [hPo]
    exact Nat.mul_le_mul_left 2 this
  have hrepAB : (Hypergraph.separationOrder A B : ℕ∞) < Painting.rep rad := by
    by_contra hn
    have h₁ : Painting.rep rad ≤ (Hypergraph.separationOrder A B : ℕ∞) := not_lt.mp hn
    have h₂ : 2 * Painting.rep rad ≤ 2 * (Hypergraph.separationOrder A B : ℕ∞) := by gcongr
    have h₃ : (2 : ℕ∞) * (Hypergraph.separationOrder A B : ℕ∞) ≤ (F.E.ncard : ℕ∞) := by
      exact_mod_cast hordAB
    exact absurd (lt_of_lt_of_le hlrep (h₂.trans h₃)) (lt_irrefl _)
  obtain ⟨F', Δ', hF', hsplit, hΔ', hbd', hsub, hcount, hmid⟩ :=
    theorem_8_1' hS h3 rad hsAB hrepAB hA hB
  -- Orient the sides of `F'`.
  have hordΔ' := disc_order hS h3 rad hF' hΔ' hbd'
  obtain ⟨hsep', -, -, -⟩ := disc_facts hS h3 rad hF' hΔ' hbd'
  have hordlt : Hypergraph.separationOrder (partIn cap Γ Δ') (partIn cap Γ (closure Δ'ᶜ)) < ord :=
    by have := h𝒯.order_lt hABT; omega
  obtain ⟨Ω₁', Ω₂', hsd', hQT, hor⟩ : ∃ Ω₁' Ω₂', Sided F' Ω₁' Ω₂' ∧
      (partIn cap Γ (closure Ω₁'), partIn cap Γ (closure Ω₂')) ∈ 𝒯 ∧
      ((partIn cap Γ (closure Ω₁') ≤ A ∨ partIn cap Γ (closure Ω₁') ≤ B) ∨
        (partIn cap Γ (closure Ω₂') ≤ A ∨ partIn cap Γ (closure Ω₂') ≤ B)) := by
    rcases h𝒯.axiom1 hsep' hordlt with h | h
    · refine ⟨discInt Δ', Δ'ᶜ, ⟨Δ', hΔ', hbd', Or.inl ⟨rfl, rfl⟩⟩, ?_, Or.inl ?_⟩
      · rwa [closure_discInt hΔ']
      · rwa [closure_discInt hΔ']
    · refine ⟨Δ'ᶜ, discInt Δ', ⟨Δ', hΔ', hbd', Or.inr ⟨rfl, rfl⟩⟩, ?_, Or.inr ?_⟩
      · rwa [closure_discInt hΔ']
      · rwa [closure_discInt hΔ']
  obtain ⟨hQs, hQm, hQo, hQe⟩ := hsd'.facts hS h3 hF'
  let Q₁ := partIn cap Γ (closure Ω₁')
  let Q₂ := partIn cap Γ (closure Ω₂')
  have hV : ∀ v ∈ (Q₁ ∩ Q₂).vertexSet, v ∈ (A ∩ B).vertexSet := fun v hv ↦
    hmid v (hQm v hv) (hQs.left_le.vertexSet_subset hv.1)
  have hE : ∀ e ∈ rad.G.E, rad.Splits Q₁ Q₂ e → rad.Splits A B e := fun e he h ↦
    hsplit e ((hQe e he).mp h)
  have hlQ : tb.lambdaOrder (Q₁, Q₂) ≤ tb.lambdaOrder (A, B) := tb.lambda_le hV hE hsAB
  obtain ⟨e₀, he₀⟩ := IsCircuit.E_nonempty hF'.2
  have he₀G := hF'.1.2 he₀
  have hs₀ : rad.Splits Q₁ Q₂ e₀ := (hQe e₀ he₀G).mpr he₀
  have hs₁ := hsd.left hT
  have hs₂ := hsd.right hT
  have hs₁' := hsd'.left hT
  have hs₂' := hsd'.right hT
  have hordF' : F'.E.ncard = 2 * Hypergraph.separationOrder Q₁ Q₂ := hQo
  have hordQ : Hypergraph.separationOrder Q₁ Q₂ < ord := h𝒯.order_lt hQT
  have h2 : 2 ≤ ord := by
    obtain ⟨c, hc⟩ := IsCircuit.E_nonempty hF.2
    have : 0 < F.E.ncard := (ncard_pos F.finite_edges).mpr ⟨c, hc⟩
    omega
  -- The side `Σ₁` is not in `Σ₂'`.
  have hnot : ¬ closure Ω₁ ⊆ closure Ω₂' := by
    intro hc
    have hP₁Q₂ : P₁ ≤ Q₂ := part_mono hc
    have hQ₁P₂ : Q₁ ≤ P₂ := by
      apply part_mono
      refine closure_minimal (fun y hy ↦ hsd.compl_subset hT fun hyΩ ↦ ?_) isClosed_closure
      obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp (hc (subset_closure hyΩ)) _ hs₁'.isOpen hy
      exact disjoint_left.mp hsd'.disjoint hz₁ hz₂
    rcases hor with hsub' | hsub'
    · exact uncross_absurd hS h3 tb h𝒯 hABT hQT hV hE he₀G hs₀ hsub' hP₁A hBP₂ hP₁Q₂ hQ₁P₂ hmin
    · obtain ⟨c, hc'⟩ := hP₁ne
      have hcA : c ∈ A.edgeSet := hP₁A.edgeSet_subset hc'
      have hcQ : c ∈ Q₂.edgeSet := hP₁Q₂.edgeSet_subset hc'
      have hcΓ : c ∈ Γ.E := hsAB.left_le.edgeSet_subset hcA
      rcases hsub' with hle | hle
      · have hT' : (Q₂, Q₁) ∈ 𝒯 := GraphMinor.GM10.theorem_2_9_proof h𝒯 hABT hQs.symm
          (by simp only [Hypergraph.separationOrder, GM10.inter_comm] at hordQ ⊢; exact hordQ)
          (Or.inr (Or.inr ⟨h2, hle.edgeSet_subset⟩))
        refine h𝒯.axiom2 hQT hT' hQT ?_
        have l₁ := hQs.left_le
        have l₂ := hQs.right_le
        have l₃ := GM10.union_le l₁ l₂
        exact eq_of_cover hQs (le_trans (GM10.le_union_left l₁ l₂) (GM10.le_union_left l₃ l₁))
          (le_trans (GM10.le_union_right l₁ l₂) (GM10.le_union_left l₃ l₁)) (GM10.union_le l₃ l₁)
      · exact (edge_cases hsAB hcΓ).elim (fun h ↦ h.2 (hle.edgeSet_subset hcQ)) fun h ↦ h.1 hcA
  -- No edge of `F'` meets the inside of `Σ₁`.
  have hedge : ∀ e ∈ F'.E, e ⊆ Ω₁ᶜ := by
    intro e he
    by_contra hn
    obtain ⟨y, hy, hyn⟩ := not_subset.mp hn
    have hyΩ : y ∈ Ω₁ := not_not.mp hyn
    have heG := hF'.1.2 he
    have heF : e ∉ F.E := fun h ↦ disjoint_left.mp hs₁.disjoint_U hyΩ
      (F.closure_subset_U h (subset_closure hy))
    have hd := edge_disjoint_U hF.1 heG heF
    have heΩ : e ⊆ Ω₁ := hs₁.subset heG.2.2.1.isConnected.isPreconnected hd ⟨y, hy, hyΩ⟩
    obtain ⟨c₁, c₂, hp, hcase⟩ := rad.splits_iff.mp (hsplit e he)
    obtain ⟨hc₁, hc₂⟩ := pair_in_side hS h3 rad hF.1 hs₁ heG hp heΩ
    have hΓ₁ : c₁ ∈ Γ.E := by
      obtain ⟨_, _, _, _, _, _, _, _, h₁, _⟩ := hp
      exact h₁.1
    have hΓ₂ : c₂ ∈ Γ.E := by
      obtain ⟨_, _, _, _, _, _, _, _, _, h₂, _⟩ := hp
      exact h₂.1
    have m₁ : c₁ ∈ A.edgeSet := hP₁A.edgeSet_subset (restrict_side hΓ₁ hc₁)
    have m₂ : c₂ ∈ A.edgeSet := hP₁A.edgeSet_subset (restrict_side hΓ₂ hc₂)
    rcases hcase with h | h
    · exact (edge_cases hsAB hΓ₂).elim (fun h' ↦ h'.2 h.2) fun h' ↦ h'.1 m₂
    · exact (edge_cases hsAB hΓ₁).elim (fun h' ↦ h'.2 h.1) fun h' ↦ h'.1 m₁
  have hUd : Disjoint Ω₁ F'.U := by
    have := U_of_edges hF'.2 hs₁.isOpen.isClosed_compl hedge
    exact disjoint_left.mpr fun x hx hxU ↦ this hxU hx
  have hΩsub : Ω₁ ⊆ Ω₁' := by
    rcases hs₁.conn.subset_or_subset hs₁'.isOpen hs₂'.isOpen hsd'.disjoint
      (fun x hx ↦ hsd'.cover (disjoint_left.mp hUd hx)) with h | h
    · exact h
    · exact absurd (closure_mono h) hnot
  have hS₁ : closure Ω₁ ⊆ closure Ω₁' := closure_mono hΩsub
  have hS₂ : closure Ω₂' ⊆ closure Ω₂ := by
    refine closure_minimal (fun y hy ↦ hsd.compl_subset hT fun hyΩ ↦ ?_) isClosed_closure
    exact disjoint_left.mp hsd'.disjoint (hΩsub hyΩ) hy
  have hP₁Q₁ : P₁ ≤ Q₁ := part_mono hS₁
  have hQ₂P₂ : Q₂ ≤ P₂ := part_mono hS₂
  have hlinked : GM18.IsLambdaLinkedTo tb.lambdaOrder 𝒯 Q₁ Q₂ :=
    ⟨hQT, fun A' B' hT' h₁ h₂ ↦ hlQ.trans (hmin hT' (le_trans hP₁Q₁ h₁) (le_trans h₂ hQ₂P₂))⟩
  have hcmp := N1_le_of_lambda_le tb (hlQ.trans hleP)
  have hN : Hypergraph.separationOrder Q₁ Q₂ ≤ Hypergraph.separationOrder P₁ P₂ := hcmp.1
  have hordF : F.E.ncard = 2 * Hypergraph.separationOrder P₁ P₂ := hPo
  have hcard : F'.E.ncard ≤ F.E.ncard := by omega
  have hN2 : ∀ {K : Drawing Shat} {X Y : Hypergraph S (Set S)},
      (∀ e ∈ rad.G.E, rad.Splits X Y e ↔ e ∈ K.E) → K.E ⊆ rad.G.E →
      tb.N2 (X, Y) = tb.weightSub K := by
    intro K X Y hiff hsub'
    have : {e ∈ rad.G.E | rad.Splits X Y e} = K.E :=
      Subset.antisymm (fun e he ↦ (hiff e he.1).mp he.2) fun e he ↦ ⟨hsub' he, (hiff _
        (hsub' he)).mpr he⟩
    simp only [TieBreaker.N2, TieBreaker.weightSub]
    rw [this]
  refine ⟨F', closure Ω₁', closure Ω₂', ⟨hF', ?_, _, _, hsd'.isSidesOf hT, hlinked⟩,
    hsd'.isSidesOf hT, hlinked, hcard, fun heq ↦ ?_, hS₁, hS₂⟩
  · exact lt_of_le_of_lt (by exact_mod_cast hcard) hlt
  · have := hcmp.2 (by simp only [TieBreaker.N1]; omega)
    rwa [hN2 hQe hF'.1.2, hN2 hPe hF.1.2] at this

end Main

end GraphMinor.GM19
