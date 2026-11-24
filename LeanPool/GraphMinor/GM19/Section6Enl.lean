/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# Graph Minors XIX, proof of (6.2): the enlargement `τ` of `sk(Γ₁)` in `sk(Γ₂)`

The opening of the proof of (6.2), page 342. An inflation `σ` of `Γ₁` in `Γ₂` gives an enlargement
`τ`
of `sk(Γ₁)` in `sk(Γ₂)`, drawn in `Σ̂`. The edge `τ(e)` is `σ(e)` for an edge of size 2. For a part
`e` of
the boundary of the disc of an edge `c` of size 3, it is the part of the boundary of the disc of
`σ(c)`
with ends in `σ(u), σ(v)`. The main result is `exists_enlargement`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Preconnected induced graphs map onto preconnected induced graphs. -/
theorem preconnected_image {α β : Type} {G : SimpleGraph α} {H : SimpleGraph β} {X : Set α} {Y :
  Set β}
    (φ : α → β) (h : (G.induce X).Preconnected) (hs : Y = φ '' X)
    (hadj : ∀ a ∈ X, ∀ b ∈ X, G.Adj a b → H.Adj (φ a) (φ b)) : (H.induce Y).Preconnected := by
  subst hs
  rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
  let ψ : G.induce X →g H.induce (φ '' X) :=
    { toFun := fun x => ⟨φ x.1, x.1, x.2, rfl⟩
      map_rel' := fun {x y} h => hadj _ x.2 _ y.2 h }
  exact (h ⟨a, ha⟩ ⟨b, hb⟩).map ψ

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}

/-! ### The drawing induced on a set of vertices -/

section Induced

variable {T : Type} [TopologicalSpace T] [T2Space T] (G : Drawing T)

/-- The subdrawing of `G` induced on `X`. -/
noncomputable def indDrawing (X : Set T) : Drawing T := G.span X {e | e ∈ G.E ∧ tilde e ⊆ X}

theorem indDrawing_V {X : Set T} (hX : X ⊆ G.V) : (indDrawing G X).V = X := by
  rw [indDrawing, Drawing.span_V]
  refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset ?_)) fun x hx
    => .inl ⟨hx, hX hx⟩
  rintro e ⟨he, -⟩ x hx
  have h : x ∈ tilde e := tilde_eq_inter_V G he.1 ▸ hx
  exact he.2 h

theorem indDrawing_E (X : Set T) : (indDrawing G X).E = {e | e ∈ G.E ∧ tilde e ⊆ X} := by
  rw [indDrawing, Drawing.span_E]
  exact inter_eq_left.mpr fun e he => he.1

theorem indDrawing_sub {X : Set T} (hX : X ⊆ G.V) : (indDrawing G X).IsSubdrawing G := by
  refine ⟨by rw [indDrawing_V G hX]; exact hX, ?_⟩
  rw [indDrawing_E G]
  exact fun e he => he.1

theorem indDrawing_adj (hl : LoopFree G) {X : Set T} (hX : X ⊆ G.V) {a b : T} (ha : a ∈ X)
  (hb : b ∈ X)
    (h : G.adj.Adj a b) : (indDrawing G X).adj.Adj a b := by
  obtain ⟨hne, -, -, e, he, hae, hbe⟩ := h
  obtain ⟨u, v, -, ht, -⟩ := hl e he
  refine ⟨hne, by rw [indDrawing_V G hX]; exact ha, by rw [indDrawing_V G hX]; exact hb,
    e, ?_, hae, hbe⟩
  rw [indDrawing_E G]
  refine ⟨he, ?_⟩
  have hsub : tilde e ⊆ {a, b} := by
    rw [ht] at hae hbe ⊢
    rintro x (rfl | rfl)
    · rcases hae with rfl | h
      · exact .inl rfl
      · rcases hbe with rfl | h'
        · exact .inr rfl
        · exact absurd (h.trans (mem_singleton_iff.mp h').symm) hne
    · rcases hae with h | h
      · rcases hbe with h' | h'
        · exact absurd (h.trans h'.symm) hne
        · exact .inr (mem_singleton_iff.mp h').symm
      · exact .inl (mem_singleton_iff.mp h).symm
  rintro x hx
  rcases hsub hx with rfl | rfl
  · exact ha
  · exact hb

end Induced

/-! ### `sk(Γ)` in `Σ̂` -/

section Sk

omit [T2Space S] in
theorem sk_of_edge (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard = 2) :
    e ∈ arcComponentsIn (Γ.skU \ Γ.V) := by
  have hsub : e ⊆ Γ.skU \ Γ.V := fun x hx =>
    ⟨Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨he, h2⟩, hx⟩)), (he.2.1 hx).2⟩
  obtain ⟨f, hf, hef⟩ := exists_arcComp_superset he.2.2.1 hsub
  obtain ⟨c, hc, hfc⟩ := exists_arcComp_superset hf.2.2.1
    (hf.2.1.trans (sdiff_subset_sdiff_left Γ.skU_subset))
  obtain ⟨x, hx⟩ := he.2.2.1.nonempty
  obtain rfl := arcComp_eq_of_mem hc he (hfc (hef hx)) hx
  exact (Subset.antisymm hef hfc) ▸ hf

omit [T2Space Shat] in
omit [T2Space S] in
theorem tilde_emb (hS : IsSurface S) (cap : IsCappedSurface S Shat) (e : Set S) :
    tilde (cap.emb '' e) = cap.emb '' tilde e := by
  rw [tilde, tilde, image_sdiff cap.isEmbedding.injective, (cap.isClosedEmbedding
    hS).closure_image_eq]

omit [T2Space Shat] in
theorem sk_adj_of (hS : IsSurface S) (hD : IsSkHat cap Γ D) {a b : S} (h : Γ.skAdj.Adj a b) :
    D.adj.Adj (cap.emb a) (cap.emb b) := by
  obtain ⟨hne, ha, hb, c, hc, hac, hbc⟩ := h
  refine ⟨fun h => hne (cap.isEmbedding.injective h), hD.hV ▸ mem_image_of_mem _ ha,
    hD.hV ▸ mem_image_of_mem _ hb, ?_⟩
  have hend : ∃ f ∈ arcComponentsIn (Γ.skU \ Γ.V), a ∈ tilde f ∧ b ∈ tilde f := by
    rcases Γ.size_cases hc with h2 | h3
    · exact ⟨c, sk_of_edge Γ hc h2, hac, hbc⟩
    · obtain ⟨f, hf, -, -, ht⟩ := exists_sk_boundary Γ hc h3 hac hbc hne
      exact ⟨f, hf, ht ▸ .inl rfl, ht ▸ .inr rfl⟩
  obtain ⟨f, hf, haf, hbf⟩ := hend
  refine ⟨cap.emb '' f, (hD.edge_iff hS).mpr ⟨f, hf, rfl⟩, ?_, ?_⟩
  · rw [tilde_emb hS]
    exact mem_image_of_mem _ haf
  · rw [tilde_emb hS]
    exact mem_image_of_mem _ hbf

omit [T2Space Shat] in
theorem adj_sk_of (hS : IsSurface S) (hD : IsSkHat cap Γ D) {a b : S}
    (h : D.adj.Adj (cap.emb a) (cap.emb b)) : Γ.skAdj.Adj a b := by
  obtain ⟨hne, ha, hb, e, he, hae, hbe⟩ := h
  obtain ⟨f, hf, rfl⟩ := (hD.edge_iff hS).mp he
  rw [tilde_emb hS] at hae hbe
  have ha' : a ∈ tilde f := by
    obtain ⟨x, hx, h⟩ := hae
    rwa [← cap.isEmbedding.injective h]
  have hb' : b ∈ tilde f := by
    obtain ⟨x, hx, h⟩ := hbe
    rwa [← cap.isEmbedding.injective h]
  obtain ⟨u, v, -, -, htV, -⟩ := Γ.sk_line hf
  have hneq : a ≠ b := fun h => hne (congrArg _ h)
  rcases Γ.sk_cases hf with ⟨hfE, -⟩ | ⟨c, hc, -, hfc, -⟩
  · exact ⟨hneq, htV ha', htV hb', f, hfE, ha', hb'⟩
  · have htil : ∀ {x}, x ∈ tilde f → x ∈ tilde c := fun {x} hx =>
      ⟨closure_mono hfc hx.1, fun h => Γ.disjoint_V hc h (htV hx)⟩
    exact ⟨hneq, htV ha', htV hb', c, hc, htil ha', htil hb'⟩

end Sk

/-! ### The edges of `τ` -/

section Tau

variable {Γ₁ Γ₂ : Painting S} {σv : S → Set S} {σe : Set S → Set S}

/-- The edge `τ(e)` of the proof of (6.2). -/
theorem exists_tau_edge (h : IsInflation Γ₁ Γ₂ σv σe) {e₀ : Set S}
    (he : e₀ ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V)) :
    ∃ e' ∈ arcComponentsIn (Γ₂.skU \ Γ₂.V), (∀ a ∈ tilde e', ∃ x ∈ tilde e₀, a ∈ σv x) ∧
      (∀ x ∈ tilde e₀, ∃ a ∈ tilde e', a ∈ σv x) ∧
      ((e₀ ∈ Γ₁.E ∧ e' = σe e₀) ∨ ∃ c ∈ Γ₁.E, e₀ ⊆ c ∧ e₀ ⊆ discBd (closure c) ∧ e' ⊆ σe c ∧
        (tilde c).ncard = 3) := by
  rcases Γ₁.sk_cases he with ⟨hE, h2⟩ | ⟨c, hc, h3, hsub, hdb⟩
  · obtain ⟨h₁, h₂⟩ := infl_ends h hE
    exact ⟨σe e₀, sk_of_edge Γ₂ (h.edge_mem _ hE) (by rw [h.edge_size _ hE, h2]), h₁, h₂,
      .inl ⟨hE, rfl⟩⟩
  · obtain ⟨u, v, huv, ht, htV, -⟩ := Γ₁.sk_line he
    have htil : ∀ {x}, x ∈ tilde e₀ → x ∈ tilde c := fun {x} hx =>
      ⟨closure_mono hsub hx.1, fun h' => Γ₁.disjoint_V hc h' (htV hx)⟩
    have hu : u ∈ tilde e₀ := ht ▸ .inl rfl
    have hv : v ∈ tilde e₀ := ht ▸ .inr rfl
    obtain ⟨-, h₂⟩ := infl_ends h hc
    obtain ⟨a, hat, ha⟩ := h₂ u (htil hu)
    obtain ⟨b, hbt, hb⟩ := h₂ v (htil hv)
    have hab : a ≠ b := fun hab =>
      disjoint_left.mp (h.vertex_disjoint u (htV hu) v (htV hv) huv) ha (hab ▸ hb)
    obtain ⟨f, hf, -, hfc, htf⟩ := exists_sk_boundary Γ₂ (h.edge_mem c hc)
      (by rw [h.edge_size _ hc, h3]) hat hbt hab
    refine ⟨f, hf, ?_, ?_, .inr ⟨c, hc, hsub, hdb, hfc, h3⟩⟩
    · rw [htf]
      rintro y (rfl | rfl)
      · exact ⟨u, hu, ha⟩
      · exact ⟨v, hv, hb⟩
    · rw [ht]
      rintro y (rfl | rfl)
      · exact ⟨a, htf ▸ .inl rfl, ha⟩
      · exact ⟨b, htf ▸ .inr rfl, hb⟩

/-- The edges `τ(e)` are distinct. -/
theorem tau_inj (h : IsInflation Γ₁ Γ₂ σv σe) {e₁ e₂ e' : Set S}
    (he₁ : e₁ ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V)) (he₂ : e₂ ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V))
    (hne : e'.Nonempty)
    (h₁ : (∀ a ∈ tilde e', ∃ x ∈ tilde e₁, a ∈ σv x) ∧ (∀ x ∈ tilde e₁, ∃ a ∈ tilde e', a ∈ σv x) ∧
      ((e₁ ∈ Γ₁.E ∧ e' = σe e₁) ∨ ∃ c ∈ Γ₁.E, e₁ ⊆ c ∧ e₁ ⊆ discBd (closure c) ∧ e' ⊆ σe c ∧
        (tilde c).ncard = 3))
    (h₂ : (∀ a ∈ tilde e', ∃ x ∈ tilde e₂, a ∈ σv x) ∧ (∀ x ∈ tilde e₂, ∃ a ∈ tilde e', a ∈ σv x) ∧
      ((e₂ ∈ Γ₁.E ∧ e' = σe e₂) ∨ ∃ c ∈ Γ₁.E, e₂ ⊆ c ∧ e₂ ⊆ discBd (closure c) ∧ e' ⊆ σe c ∧
        (tilde c).ncard = 3)) :
    e₁ = e₂ := by
  obtain ⟨y, hy⟩ := hne
  have hsize : ∀ {e}, e ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V) → (tilde e).ncard = 2 := fun {e} he => by
    obtain ⟨u, v, huv, ht, -, -⟩ := Γ₁.sk_line he
    rw [ht, ncard_pair huv]
  have hmix : ∀ {e c : Set S}, e ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V) → e ∈ Γ₁.E → c ∈ Γ₁.E →
      y ∈ σe e → y ∈ σe c → (tilde c).ncard = 3 → False := by
    intro e c he hE hc hye hyc h3
    have h1 := arcComp_eq_of_mem (h.edge_mem _ hE) (h.edge_mem _ hc) hye hyc
    obtain rfl := h.edge_injOn hE hc h1
    rw [hsize he] at h3
    omega
  rcases h₁.2.2 with ⟨hE₁, rfl⟩ | ⟨c₁, hc₁, hs₁, hb₁, hy₁, h3₁⟩ <;>
    rcases h₂.2.2 with ⟨hE₂, heq⟩ | ⟨c₂, hc₂, hs₂, hb₂, hy₂, h3₂⟩
  · exact h.edge_injOn hE₁ hE₂ heq
  · exact (hmix he₁ hE₁ hc₂ hy (hy₂ hy) h3₂).elim
  · exact (hmix he₂ hE₂ hc₁ (heq ▸ hy) (hy₁ hy) h3₁).elim
  · have h1 := arcComp_eq_of_mem (h.edge_mem _ hc₁) (h.edge_mem _ hc₂) (hy₁ hy) (hy₂ hy)
    obtain rfl := h.edge_injOn hc₁ hc₂ h1
    have hVs : ∀ {e}, e ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V) → tilde e ⊆ Γ₁.V := fun {e} he => by
      obtain ⟨u, v, -, -, htV, -⟩ := Γ₁.sk_line he
      exact htV
    have hsub : ∀ {e e''}, e ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V) → e'' ∈ arcComponentsIn
      (Γ₁.skU \ Γ₁.V) →
        (∀ x ∈ tilde e, ∃ a ∈ tilde e', a ∈ σv x) → (∀ a ∈ tilde e', ∃ x ∈ tilde e'', a ∈ σv x) →
        tilde e ⊆ tilde e'' := by
      intro e e'' hee hee'' hA hB x hx
      obtain ⟨a, hat, ha⟩ := hA x hx
      obtain ⟨w, hw, haw⟩ := hB a hat
      by_cases hxw : x = w
      · exact hxw ▸ hw
      · exact absurd haw (disjoint_left.mp (h.vertex_disjoint x (hVs hee hx) w
        (hVs hee'' hw) hxw) ha)
    have ht : tilde e₁ = tilde e₂ :=
      Subset.antisymm (hsub he₁ he₂ h₁.2.1 h₂.1) (hsub he₂ he₁ h₂.2.1 h₁.1)
    exact sk_boundary_unique Γ₁ hc₁ h3₁ he₁ he₂ hb₁ hb₂ ht

/-- **The enlargement `τ`** of `sk(Γ₁)` in `sk(Γ₂)` given by an inflation `σ` (Graph Minors XIX,
proof of
(6.2), page 342). -/
theorem exists_enlargement (hS : IsSurface S) {D₁ D₂ : Drawing Shat} (hD₁ : IsSkHat cap Γ₁ D₁)
    (hD₂ : IsSkHat cap Γ₂ D₂) (hl₂ : LoopFree D₂) (h : IsInflation Γ₁ Γ₂ σv σe) :
    ∃ (τv : Shat → Drawing Shat) (τe : Set Shat → Set Shat), IsEnlargement D₁ D₂ τv τe ∧
      (∀ e ∈ Γ₁.E, (tilde e).ncard = 2 → τe (cap.emb '' e) = cap.emb '' σe e) ∧
      ∀ v ∈ Γ₁.V, (τv (cap.emb v)).V = cap.emb '' σv v := by
  classical
  have hinj := cap.isEmbedding.injective
  have hE := fun e₀ (he : e₀ ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V)) => exists_tau_edge h he
  choose! τ₀ hτ using hE
  let σh : Shat → Set Shat := fun x => {a | ∃ v, cap.emb v = x ∧ a ∈ cap.emb '' σv v}
  have hσh : ∀ v, σh (cap.emb v) = cap.emb '' σv v := by
    intro v
    ext a
    constructor
    · rintro ⟨w, hw, ha⟩
      rwa [← hinj hw]
    · exact fun ha => ⟨v, rfl, ha⟩
  have hsub : ∀ v ∈ Γ₁.V, σh (cap.emb v) ⊆ D₂.V := fun v hv => by
    rw [hσh, hD₂.hV]
    exact image_mono (h.vertex_subset v hv)
  have hVemb : ∀ {x}, x ∈ D₁.V → ∃ v ∈ Γ₁.V, cap.emb v = x := fun {x} hx => by
    rw [hD₁.hV] at hx
    exact hx
  let τe : Set Shat → Set Shat := fun e => cap.emb '' τ₀ (cap.emb ⁻¹' e)
  have hτe : ∀ e, τe (cap.emb '' e) = cap.emb '' τ₀ e := fun e => by
    change cap.emb '' τ₀ (cap.emb ⁻¹' (cap.emb '' e)) = _
    rw [preimage_image_eq _ hinj]
  have hVw : ∀ {e₀}, e₀ ∈ arcComponentsIn (Γ₁.skU \ Γ₁.V) → tilde e₀ ⊆ Γ₁.V := fun {e₀} he => by
    obtain ⟨u, v, -, -, htV, -⟩ := Γ₁.sk_line he
    exact htV
  refine ⟨fun x => indDrawing D₂ (σh x), τe, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := (hD₁.edge_iff hS).mp he
    rw [hτe]
    exact (hD₂.edge_iff hS).mpr ⟨_, (hτ e₀ he₀).1, rfl⟩
  · intro e₁ he₁ e₂ he₂ heq
    obtain ⟨c₁, hc₁, rfl⟩ := (hD₁.edge_iff hS).mp he₁
    obtain ⟨c₂, hc₂, rfl⟩ := (hD₁.edge_iff hS).mp he₂
    change τe _ = τe _ at heq
    rw [hτe, hτe] at heq
    have heq' := hinj.image_injective heq
    have h₂ := (hτ c₂ hc₂).2
    rw [← heq'] at h₂
    rw [tau_inj h hc₁ hc₂ (hτ c₁ hc₁).1.2.2.1.nonempty (hτ c₁ hc₁).2 h₂]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hVemb hx
    exact indDrawing_sub D₂ (hsub v hv)
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hVemb hx
    rw [indDrawing_V D₂ (hsub v hv), hσh]
    exact (h.vertex_nonempty v hv).image _
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hVemb hx
    rw [indDrawing_V D₂ (hsub v hv)]
    refine preconnected_image cap.emb (h.vertex_connected v hv) (hσh v) fun a ha b hb hab => ?_
    have hmem : ∀ {y}, y ∈ σv v → cap.emb y ∈ σh (cap.emb v) := fun hy => by
      rw [hσh]
      exact mem_image_of_mem _ hy
    exact indDrawing_adj D₂ hl₂ (hsub v hv) (hmem ha) (hmem hb) (sk_adj_of hS hD₂ hab)
  · intro x₁ hx₁ x₂ hx₂ hne
    obtain ⟨v₁, hv₁, rfl⟩ := hVemb hx₁
    obtain ⟨v₂, hv₂, rfl⟩ := hVemb hx₂
    rw [indDrawing_V D₂ (hsub v₁ hv₁), indDrawing_V D₂ (hsub v₂ hv₂), hσh, hσh]
    exact (disjoint_image_iff hinj).mpr
      (h.vertex_disjoint v₁ hv₁ v₂ hv₂ fun h' => hne (congrArg _ h'))
  · intro e he x hx
    obtain ⟨e₀, he₀, rfl⟩ := (hD₁.edge_iff hS).mp he
    obtain ⟨v, hv, rfl⟩ := hVemb hx
    rw [indDrawing_V D₂ (hsub v hv), hτe, hσh, tilde_emb hS, tilde_emb hS, ← image_inter hinj,
      image_nonempty, hinj.mem_set_image]
    obtain ⟨-, h₁, h₂, -⟩ := hτ e₀ he₀
    constructor
    · rintro ⟨a, ha, hat⟩
      obtain ⟨y, hy, hay⟩ := h₁ a hat
      by_cases hvy : v = y
      · exact hvy ▸ hy
      · exact absurd hay (disjoint_left.mp (h.vertex_disjoint v hv y (hVw he₀ hy) hvy) ha)
    · intro hvt
      obtain ⟨a, hat, ha⟩ := h₂ v hvt
      exact ⟨a, ha, hat⟩
  · intro e he h2
    rw [hτe]
    have hk := sk_of_edge Γ₁ he h2
    rcases (hτ e hk).2.2.2 with ⟨-, h'⟩ | ⟨c, hc, hsubc, -, -, h3⟩
    · rw [h']
    · obtain ⟨x, hx⟩ := he.2.2.1.nonempty
      obtain rfl := arcComp_eq_of_mem he hc hx (hsubc hx)
      omega
  · intro v hv
    exact (indDrawing_V D₂ (hsub v hv)).trans (hσh v)

end Tau

end GraphMinor.GM19
