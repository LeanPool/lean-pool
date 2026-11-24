/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15m

/-!
# Graph Minors XIX, (15.2): the ends of the edges `β(e)`

We collect what step (1) of the proof of (15.2) says about the ends of the edges `β(e)`, once the
first and second outcomes of (15.2) are excluded. Two edges `β(e)`, `β(e')` with `e ≠ e'` have no
common end, unless `e` and `e'` are short sides
(`no_common_end`). The paper uses this in step (2), and we use it to show that the sets `Z_v` of
(3.2) of Graph Minors XII are disjoint. A short side has the same direction in `Γ₀` and in `Γ`
(`short_γ_eq`), so in that last case the two ends belong to the same vertex.
The sets `Z_v` are `TangleDatum.endClass`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

omit [T2Space S] in
/-- The length of `γ(e)` is the size of `e`. -/
theorem Painting.length_γ_eq (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.E) : (Γ.γ c).length =
  (tilde c).ncard := by
  classical
  have e : tilde c = ↑(Γ.γ c).toFinset := by
    rw [← Γ.γ_set c hc]
    ext
    simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup (Γ.γ_nodup c hc)]

omit [T2Space S] in
/-- A short side has the direction of the frame in every painting that fits the frame. -/
theorem short_γ_eq (P : ColouredPainting χ) {s : Set S}
  (hs : s ∈ χ.Φ.shortSides) : P.Γ.γ s = χ.Φ.γ s := by
  classical
  have hE := P.fits.short_sides hs
  obtain ⟨x, hx⟩ : s.Nonempty := hE.1
  have hB : Painting.IsBorder s := ⟨x, hx, (hs.1.2.1 hx).1⟩
  obtain ⟨f, t₁, t₂, hlt, -, h₁, h₂, h₃, h₄⟩ := P.fits.border_dir s hE hB s hs.1 Subset.rfl
  have hl₁ : (P.Γ.γ s).length = 2 := by
    rw [P.Γ.length_γ_eq hE]
    exact (P.Γ.border_edge s hE hB).1
  have hl₂ : (χ.Φ.γ s).length = 2 := by
    have h2 := (P.Γ.border_edge s hE hB).1
    have e : tilde s = ↑(χ.Φ.γ s).toFinset := by
      rw [← χ.Φ.γ_set s hs.1]
      ext
      simp
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup (χ.Φ.γ_nodup s hs.1)] at h2
    exact h2
  obtain ⟨a', b', ha⟩ := List.length_eq_two.mp hl₁
  obtain ⟨a, b, hb⟩ := List.length_eq_two.mp hl₂
  have hset : ∀ y, y ∈ tilde s → y = a ∨ y = b := fun y hy => by
    have : y ∈ {v | v ∈ χ.Φ.γ s} := by rwa [χ.Φ.γ_set s hs.1]
    simpa [hb] using this
  have hset' : ∀ y, y ∈ P.Γ.γ s → y ∈ tilde s := fun y hy => by
    have : y ∈ {v | v ∈ P.Γ.γ s} := hy
    rwa [P.Γ.γ_set s hE] at this
  rw [ha] at h₃ h₄ hset'
  rw [hb] at h₁ h₂
  simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq] at h₁ h₂ h₃ h₄
  have hinj : Function.Injective fun t => (f t).1 := Subtype.val_injective.comp f.injective
  have ht₁ : a' = a := by
    rcases hset a' (hset' a' (by simp)) with h | h
    · exact h
    · exfalso
      rw [h₃, h₂] at h
      have := hinj h
      have h' : t₂.1 ≤ 1 := t₂.2.2
      have h'' : t₁.1 < t₂.1 := hlt
      rw [this] at h''
      simp only at h''
      linarith
  have ht₂ : b' = b := by
    rcases hset b' (hset' b' (by simp)) with h | h
    · exfalso
      rw [h₄, h₁] at h
      have := hinj h
      have h' : 0 ≤ t₁.1 := t₁.2.1
      have h'' : t₁.1 < t₂.1 := hlt
      rw [this] at h''
      simp only at h''
      linarith
    · exact h
  rw [ha, hb, ht₁, ht₂]

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- What we know about `β` in the proof of (15.2) once the first and second outcomes are excluded.
-/
structure IsMatchSetting (D : TangleDatum cap χ) (P₀ : ColouredPainting χ) (n : ℕ) (b : Set S
  → Set S) : Prop where
  edge : D.IsEdgeMap P₀ n b
  large : 16 ≤ n
  rep_gt : n < D.rep
  free : ∀ C, ¬ D.IsFreeCircuit n C
  far : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → n < D.vDist r₁ r₂

/-- An edge with an end on a cuff is close to the pole of the cuff. -/
theorem edgeVertDist_pole_le (hS : IsSurface S) (hrep : 4 ≤ D.rep) {c : Set S}
  (hc : c ∈ D.P.Γ.E) {y : S} (hy : y ∈ tilde c) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hyΘ : y ∈ Θ) {p : Shat} (hp : p ∈ D.rad.poles)
    (hreg : D.rad.regionOf p = cap.cuffDisc Θ) : D.edgeVertDist c p ≤ 4 := by
  have h3 := D.P.fits.internally_three_connected
  have hyV := D.P.Γ.tilde_subset_V hc hy
  obtain ⟨e, he, hs⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hyV hyΘ
  have hl : D.rad.G.toGraph.IsLink e (cap.emb y) p := ⟨he, D.rad.isPreRadial.2.1
    (mem_image_of_mem _ hyV), hp.1.1, hs⟩
  let W : GraphWalk D.rad.G.toGraph (cap.emb y) p := .cons hl (.nil hp.1.1)
  have h₁ : D.dist (D.rad.atomOf (cap.emb y)) (D.rad.atomOf p) ≤ 1 :=
    D.dist_atomOf_le_of_walk W (by change 1 < _; omega)
  rw [D.atomOf_emb hyV] at h₁
  have h₂ := D.edgeVertDist_self_le hrep hc hy hyV
  unfold edgeVertDist at h₂ ⊢
  rw [D.atomOf_emb hyV] at h₂
  have h₃ := D.dist_triangle hrep (a := cap.emb '' c) (c := D.rad.atomOf p) (b := {cap.emb y})
    (Or.inl (Or.inl ⟨y, hyV, rfl⟩))
  omega

/-- Two edges with a common end are close. -/
theorem edgeDist_le_of_common_end (hrep : 4 ≤ D.rep) {c c' : Set S} (hc : c ∈ D.P.Γ.E)
  (hc' : c' ∈ D.P.Γ.E) {y : S} (hy : y ∈ tilde c) (hy' : y ∈ tilde c') : D.edgeDist c c' ≤ 6 := by
  have hyV := D.P.Γ.tilde_subset_V hc hy
  have h₁ := D.edgeVertDist_self_le hrep hc hy hyV
  have h₂ := D.edgeVertDist_self_le hrep hc' hy' hyV
  unfold edgeVertDist at h₁ h₂
  rw [D.atomOf_emb hyV] at h₁ h₂
  have h₃ := D.dist_triangle hrep (a := cap.emb '' c) (c := cap.emb '' c') (b := {cap.emb y})
    (Or.inl (Or.inl ⟨y, hyV, rfl⟩))
  rw [D.dist_comm {cap.emb y} (cap.emb '' c')] at h₃
  unfold edgeDist
  omega

/-- Two edges on a cuff with a common end are close along the cuff. -/
theorem IsSideSetting.borderEdgeDist_le_of_common_end {side Θ : Set S} {r : Shat} {N : ℕ}
  (X : D.IsSideSetting side Θ r N) (hS : IsSurface S) (hN : 6 ≤ N) {t₁ t₂ : Set S}
    (h₁ : t₁ ∈ D.P.Γ.E) (h₂ : t₂ ∈ D.P.Γ.E)
    (h₁Θ : t₁ ⊆ Θ) (h₂Θ : t₂ ⊆ Θ) {z : S} (hz₁ : z ∈ closure t₁) (hz₂ : z ∈ closure t₂) :
      D.borderEdgeDist r t₁ t₂ ≤ 6 := by
  have hΘcl : IsClosed Θ := ((cuff_statement S hS).2.2 Θ X.cuff).isCompact.isClosed
  have hrep : 4 ≤ D.rep := by
    have := X.rep_gt
    omega
  obtain ⟨G₁, hG₁, h₆₁, hs₁⟩ := exists_bite_of_edge hS (by omega) hrep X.free X.long X.side_cuff
    X.cuff X.pole X.reg h₁ h₁Θ
  obtain ⟨G₂, hG₂, h₆₂, hs₂⟩ := exists_bite_of_edge hS (by omega) hrep X.free X.long X.side_cuff
    X.cuff X.pole X.reg h₂ h₂Θ
  have key : ∀ {G : Drawing Shat} {t : Set S}, D.IsBiteAt r G → cap.emb '' t ⊆ D.ins G
    → z ∈ closure t → cap.emb z ∈ D.ins G := fun {G t} hG hs hz => by
    refine closure_minimal hs (D.ins_spec hG.is_circuit hG.card_lt).2.2.1.isClosed ?_
    rw [(cap.isClosedEmbedding hS).closure_image_eq t]
    exact mem_image_of_mem _ hz
  have hzΘ : cap.emb z ∈ cap.emb '' Θ := mem_image_of_mem _ (closure_minimal h₁Θ hΘcl hz₁)
  obtain ⟨C, hC, hC₂, hC₃, hC₄⟩ := X.exists_bite_superset hS hG₁ hG₂ (by omega) hzΘ
    (key hG₁ hs₁ hz₁) (key hG₂ hs₂ hz₂)
  have := D.borderEdgeDist_le_of_bite hC (hs₁.trans hC₃) (hs₂.trans hC₄)
  omega

variable (hM : D.IsMatchSetting P₀ n b)
include hM

omit [T2Space S] in
/-- A setting for each cuff that holds a long side. -/
theorem IsMatchSetting.setting {side Θ : Set S} (hside : side ∈ χ.Φ.longSides)
  (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S) {r : Shat} (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r
    = cap.cuffDisc Θ) : D.IsSideSetting side Θ r n :=
  ⟨D.P.fits.internally_three_connected, hside, hsΘ, hΘ, hr, hreg, hM.rep_gt, hM.far, hM.free⟩

/-- The image of a border edge on a long side has no end in common with an edge on the same cuff
that is the image of another edge on the side, or a short side. -/
theorem IsMatchSetting.no_common_end_long (hS : IsSurface S) {e : Set S}
  (he : e ∈ P₀.Γ.E) {s Θ : Set S} (hs : s ∈ χ.Φ.longSides) (hsΘ : s ⊆ Θ) (hΘ : Θ ∈ cuffs S)
    (hes : e ⊆ s) {t : Set S}
    (ht : (∃ e' ∈ P₀.Γ.E, e' ≠ e ∧ e' ⊆ s ∧ t = b e') ∨ (t ∈ χ.Φ.shortSides ∧ t ⊆ Θ)) {y : S}
      (hy : y ∈ closure (b e)) (hyt : y ∈ closure t) : False := by
  obtain ⟨m, f, g, c, r', u₀, u₁, u₀', u₁', hM'⟩ := hM.edge.side s hs
  obtain ⟨x, hx⟩ : e.Nonempty := he.1
  have hcE : c = Θ := cuffs_eq_of_mem hM'.cuff hΘ (hM'.side_cuff (hes hx)) (hsΘ (hes hx))
  rw [hcE] at hM'
  obtain ⟨r, hr, -, hreg⟩ := D.rad.exists_pole hS hΘ
  have hrE : r' = r := pole_eq_of_mem_cuffDisc hS hr hΘ hreg hM'.pole hM'.pole_disc
  rw [hrE] at hM'
  have X := hM.setting hs hsΘ hΘ hr hreg
  have hn := hM.large
  obtain ⟨i, rfl⟩ := hM'.all₀ e he hes
  have hgi := hM'.map i
  have hbm := hM.edge.mem _ he
  have hbΘ : b (f i) ⊆ Θ := hgi ▸ (hM'.order.2.2.2.1 i).2.trans hsΘ
  rcases ht with ⟨e', he', hne, hes', rfl⟩ | ⟨hts, htΘ⟩
  · obtain ⟨j, rfl⟩ := hM'.all₀ e' he' hes'
    have hgj := hM'.map j
    have hbΘ' : b (f j) ⊆ Θ := hgj ▸ (hM'.order.2.2.2.1 j).2.trans hsΘ
    have hij : i ≠ j := fun h => hne (by rw [h])
    have h₁ := X.borderEdgeDist_le_of_common_end hS (by omega) hbm (hM.edge.mem _ he') hbΘ hbΘ' hy
      hyt
    rcases lt_or_gt_of_ne hij with h | h
    · have h₂ := hM'.far i j h
      rw [← hgi, ← hgj] at h₂
      omega
    · have h₂ := hM'.far j i h
      rw [← hgi, ← hgj] at h₂
      have h₃ := X.borderEdgeDist_le_of_common_end hS (by omega) (hM.edge.mem _ he') hbm hbΘ' hbΘ
        hyt hy
      omega
  · have h₁ := X.borderEdgeDist_le_of_common_end hS (by omega) hbm (D.P.fits.short_sides hts) hbΘ
      htΘ hy hyt
    have h₂ := hM'.far_short i t hts htΘ
    rw [← hgi] at h₂
    omega

/-- A border edge of `Γ₀`, and its image, lie on one side, and the side lies on one cuff. -/
theorem IsMatchSetting.exists_cuff_of_border (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E)
  (hB : Painting.IsBorder e) :
    ∃ s ∈ χ.Φ.sides, ∃ Θ ∈ cuffs S, s ⊆ Θ ∧ e ⊆ s ∧ b e ⊆ s ∧ (s ∉ χ.Φ.longSides → b e = s) := by
  obtain ⟨s, hs, hes, -, -⟩ := hM.edge.border he hB
  obtain ⟨Θ, hΘ, hsΘ, -⟩ := χ.Φ.side_on_cuff hS hs
  obtain ⟨s', hs', hs'Θ, hes', hbs', hsh⟩ := exists_side_of_cuffEnds hS hM.edge hΘ he
    (hes.trans hsΘ)
  exact ⟨s', hs', Θ, hΘ, hs'Θ, hes', hbs', hsh⟩

/-- The image of an internal edge has no end on a cuff. -/
theorem IsMatchSetting.not_mem_cuff_of_internal (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E)
  (hi : Painting.IsInternal e) {y : S} (hy : y ∈ tilde (b e)) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) : y ∉ Θ := by
  intro hyΘ
  obtain ⟨r, hr, -, hreg⟩ := D.rad.exists_pole hS hΘ
  have hrep : 4 ≤ D.rep := by
    have := hM.rep_gt
    have := hM.large
    omega
  have h₁ := edgeVertDist_pole_le hS hrep (hM.edge.mem e he) hy hΘ hyΘ hr hreg
  have h₂ := hM.edge.pole_far e he hi r hr
  have := hM.large
  omega

/-- **Common ends.** If `e ≠ e'`, then `β(e)` and `β(e')` have no common end, unless `e` and `e'`
are short sides. -/
theorem IsMatchSetting.no_common_end (hS : IsSurface S) {e e' : Set S} (he : e ∈ P₀.Γ.E)
  (he' : e' ∈ P₀.Γ.E) (hne : e ≠ e') {y : S} (hy : y ∈ tilde (b e)) (hy' : y ∈ tilde (b e')) :
    e ∈ χ.Φ.shortSides ∧ e' ∈ χ.Φ.shortSides := by
  classical
  have hn := hM.large
  have hrep : 4 ≤ D.rep := by
    have := hM.rep_gt
    omega
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  have hcl : ∀ {Θ}, Θ ∈ cuffs S → IsClosed Θ := fun hΘ => ((cuff_statement S hS).2.2 _
    hΘ).isCompact.isClosed
  by_cases hi : Painting.IsInternal e
  · by_cases hi' : Painting.IsInternal e'
    · have h₁ := edgeDist_le_of_common_end hrep (hM.edge.mem e he) (hM.edge.mem e' he') hy hy'
      have h₂ := hM.edge.far e he hi e' he' hi' hne
      omega
    · obtain ⟨s, -, Θ, hΘ, hsΘ, -, hbs, -⟩ := hM.exists_cuff_of_border hS he'
        (not_disjoint_iff_nonempty_inter.mp hi')
      exact absurd (closure_minimal (hbs.trans hsΘ) (hcl hΘ) hy'.1) (hM.not_mem_cuff_of_internal hS
        he hi hy hΘ)
  by_cases hi' : Painting.IsInternal e'
  · obtain ⟨s, -, Θ, hΘ, hsΘ, -, hbs, -⟩ := hM.exists_cuff_of_border hS he
      (not_disjoint_iff_nonempty_inter.mp hi)
    exact absurd (closure_minimal (hbs.trans hsΘ) (hcl hΘ) hy.1) (hM.not_mem_cuff_of_internal hS
      he' hi' hy' hΘ)
  obtain ⟨s, hs, Θ, hΘ, hsΘ, hes, hbs, hsh⟩ := hM.exists_cuff_of_border hS he
    (not_disjoint_iff_nonempty_inter.mp hi)
  obtain ⟨s', hs', Θ', hΘ', hsΘ', hes', hbs', hsh'⟩ := hM.exists_cuff_of_border hS he'
    (not_disjoint_iff_nonempty_inter.mp hi')
  obtain rfl : Θ' = Θ := cuffs_eq_of_mem hΘ' hΘ (closure_minimal (hbs'.trans hsΘ') (hcl hΘ') hy'.1)
    (closure_minimal (hbs.trans hsΘ) (hcl hΘ) hy.1)
  by_cases hl : s ∈ χ.Φ.longSides
  · by_cases hl' : s' ∈ χ.Φ.longSides
    · by_cases hss : s = s'
      · subst hss
        exact (hM.no_common_end_long hS he hl hsΘ hΘ hes (.inl ⟨e', he', hne.symm, hes',
          rfl⟩) hy.1 hy'.1).elim
      · exfalso
        have hyc : y ∈ closure s := closure_mono hbs hy.1
        have hyc' : y ∈ closure s' := closure_mono hbs' hy'.1
        have hyV := χ.Φ
        by_cases h₁ : y ∈ s
        · by_cases h₂ : y ∈ s'
          · exact hss (GM11.arcComponent_eq hs hs' h₁ h₂)
          · exact (hs.2.1 h₁).2 (χ.Φ.tilde_subset hbd hs' ⟨hyc', h₂⟩)
        · have ht : y ∈ tilde s := ⟨hyc, h₁⟩
          by_cases h₂ : y ∈ s'
          · exact (hs'.2.1 h₂).2 (χ.Φ.tilde_subset hbd hs ht)
          · exact disjoint_left.mp (χ.Φ.long_disjoint s hs s' hs' hss hl.2 hl'.2) ht ⟨hyc', h₂⟩
    · have hsl : s' ∈ χ.Φ.shortSides := ⟨hs', fun h => hl' ⟨hs', h⟩⟩
      exact (hM.no_common_end_long hS he hl hsΘ hΘ hes (.inr ⟨hsl,
        hsΘ'⟩) hy.1 (hsh' hl' ▸ hy'.1)).elim
  · have hsl : s ∈ χ.Φ.shortSides := ⟨hs, fun h => hl ⟨hs, h⟩⟩
    by_cases hl' : s' ∈ χ.Φ.longSides
    · exact (hM.no_common_end_long hS he' hl' hsΘ' hΘ hes' (.inr ⟨hsl,
        hsΘ⟩) hy'.1 (hsh hl ▸ hy.1)).elim
    · have hsl' : s' ∈ χ.Φ.shortSides := ⟨hs', fun h => hl' ⟨hs', h⟩⟩
      exact ⟨eq_short_of_subset P₀.fits he hsl hes ▸ hsl, eq_short_of_subset P₀.fits he' hsl' hes'
        ▸ hsl'⟩

omit hM in
/-- Each cuff has a short side. -/
theorem exists_short_on_cuff (hS : IsSurface S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) : ∃ s ∈
  χ.Φ.shortSides, s ⊆ Θ := by
  obtain ⟨p, hp, -⟩ := χ.Φ.two_on_cuff hS ⟨Θ, hΘ⟩
  obtain ⟨s, hs, hps⟩ := χ.Φ.exists_short_side hS hp.1
  obtain ⟨Θ', hΘ', hsΘ', -⟩ := χ.Φ.side_on_cuff hS hs.1
  have hcl : IsClosed Θ' := ((cuff_statement S hS).2.2 _ hΘ').isCompact.isClosed
  obtain rfl := cuffs_eq_of_mem hΘ' hΘ (closure_minimal hsΘ' hcl hps.1) hp.2
  exact ⟨s, hs, hsΘ'⟩

/-- The set `Z_v` of (3.2) of Graph Minors XII: the ends of the edges `β(e)` that correspond to `v`.
-/
def endClass (cap : IsCappedSurface S Shat) (P₀ P : ColouredPainting χ) (b : Set S → Set S)
  (v : S) : Set Shat :=
  cap.emb '' {y | ∃ e ∈ P₀.Γ.E, ∃ (i : ℕ) (hi : i < (P₀.Γ.γ e).length) (hi' : i < (P.Γ.γ
    (b e)).length), (P₀.Γ.γ e)[i] = v ∧ (P.Γ.γ (b e))[i] = y}

/-- Different vertices of `Γ₀` have disjoint sets of ends. -/
theorem IsMatchSetting.disjoint_endClass (hS : IsSurface S) {v v' : S} (hne : v ≠ v') : Disjoint
  (endClass cap P₀ D.P b v) (endClass cap P₀ D.P b v') := by
  have hinj := cap.isEmbedding.injective
  refine disjoint_left.mpr ?_
  rintro _ ⟨y, ⟨e, he, i, hi, hi', hv, hy⟩, rfl⟩ ⟨y', ⟨e', he', i', hi₂, hi₂', hv', hy'⟩, h⟩
  obtain rfl := hinj h
  have hmem := fun {c : Set S} (hc : c ∈ D.P.Γ.E) {j : ℕ} (hj : j < (D.P.Γ.γ c).length) => show
    (D.P.Γ.γ c)[j] ∈ tilde c by
    have : (D.P.Γ.γ c)[j] ∈ {v | v ∈ D.P.Γ.γ c} := List.getElem_mem hj
    rwa [D.P.Γ.γ_set c hc] at this
  by_cases hee : e = e'
  · subst hee
    have hii : i = i' := by
      have := (D.P.Γ.γ_nodup _ (hM.edge.mem e he)).getElem_inj_iff (hi := hi') (hj := hi₂') |>.mp
        (hy.trans hy'.symm)
      exact this
    subst hii
    exact hne (hv.symm.trans hv')
  obtain ⟨hs, hs'⟩ := hM.no_common_end hS he he' hee (hy ▸ hmem (hM.edge.mem e he) hi') (hy' ▸ hmem
    (hM.edge.mem e' he') hi₂')
  have e₁ : ∀ {s : Set S}, s ∈ χ.Φ.shortSides → P₀.Γ.γ s = D.P.Γ.γ s := fun h =>
    (short_γ_eq P₀ h).trans (short_γ_eq D.P h).symm
  have e₂ : ∀ {s : Set S}, s ∈ χ.Φ.shortSides → P₀.Γ.γ s = D.P.Γ.γ (b s) := by
    intro s h
    rw [hM.edge.short s h]
    exact e₁ h
  have g₁ : v = (D.P.Γ.γ (b e))[i] := hv.symm.trans (List.getElem_of_eq (e₂ hs) hi)
  have g₂ : v' = (D.P.Γ.γ (b e'))[i'] := hv'.symm.trans (List.getElem_of_eq (e₂ hs') hi₂)
  rw [hy] at g₁
  rw [hy'] at g₂
  exact hne (g₁.trans g₂.symm)

end TangleDatum

end GraphMinor.GM19
