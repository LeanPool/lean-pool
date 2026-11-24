/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15n

/-!
# Graph Minors XIX, (15.2): the family of discs

We now put together the discs of `exists_cuff_disc`, `exists_two_disc` and `exists_three_disc`: one
disc for each cuff and one for each internal edge of `Γ₀`. The closed sets in which they lie are
disjoint, because the edges `β(e)` are far from each other and
from the poles (`disjoint_discHull`). So we can take thin discs around the edges of size 2 and keep
them disjoint (`exists_discFamily`).

The metric of `sk(Γ)` sees these discs as far apart (`le_skMetric`), and the sets of ends are free
(`isFreeSet_of_circuit`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

/-- Disjoint compact sets lie in disjoint open sets. -/
theorem exists_open_separation {ι T : Type} [TopologicalSpace T] [T2Space T] [Finite ι] {K : ι
  → Set T} (hK : ∀ i, IsCompact (K i)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) :
    ∃ U : ι → Set T, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧ ∀ i j, i ≠ j → Disjoint (U i) (U j)
      := by
  have hsep : ∀ i j, i ≠ j → ∃ u v : Set T, IsOpen u ∧ IsOpen v ∧ K i ⊆ u ∧ K j ⊆ v ∧ Disjoint u v
    := fun i j h => by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩ := SeparatedNhds.of_isCompact_isCompact (hK i) (hK j)
      (hd i j h)
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩
  choose u v h₁ h₂ h₃ h₄ h₅ using hsep
  refine ⟨fun i => ⋂ (j : ι), ⋂ (h : i ≠ j), u i j h ∩ v j i h.symm, fun i => ?_, fun i => ?_,
    fun i j h => ?_⟩
  · exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun h => (h₁ _ _ h).inter
      (h₂ _ _ h.symm)
  · exact subset_iInter fun j => subset_iInter fun h => subset_inter (h₃ _ _ h) (h₄ _ _ h.symm)
  · refine (h₅ i j h).mono ?_ ?_
    · exact fun x hx => (mem_iInter.mp (mem_iInter.mp hx j) h).1
    · exact fun x hx => (mem_iInter.mp (mem_iInter.mp hx i) h.symm).2

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

omit [T2Space Shat] in
omit [T2Space S] in
/-- The boundary of an anchored disc holds just the vertices `N`. -/
theorem IsAnchoredDisc.vertex_inter_subBd {Γ : Painting S} {H : Drawing Shat} {Δ N : Set Shat} {a :
  Set S} (h : IsAnchoredDisc cap Γ H Δ N a) : H.V ∩ subBd Δ = N := by
  have hT := cap.isClosedSurface
  have e : subBd Δ = discBd Δ := by
    rw [subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hT h.disc]
  rw [e]
  apply Subset.antisymm
  · rintro x ⟨hxV, hxb⟩
    rw [← h.inter]
    exact ⟨H.V_subset_U hxV, Surface.discBd_subset _ hxb⟩
  · exact fun x hx => ⟨h.sub_V hx, h.sub_bd hx⟩

omit [T2Space S] [T2Space Shat] in
/-- Some region of `sk(Γ)` meets an anchored disc. -/
theorem IsAnchoredDisc.exists_region {Γ : Painting S} {H : Drawing Shat} {Δ N : Set Shat} {a : Set
  S} (h : IsAnchoredDisc cap Γ H Δ N a) : ∃ r ∈ H.R, (r ∩ Δ).Nonempty := by
  obtain ⟨p, hp⟩ := h.disc.nonempty_discInt
  have hpU : p ∉ H.U := fun hU => hp.2 (h.sub_bd (h.inter ▸ ⟨hU, hp.1⟩))
  obtain ⟨r, hr, hpr⟩ := exists_region_of_notMem hpU
  exact ⟨r, hr, p, hpr, hp.1⟩

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- The cuffs, and the internal edges of `Γ₀`. These index the discs. -/
abbrev DiscIndex (S : Type) [TopologicalSpace S] {β : Type w} {χ : ColourScheme S β}
  (P₀ : ColouredPainting χ) : Type :=
  {Θ : Set S // Θ ∈ cuffs S} ⊕ {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}

omit [T2Space S] in
theorem finite_discIndex (hS : IsSurface S) (P₀ : ColouredPainting χ) : Finite (DiscIndex S P₀)
  := by
  have h₁ : Finite {Θ : Set S // Θ ∈ cuffs S} := (cuff_statement S hS).2.1
  have h₂ : {e : Set S | e ∈ P₀.Γ.E ∧ Painting.IsInternal e}.Finite :=
    P₀.Γ.finite_edges.subset fun _ h => h.1
  have := h₂.to_subtype
  infer_instance

/-- The closed set in which a disc lies, up to a thin neighbourhood. -/
def discHull (cap : IsCappedSurface S Shat) (b : Set S → Set S) : DiscIndex S P₀ → Set Shat
  | .inl Θ => closure (cap.cuffDisc Θ.1)
  | .inr e => cap.emb '' closure (b e.1)

/-- The vertices of `sk(Γ)` on a disc. -/
def discEnds (cap : IsCappedSurface S Shat) (b : Set S → Set S) (P₀ : ColouredPainting χ) :
  DiscIndex S P₀ → Set Shat
  | .inl Θ => cap.emb '' cuffEnds P₀ b Θ.1
  | .inr e => cap.emb '' tilde (b e.1)

/-- The edge of `Γ` on the boundary of each region that meets a disc. -/
def discAnchor (σ b : Set S → Set S) : DiscIndex S P₀ → Set S
  | .inl Θ => σ Θ.1
  | .inr e => b e.1

variable (hM : D.IsMatchSetting P₀ n b)
include hM

/-- **The closed sets are disjoint.** -/
theorem IsMatchSetting.disjoint_discHull (hS : IsSurface S) (i j : DiscIndex S P₀)
  (hne : i ≠ j) : Disjoint (discHull cap b i) (discHull cap b j) := by
  have hinj := cap.isEmbedding.injective
  have key : ∀ (Θ : {Θ : Set S // Θ ∈ cuffs S}) (e : {e : Set S // e ∈ P₀.Γ.E
    ∧ Painting.IsInternal e}), Disjoint (closure (cap.cuffDisc Θ.1)) (cap.emb '' closure (b e.1))
      := fun Θ e => by
    refine disjoint_left.mpr ?_
    rintro x hx ⟨z, hz, rfl⟩
    rw [cap.closure_cuffDisc hS Θ.2] at hx
    rcases hx with h | ⟨y, hy, hyz⟩
    · exact cap.notMem_range Θ.2 h (mem_range_self z)
    · obtain rfl := hinj hyz
      have hint := hM.edge.internal e.1 e.2.1 e.2.2
      have hnz : y ∉ b e.1 := fun h' => disjoint_left.mp hint h' (cuff_subset_bd ⟨Θ.1, Θ.2⟩ hy)
      exact hM.not_mem_cuff_of_internal hS e.2.1 e.2.2 ⟨hz, hnz⟩ Θ.2 hy
  rcases i with Θ | e <;> rcases j with Θ' | e'
  · exact cap.cuffDisc_disjoint Θ.1 Θ.2 Θ'.1 Θ'.2 fun h => hne (congrArg Sum.inl (Subtype.ext h))
  · exact key Θ e'
  · exact (key Θ' e).symm
  · have hee : e.1 ≠ e'.1 := fun h => hne (congrArg Sum.inr (Subtype.ext h))
    change Disjoint (cap.emb '' closure (b e.1)) (cap.emb '' closure (b e'.1))
    refine (disjoint_image_iff hinj).mpr (disjoint_left.mpr fun z hz hz' => ?_)
    have hbm := hM.edge.mem _ e.2.1
    have hbm' := hM.edge.mem _ e'.2.1
    have hbne : b e.1 ≠ b e'.1 := fun h => hee (hM.edge.injOn e.2.1 e'.2.1 h)
    by_cases h₁ : z ∈ b e.1
    · by_cases h₂ : z ∈ b e'.1
      · exact hbne (GM11.arcComponent_eq hbm hbm' h₁ h₂)
      · exact D.P.Γ.disjoint_V hbm h₁ (D.P.Γ.tilde_subset_V hbm' ⟨hz', h₂⟩)
    · by_cases h₂ : z ∈ b e'.1
      · exact D.P.Γ.disjoint_V hbm' h₂ (D.P.Γ.tilde_subset_V hbm ⟨hz, h₁⟩)
      · have h := (hM.no_common_end hS e.2.1 e'.2.1 hee ⟨hz, h₁⟩ ⟨hz', h₂⟩).1
        obtain ⟨x, hx⟩ : e.1.Nonempty := e.2.1.1
        exact disjoint_left.mp e.2.2 hx (h.1.2.1 (by exact hx) |>.1)

/-- The ends of the edges on a cuff are vertices of `Γ` on the cuff. -/
theorem IsMatchSetting.cuffEnds_subset (hS : IsSurface S) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) : cuffEnds P₀ b Θ ⊆ Θ ∩ D.P.Γ.V := by
  rintro y ⟨e, he, heΘ, hy⟩
  obtain ⟨s, -, -, -, hbs, -⟩ := exists_side_of_cuffEnds hS hM.edge hΘ he heΘ
  obtain ⟨s', -, hs'Θ, -, hbs', -⟩ := exists_side_of_cuffEnds hS hM.edge hΘ he heΘ
  have hcl : IsClosed Θ := ((cuff_statement S hS).2.2 _ hΘ).isCompact.isClosed
  exact ⟨closure_minimal (hbs'.trans hs'Θ) hcl hy.1, D.P.Γ.tilde_subset_V (hM.edge.mem e he) hy⟩

omit [T2Space S] in
theorem IsMatchSetting.finite_cuffEnds (Θ : Set S) : (cuffEnds P₀ b Θ).Finite := by
  refine (P₀.Γ.finite_edges.biUnion (t := fun e => tilde (b e)) fun e he => D.P.Γ.finite_V.subset
    (D.P.Γ.tilde_subset_V (hM.edge.mem e he))).subset ?_
  rintro y ⟨e, he, -, hy⟩
  exact mem_biUnion he hy

/-- **The discs.** -/
theorem IsMatchSetting.exists_discFamily (hS : IsSurface S) {H : Drawing Shat}
  (hH : IsSkHat cap D.P.Γ H) {σ : Set S → Set S} (hσ : ∀ Θ ∈ cuffs S, σ Θ ∈ χ.Φ.shortSides
    ∧ σ Θ ⊆ Θ) :
    ∃ Δ : DiscIndex S P₀ → Set Shat, (∀ i, IsAnchoredDisc cap D.P.Γ H (Δ i) (discEnds cap b P₀ i)
      (discAnchor σ b i)) ∧ (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
      (∀ Θ : {Θ : Set S // Θ ∈ cuffs S}, Δ (.inl Θ) ⊆ closure (cap.cuffDisc Θ.1)) ∧
      ∀ e : {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}, (tilde (b e.1)).ncard = 3 → Δ
        (.inr e) ⊆ cap.emb '' closure (b e.1) := by
  classical
  have := finite_discIndex hS P₀
  have hK : ∀ i : DiscIndex S P₀, IsCompact (discHull cap b i) := by
    rintro (Θ | e)
    · exact (cap.cuffDisc_closedDisc Θ.1 Θ.2).isCompact
    · have : CompactSpace S := hS.1
      exact (isClosed_closure.isCompact).image cap.isEmbedding.continuous
  obtain ⟨U, hUo, hKU, hUd⟩ := exists_open_separation hK fun i j h => hM.disjoint_discHull hS i j h
  have key : ∀ i : DiscIndex S P₀, ∃ Δ, Δ ⊆ U i ∧ (∀ Θ, i = .inl Θ → Δ ⊆ closure
    (cap.cuffDisc Θ.1)) ∧ (∀ e, i = .inr e → (tilde (b e.1)).ncard = 3 → Δ ⊆ cap.emb '' closure
      (b e.1)) ∧ IsAnchoredDisc cap D.P.Γ H Δ (discEnds cap b P₀ i) (discAnchor σ b i) := by
    rintro (Θ | e)
    · have hs := hσ Θ.1 Θ.2
      have hs₀ := P₀.fits.short_sides hs.1
      have hne : (cuffEnds P₀ b Θ.1).Nonempty := by
        obtain ⟨y, hy⟩ : (tilde (σ Θ.1)).Nonempty := nonempty_of_ncard_ne_zero (by
          rw [(χ.Φ.side_shape _ hs.1.1).1]
          omega)
        exact ⟨y, σ Θ.1, hs₀, hs.2, by rw [hM.edge.short _ hs.1]; exact hy⟩
      obtain ⟨Δ, h₁, h₂⟩ := exists_cuff_disc hS hH Θ.2 (hM.cuffEnds_subset hS Θ.2)
        (hM.finite_cuffEnds Θ.1) hne (D.P.fits.short_sides hs.1) hs.2
      exact ⟨Δ, h₁.trans (hKU (.inl Θ)), fun Θ' h => (Sum.inl_injective h : Θ = Θ') ▸ h₁,
        fun _ h => (by cases h), h₂⟩
    · have hbm := hM.edge.mem _ e.2.1
      rcases D.P.Γ.size_cases hbm with h2 | h3
      · obtain ⟨Δ, h₁, h₂⟩ := exists_two_disc hS hH hbm h2 (hUo (.inr e)) (hKU (.inr e))
        exact ⟨Δ, h₁, fun _ h => (by cases h), fun e' h h₃ => by
          obtain rfl : e = e' := Sum.inr_injective h
          omega, h₂⟩
      · obtain ⟨Δ, h₁, h₂⟩ := exists_three_disc hH hbm h3
        exact ⟨Δ, h₁.trans (hKU (.inr e)), fun _ h => (by cases h), fun e' h _ => by
          obtain rfl : e = e' := Sum.inr_injective h
          exact h₁, h₂⟩
  choose Δ h₁ h₂ h₄ h₃ using key
  exact ⟨Δ, h₃, fun i j h => (hUd i j h).mono (h₁ i) (h₁ j), fun Θ => h₂ _ Θ rfl,
    fun e => h₄ _ e rfl⟩

/-- **The discs are far apart in `Γ`.** -/
theorem IsMatchSetting.lt_dist_discAnchor (hS : IsSurface S) {σ : Set S → Set S}
  (hσ : ∀ Θ ∈ cuffs S, σ Θ ∈ χ.Φ.shortSides ∧ σ Θ ⊆ Θ) (i j : DiscIndex S P₀) (hne : i ≠ j) :
    n / 2 < D.dist (cap.emb '' discAnchor σ b i) (cap.emb '' discAnchor σ b j) + 8 := by
  classical
  have hn := hM.large
  have hrep : 4 ≤ D.rep := by
    have := hM.rep_gt
    omega
  have hpole : ∀ Θ : {Θ : Set S // Θ ∈ cuffs S}, ∃ p ∈ D.rad.poles, D.rad.regionOf p
    = cap.cuffDisc Θ.1 ∧ p ∈ cap.cuffDisc Θ.1 ∧ D.dist (cap.emb '' σ Θ.1) (D.rad.atomOf p) ≤ 4
      := fun Θ => by
    obtain ⟨p, hp, hpΘ, hreg⟩ := D.rad.exists_pole hS Θ.2
    have hs := hσ Θ.1 Θ.2
    have hE := D.P.fits.short_sides hs.1
    obtain ⟨y, hy⟩ : (tilde (σ Θ.1)).Nonempty := nonempty_of_ncard_ne_zero (by
      rw [(χ.Φ.side_shape _ hs.1.1).1]
      omega)
    have hcl : IsClosed Θ.1 := ((cuff_statement S hS).2.2 _ Θ.2).isCompact.isClosed
    have := edgeVertDist_pole_le hS hrep hE hy Θ.2 (closure_minimal hs.2 hcl hy.1) hp hreg
    exact ⟨p, hp, hreg, hpΘ, this⟩
  have hatom : ∀ Θ : {Θ : Set S // Θ ∈ cuffs S}, cap.emb '' σ Θ.1 ∈ D.P.Γ.atoms cap := fun Θ
    => Or.inl (Or.inr ⟨_, D.P.fits.short_sides (hσ Θ.1 Θ.2).1, rfl⟩)
  rcases i with Θ | e <;> rcases j with Θ' | e'
  · obtain ⟨p, hp, -, hpΘ, h₁⟩ := hpole Θ
    obtain ⟨p', hp', -, hpΘ', h₂⟩ := hpole Θ'
    have hΘ : Θ.1 ≠ Θ'.1 := fun h => hne (congrArg Sum.inl (Subtype.ext h))
    have hpp : p ≠ p' := fun h => disjoint_left.mp (cap.cuffDisc_disjoint _ Θ.2 _ Θ'.2 hΘ)
      (subset_closure hpΘ) (subset_closure (h ▸ hpΘ'))
    have h₃ := hM.far p hp p' hp' hpp
    have h₄ := D.dist_triangle hrep (a := D.rad.atomOf p) (c := D.rad.atomOf p') (b
      := cap.emb '' σ Θ.1) (hatom Θ)
    have h₅ := D.dist_triangle hrep (a := cap.emb '' σ Θ.1) (c := D.rad.atomOf p') (b
      := cap.emb '' σ Θ'.1) (hatom Θ')
    rw [D.dist_comm (D.rad.atomOf p) (cap.emb '' σ Θ.1)] at h₄
    unfold vDist at h₃
    change n / 2 < D.dist (cap.emb '' σ Θ.1) (cap.emb '' σ Θ'.1) + 8
    omega
  · obtain ⟨p, hp, -, -, h₁⟩ := hpole Θ
    have h₂ := hM.edge.pole_far e'.1 e'.2.1 e'.2.2 p hp
    have h₃ := D.dist_triangle hrep (a := cap.emb '' b e'.1) (c := D.rad.atomOf p) (b
      := cap.emb '' σ Θ.1) (hatom Θ)
    unfold edgeVertDist at h₂
    rw [D.dist_comm (cap.emb '' b e'.1) (cap.emb '' σ Θ.1)] at h₃
    change n / 2 < D.dist (cap.emb '' σ Θ.1) (cap.emb '' b e'.1) + 8
    omega
  · obtain ⟨p, hp, -, -, h₁⟩ := hpole Θ'
    have h₂ := hM.edge.pole_far e.1 e.2.1 e.2.2 p hp
    have h₃ := D.dist_triangle hrep (a := cap.emb '' b e.1) (c := D.rad.atomOf p) (b
      := cap.emb '' σ Θ'.1) (hatom Θ')
    unfold edgeVertDist at h₂
    change n / 2 < D.dist (cap.emb '' b e.1) (cap.emb '' σ Θ'.1) + 8
    omega
  · have hee : e.1 ≠ e'.1 := fun h => hne (congrArg Sum.inr (Subtype.ext h))
    have := hM.edge.far e.1 e.2.1 e.2.2 e'.1 e'.2.1 e'.2.2 hee
    unfold edgeDist at this
    change n / 2 < D.dist (cap.emb '' b e.1) (cap.emb '' b e'.1) + 8
    omega

end TangleDatum

end GraphMinor.GM19
