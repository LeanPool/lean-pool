/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section11e

/-!
# Graph Minors XIX, Section 11: the data of a flaw on a side

A flaw `ℱ` on a side is turned into a feature `K`, the lines `L(F)` of the bites in `Σ`, a closed
disc `Z` around the cuff and all the bites, and the family of the discs `ins(F)`. This
is `TangleDatum.IsSideSetting.exists_side_data`, and `IsSideData` says what is obtained.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- What a flaw on `side` gives. -/
structure IsSideData (D : TangleDatum cap χ) (side : Set S) (N : ℕ) (ω : List β) (𝓓 : Set
  (Set Shat)) (Z : Set Shat) (K : Drawing S) : Prop where
  shape : IsSideShape cap χ.Φ side K Z
  finite : 𝓓.Finite
  discs : ∀ Δ ∈ 𝓓, IsClosedDisc Δ
  int_eq : cap.emb ⁻¹' discInt Z = ⋃ Δ ∈ 𝓓, cap.emb ⁻¹' discInt Δ
  family : IsLinkedFamily D N (discPairs cap 𝓓)
  card : 𝓓.ncard ≤ ω.length + 1
  feature : IsFeature χ.Φ K
  inter : D.P.Γ.U ∩ K.U ⊆ D.P.Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v
  size : K.V.ncard + K.E.ncard ≤ 8 * N
  pieces : ∃ 𝓞 𝓛 : Set (Set S), 𝓞.Finite ∧ 𝓛.Finite ∧ (∀ C ∈ 𝓞, IsOArc C) ∧
    (∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞) ∧ K.U
      = ⋃₀ 𝓞 ∪ ⋃₀ 𝓛
  roots : ∀ Δ ∈ 𝓓, ∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ closure Δᶜ → v ∈ K.U
  outer : ∀ v ∈ K.U, ∀ Δ ∈ 𝓓, cap.emb v ∈ closure Δᶜ
  anchored : IsAnchored D.P.Γ K
  omits : ∀ B ⊆ side \ (cap.emb ⁻¹' discInt Z ∪ K.U), IsPreconnected B → ∃ (h : ℕ)
    (hh : h < ω.length), ∀ e ∈ D.P.Γ.E, e ⊆ B → ¬ (χ.ΩS side).le ω[h] (D.P.φ e)

theorem ncard_biUnion_le_sum {ι T : Type*} (ℐ : Finset ι) (f : ι → Set T) (hf : ∀ i ∈ ℐ,
  (f i).Finite) : (⋃ i ∈ ℐ, f i).ncard ≤ ∑ i ∈ ℐ, (f i).ncard := by
  classical
  induction ℐ using Finset.induction_on with
  | empty => simp
  | insert a ℐ ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    have hfi : (⋃ i ∈ ℐ, f i).Finite := ℐ.finite_toSet.biUnion fun i hi ↦ hf i
      (Finset.mem_insert_of_mem hi)
    have := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have h₂ := ncard_union_le (f a) (⋃ i ∈ ℐ, f i)
    omega

namespace TangleDatum.IsSideSetting

variable {D : TangleDatum cap χ} {side Θ : Set S} {r : Shat} {N : ℕ} (X : D.IsSideSetting side Θ r
  N)
include X

omit X in
private theorem side_vertices_card_le_order
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {side : Set S}
    {r : Shat}
    {N : ℕ}
    {n : ℕ}
    {ω : List β}
    {ℱ : Set (Drawing Shat)}
    (hN : N = (ω.length + 1) * n)
    (hfl : D.IsSideLabelFlaw r side n ω ℱ)
    (hf : ℱ.Finite)
    (hG : ∀ {F : Drawing Shat}, F ∈ ℱ → F.IsCircuitOf D.rad.G)
    (U₀ : Set S)
    (hU : ∀ {x : S}, x ∈ U₀ ↔ ∃ F ∈ ℱ, cap.emb x ∈ F.U) :
    (U₀ ∩ D.P.Γ.V).ncard ≤ N := by
  have hsubV : U₀ ∩ D.P.Γ.V ⊆ ⋃ F ∈ hf.toFinset, cap.emb ⁻¹' F.U ∩ D.P.Γ.V := fun x hx ↦ by
    obtain ⟨F, hF, hxF⟩ := hU.1 hx.1
    exact mem_biUnion (hf.mem_toFinset.2 hF) ⟨hxF, hx.2⟩
  have hfin : ∀ F ∈ hf.toFinset, (cap.emb ⁻¹' F.U ∩ D.P.Γ.V).Finite := fun F _ ↦
    D.P.Γ.finite_V.subset inter_subset_right
  have h₁ := ncard_le_ncard hsubV (hf.toFinset.finite_toSet.biUnion hfin)
  have h₂ := ncard_biUnion_le_sum hf.toFinset (fun F ↦ cap.emb ⁻¹' F.U ∩ D.P.Γ.V) hfin
  have h₃ : ∑ F ∈ hf.toFinset, (cap.emb ⁻¹' F.U ∩ D.P.Γ.V).ncard ≤ ∑ F ∈ hf.toFinset, F.E.ncard / 2
    := Finset.sum_le_sum fun F hF ↦ by
    have := D.two_mul_ncard_le (hG (hf.mem_toFinset.1 hF)) (U₀ := cap.emb ⁻¹' F.U) fun x hx ↦ hx
    omega
  have h₄ : feastOrder ℱ = ∑ F ∈ hf.toFinset, F.E.ncard / 2 := dite_eq_left hf
  have h₅ := hfl.order_le
  omega

omit X in
private theorem side_shape_of_feast_discs
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [T2Space S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {side : Set S}
    {Θ : Set S}
    {r : Shat}
    {N : ℕ}
    (X : D.IsSideSetting side Θ r N)
    (hS : IsSurface S)
    (hgt : ↑(N + 2) < 2 * Painting.dist D.rad)
    {ω : List β}
    {ℱ : Set (Drawing Shat)}
    (hfe : D.IsDisjointFeast r side ω ℱ)
    (hf : ℱ.Finite)
    (hsm' : ∀ F ∈ ℱ, (Drawing.E F).ncard ≤ 2 * N)
    (v₁ : Drawing Shat → S)
    (v₂ : Drawing Shat → S)
    (Β : Drawing Shat → Set Shat)
    (L : Drawing Shat → Set Shat)
    (A : Drawing Shat → Set Shat)
    (A' : Drawing Shat → Set Shat)
    (Di : Drawing Shat → Set Shat)
    (Do : Drawing Shat → Set Shat)
    (hshape : ∀ F ∈ ℱ, D.IsBiteShape r Θ F (v₁ F) (v₂ F) (Β F) (L F) (A F) (A' F) (Di F) (Do F))
    (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf r = cap.cuffDisc Θ)
    (hi : ∀ {F : Drawing Shat}, F ∈ ℱ → IsClosedDisc (D.ins F) ∧ discBd (D.ins F) = F.U)
    (hrd : r ∈ cap.cuffDisc Θ)
    (hE : IsClosedDisc (closure (cap.cuffDisc Θ)))
    (hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ)
    (hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)))
    (hemb : ∀ (x : S), cap.emb x ∉ discInt (closure (cap.cuffDisc Θ)))
    (Z : Set Shat)
    (hZ : IsClosedDisc Z)
    (hEZ : closure (cap.cuffDisc Θ) ⊆ Z)
    (hZc : Z ⊆ closure (cap.cuffDisc Θ) ∪ ⋃ i ∈ hf.toFinset, D.ins i)
    (hJ3 : ∀ x ∉ discInt (closure (cap.cuffDisc Θ)), x ∈ discInt Z ↔ ∃ i ∈ hf.toFinset, x ∈
      discInt (D.ins i))
    (hJ1 : discBd Z ⊆ discBd (closure (cap.cuffDisc Θ)) ∪ ⋃ i ∈ hf.toFinset, discBd (D.ins i) \
      discInt (closure (cap.cuffDisc Θ)))
    (hJ2 : discBd (closure (cap.cuffDisc Θ)) \ ⋃ i ∈ hf.toFinset, D.ins i ⊆ discBd Z)
    (hJ4 : ∀ i ∈ hf.toFinset, discBd (D.ins i) \ (Β i \ {cap.emb (v₁ i), cap.emb (v₂ i)}) ⊆ discBd
      Z)
    (hv₁L : ∀ {F : Drawing Shat}, F ∈ ℱ → cap.emb (v₁ F) ∈ L F)
    (K : Drawing S) (hKU : K.U = ⋃₀ ((fun F => cap.emb ⁻¹' L F) '' ℱ))
    (hIn : cap.emb ⁻¹' ⋃ F ∈ ℱ, D.ins F ⊆ cap.emb ⁻¹' discInt Z ∪ K.U)
    (hKsub : ∀ {x : S}, x ∈ cap.emb ⁻¹' discInt Z ∪ K.U → ∃ F ∈ ℱ, cap.emb x ∈ D.ins F)
    (hmeets : ∀ F ∈ ℱ, (cap.emb ⁻¹' D.biteArc r F ∩ closure side).Nonempty)
    (hne : ℱ.Nonempty) :
    IsSideShape cap χ.Φ side K Z := by
  refine ⟨hZ, ?_, ?_, ⟨Θ, hΘ, hEZ, fun Θ' hΘ' hne' ↦ ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hKU] at hx
    obtain ⟨_, ⟨F, hF, rfl⟩, hxL⟩ := hx
    refine hJ4 F (hf.mem_toFinset.2 hF) ⟨(hi hF).2 ▸ (hshape F hF).F_eq ▸ Or.inr hxL,
      fun hc' ↦ hc'.2 ?_⟩
    rw [← (hshape F hF).Β_L]
    exact ⟨hc'.1, hxL⟩
  · intro x hx
    rcases hJ1 hx with h | h
    · exact Or.inl (mem_biUnion hΘ (Surface.discBd_subset _ h))
    · obtain ⟨F, hF, hxF, -⟩ := mem_iUnion₂.1 h
      have hF' := hf.mem_toFinset.1 hF
      rw [(hi hF').2, (hshape F hF').F_eq] at hxF
      rcases hxF with h' | h'
      · exact Or.inl (mem_biUnion hΘ ((hshape F hF').Β_E h'))
      · refine Or.inr ?_
        obtain ⟨y, hy⟩ := (hshape F hF').L_range h'
        refine ⟨y, ?_, hy⟩
        rw [hKU]
        refine ⟨_, ⟨F, hF', rfl⟩, ?_⟩
        change cap.emb y ∈ L F
        rwa [hy]
  · refine disjoint_left.2 fun x hx hxZ ↦ ?_
    rcases hZc hxZ with h | h
    · exact disjoint_left.1 (cap.cuffDisc_disjoint _ hΘ' _ hΘ hne') hx h
    · obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.1 h
      have hF' := hf.mem_toFinset.1 hF
      exact disjoint_left.1 (X.disjoint_cuff_ins hS hgt (hsm' F hF') (hshape F hF') hΘ' hne') hx hxF
  · obtain ⟨F, hF⟩ := hne
    rw [hKU]
    exact ⟨v₁ F, _, ⟨F, hF, rfl⟩, hv₁L hF⟩
  · intro s hs hne'
    obtain ⟨Θ', hΘ', hsΘ', -⟩ := Frame.side_on_cuff hS χ.Φ hs.1
    have hspc : IsPathConnected s := hs.1.2.2.1
    by_cases hsame : Θ' = Θ
    · subst hsame
      have hset : s \ (cap.emb ⁻¹' discInt Z ∪ K.U) = s \ ⋃ F ∈ hf.toFinset, cap.emb ⁻¹' D.biteArc
        r F := by
        ext x
        constructor
        · rintro ⟨h₁, h₂⟩
          refine ⟨h₁, fun h₃ ↦ h₂ (hIn ?_)⟩
          obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.1 h₃
          have hF' := hf.mem_toFinset.1 hF
          exact mem_biUnion hF' ((hshape F hF').biteArc_subset hS hxF).1
        · rintro ⟨h₁, h₂⟩
          refine ⟨h₁, fun h₃ ↦ h₂ ?_⟩
          obtain ⟨F, hF, hxF⟩ := hKsub h₃
          refine mem_biUnion (hf.mem_toFinset.2 hF) ?_
          change cap.emb x ∈ D.biteArc r F
          rw [hfe.arc_eq F hF, closure_region_sdiff hS hΘ' hreg]
          exact ⟨hxF, mem_image_of_mem _ (hsΘ' h₁)⟩
      rw [hset]
      have hdis : Disjoint (closure side) s := by
        refine disjoint_left.2 fun x hx hxs ↦ ?_
        have hnot : x ∉ side := fun hxd ↦ hne' (GM11.arcComponent_eq hs.1 X.long.1 hxs hxd)
        exact (hs.1.2.1 hxs).2 (χ.Φ.tilde_subset (cuff_statement S hS).1 X.long.1 ⟨hx, hnot⟩)
      refine X.keep_of_meets hS hsΘ' hspc hdis (fun F hF ↦ ?_) fun F hF ↦ hmeets F
        (hf.mem_toFinset.1 hF)
      have hF' := hf.mem_toFinset.1 hF
      refine ⟨A' F, (hshape F hF').isPreconnected_A', fun x hx ↦
        ⟨(hshape F hF').cuff_mem_A' hS hx, fun y hy ↦ ?_⟩⟩
      obtain ⟨z, hz, he⟩ := ((hshape F hF').A'_sub hy).1
      exact cap.isEmbedding.injective he ▸ hz
    · right
      have hset : s \ (cap.emb ⁻¹' discInt Z ∪ K.U) = s := by
        refine sdiff_eq_left.2 (disjoint_right.2 fun x hx hxs ↦ ?_)
        obtain ⟨F, hF, hxF⟩ := hKsub hx
        exact disjoint_left.1 (X.disjoint_cuff_ins hS hgt (hsm' F hF) (hshape F hF) hΘ' hsame)
          (cap.mem_closure_emb hS hΘ' (hsΘ' hxs)) hxF
      rw [hset]
      exact hspc

omit X in
private theorem disjoint_boundary_lines_of_feast
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {r : Shat}
    {ℱ : Set (Drawing Shat)}
    (L : Drawing Shat → Set Shat)
    (hsub : ∀ {F : Drawing Shat}, F ∈ ℱ → F.U ⊆ D.ins F)
    (hrnr : r ∉ range cap.emb)
    (hinter : ∀ {F F' : Drawing Shat}, F ∈ ℱ → F' ∈ ℱ → F ≠ F' → D.ins F ∩ D.ins F' = {r})
    (hLU : ∀ {F : Drawing Shat}, F ∈ ℱ → cap.emb ⁻¹' L F = cap.emb ⁻¹' F.U)
    {F : Drawing Shat}
    {F' : Drawing Shat}
    (hF : F ∈ ℱ)
    (hF' : F' ∈ ℱ)
    (hne : F ≠ F') :
    Disjoint (cap.emb ⁻¹' L F) (cap.emb ⁻¹' L F') := by
  refine disjoint_left.2 fun x hx hx' ↦ ?_
  rw [hLU hF] at hx
  rw [hLU hF'] at hx'
  have : cap.emb x ∈ D.ins F ∩ D.ins F' := ⟨hsub hF hx, hsub hF' hx'⟩
  rw [hinter hF hF' hne] at this
  exact hrnr (this ▸ mem_range_self x)

omit X in
private theorem feast_disc_family
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [T2Space S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {side : Set S}
    {Θ : Set S}
    {r : Shat}
    {N : ℕ}
    (X : D.IsSideSetting side Θ r N)
    (hS : IsSurface S)
    {n : ℕ}
    {ω : List β}
    {ℱ : Set (Drawing Shat)}
    (hN : N = (ω.length + 1) * n)
    (hpos : 1 ≤ N)
    (hfl : D.IsSideLabelFlaw r side n ω ℱ)
    (hsm : ∀ F ∈ ℱ, (Drawing.E F).ncard ≤ 2 * (N - 1))
    (hlink : ∀ F ∈ ℱ, GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F))
      (partIn cap D.P.Γ (closure (D.ins F)ᶜ)))
    (hmin : ∀ F ∈ ℱ, ¬D.IsFeast r side ω (ℱ \ {F}))
    (hT : IsClosedSurface Shat)
    (hfe : D.IsDisjointFeast r side ω ℱ)
    (hf : ℱ.Finite)
    (v₁ : Drawing Shat → S)
    (v₂ : Drawing Shat → S)
    (Β : Drawing Shat → Set Shat)
    (L : Drawing Shat → Set Shat)
    (A : Drawing Shat → Set Shat)
    (A' : Drawing Shat → Set Shat)
    (Di : Drawing Shat → Set Shat)
    (Do : Drawing Shat → Set Shat)
    (hshape : ∀ F ∈ ℱ, D.IsBiteShape r Θ F (v₁ F) (v₂ F) (Β F) (L F) (A F) (A' F) (Di F) (Do F))
    (hreg : D.rad.regionOf r = cap.cuffDisc Θ)
    (hG : ∀ {F : Drawing Shat}, F ∈ ℱ → F.IsCircuitOf D.rad.G)
    (hi : ∀ {F : Drawing Shat}, F ∈ ℱ → IsClosedDisc (D.ins F) ∧ discBd (D.ins F) = F.U)
    (hrnr : r ∉ range cap.emb)
    (hrd : r ∈ cap.cuffDisc Θ)
    (hinter : ∀ {F F' : Drawing Shat}, F ∈ ℱ → F' ∈ ℱ → F ≠ F' → D.ins F ∩ D.ins F' = {r})
    (hmeets : ∀ F ∈ ℱ, (cap.emb ⁻¹' D.biteArc r F ∩ closure side).Nonempty) :
    IsLinkedFamily D N (discPairs cap (D.ins '' ℱ)) := by
  refine family_of_discs (hf.image _) ?_ ?_ ?_
  · rintro _ ⟨F, hF, rfl⟩
    exact hlink F hF
  · rintro _ ⟨F, hF, rfl⟩
    have := disc_order hS X.h3 D.rad (hG hF) (hi hF).1 (hi hF).2
    have := hsm F hF
    omega
  · rintro _ ⟨F, hF, rfl⟩ _ ⟨F', hF', rfl⟩ hne'
    rw [closure_compl_eq_compl_discInt hT (hi hF').1]
    intro x hx hxi
    have hFF : F ≠ F' := fun he ↦ hne' (by rw [he])
    have hm : x ∈ D.ins F ∩ D.ins F' := ⟨hx, discInt_subset _ hxi⟩
    rw [hinter hF hF' hFF] at hm
    have hxr : x = r := hm
    subst hxr
    exact hxi.2 ((hi hF').2 ▸ F'.V_subset_U (hshape F' hF').r_mem)

/-- **The data of a flaw.** -/
theorem exists_side_data [ConnectedSpace S] (hS : IsSurface S)
    (hgt : ((N + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad) {n : ℕ} {ω : List β}
    {ℱ : Set (Drawing Shat)} (hN : N = (ω.length + 1) * n) (hpos : 1 ≤ N)
    (hfl : D.IsSideLabelFlaw r side n ω ℱ)
    (hsm : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * (N - 1))
    (hlink : ∀ F ∈ ℱ, GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F))
      (partIn cap D.P.Γ (closure (D.ins F)ᶜ)))
    (hmin : ∀ F ∈ ℱ, ¬ D.IsFeast r side ω (ℱ \ {F})) (hω : ω ≠ []) : ∃ 𝓓 Z K, IsSideData D side N ω
      𝓓 Z K := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hj := cap.isClosedEmbedding hS
  have hfe := hfl.toIsDisjointFeast
  have hf := hfe.finite_bites
  have hsm' : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * N := fun F hF ↦ (hsm F hF).trans (by omega)
  have hsh : ∀ F ∈ ℱ, ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do
    := fun F hF ↦ X.shape hS (hfe.all_bites F hF) (hsm' F hF)
  choose! v₁ v₂ Β L A A' Di Do hshape using hsh
  have hΘ := X.cuff
  have hreg := X.reg
  have hG : ∀ {F}, F ∈ ℱ → F.IsCircuitOf D.rad.G := fun {F} hF ↦ (hshape F hF).circuit
  have hlt : ∀ {F}, F ∈ ℱ → F.E.ncard < 2 * D.rep := fun {F} hF ↦ (hshape F hF).lt
  have hi : ∀ {F}, F ∈ ℱ → IsClosedDisc (D.ins F) ∧ discBd (D.ins F) = F.U := fun {F} hF ↦ by
    have := D.ins_spec (hG hF) (hlt hF)
    exact ⟨this.2.2.1, this.2.2.2.1⟩
  have hsub : ∀ {F}, F ∈ ℱ → F.U ⊆ D.ins F := fun {F} hF ↦ D.U_subset_ins (hG hF) (hlt hF)
  have hrnr := D.pole_notMem_range hS X.pole
  have hrd : r ∈ cap.cuffDisc Θ := by
    rw [← hreg]
    exact (D.rad.regionOf_mem X.pole.1).2
  have hE := cap.cuffDisc_closedDisc Θ hΘ
  have hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := cap.cuffDisc_eq_discInt hS hΘ
  have hemb : ∀ x, cap.emb x ∉ discInt (closure (cap.cuffDisc Θ)) := fun x h ↦ cap.notMem_range hΘ
    (hdE ▸ h) (mem_range_self x)
  have hinter : ∀ {F F'}, F ∈ ℱ → F' ∈ ℱ → F ≠ F' → D.ins F ∩ D.ins F' = {r}
    := fun hF hF' hne ↦ hfe.ins_inter _ hF _ hF' hne
  obtain ⟨Z, hZ, hEZ, hΔZ, hZc, -, hJ3, hJ1, hJ2, hJ4⟩ := exists_disc_union hT hE hf.toFinset D.ins
    Β (fun F ↦ cap.emb (v₁ F)) (fun F ↦ cap.emb (v₂ F))
    (fun F hF ↦ (hshape F (hf.mem_toFinset.1 hF)).isChordDisc hS (hfe.arc_eq F
      (hf.mem_toFinset.1 hF)))
    (fun F hF F' hF' hne ↦ by
      rw [hinter (hf.mem_toFinset.1 hF) (hf.mem_toFinset.1 hF') hne, singleton_subset_iff, ← hdE]
      exact hrd)
  have hiff : ∀ x, cap.emb x ∈ discInt Z ↔ ∃ F ∈ ℱ, cap.emb x ∈ discInt (D.ins F) := fun x ↦ by
    simpa using hJ3 _ (hemb x)
  -- the lines in `Σ`
  have hLr : ∀ {F}, F ∈ ℱ → cap.emb '' (cap.emb ⁻¹' L F) = L F := fun {F} hF ↦
    image_preimage_eq_of_subset (hshape F hF).L_range
  have hv₁L : ∀ {F}, F ∈ ℱ → cap.emb (v₁ F) ∈ L F := fun {F} hF ↦ ((hshape F hF).Β_L ▸ mem_insert _
    _ : cap.emb (v₁ F) ∈ Β F ∩ L F).2
  have hv₂L : ∀ {F}, F ∈ ℱ → cap.emb (v₂ F) ∈ L F := fun {F} hF ↦ ((hshape F hF).Β_L ▸
    mem_insert_of_mem _ rfl : cap.emb (v₂ F) ∈ Β F ∩ L F).2
  have hline : ∀ {F}, F ∈ ℱ → IsLineWithEnds (cap.emb ⁻¹' L F) (v₁ F) (v₂ F)
    := fun {F} hF ↦ isLine_comap hj (by rw [hLr hF]; exact (hshape F hF).L_line)
  have hLU : ∀ {F}, F ∈ ℱ → cap.emb ⁻¹' L F = cap.emb ⁻¹' F.U := fun {F} hF ↦
    ((hshape F hF).preimage_U hS).symm
  set 𝓛 : Set (Set S) := (fun F ↦ cap.emb ⁻¹' L F) '' ℱ with h𝓛
  have h𝓛f : 𝓛.Finite := hf.image _
  have hLdis : ∀ {F F'}, F ∈ ℱ → F' ∈ ℱ → F ≠ F' → Disjoint (cap.emb ⁻¹' L F) (cap.emb ⁻¹' L F')
    := fun {F F'} hF hF' hne ↦ by
    exact disjoint_boundary_lines_of_feast (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ)
      (D := D) (r := r) (ℱ := ℱ) L hsub hrnr hinter hLU (F := F) (F' := F') hF hF' hne
  obtain ⟨hc, hfa, hcard, hmk⟩ := finite_lines_union h𝓛f D.P.Γ.finite_V (by
      rintro _ ⟨F, hF, rfl⟩
      exact ⟨v₁ F, v₂ F, hline hF, (hshape F hF).v₁_mem, (hshape F hF).v₂_mem⟩) (by
      rintro _ ⟨F, hF, rfl⟩ _ ⟨F', hF', rfl⟩ hne
      exact hLdis hF hF' fun he ↦ hne (by rw [he]))
  set U₀ : Set S := ⋃₀ 𝓛 with hU₀
  have hU : ∀ {x}, x ∈ U₀ ↔ ∃ F ∈ ℱ, cap.emb x ∈ F.U := fun {x} ↦ by
    constructor
    · rintro ⟨_, ⟨F, hF, rfl⟩, hx⟩
      refine ⟨F, hF, ?_⟩
      have hx' : x ∈ cap.emb ⁻¹' L F := hx
      rw [hLU hF] at hx'
      exact hx'
    · rintro ⟨F, hF, hx⟩
      refine ⟨_, ⟨F, hF, rfl⟩, ?_⟩
      change x ∈ cap.emb ⁻¹' L F
      rw [hLU hF]
      exact hx
  set K := coarseDrawing D.P.Γ U₀ hc hfa hmk with hK
  have hKimg : ∀ {x}, x ∈ K.U → ∃ F ∈ ℱ, cap.emb x ∈ F.U := fun hx ↦ hU.1 hx
  have hIn : cap.emb ⁻¹' ⋃ F ∈ ℱ, D.ins F ⊆ cap.emb ⁻¹' discInt Z ∪ K.U := fun x hx ↦ by
    obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.1 hx
    by_cases hb' : cap.emb x ∈ discBd (D.ins F)
    · refine Or.inr (hU.2 ⟨F, hF, ?_⟩)
      rw [← (hi hF).2]
      exact hb'
    · exact Or.inl ((hiff x).2 ⟨F, hF, hxF, hb'⟩)
  have hKsub : ∀ {x}, x ∈ cap.emb ⁻¹' discInt Z ∪ K.U → ∃ F ∈ ℱ, cap.emb x ∈ D.ins F := by
    rintro x (h | h)
    · obtain ⟨F, hF, hx⟩ := (hiff x).1 h
      exact ⟨F, hF, discInt_subset _ hx⟩
    · obtain ⟨F, hF, hx⟩ := hKimg h
      exact ⟨F, hF, hsub hF hx⟩
  have hinterK : D.P.Γ.U ∩ U₀ ⊆ D.P.Γ.V ∩ (U₀ ∩ D.P.Γ.V) := by
    rintro x ⟨hxΓ, hxK⟩
    obtain ⟨F, hF, hxF⟩ := hU.1 hxK
    have hm' : cap.emb x ∈ D.P.Γ.hatU cap ∩ D.rad.G.U := ⟨mem_image_of_mem _ hxΓ,
      (hG hF).1.U_subset hxF⟩
    rw [D.rad.isPreRadial.1] at hm'
    obtain ⟨v, hv, hvx⟩ := hm'
    obtain rfl := cap.isEmbedding.injective hvx
    exact ⟨hv, hxK, hv⟩
  have hbdN : ∀ {x}, x ∈ U₀ → x ∈ bd S → x ∈ U₀ ∩ D.P.Γ.V := fun hx hb ↦
    (hinterK ⟨D.P.Γ.bd_subset hb, hx⟩).2
  have hdense : U₀ ⊆ closure (U₀ \ (U₀ ∩ D.P.Γ.V)) := by
    rintro x ⟨_, ⟨F, hF, rfl⟩, hx⟩
    have hNf : (U₀ ∩ D.P.Γ.V).Finite := D.P.Γ.finite_V.subset inter_subset_right
    refine closure_mono ?_ (line_subset_closure_sdiff (hline hF) hNf hx)
    exact sdiff_subset_sdiff_left (subset_sUnion_of_mem ⟨F, hF, rfl⟩)
  have hcov : U₀ \ (U₀ ∩ D.P.Γ.V) ⊆ ⋃ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V)), e := fun x hx ↦ by
    obtain ⟨c, hc', hxc⟩ := exists_arcComp_superset (isPathConnected_singleton x)
      (singleton_subset_iff.2 hx)
    exact mem_biUnion hc' (hxc rfl)
  have hVle : (U₀ ∩ D.P.Γ.V).ncard ≤ N := by
    exact side_vertices_card_le_order (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ) (D :=
      D) (side := side) (r := r) (N := N) (n := n) (ω := ω) (ℱ := ℱ) hN hfl hf hG U₀ hU
  have hmeets := fun F hF ↦ X.biteArc_meets_side hS hfe (fun G hG' ↦ hsm' G hG') hmin (F := F) hF
  have hne : ℱ.Nonempty := by
    obtain ⟨s, hs, hto⟩ := exists_short_touching hS χ D.P.fits X.long
    obtain ⟨x, hx⟩ : s.Nonempty := hs.1.1
    obtain ⟨F, hF, -⟩ := mem_iUnion₂.1 (hfe.includes_short_sides s hs hto (mem_image_of_mem _ hx))
    exact ⟨F, hF⟩
  have hshapeZ : IsSideShape cap χ.Φ side K Z := by
    exact side_shape_of_feast_discs (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ) (D :=
      D) (side := side) (Θ := Θ) (r := r) (N := N) X hS hgt (ω := ω) (ℱ := ℱ) hfe hf hsm' v₁ v₂ Β
      L A A' Di Do hshape hΘ hreg hi hrd hE hEb hdE hemb Z hZ hEZ hZc hJ3 hJ1 hJ2 hJ4 hv₁L K rfl hIn
      hKsub hmeets hne
  refine ⟨D.ins '' ℱ, Z, K, hshapeZ, hf.image _, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, hinterK,
    fun e he ↦ hmk e he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact (hi hF).1
  · ext x
    simp only [mem_preimage, hiff, mem_iUnion₂, mem_image, exists_prop, exists_exists_and_eq_and]
  · exact feast_disc_family (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ) (D := D) (side
      := side) (Θ := Θ) (r := r) (N := N) X hS (n := n) (ω := ω) (ℱ := ℱ) hN hpos hfl hsm hlink
      hmin hT hfe hf v₁ v₂ Β L A A' Di Do hshape hreg hG hi hrnr hrd hinter hmeets
  · exact (ncard_image_le hf).trans hfe.card_le
  · exact fun e he ↦ disjoint_left.2 fun x hxe hxb ↦ (he.2.1 hxe).2 (hbdN (he.2.1 hxe).1 hxb)
  · intro v hv
    have hvc := hdense hv.1
    have : v ∈ closure (⋃ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V)), e) := closure_mono hcov hvc
    rw [hfa.closure_biUnion] at this
    obtain ⟨e, he, hve⟩ := mem_iUnion₂.1 this
    exact ⟨e, he, hve, fun h ↦ (he.2.1 h).2 hv⟩
  · refine fun s₀ hs₀ ↦ disjoint_left.2 fun x hx hxs ↦ ?_
    have hxb : x ∈ bd S := (hs₀.1.2.1 hxs).1
    exact D.P.Γ.disjoint_V (D.P.fits.short_sides hs₀) hxs (hbdN hx hxb).2
  · change (U₀ ∩ D.P.Γ.V).ncard + (arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V))).ncard ≤ 8 * N
    omega
  · refine ⟨∅, 𝓛, finite_empty, h𝓛f, by simp, ?_, by rw [sUnion_empty, empty_union]; rfl⟩
    rintro _ ⟨F, hF, rfl⟩
    have hs := hshape F hF
    exact ⟨v₁ F, v₂ F, hs.ne, hline hF, Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hs.v₁_cuff),
      Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hs.v₂_cuff)⟩
  · rintro _ ⟨F, hF, rfl⟩ v _ h₁ h₂
    have : cap.emb v ∈ frontier (D.ins F) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure h₁, h₂⟩
    rw [IsClosedDisc.frontier_eq_discBd hT (hi hF).1, (hi hF).2] at this
    exact hU.2 ⟨F, hF, this⟩
  · rintro v hv _ ⟨F', hF', rfl⟩
    rw [closure_compl_eq_compl_discInt hT (hi hF').1]
    intro hvi
    obtain ⟨F, hF, hxF⟩ := hKimg hv
    by_cases he : F = F'
    · subst he
      exact hvi.2 ((hi hF).2 ▸ hxF)
    · have hm : cap.emb v ∈ D.ins F ∩ D.ins F' := ⟨hsub hF hxF, discInt_subset _ hvi⟩
      rw [hinter hF hF' he] at hm
      exact hrnr ((hm : cap.emb v = r) ▸ mem_range_self v)
  · intro w' x hx hne'
    obtain ⟨_, ⟨F, hF, rfl⟩, hxL⟩ := hx
    have hs := hshape F hF
    have hsubL : cap.emb ⁻¹' L F ⊆ U₀ := subset_sUnion_of_mem ⟨F, hF, rfl⟩
    refine line_anchor (hline hF) hsubL (fun w'' h ↦ ?_) (fun w'' h ↦ ?_) hxL hne'
    · refine ⟨{v₁ F}, ?_, rfl, isPreconnected_singleton, ⟨v₁ F, rfl, hs.v₁_mem⟩⟩
      rintro _ rfl
      exact ⟨hsubL (hv₁L hF), h⟩
    · refine ⟨{v₂ F}, ?_, rfl, isPreconnected_singleton, ⟨v₂ F, rfl, hs.v₂_mem⟩⟩
      rintro _ rfl
      exact ⟨hsubL (hv₂L hF), h⟩
  · intro B hB hconn
    by_cases hBe : B.Nonempty
    · obtain ⟨x, hx⟩ := hBe
      have hoff : ∀ {y}, y ∈ B → y ∈ side \ cap.emb ⁻¹' D.feastArcUnion r ℱ := fun {y} hy ↦ by
        refine ⟨(hB hy).1, fun h ↦ (hB hy).2 (hIn ?_)⟩
        obtain ⟨F, hF, hyF⟩ := mem_iUnion₂.1 h
        exact mem_biUnion hF ((hshape F hF).biteArc_subset hS hyF).1
      obtain ⟨h, hh, hall⟩ := hfe.component_omits _ (mem_image_of_mem _ (hoff hx))
      exact ⟨h, hh, fun e he hsub' ↦ hall e he (hsub'.trans (hconn.subset_connectedComponentIn hx
        fun y hy ↦ hoff hy))⟩
    · rw [not_nonempty_iff_eq_empty] at hBe
      refine ⟨0, List.length_pos_iff.2 hω, fun e he hsub' ↦ ?_⟩
      obtain ⟨y, hy⟩ := he.1
      have := hsub' hy
      rw [hBe] at this
      exact absurd this (notMem_empty _)

end TangleDatum.IsSideSetting

end GraphMinor.GM19
