/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeFlaw

/-!
# The data of a freedom flaw

From a flaw circuit `F` we make the drawing `K` of `F ∩ Σ`, with the vertices of `Γ` as its only
vertices, and the closed disc `Z`.
`K` has at most `½|E(F)|` vertices, and this is what the count of `fragScheme_isRefinement` needs.
If `F` misses the poles then `Z` is
`ins(F)`. If `F` runs through the pole of a cuff disc `E`, then `Z` is `ins(F)` with the half of `E`
outside `ins(F)` added
(`exists_outer_half`). The result used later is `exists_free_data`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- The drawing on `U₀` whose vertices are the vertices of `Γ` on `U₀`. -/
def coarseDrawing (Γ : Painting S) (U₀ : Set S) (hc : IsClosed U₀) (hfe : (arcComponentsIn (U₀ \
  (U₀ ∩ Γ.V))).Finite)
    (hm : ∀ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ Γ.V)), IsMarkedArc (U₀ ∩ Γ.V) e) : Drawing S where
  U := U₀
  V := U₀ ∩ Γ.V
  V_subset_U := inter_subset_left
  isClosed_U := hc
  finite_V := Γ.finite_V.subset inter_subset_right
  finite_edges := hfe
  edge_cond := fun e he ↦ Or.inl (hm e he)

namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] [T2Space Shat] in
/-- `F ∩ Σ` holds at most `½|E(F)|` vertices of `Γ`. -/
theorem two_mul_ncard_le (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
  {U₀ : Set S} (hU : ∀ x ∈ U₀, cap.emb x ∈ F.U) :
    2 * (U₀ ∩ D.P.Γ.V).ncard ≤ F.E.ncard := by
  have : ConnectedSpace Shat := cap.connected
  rw [D.ncard_E_eq_hat hF, ← ncard_image_of_injective _ cap.isEmbedding.injective]
  refine Nat.mul_le_mul_left 2 (ncard_le_ncard ?_ (F.finite_V.subset inter_subset_left))
  rintro _ ⟨x, hx, rfl⟩
  have hh : cap.emb x ∈ D.P.Γ.hatV cap := mem_image_of_mem _ hx.2
  exact ⟨mem_V_of_mem_U hF.1 (hU x hx.1) (D.rad.isPreRadial.2.1 hh), hh⟩

omit [T2Space S] in
omit [T2Space Shat] in
/-- The flaw gives the count of `FreeFacts`. -/
theorem free_count {n : ℕ} {F : Drawing Shat} (hF : D.IsFreeCircuit n F) {K : Drawing S}
  (hK : 2 * K.V.ncard ≤ F.E.ncard) {In : Set S}
    (hIn : cap.emb ⁻¹' D.ins F ⊆ In) : (∃ s ∈ χ.Φ.longSides, s ⊆ In) ∨ K.V.ncard <
      (χ.Φ.V ∩ In).ncard := by
  rcases hF.2.2 with ⟨s, hs, hsub⟩ | hlt
  · exact Or.inl ⟨s, hs, (image_subset_iff.1 hsub).trans hIn⟩
  · right
    have h₁ : ((cap.emb '' χ.Φ.V) ∩ D.ins F).ncard ≤ (χ.Φ.V ∩ In).ncard := by
      rw [← ncard_image_of_injective (χ.Φ.V ∩ In) cap.isEmbedding.injective]
      refine ncard_le_ncard ?_ ((χ.Φ.finite_V.subset inter_subset_left).image _)
      rintro _ ⟨⟨x, hx, rfl⟩, hxi⟩
      exact mem_image_of_mem _ ⟨hx, hIn hxi⟩
    omega

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- **The facts about `K` that do not depend on the shape.** -/
theorem free_data_of_cut {n : ℕ} (hn : n < D.rep) {F : Drawing Shat} (hF : D.IsFreeCircuit n F)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F))
      (partIn cap D.P.Γ (closure (D.ins F)ᶜ))) {U₀ : Set S}
    (hc : IsClosed U₀) (hfe : (arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V))).Finite)
    (hm : ∀ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V)), IsMarkedArc (U₀ ∩ D.P.Γ.V) e)
      (hUF : cap.emb ⁻¹' F.U = U₀)
    (hdense : U₀ ⊆ closure (U₀ \ (U₀ ∩ D.P.Γ.V))) (hcard : (arcComponentsIn (U₀ \
      (U₀ ∩ D.P.Γ.V))).ncard ≤ (U₀ ∩ D.P.Γ.V).ncard) {Z : Set Shat}
    (hshape : IsFreeShape cap χ.Φ (coarseDrawing D.P.Γ U₀ hc hfe hm) Z)
      (hint : cap.emb ⁻¹' discInt Z = cap.emb ⁻¹' discInt (D.ins F))
    (hpieces : ∃ 𝓞 𝓛 : Set (Set S), 𝓞.Finite ∧ 𝓛.Finite ∧ (∀ C ∈ 𝓞, IsOArc C) ∧
      (∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞) ∧ U₀
        = ⋃₀ 𝓞 ∪ ⋃₀ 𝓛)
    (hanc : ∀ u x, x ∈ U₀ → x ≠ u → ∃ C ⊆ U₀ \ {u}, x ∈ C ∧ IsPreconnected C ∧
      (C ∩ D.P.Γ.V).Nonempty) :
    IsFreeData D n (D.ins F) Z (coarseDrawing D.P.Γ U₀ hc hfe hm) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hle := hF.2.1
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hF.1 hlt
  have hdisc := hi.2.2.1
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  have hfr : frontier (D.ins F) = F.U := by rw [IsClosedDisc.frontier_eq_discBd hT hdisc, hbd]
  have hU : ∀ {x}, x ∈ U₀ ↔ cap.emb x ∈ F.U := fun {x} ↦ by rw [← hUF]; rfl
  have hinter : D.P.Γ.U ∩ U₀ ⊆ D.P.Γ.V ∩ (U₀ ∩ D.P.Γ.V) := by
    rintro x ⟨hxΓ, hxK⟩
    have hm' : cap.emb x ∈ D.P.Γ.hatU cap ∩ D.rad.G.U := ⟨mem_image_of_mem _ hxΓ, hF.1.1.U_subset
      (hU.1 hxK)⟩
    rw [D.rad.isPreRadial.1] at hm'
    obtain ⟨v, hv, hvx⟩ := hm'
    obtain rfl := cap.isEmbedding.injective hvx
    exact ⟨hv, hxK, hv⟩
  have hbdN : ∀ {x}, x ∈ U₀ → x ∈ bd S → x ∈ U₀ ∩ D.P.Γ.V := fun hx hb ↦
    (hinter ⟨D.P.Γ.bd_subset hb, hx⟩).2
  have hNle : 2 * (U₀ ∩ D.P.Γ.V).ncard ≤ F.E.ncard := D.two_mul_ncard_le hF.1 fun x hx ↦ hU.1 hx
  have hcov : U₀ \ (U₀ ∩ D.P.Γ.V) ⊆ ⋃ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V)), e := fun x hx ↦ by
    obtain ⟨c, hc', hxc⟩ := exists_arcComp_superset (isPathConnected_singleton x)
      (singleton_subset_iff.2 hx)
    exact mem_biUnion hc' (hxc rfl)
  refine ⟨hshape, hdisc, hint, ?_, ⟨?_, ?_, ?_⟩, hinter, fun e he ↦ hm e he, ?_, hpieces, ?_, ?_,
    hanc⟩
  · refine family_of_discs (finite_singleton _) (by rintro _ rfl; exact hlink) ?_ ?_
    · rintro _ rfl
      have := disc_order hS h3 D.rad hF.1 hdisc hbd
      omega
    · rintro _ rfl _ rfl h
      exact (h rfl).elim
  · exact fun e he ↦ disjoint_left.2 fun x hxe hxb ↦ (he.2.1 hxe).2 (hbdN (he.2.1 hxe).1 hxb)
  · intro v hv
    have hvc := hdense hv.1
    have : v ∈ closure (⋃ e ∈ arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V)), e) := closure_mono hcov hvc
    rw [hfe.closure_biUnion] at this
    obtain ⟨e, he, hve⟩ := mem_iUnion₂.1 this
    exact ⟨e, he, hve, fun h ↦ (he.2.1 h).2 hv⟩
  · refine fun s₀ hs₀ ↦ disjoint_left.2 fun x hx hxs ↦ ?_
    have hxb : x ∈ bd S := (hs₀.1.2.1 hxs).1
    exact D.P.Γ.disjoint_V (D.P.fits.short_sides hs₀) hxs (hbdN hx hxb).2
  · change (U₀ ∩ D.P.Γ.V).ncard + (arcComponentsIn (U₀ \ (U₀ ∩ D.P.Γ.V))).ncard ≤ 8 * n
    omega
  · intro v _ h₁ h₂
    have : cap.emb v ∈ frontier (D.ins F) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure h₁, h₂⟩
    rw [hfr] at this
    exact hU.2 this
  · intro v hv
    have : cap.emb v ∈ frontier (D.ins F) := hfr ▸ hU.1 hv
    rw [frontier_eq_closure_inter_closure] at this
    exact this.2

/-- A least flaw circuit has a pole inside. Without one, each cuff would touch `ins(F)` in at most
one point, so `ins(F)` would hold no long
side and no vertices of the frame off `F`. -/
theorem exists_pole_ins {n : ℕ} (hn : n < D.rep) {F : Drawing Shat} (hF : D.IsFreeCircuit n F)
    (hmin : ∀ C, D.IsFreeCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard
      → D.insCount C ≤ D.insCount F)) :
    ∃ r ∈ D.rad.poles, r ∈ D.ins F := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hle := hF.2.1
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hF.1 hlt
  by_contra hno
  push Not at hno
  have hnp : ∀ z ∈ F.V, z ∉ D.rad.poles := fun z hz hzp ↦ hno z hzp (D.U_subset_ins hF.1 hlt
    (F.V_subset_U hz))
  have hrange := subset_range_of_no_pole D.rad hF.1.1 hnp
  have hall : ∀ Θ ∈ cuffs S, (closure (cap.cuffDisc Θ) ∩ D.ins F).Subsingleton ∧ closure
    (cap.cuffDisc Θ) ∩ D.ins F ⊆ F.U := fun Θ hΘ ↦ by
    obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
    have hdis : Disjoint (cap.cuffDisc Θ) F.U := disjoint_left.2 fun x hx hxF ↦ cap.notMem_range hΘ
      hx (hrange hxF)
    exact ⟨touch_subsingleton hS h3 hn hF hmin hp (hno p hp) hΘ hreg hdis,
      fun x hx ↦ D.cuff_inter_ins_of_disjoint hF.1 hlt hp (hno p hp) hreg hdis hx.1 hx.2⟩
  rcases hF.2.2 with ⟨s, hs, hsub⟩ | hlt'
  · obtain ⟨Θ, hΘ, hsΘ, u, v, huv, hset, -⟩ := Frame.side_on_cuff hS χ.Φ hs.1
    have hcl : closure s ⊆ cap.emb ⁻¹' D.ins F ∩ Θ := closure_minimal (fun x hx ↦ ⟨hsub
      (mem_image_of_mem _ hx), hsΘ hx⟩)
      ((hi.2.2.1.isClosed.preimage cap.isEmbedding.continuous).inter (isClosed_cuff hS ⟨Θ, hΘ⟩))
    have hu : u ∈ closure s := (hset ▸ mem_insert u {v} : u ∈ closure s ∩ (χ.Φ.V ∩ Θ)).1
    have hv : v ∈ closure s := (hset ▸ mem_insert_of_mem u rfl : v ∈ closure s ∩ (χ.Φ.V ∩ Θ)).1
    have h₁ := hcl hu
    have h₂ := hcl hv
    exact huv (cap.isEmbedding.injective ((hall Θ hΘ).1 ⟨cap.mem_closure_emb hΘ h₁.2,
      h₁.1⟩ ⟨cap.mem_closure_emb hΘ h₂.2, h₂.1⟩))
  · have hsub : (cap.emb '' χ.Φ.V) ∩ D.ins F ⊆ F.V ∩ D.P.Γ.hatV cap := by
      rintro _ ⟨⟨v, hv, rfl⟩, hvi⟩
      have hvb := χ.Φ.V_subset hv
      have hΘ : connectedComponentIn (bd S) v ∈ cuffs S := ⟨v, hvb, rfl⟩
      have hF' := (hall _ hΘ).2 ⟨cap.mem_closure_emb hΘ (mem_connectedComponentIn hvb), hvi⟩
      exact ⟨(D.rad.bd_point hF.1.1 hvb hF').2.1, mem_image_of_mem _ (D.P.fits.V_subset hv)⟩
    have h₁ := ncard_le_ncard hsub (F.finite_V.subset inter_subset_left)
    have h₂ := D.ncard_E_eq_hat hF.1
    omega

omit hS h3 in
private theorem pole_edges_form_boundary_line
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {F : Drawing Shat} {r : Shat} {e₁ e₂ : Set Shat} {v₁ v₂ : S}
    (hr : r ∈ D.rad.poles) (he₁ : e₁ ∈ F.E) (he₂ : e₂ ∈ F.E)
    (hv₁ : v₁ ∈ D.P.Γ.V) (hv₂ : v₂ ∈ D.P.Γ.V)
    (hFc : F.IsCircuitOf D.rad.G)
    (hs₁ : closure e₁ ∩ D.rad.G.V = {cap.emb v₁, r})
    (hs₂ : closure e₂ ∩ D.rad.G.V = {cap.emb v₂, r})
    (hvG : ∀ {v : S}, v ∈ D.P.Γ.V → cap.emb v ∈ D.rad.G.V)
    (hvp : ∀ {v : S}, v ∈ D.P.Γ.V → cap.emb v ≠ r)
    (hsne : cap.emb v₁ ≠ cap.emb v₂) (hm₁ : cap.emb v₁ ∈ closure e₁)
    (hm₂ : cap.emb v₂ ∈ closure e₂) (hr₁ : r ∈ closure e₁) :
    IsLineWithEnds (closure e₁ ∪ closure e₂) (cap.emb v₁) (cap.emb v₂) := by
  let G := D.rad.G
  let Β := closure e₁ ∪ closure e₂
  have hl₁ : G.toGraph.IsLink e₁ (cap.emb v₁) r := ⟨hFc.1.2 he₁, hvG hv₁, hr.1.1, hs₁⟩
  have hl₂ : G.toGraph.IsLink e₂ r (cap.emb v₂) := ⟨hFc.1.2 he₂, hr.1.1, hvG hv₂, by rw [hs₂,
    pair_comm]⟩
  let W : GraphWalk G.toGraph (cap.emb v₁) (cap.emb v₂) := .cons hl₁ (.cons hl₂ (.nil (hvG hv₂)))
  have hWs : W.IsSimple := by
    simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp hv₁, hsne, (hvp hv₂).symm]
  have := walk_isLine G W hWs hsne
  have heq : ({x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e) = Β := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · simp only [W, GraphWalk.support, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
          at hx
        rcases hx with rfl | rfl | rfl
        · exact Or.inl hm₁
        · exact Or.inl hr₁
        · exact Or.inr hm₂
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 hx
        simp only [W, GraphWalk.edges, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
          at hf
        rcases hf with rfl | rfl
        · exact Or.inl hxf
        · exact Or.inr hxf
    · rintro x (h | h)
      · exact Or.inr (mem_biUnion (by simp [W, GraphWalk.edges]) h)
      · exact Or.inr (mem_biUnion (by simp [W, GraphWalk.edges]) h)
  rwa [heq] at this

omit hS h3 in
private theorem pole_edges_meet_embedded_surface_only_at_ends
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    (F : Drawing Shat)
    (r : Shat)
    (e₁ : Set Shat)
    (e₂ : Set Shat)
    (v₁ : S)
    (v₂ : S)
    (he₁ : e₁ ∈ Drawing.E F)
    (he₂ : e₂ ∈ Drawing.E F)
    (hd₁ : Disjoint e₁ (range cap.emb))
    (hd₂ : Disjoint e₂ (range cap.emb)) (G : Drawing Shat) :
    (F.IsCircuitOf G) →
    (closure e₁ ∩ G.V = {cap.emb v₁, r}) →
    (closure e₂ ∩ G.V = {cap.emb v₂, r}) →
    (r ∉ range cap.emb) →
    let Β : Set Shat := closure e₁ ∪ closure e₂
    ∀ {x : Shat}, x ∈ Β → x ∈ range cap.emb → x = cap.emb v₁ ∨ x = cap.emb v₂ := by
  intro hFc hs₁ hs₂ hrnr Β
  have key : ∀ {e : Set Shat} {v : S} {x}, e ∈ G.E → closure e ∩ G.V = {cap.emb v, r} → Disjoint e
    (range cap.emb) → x ∈ closure e →
      x ∈ range cap.emb → x = cap.emb v := by
    intro e v x he hs hdj hx hxr
    by_cases hxe : x ∈ e
    · exact absurd hxr (disjoint_left.1 hdj hxe)
    · have hxG : x ∈ G.V := by
        by_contra hn
        have : x ∈ closure e \ G.V := ⟨hx, hn⟩
        rw [G.closure_diff_V he] at this
        exact hxe this
      have hm : x ∈ ({cap.emb v, r} : Set Shat) := hs ▸ ⟨hx, hxG⟩
      rcases hm with h | h
      · exact h
      · exact absurd (h ▸ hxr) hrnr
  rintro x (h | h) hxr
  · exact Or.inl (key (hFc.1.2 he₁) hs₁ hd₁ h hxr)
  · exact Or.inr (key (hFc.1.2 he₂) hs₂ hd₂ h hxr)

omit hS h3 in
private theorem flaw_circuit_meets_pole_disc_only_on_boundary_line
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat}
    {β : Type w}
    {χ : ColourScheme S β}
    {D : TangleDatum cap χ}
    {F : Drawing Shat} {r : Shat} {Θ : Set S} {e₁ e₂ : Set Shat}
    (hΘ : Θ ∈ cuffs S) (hFc : F.IsCircuitOf D.rad.G)
    (hone : ∀ p ∈ D.rad.poles, p ∈ F.V → p = r)
    (hedges : ∀ e ∈ F.E, r ∈ closure e → e = e₁ ∨ e = e₂)
    (hr₁ : r ∈ closure e₁) :
    ∀ {x : Shat}, x ∈ F.U → x ∈ cap.cuffDisc Θ → x ∈ closure e₁ ∪ closure e₂ := by
  let G := D.rad.G
  intro x hxF hxd
  have hxr : x ∉ range cap.emb := cap.notMem_range hΘ hxd
  by_cases hxV : x ∈ F.V
  · have hxh : x ∉ D.P.Γ.hatV cap := fun ⟨v, _, hv⟩ ↦ hxr ⟨v, hv⟩
    have hw : x ∈ D.rad.Rstar := ⟨hFc.1.1 hxV, hxh⟩
    by_cases hp : x ∈ D.rad.poles
    · rw [hone x hp hxV]
      exact Or.inl hr₁
    · exact absurd (D.rad.region_subset_range hw hp (D.rad.regionOf_mem hw).2) hxr
  · obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hxF hxV
    obtain ⟨v, -, w', hw', hset⟩ := D.rad.edge_ends (hFc.1.2 hf)
    have hwm : w' ∈ closure f ∩ G.V := by rw [hset]; exact Or.inr rfl
    have hwF : w' ∈ F.V := mem_V_of_mem_U hFc.1 (F.closure_subset_U hf hwm.1) hwm.2
    by_cases hp : w' ∈ D.rad.poles
    · have hwr := hone w' hp hwF
      rw [hwr] at hwm
      rcases hedges f hf hwm.1 with rfl | rfl
      · exact Or.inl (subset_closure hxf)
      · exact Or.inr (subset_closure hxf)
    · exact absurd (D.rad.edge_subset_range (hFc.1.2 hf) hw' hp hset hxf) hxr

omit hS h3 in
private theorem cuff_contact_off_pole_edges_follows_from_incidence
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
    (hS : IsSurface S)
    (h3 : D.P.Γ.IsInternallyThreeConnected)
    {n : ℕ}
    (hn : n < D.rep)
    (hman : ∀ (x : Shat), IsManifoldPoint x)
    {F : Drawing Shat} (hF : D.IsFreeCircuit n F)
    (hmin : ∀ C : Drawing Shat, D.IsFreeCircuit n C → F.E.ncard ≤ C.E.ncard
      ∧ (F.E.ncard = C.E.ncard → D.insCount C ≤ D.insCount F))
    (hdisc : IsClosedDisc (D.ins F)) (hbd : discBd (D.ins F) = F.U)
    {r : Shat} {Θ : Set S} (hr : r ∈ D.rad.poles) (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf r = cap.cuffDisc Θ) (hrF : r ∈ F.V)
    {e₁ e₂ : Set Shat} (hedges : ∀ e ∈ F.E, r ∈ closure e → e = e₁ ∨ e = e₂)
    (hFc : F.IsCircuitOf D.rad.G)
    {Β : Set Shat} (hΒ : Β = closure e₁ ∪ closure e₂) (hΒF : Β ⊆ F.U)
    (hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ)
    (hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ))) :
    ∀ x ∈ discBd (closure (cap.cuffDisc Θ)) ∩ discBd (D.ins F), x ∉ Β →
      ∃ C ⊆ discInt (closure (cap.cuffDisc Θ)) \ Β,
        C ⊆ D.ins F ∧ C.Nonempty ∧ IsPreconnected C ∧ x ∈ closure C := by
  let G := D.rad.G
  rintro x ⟨hxE, hxb⟩ hxΒ
  rw [hEb] at hxE
  obtain ⟨v, hvΘ, rfl⟩ := hxE
  rw [hbd] at hxb
  obtain ⟨hvV, hvF, -⟩ := D.rad.bd_point hFc.1 (cuff_subset_bd ⟨Θ, hΘ⟩ hvΘ) hxb
  obtain ⟨e, he, hs⟩ := D.rad.exists_pole_edge hS h3 hr hΘ hreg hvV hvΘ
  have hvm : cap.emb v ∈ closure e := (hs ▸ mem_insert _ _ : cap.emb v ∈ closure e ∩ G.V).1
  have hrm : r ∈ closure e := (hs ▸ mem_insert_of_mem _ rfl : r ∈ closure e ∩ G.V).1
  have heF : e ∉ F.E := by
    intro h
    rcases hedges e h hrm with rfl | rfl
    · exact hxΒ (hΒ.symm ▸ Or.inl hvm)
    · exact hxΒ (hΒ.symm ▸ Or.inr hvm)
  have heU : Disjoint e F.U := disjoint_left.2 fun y hy hyF ↦ by
    by_cases hyV : y ∈ F.V
    · exact edge_notMem_V he hy (hFc.1.1 hyV)
    · obtain ⟨f, hf, hyf⟩ := F.exists_edge_of_mem hyF hyV
      exact heF (G.edge_eq_of_mem he (hFc.1.2 hf) hy hyf ▸ hf)
  have hconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hsub : e ⊆ discInt (closure (cap.cuffDisc Θ)) := fun y hy ↦ hdE ▸
    (hreg ▸ D.rad.edge_subset_region he hr.1 (by rw [hs]) hy : y ∈ cap.cuffDisc Θ)
  have hin : e ⊆ discInt (D.ins F) := by
    rcases hdisc.side hman hconn (by rw [hbd]; exact heU) with h | h
    · exact h
    · exfalso
      obtain ⟨A, B, Q, ht, hQU, c₁, c₂⟩ := exists_theta_chord hS h3 hFc hr hrF hvV hvF he hs heF
      have hdj : Disjoint (closure e) (discInt (D.ins F)) := disjoint_left.2 fun y hy hyi ↦ by
        obtain ⟨z, hzi, hze⟩ := _root_.mem_closure_iff.1 hy _ (hdisc.isOpen_discInt hman) hyi
        exact disjoint_left.1 h hze (discInt_subset _ hzi)
      exact theta_contra hn hF hmin ht (hdj.mono_left hQU) c₁.le c₂.le (Or.inr ⟨c₁, c₂⟩)
  exact ⟨e, fun y hy ↦ ⟨hsub hy, fun hyΒ ↦ disjoint_left.1 heU hy (hΒF hyΒ)⟩,
    hin.trans (discInt_subset _), he.1, hconn, hvm⟩

omit hS h3 in
private theorem remaining_boundary_line_forms_free_shape
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
    (hS : IsSurface S)
    {n : ℕ}
    (F : Drawing Shat)
    (hF : D.IsFreeCircuit n F)
    (hdisc : IsClosedDisc (D.ins F))
    (hbd : discBd (D.ins F) = F.U)
    (Θ : Set S)
    (hΘ : Θ ∈ cuffs S)
    (hEE : ∀ {Θ' : Set S}, Θ' ∈ cuffs S → Θ' ≠ Θ → Disjoint (closure (cap.cuffDisc Θ')) (closure
      (cap.cuffDisc Θ)))
    (hother : ∀ {Θ' : Set S}, Θ' ∈ cuffs S → Θ' ≠ Θ → ∃ p' ∈ D.rad.poles, p' ∈ cap.cuffDisc Θ' ∧
      p' ∉ D.ins F ∧ Disjoint (cap.cuffDisc Θ') F.U ∧ (closure (cap.cuffDisc Θ') ∩ D.ins
      F).Subsingleton ∧ closure (cap.cuffDisc Θ') ∩ D.ins F ⊆ F.U)
    (hNle : ∀ {U₀ : Set S}, (∀ x ∈ U₀, cap.emb x ∈ F.U) → 2 * (U₀ ∩ D.P.Γ.V).ncard ≤ (Drawing.E
      F).ncard)
    (v₁ : S)
    (v₂ : S)
    (Β : Set Shat)
    (L : Set Shat)
    (hΒL : Β ∩ L = {cap.emb v₁, cap.emb v₂})
    (hFL : F.U = Β ∪ L) :
    let U₀ : Set S := cap.emb ⁻¹' L
    (cap.emb v₁ ∈ L) →
    (cap.emb v₂ ∈ L) →
    ∀ (K : Drawing S),
    (K.V = U₀ ∩ D.P.Γ.V) →
    (cap.emb '' K.U = L) →
    (discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ) →
    ∀ (Z : Set Shat),
    ∀ (A' : Set Shat),
    (IsClosedDisc Z) →
    (A' ⊆ discBd (closure (cap.cuffDisc Θ))) →
    (IsPreconnected A') →
    (discBd Z = discBd (D.ins F) \ (Β \ {cap.emb v₁, cap.emb v₂}) ∪ A') →
    (Disjoint A' (D.ins F)) →
    (discBd (closure (cap.cuffDisc Θ)) \ A' ⊆ D.ins F) →
    (closure (cap.cuffDisc Θ) ⊆ Z) →
    (Z \ D.ins F ⊆ closure (cap.cuffDisc Θ)) →
    (cap.emb ⁻¹' D.ins F ⊆ cap.emb ⁻¹' discInt Z ∪ K.U) →
    (∀ {x : S}, x ∈ K.U → cap.emb x ∈ D.ins F) →
    (cap.emb ⁻¹' discInt Z ∪ K.U ⊆ cap.emb ⁻¹' Z) →
    IsFreeShape cap χ.Φ K Z := by
  intro U₀ hv₁L hv₂L K hK_V hKimg hEb Z A' hZ hA'b hA'c hbZ hA'd hAc hEZ hZΔ hIn hKsub hInZ
  refine ⟨hZ, ?_, ?_, ?_, ⟨Θ, hΘ, hEZ⟩, fun hall ↦ ?_⟩
  · rw [hKimg, hbZ]
    intro x hx
    refine Or.inl ⟨hbd ▸ hFL ▸ Or.inr hx, fun h ↦ h.2 ?_⟩
    have : x ∈ Β ∩ L := ⟨h.1, hx⟩
    rwa [hΒL] at this
  · rw [hbZ]
    rintro x (⟨hx, hn⟩ | hx)
    · refine Or.inr ?_
      rw [hKimg]
      rw [hbd, hFL] at hx
      rcases hx with h | h
      · by_cases he : x ∈ ({cap.emb v₁, cap.emb v₂} : Set Shat)
        · rcases he with h' | h'
          · exact h' ▸ hv₁L
          · exact (mem_singleton_iff.1 h') ▸ hv₂L
        · exact absurd ⟨h, he⟩ hn
      · exact h
    · exact Or.inl (mem_biUnion hΘ (Surface.discBd_subset _ (hA'b hx)))
  · intro Θ' hΘ' hn'
    have hne' : Θ' ≠ Θ := fun h ↦ hn' (h ▸ hEZ)
    obtain ⟨-, -, -, -, -, h, -⟩ := hother hΘ' hne'
    refine h.anti fun x hx ↦ ⟨hx.1, ?_⟩
    by_contra hxΔ
    exact disjoint_left.1 (hEE hΘ' hne') hx.1 (hZΔ ⟨hx.2, hxΔ⟩)
  · have hoth : ∀ Θ' ∈ cuffs S, Θ' ≠ Θ → Disjoint (closure (cap.cuffDisc Θ')) Z
      := fun Θ' hΘ' hne' ↦ by
      obtain ⟨p, -, hpd, hpi, -⟩ := hother hΘ' hne'
      rcases hall Θ' hΘ' with h | h
      · exfalso
        have hpZ := h (subset_closure hpd)
        exact disjoint_left.1 (hEE hΘ' hne') (subset_closure hpd) (hZΔ ⟨hpZ, hpi⟩)
      · exact h
    have hA'sub : A' ⊆ cap.emb '' Θ := hEb ▸ hA'b
    have hmemA : ∀ {x}, x ∈ Θ → (x ∈ cap.emb ⁻¹' A' ↔ cap.emb x ∉ D.ins F) := fun {x} hx ↦ by
      constructor
      · exact fun h ↦ disjoint_left.1 hA'd h
      · intro h
        by_contra hn
        exact h (hAc ⟨hEb ▸ mem_image_of_mem _ hx, hn⟩)
    have hcountK : 2 * K.V.ncard ≤ F.E.ncard := by
      rw [hK_V]
      exact hNle fun x hx => hFL ▸ Or.inr hx
    refine freeFacts_of_cuff (A := cap.emb ⁻¹' A') hS χ.Φ cap hΘ hInZ hoth ?_ ?_ ?_ ?_
      (free_count hF hcountK hIn)
    · rw [← cap.isEmbedding.isInducing.isPreconnected_image, image_preimage_eq_of_subset
        (hA'sub.trans (image_subset_range _ _))]
      exact hA'c
    · intro x hx
      obtain ⟨y, hy, he⟩ := hA'sub hx
      exact cap.isEmbedding.injective he ▸ hy
    · intro x hx
      constructor
      · rintro (h | h) hxA
        · exact h.2 (hbZ ▸ Or.inr hxA)
        · exact (hmemA hx).1 hxA (hKsub h)
      · intro h
        exact hIn (by_contra fun hn ↦ h ((hmemA hx).2 hn))
    · have : Θ \ cap.emb ⁻¹' A' = Θ ∩ cap.emb ⁻¹' D.ins F := by
        ext x
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨h₁, by_contra fun hn ↦ h₂ ((hmemA h₁).2 hn)⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨h₁, fun h ↦ (hmemA h₁).1 h h₂⟩
      rw [this]
      exact (isClosed_cuff hS ⟨Θ, hΘ⟩).inter (hdisc.isClosed.preimage cap.isEmbedding.continuous)

omit hS h3 in
private theorem free_data_when_pole_is_on_circuit
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
    (hS : IsSurface S)
    (h3 : D.P.Γ.IsInternallyThreeConnected)
    {n : ℕ}
    (hn : n < D.rep)
    (hT : IsClosedSurface Shat)
    (hman : ∀ (x : Shat), IsManifoldPoint x)
    (hj : IsClosedEmbedding cap.emb)
    (F : Drawing Shat)
    (hF : D.IsFreeCircuit n F)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins F)) (partIn cap
      D.P.Γ (closure (D.ins F)ᶜ)))
    (hmin : ∀ (C : Drawing Shat), D.IsFreeCircuit n C → (Drawing.E F).ncard ≤ (Drawing.E C).ncard
      ∧ ((Drawing.E F).ncard = (Drawing.E C).ncard → D.insCount C ≤ D.insCount F))
    (hFc : F.IsCircuitOf D.rad.G)
    (hlt : (Drawing.E F).ncard < 2 * D.rep)
    (hdisc : IsClosedDisc (D.ins F))
    (hbd : discBd (D.ins F) = F.U)
    (r : Shat)
    (hr : r ∈ D.rad.poles)
    (Θ : Set S)
    (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf r = cap.cuffDisc Θ)
    (hE : IsClosedDisc (closure (cap.cuffDisc Θ)))
    (hone : ∀ p ∈ D.rad.poles, p ∈ F.V → p = r)
    (hcover : F.U ⊆ range cap.emb ∪ cap.cuffDisc Θ)
    (hEE : ∀ {Θ' : Set S}, Θ' ∈ cuffs S → Θ' ≠ Θ → Disjoint (closure (cap.cuffDisc Θ')) (closure
      (cap.cuffDisc Θ)))
    (hother : ∀ {Θ' : Set S}, Θ' ∈ cuffs S → Θ' ≠ Θ → ∃ p' ∈ D.rad.poles, p' ∈ cap.cuffDisc Θ' ∧
      p' ∉ D.ins F ∧ Disjoint (cap.cuffDisc Θ') F.U ∧ (closure (cap.cuffDisc Θ') ∩ D.ins
      F).Subsingleton ∧ closure (cap.cuffDisc Θ') ∩ D.ins F ⊆ F.U)
    (hNle : ∀ {U₀ : Set S}, (∀ x ∈ U₀, cap.emb x ∈ F.U) → 2 * (U₀ ∩ D.P.Γ.V).ncard ≤ (Drawing.E
      F).ncard)
    (hrF : r ∈ F.V) :
    ∃ Δ Z K, IsFreeData D n Δ Z K := by
  obtain ⟨e₁, e₂, v₁, v₂, he₁, he₂, hv₁, hv₂, hne, hs₁, hs₂, hedges⟩ := D.rad.circuit_edges hS h3
    hFc hrF hr.1
  obtain ⟨hd₁, hvΘ₁⟩ := D.rad.pole_edge (hFc.1.2 he₁) hr hΘ hreg hs₁
  obtain ⟨hd₂, hvΘ₂⟩ := D.rad.pole_edge (hFc.1.2 he₂) hr hΘ hreg hs₂
  set G := D.rad.G with hG
  have hrnr := D.pole_notMem_range hr
  have hvG : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ∈ G.V := fun hv ↦ D.rad.isPreRadial.2.1
    (mem_image_of_mem _ hv)
  have hvp : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ≠ r := fun hv h ↦ hr.1.2 (h ▸ mem_image_of_mem _ hv)
  have hsne : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ hne (cap.isEmbedding.injective h)
  have hclE : ∀ {e x}, e ∈ G.E → closure e ∩ G.V = {x, r} → closure e ⊆ closure (cap.cuffDisc Θ)
    := fun he hs ↦
    closure_mono (hreg ▸ D.rad.edge_subset_region he hr.1 (by rw [hs]))
  set Β : Set Shat := closure e₁ ∪ closure e₂ with hΒ
  have hm₁ : cap.emb v₁ ∈ closure e₁ := (hs₁ ▸ mem_insert _ _ : cap.emb v₁ ∈ closure e₁ ∩ G.V).1
  have hm₂ : cap.emb v₂ ∈ closure e₂ := (hs₂ ▸ mem_insert _ _ : cap.emb v₂ ∈ closure e₂ ∩ G.V).1
  have hr₁ : r ∈ closure e₁ := (hs₁ ▸ mem_insert_of_mem _ rfl : r ∈ closure e₁ ∩ G.V).1
  have hΒF : Β ⊆ F.U := union_subset (F.closure_subset_U he₁) (F.closure_subset_U he₂)
  have hΒline : IsLineWithEnds Β (cap.emb v₁) (cap.emb v₂) := by
    exact pole_edges_form_boundary_line hr he₁ he₂ hv₁ hv₂ hFc hs₁ hs₂ hvG hvp hsne hm₁ hm₂ hr₁
  have hΒr : ∀ {x}, x ∈ Β → x ∈ range cap.emb → x = cap.emb v₁ ∨ x = cap.emb v₂ := by
    exact pole_edges_meet_embedded_surface_only_at_ends (S := S) (Shat := Shat) (cap := cap) F r
      e₁ e₂ v₁ v₂ he₁ he₂ hd₁ hd₂ G hFc hs₁ hs₂ hrnr
  obtain ⟨u, w, h2a, hru, hu0, hu1, hun⟩ := exists_arcs_of_line (IsCircuit.isOArc_U hFc.2) hΒline
    hΒF
  set L : Set Shat := range w with hL
  have hLline : IsLineWithEnds L (cap.emb v₁) (cap.emb v₂) := by
    have := h2a.arc_right.isLineWithEnds
    rwa [h2a.zero, h2a.one, hu0, hu1] at this
  have hΒL : Β ∩ L = {cap.emb v₁, cap.emb v₂} := by
    have := h2a.inter
    rwa [hru, hu0, hu1] at this
  have hFL : F.U = Β ∪ L := by rw [← hun, hru]
  have hFcd : ∀ {x}, x ∈ F.U → x ∈ cap.cuffDisc Θ → x ∈ Β := by
    exact flaw_circuit_meets_pole_disc_only_on_boundary_line hΘ hFc hone hedges hr₁
  have hLr : L ⊆ range cap.emb := fun x hx ↦ by
    have hxF : x ∈ F.U := hFL ▸ Or.inr hx
    rcases hcover hxF with h | h
    · exact h
    · have : x ∈ Β ∩ L := ⟨hFcd hxF h, hx⟩
      rw [hΒL] at this
      rcases this with h' | h'
      · exact ⟨_, h'.symm⟩
      · exact ⟨_, (mem_singleton_iff.1 h').symm⟩
  set U₀ : Set S := cap.emb ⁻¹' L with hU₀
  have hU₀i : cap.emb '' U₀ = L := image_preimage_eq_of_subset hLr
  have hv₁L : cap.emb v₁ ∈ L := (hΒL.symm ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ L).2
  have hv₂L : cap.emb v₂ ∈ L := (hΒL.symm ▸ mem_insert_of_mem _ rfl : cap.emb v₂ ∈ Β ∩ L).2
  have hUF : cap.emb ⁻¹' F.U = U₀ := by
    ext x
    constructor
    · intro hx
      change cap.emb x ∈ F.U at hx
      rw [hFL] at hx
      rcases hx with h | h
      · change cap.emb x ∈ L
        rcases hΒr h (mem_range_self x) with h' | h'
        · rw [h']
          exact hv₁L
        · rw [h']
          exact hv₂L
      · exact h
    · intro hx
      change cap.emb x ∈ F.U
      rw [hFL]
      exact Or.inr hx
  have hl : IsLineWithEnds U₀ v₁ v₂ := isLine_comap hj (by rw [hU₀i]; exact hLline)
  have hc : IsClosed U₀ := hUF ▸ F.isClosed_U.preimage cap.isEmbedding.continuous
  have hNf : (U₀ ∩ D.P.Γ.V).Finite := D.P.Γ.finite_V.subset inter_subset_right
  have ha : v₁ ∈ U₀ ∩ D.P.Γ.V := ⟨hv₁L, hv₁⟩
  have hb : v₂ ∈ U₀ ∩ D.P.Γ.V := ⟨hv₂L, hv₂⟩
  obtain ⟨hfe, hcount, hmk⟩ := arcs_of_line _ hNf rfl hl ha hb inter_subset_left
  set K := coarseDrawing D.P.Γ U₀ hc hfe fun e he ↦ (hmk e he).1 with hK
  have hKimg : cap.emb '' K.U = L := hU₀i
  have hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := cap.cuffDisc_eq_discInt hΘ
  have hΒE : Β ⊆ closure (cap.cuffDisc Θ) := union_subset (hclE (hFc.1.2 he₁) hs₁) (hclE
    (hFc.1.2 he₂) hs₂)
  have hmeet : Β ∩ discBd (closure (cap.cuffDisc Θ)) = {cap.emb v₁, cap.emb v₂} := by
    rw [hEb]
    apply Subset.antisymm
    · rintro x ⟨hx, y, -, rfl⟩
      exact hΒr hx (mem_range_self y)
    · rintro _ (rfl | h)
      · exact ⟨Or.inl hm₁, mem_image_of_mem _ hvΘ₁⟩
      · rw [mem_singleton_iff.1 h]
        exact ⟨Or.inr hm₂, mem_image_of_mem _ hvΘ₂⟩
  have hoff : discInt (closure (cap.cuffDisc Θ)) ∩ discBd (D.ins F) ⊆ Β := by
    rw [← hdE, hbd]
    exact fun x hx ↦ hFcd hx.2 hx.1
  have htouch : ∀ x ∈ discBd (closure (cap.cuffDisc Θ)) ∩ discBd (D.ins F), x ∉ Β →
      ∃ C, C ⊆ discInt (closure (cap.cuffDisc Θ)) \ Β ∧ C ⊆ D.ins F ∧ C.Nonempty ∧ IsPreconnected C
        ∧ x ∈ closure C := by
    exact cuff_contact_off_pole_edges_follows_from_incidence hS h3 hn hman hF hmin hdisc hbd
      hr hΘ hreg hrF hedges hFc hΒ hΒF hEb hdE
  obtain ⟨Z, A', hZ, hA'b, hA'c, hbZ, hA'd, hAc, hEZ, hΔZ, hZΔ, hiff⟩ :=
    exists_outer_half hT hdisc hE hsne hΒline (hbd ▸ hΒF) hΒE hmeet hoff htouch
  have hemb : ∀ x, cap.emb x ∉ discInt (closure (cap.cuffDisc Θ)) := fun x h ↦ cap.notMem_range hΘ
    (hdE ▸ h) (mem_range_self x)
  have hint : cap.emb ⁻¹' discInt Z = cap.emb ⁻¹' discInt (D.ins F) := by
    ext x
    exact hiff _ (hemb x)
  have hIn : cap.emb ⁻¹' D.ins F ⊆ cap.emb ⁻¹' discInt Z ∪ K.U := fun x hx ↦ by
    by_cases hb' : cap.emb x ∈ discBd (D.ins F)
    · refine Or.inr ?_
      change x ∈ U₀
      rw [← hUF]
      change cap.emb x ∈ F.U
      rw [← hbd]
      exact hb'
    · exact Or.inl ((hiff _ (hemb x)).2 ⟨hx, hb'⟩)
  have hKsub : ∀ {x}, x ∈ K.U → cap.emb x ∈ D.ins F := fun {x} hx ↦ D.U_subset_ins hFc hlt
    (hFL ▸ Or.inr hx)
  have hInZ : cap.emb ⁻¹' discInt Z ∪ K.U ⊆ cap.emb ⁻¹' Z := by
    rintro x (h | h)
    · exact discInt_subset Z h
    · exact hΔZ (hKsub h)
  have hshape : IsFreeShape cap χ.Φ K Z := by
    exact remaining_boundary_line_forms_free_shape (S := S) (Shat := Shat) (cap := cap) (β := β)
      (χ := χ) (D := D) hS (n := n) F hF hdisc hbd Θ hΘ hEE hother hNle v₁ v₂ Β L hΒL hFL
      hv₁L hv₂L K rfl hKimg hEb Z A' hZ hA'b hA'c hbZ hA'd hAc hEZ hZΔ hIn hKsub hInZ
  refine ⟨D.ins F, Z, K, free_data_of_cut hS h3 hn hF hlink hc hfe _ hUF ?_
    (by omega) hshape hint ?_ ?_⟩
  · exact line_subset_closure_sdiff hl hNf
  · refine ⟨∅, {U₀}, finite_empty, finite_singleton _, by simp, ?_, by simp⟩
    rintro _ rfl
    exact ⟨v₁, v₂, hne, hl, Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hvΘ₁), Or.inl (cuff_subset_bd ⟨Θ,
      hΘ⟩ hvΘ₂)⟩
  · intro w' x hx hne'
    refine line_anchor hl Subset.rfl (fun w'' h ↦ ?_) (fun w'' h ↦ ?_) hx hne'
    · refine ⟨{v₁}, ?_, rfl, isPreconnected_singleton, ⟨v₁, rfl, hv₁⟩⟩
      rintro _ rfl
      exact ⟨hv₁L, h⟩
    · refine ⟨{v₂}, ?_, rfl, isPreconnected_singleton, ⟨v₂, rfl, hv₂⟩⟩
      rintro _ rfl
      exact ⟨hv₂L, h⟩

/-- **A freedom flaw gives the data.** -/
theorem exists_free_data {n : ℕ} (hn : n < D.rep) (hd : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁
  ≠ r₂ → n < D.vDist r₁ r₂)
    (hex : ∃ C, D.IsFreeCircuit n C) : ∃ Δ Z K, IsFreeData D n Δ Z K := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have : ConnectedSpace S := χ.connected
  have hj := cap.isClosedEmbedding hS
  obtain ⟨F, hF, hlink, hmin⟩ := exists_least_free hS h3 hn hex
  have hFc := hF.1
  have hle := hF.2.1
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hFc hlt
  have hdisc := hi.2.2.1
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  have huniq : ∀ p ∈ D.rad.poles, ∀ q ∈ D.rad.poles, p ∈ D.ins F → q ∈ D.ins F → p = q
    := fun p hp q hq h₁ h₂ ↦ by
    by_contra hne
    have := vDist_le_of_ins hn hFc hle hp hq hne h₁ h₂
    have := hd p hp q hq hne
    omega
  obtain ⟨r, hr, hri⟩ := exists_pole_ins hS h3 hn hF hmin
  obtain ⟨Θ, hΘ, hreg, hrd⟩ := D.rad.pole_cases hr
  have hE := cap.cuffDisc_closedDisc Θ hΘ
  have hone : ∀ p ∈ D.rad.poles, p ∈ F.V → p = r := fun p hp hpF ↦
    huniq p hp r hr (D.U_subset_ins hFc hlt (F.V_subset_U hpF)) hri
  have hcover := U_subset_of_one_pole hFc.1 hreg hrd hone
  have hEE : ∀ {Θ'}, Θ' ∈ cuffs S → Θ' ≠ Θ → Disjoint (closure (cap.cuffDisc Θ')) (closure
    (cap.cuffDisc Θ)) := fun hΘ' hne ↦
    cap.cuffDisc_disjoint _ hΘ' _ hΘ hne
  have hother : ∀ {Θ'}, Θ' ∈ cuffs S → Θ' ≠ Θ → ∃ p' ∈ D.rad.poles, p' ∈ cap.cuffDisc Θ'
    ∧ p' ∉ D.ins F ∧
      Disjoint (cap.cuffDisc Θ') F.U ∧ (closure (cap.cuffDisc Θ') ∩ D.ins F).Subsingleton ∧ closure
        (cap.cuffDisc Θ') ∩ D.ins F ⊆ F.U := fun {Θ'} hΘ' hne ↦ by
    obtain ⟨p, hp, hpd, hreg'⟩ := D.rad.exists_pole hΘ'
    have hne' : p ≠ r := by
      rintro rfl
      exact disjoint_left.1 (hEE hΘ' hne) (subset_closure hpd) (subset_closure hrd)
    have hpi : p ∉ D.ins F := fun h ↦ hne' (huniq p hp r hr h hri)
    have hdis : Disjoint (cap.cuffDisc Θ') F.U := disjoint_left.2 fun x hx hxF ↦ by
      rcases hcover hxF with h | h
      · exact cap.notMem_range hΘ' hx h
      · exact disjoint_left.1 (hEE hΘ' hne) (subset_closure hx) (subset_closure h)
    exact ⟨p, hp, hpd, hpi, hdis, touch_subsingleton hS h3 hn hF hmin hp hpi hΘ' hreg' hdis,
      fun x hx ↦ D.cuff_inter_ins_of_disjoint hFc hlt hp hpi hreg' hdis hx.1 hx.2⟩
  have hNle := fun {U₀ : Set S} (hU : ∀ x ∈ U₀, cap.emb x ∈ F.U) ↦ D.two_mul_ncard_le hFc hU
  by_cases hrF : r ∈ F.V
  · exact free_data_when_pole_is_on_circuit (S := S) (Shat := Shat) (cap := cap) (β := β) (χ := χ)
      (D := D) hS h3 (n := n) hn hT hman hj F hF hlink hmin hFc hlt hdisc hbd r hr Θ hΘ hreg
      hE hone hcover hEE hother hNle hrF
  · have hnp : ∀ z ∈ F.V, z ∉ D.rad.poles := fun z hz hzp ↦ hrF (hone z hzp hz ▸ hz)
    have hrange := subset_range_of_no_pole D.rad hFc.1 hnp
    have hrnr := D.pole_notMem_range hr
    have hrint : r ∈ discInt (D.ins F) := ⟨hri, fun hb ↦ hrnr (hrange (hbd ▸ hb))⟩
    have hEin : closure (cap.cuffDisc Θ) ⊆ D.ins F := by
      rcases cap.side hdisc (hbd.trans_subset hrange) hΘ with h | h
      · exact h
      · exact absurd hrint (disjoint_left.1 h (subset_closure hrd))
    obtain ⟨hinter₀, -, -, -, -⟩ := comap_facts D.rad D.P.fits hFc.1 hrange hj (circuit_iso hFc.2)
    set K₀ : Drawing S := GM19.Drawing.comap F hj hrange with hK₀
    have hK₀U : K₀.U = cap.emb ⁻¹' F.U := rfl
    have hKU : cap.emb '' K₀.U = F.U := image_preimage_eq_of_subset hrange
    set U₀ : Set S := cap.emb ⁻¹' F.U with hU₀
    have hO : IsOArc U₀ := isOArc_comap hj (hKU ▸ IsCircuit.isOArc_U hFc.2)
    have hNf : (U₀ ∩ D.P.Γ.V).Finite := D.P.Γ.finite_V.subset inter_subset_right
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ U₀ ∩ D.P.Γ.V, ∃ b ∈ U₀ ∩ D.P.Γ.V, a ≠ b := by
      by_cases hsing : (U₀ ∩ bd S).Subsingleton
      · exact two_vertices_of_ring (K := K₀) (D := D) h3 hO hinter₀ hsing fun Δ' d₁ d₂ d₃ d₄ ↦
          D.no_empty_disc hFc hlt hr hri d₁ d₂ (d₃.trans hKU) (by rwa [hKU] at d₄)
      · obtain ⟨x, hx, y, hy, hxy⟩ := not_subsingleton_iff.1 hsing
        exact ⟨x, ⟨hx.1, (D.rad.bd_point hFc.1 hx.2 hx.1).1⟩, y, ⟨hy.1,
          (D.rad.bd_point hFc.1 hy.2 hy.1).1⟩, hxy⟩
    have h2 : 2 ≤ (U₀ ∩ D.P.Γ.V).ncard := (one_lt_ncard hNf).2 ⟨a, ha, b, hb, hab⟩
    obtain ⟨hfe, hcount, hmk⟩ := arcs_of_oArc hNf hO inter_subset_left h2
    have hc : IsClosed U₀ := F.isClosed_U.preimage cap.isEmbedding.continuous
    set K := coarseDrawing D.P.Γ U₀ hc hfe fun e he ↦ (hmk e he).1 with hK
    have hIn : cap.emb ⁻¹' D.ins F ⊆ cap.emb ⁻¹' discInt (D.ins F) ∪ K.U := fun x hx ↦ by
      by_cases hb' : cap.emb x ∈ discBd (D.ins F)
      · refine Or.inr ?_
        change cap.emb x ∈ F.U
        rw [← hbd]
        exact hb'
      · exact Or.inl ⟨hx, hb'⟩
    have hInZ : cap.emb ⁻¹' discInt (D.ins F) ∪ K.U ⊆ cap.emb ⁻¹' D.ins F := by
      rintro x (h | h)
      · exact discInt_subset (D.ins F) h
      · exact D.U_subset_ins hFc hlt h
    have hshape : IsFreeShape cap χ.Φ K (D.ins F) := by
      refine ⟨hdisc, ?_, ?_, ?_, ⟨Θ, hΘ, hEin⟩, fun hall ↦ ?_⟩
      · rw [hbd]
        exact image_preimage_subset _ _
      · rw [hbd]
        exact fun x hx ↦ Or.inr (hKU ▸ hx)
      · intro Θ' hΘ' hn'
        have hne : Θ' ≠ Θ := fun h ↦ hn' (h ▸ hEin)
        obtain ⟨-, -, -, -, -, h, -⟩ := hother hΘ' hne
        exact h
      · refine freeFacts_of_cuff (A := ∅) hS χ.Φ cap hΘ hInZ (fun Θ' hΘ' hne ↦ ?_)
          isPreconnected_empty (empty_subset _) ?_ ?_
          (free_count hF (hNle fun x hx ↦ hx) hIn)
        · obtain ⟨p, -, hpd, hpi, -⟩ := hother hΘ' hne
          rcases hall Θ' hΘ' with h | h
          · exact absurd (h (subset_closure hpd)) hpi
          · exact h
        · intro x hx
          exact ⟨fun _ h ↦ h, fun _ ↦ hIn (hEin (cap.mem_closure_emb hΘ hx))⟩
        · rw [sdiff_empty]
          exact isClosed_cuff hS ⟨Θ, hΘ⟩
    refine ⟨D.ins F, D.ins F, K, free_data_of_cut hS h3 hn hF hlink hc hfe _ rfl ?_ hcount.le
      hshape rfl ?_ ?_⟩
    · exact oArc_subset_closure_sdiff hO ha.1 hb.1 hab hNf
    · refine ⟨{U₀}, ∅, finite_singleton _, finite_empty, by rintro _ rfl; exact hO, by simp, by
        simp⟩
    · intro u x hx hne
      exact ring_part hO ha hb hab hx hne

end TangleDatum

end GraphMinor.GM19
