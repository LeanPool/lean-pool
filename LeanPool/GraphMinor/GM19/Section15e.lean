/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15d

/-!
# Graph Minors XIX, (15.2): the inflation

The last step of the proof of (15.2). Suppose that `sk(Γ)`, drawn in `Σ̂`, has mutually disjoint
connected subdrawings, one for
each vertex `v` of `Γ₀`, that contain the ends of the edges `β(e)` in the right places. Then their
vertex sets, and the map `β`,
form an inflation of `(Γ₀, φ₀)` in `(Γ, φ)`. The result used later is
`isColouredInflation_of_subdrawings`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM12

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

omit [T2Space Shat] in
/-- Two vertices joined by an edge of `sk(Γ)` drawn in `Σ̂` are adjacent in `sk(Γ)`. -/
theorem IsSkHat.skAdj_of_edge (hS : IsSurface S) {Γ : Painting S} {H : Drawing Shat}
  (h : IsSkHat cap Γ H) {C : Set Shat} (hC : C ∈ H.E) {x y : Shat} (hcap : closure C ∩ H.V
    = {x, y}) :
    ∃ u w, x = cap.emb u ∧ y = cap.emb w ∧ Γ.skAdj.Adj u w := by
  obtain ⟨e, he, rfl⟩ := (h.edge_iff hS).mp hC
  obtain ⟨u, w, huw, ht, htV, -⟩ := Γ.sk_line he
  have hcl : closure (cap.emb '' e) = cap.emb '' closure e := ((cap.isClosedEmbedding
    hS).closure_image_eq e).symm ▸ rfl
  have huS : u ∈ tilde e := ht ▸ mem_insert u _
  have hwS : w ∈ tilde e := ht ▸ mem_insert_of_mem u rfl
  have hset : closure (cap.emb '' e) ∩ H.V = {cap.emb u, cap.emb w} := by
    rw [hcl, h.hV]
    ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
      obtain rfl := cap.isEmbedding.injective hpq
      have hpe : q ∉ e := fun hc ↦ (he.2.1 hc).2 hq
      have : q ∈ tilde e := ⟨hp, hpe⟩
      rw [ht] at this
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨mem_image_of_mem _ huS.1, mem_image_of_mem _ (htV huS)⟩
      · exact ⟨mem_image_of_mem _ hwS.1, mem_image_of_mem _ (htV hwS)⟩
  have hadj : Γ.skAdj.Adj u w := by
    refine ⟨huw, htV huS, htV hwS, ?_⟩
    rcases Γ.sk_cases he with ⟨heE, -⟩ | ⟨c, hc, -, hec, -⟩
    · exact ⟨e, heE, huS, hwS⟩
    · have hin : ∀ {z}, z ∈ tilde e → z ∈ tilde c := fun {z} hz ↦
        ⟨closure_mono hec hz.1, fun hzc ↦ Γ.disjoint_V hc hzc (htV hz)⟩
      exact ⟨c, hc, hin huS, hin hwS⟩
  have hpair : ({x, y} : Set Shat) = {cap.emb u, cap.emb w} := hcap.symm.trans hset
  have hx : x ∈ ({cap.emb u, cap.emb w} : Set Shat) := hpair ▸ mem_insert x _
  have hy : y ∈ ({cap.emb u, cap.emb w} : Set Shat) := hpair ▸ mem_insert_of_mem x rfl
  have hu' : cap.emb u ∈ ({x, y} : Set Shat) := hpair ▸ mem_insert _ _
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exfalso
      have hw' : cap.emb w ∈ ({cap.emb u, cap.emb u} : Set Shat) := hpair ▸ mem_insert_of_mem _ rfl
      rcases hw' with hw' | hw' <;> exact huw (cap.isEmbedding.injective hw').symm
    · exact ⟨u, w, rfl, rfl, hadj⟩
  · rcases hy with rfl | rfl
    · exact ⟨w, u, rfl, rfl, hadj.symm⟩
    · exfalso
      rcases hu' with hu' | hu' <;> exact huw (cap.isEmbedding.injective hu')

omit [T2Space Shat] in
/-- A walk in a subdrawing of `sk(Γ)` gives a walk in the induced subgraph of the skeleton. -/
theorem IsSkHat.reachable_of_walk (hS : IsSurface S) {Γ : Painting S} {H H' : Drawing Shat}
  (h : IsSkHat cap Γ H) (hs : H'.IsSubdrawing H) {x y : Shat} (W : GraphWalk H'.toGraph x y) {a b :
    S}
    (ha : cap.emb a = x) (hb : cap.emb b = y) (hmem : a ∈ cap.emb ⁻¹' H'.V)
      (hmemb : b ∈ cap.emb ⁻¹' H'.V) :
    (Γ.skAdj.induce (cap.emb ⁻¹' H'.V)).Reachable ⟨a, hmem⟩ ⟨b, hmemb⟩ := by
  induction W generalizing a with
  | nil hv =>
    obtain rfl : a = b := cap.isEmbedding.injective (ha.trans hb.symm)
    exact SimpleGraph.Reachable.refl _
  | @cons u v w g hlink rest ih =>
    obtain ⟨hg, hu, hv, hcap⟩ := hlink
    have hcap' : closure g ∩ H.V = {u, v} := by
      rw [← hcap]
      exact (hs.closure_inter_V hg).symm
    obtain ⟨p, q, hp, hq, hadj⟩ := h.skAdj_of_edge hS (hs.2 hg) hcap'
    obtain rfl : a = p := cap.isEmbedding.injective (ha.trans hp)
    have hqm : q ∈ cap.emb ⁻¹' H'.V := by
      rw [mem_preimage, ← hq]
      exact hv
    exact (SimpleGraph.Adj.reachable (G := Γ.skAdj.induce (cap.emb ⁻¹' H'.V)) (u := ⟨a,
      hmem⟩) (v := ⟨q, hqm⟩) hadj).trans (ih hq.symm hb hqm)

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

omit [T2Space S] in
/-- A border edge of `Γ₀` and its image lie on the same sides. -/
theorem IsEdgeMap.border (hb : D.IsEdgeMap P₀ n b) {e : Set S} (he : e ∈ P₀.Γ.E)
  (hB : Painting.IsBorder e) :
    ∃ s ∈ χ.Φ.sides, e ⊆ s ∧ b e ⊆ s ∧ (χ.ΩS s).le (P₀.φ e) (D.P.φ (b e)) := by
  obtain ⟨s, hs, -, hsub⟩ := Painting.exists_side P₀.fits he hB
  by_cases hl : s ∈ χ.Φ.longSides
  · obtain ⟨m, f, g, c, r, u₀, u₁, u₀', u₁', hM⟩ := hb.side s hl
    obtain ⟨i, rfl⟩ := hM.all₀ e he hsub
    rw [hM.map i]
    exact ⟨s, hs, hsub, (hM.order.2.2.2.1 i).2, hM.le i⟩
  · have hss : s ∈ χ.Φ.shortSides := ⟨hs, fun h ↦ hl ⟨hs, h⟩⟩
    obtain rfl := eq_short_of_subset P₀.fits he hss hsub
    rw [hb.short e hss]
    have hm₀ := P₀.border_mem e he e hs ⟨hB, Subset.rfl⟩
    have hm₁ := D.P.border_mem e (D.P.fits.short_sides hss) e hs ⟨hB, Subset.rfl⟩
    rw [χ.short_singleton e hss] at hm₀ hm₁
    rw [mem_singleton_iff.1 hm₀, mem_singleton_iff.1 hm₁]
    exact ⟨e, hs, Subset.rfl, Subset.rfl, (χ.ΩS e).refl _ (by rw [χ.short_singleton e hss]; exact
      rfl)⟩

end TangleDatum

/-- **The end of the proof of (15.2).** -/
theorem isColouredInflation_of_subdrawings {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n :
  ℕ} {b : Set S → Set S} (hS : IsSurface S) {H : Drawing Shat} (hH : IsSkHat cap D.P.Γ H)
    (hb : D.IsEdgeMap P₀ n b) (Hv : S → Drawing Shat) (hsub : ∀ v ∈ P₀.Γ.V, (Hv v).IsSubdrawing H)
      (hconn : ∀ v ∈ P₀.Γ.V, IsConnectedDrawing (Hv v))
    (hdisj : ∀ v ∈ P₀.Γ.V, ∀ v' ∈ P₀.Γ.V, v ≠ v' → Disjoint (Hv v).V (Hv v').V)
      (hne : ∀ v ∈ P₀.Γ.V, (Hv v).V.Nonempty)
    (hends : ∀ e ∈ P₀.Γ.E, ∀ (i : ℕ) (hi : i < (P₀.Γ.γ e).length) (hi' : i < (D.P.Γ.γ
      (b e)).length), cap.emb (D.P.Γ.γ (b e))[i] ∈ (Hv (P₀.Γ.γ e)[i]).V) :
    IsColouredInflation χ P₀ D.P (fun v ↦ cap.emb ⁻¹' (Hv v).V) b := by
  have hVS : ∀ v ∈ P₀.Γ.V, ∀ x ∈ (Hv v).V, ∃ y ∈ D.P.Γ.V, cap.emb y = x := fun v hv x hx ↦ by
    have := (hsub v hv).1 hx
    rw [hH.hV] at this
    exact this
  refine ⟨⟨hb.mem, hb.size, hb.injOn, fun v hv ↦ ?_, fun v hv x hx ↦ ?_, fun v hv ⟨x, hx⟩ ⟨y, hy⟩ ↦
    ?_, fun v hv v' hv' hne' ↦ ?_, hends⟩, fun e he hB ↦ ?_, fun e he hi h2 ↦ ?_, fun e he hi h3 ↦
      ?_, fun e he s hs hbs ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hne v hv
    obtain ⟨y, -, rfl⟩ := hVS v hv x hx
    exact ⟨y, hx⟩
  · obtain ⟨y, hy, hyx⟩ := hVS v hv _ hx
    exact cap.isEmbedding.injective hyx ▸ hy
  · obtain ⟨W⟩ := hconn v hv _ hx _ hy
    exact hH.reachable_of_walk hS (hsub v hv) W rfl rfl hx hy
  · exact disjoint_left.mpr fun x h₁ h₂ ↦ disjoint_left.mp (hdisj v hv v' hv' hne') h₁ h₂
  · obtain ⟨s, hs, hes, hbs, -⟩ := hb.border he hB
    obtain ⟨x, hxe⟩ : (b e).Nonempty := (hb.mem e he).1
    have hbe : Painting.IsBorder (b e) := ⟨x, hxe, (hs.2.1 (hbs hxe)).1⟩
    refine ⟨hbe, fun s' hs' ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · obtain ⟨y, hy⟩ : e.Nonempty := he.1
      rw [← GM11.arcComponent_eq hs hs' (hes hy) (h hy)]
      exact hbs
    · rw [← GM11.arcComponent_eq hs hs' (hbs hxe) (h hxe)]
      exact hes
  · rcases hb.internal_le e he hi with ⟨-, h⟩ | ⟨h', -⟩
    · exact h
    · omega
  · rcases hb.internal_le e he hi with ⟨h', -⟩ | ⟨-, h⟩
    · omega
    · exact h
  · obtain ⟨s', hs', hes, -, hle⟩ := hb.border he hbs.1
    obtain ⟨y, hy⟩ : e.Nonempty := he.1
    rw [GM11.arcComponent_eq hs hs' (hbs.2 hy) (hes hy)]
    exact hle

end GraphMinor.GM19
