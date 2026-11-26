/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Bound

/-!
# A triangulation as a drawing

A graph in a surface gives a drawing (`IsGraph.toDrawing`). A triangulation of a connected closed
surface `S`, drawn this way, has no loops, no parallel edges, and no vertex that cuts it, and its
number of edges is `3 |V| - 6 + 3 κ`, where `2 ^ κ` is the number of classes of local cocycles of
`S` (`exists_triang_drawing`). This is the drawing `H` in the proof of Graph Minors XIX, (6.5) (page
341).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

local notation "K" => ZMod 2

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem isPathConnected_edge {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    IsPathConnected (L \ {u, v}) :=
  h.isPathConnected_interior

namespace IsGraphD

variable {V : Set S} {E : Set (Set S)}

omit [T2Space S] in
theorem inner_nonempty (h : IsGraph V E) {e : Set S} (he : e ∈ E) : (e \ V).Nonempty := by
  obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
  have h2 := hl.subset_closure_diff
  have hne : (e \ {u, v}).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    rw [hc, closure_empty] at h2
    obtain ⟨f, h0, -⟩ := id hl
    exact h2 (h0 ▸ (f 0).2)
  obtain ⟨x, hx, hxn⟩ := hne
  exact ⟨x, hx, fun hxV => hxn (hi ▸ ⟨hx, hxV⟩)⟩

omit [T2Space S] in
theorem diff_eq (_h : IsGraph V E) {e : Set S} {u v : S} (hi : e ∩ V = {u, v}) : e \ V = e \ {u, v}
  := by
  ext x
  constructor
  · exact fun hx => ⟨hx.1, fun h' => hx.2 ((hi ▸ h' : x ∈ e ∩ V).2)⟩
  · exact fun hx => ⟨hx.1, fun h' => hx.2 (hi ▸ ⟨hx.1, h'⟩)⟩

theorem closure_diff (h : IsGraph V E) {e : Set S} (he : e ∈ E) : closure (e \ V) = e := by
  obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
  rw [diff_eq h hi]
  exact Subset.antisymm (closure_minimal sdiff_subset hl.isCompact.isClosed) hl.subset_closure_diff

theorem arcComponents_eq (h : IsGraph V E) : arcComponentsIn (gr V E \ V) = (fun e => e \ V) '' E
  := by
  have hmem : ∀ e ∈ E, e \ V ∈ arcComponentsIn (gr V E \ V) := fun e he => by
    obtain ⟨u, v, _, hl, hi⟩ := h.edge e he
    have hne := inner_nonempty h
      he
    have hs : e \ V ⊆ gr V E \ V := fun x hx => ⟨.inr ⟨e, he, hx.1⟩, hx.2⟩
    refine ⟨hne, hs, ?_, fun D hD hc hsub => ?_⟩
    · rw [diff_eq h hi]
      exact isPathConnected_edge hl
    have hclosed : ∀ f ∈ E, IsClosed f := fun f hf => by
      obtain ⟨p, q, -, hl', -⟩ := h.edge f hf
      exact hl'.isCompact.isClosed
    have hO : IsClosed (⋃₀ (E \ {e})) := (h.fine.subset sdiff_subset).isClosed_sUnion fun f hf
      => hclosed f hf.1
    have hcov : D ⊆ e ∪ ⋃₀ (E \ {e}) := fun y hy => by
      obtain ⟨hyG, hyV⟩ := hD hy
      rcases hyG with hy' | ⟨f, hf, hyf⟩
      · exact absurd hy' hyV
      · by_cases hfe : f = e
        · exact .inl (hfe ▸ hyf)
        · exact .inr ⟨f, ⟨hf, hfe⟩, hyf⟩
    refine Subset.antisymm (fun y hy => ?_) hsub
    have hyV := (hD hy).2
    rcases hcov hy with hye | ⟨f, hf, hyf⟩
    · exact ⟨hye, hyV⟩
    · exfalso
      obtain ⟨x, hx⟩ :=
        hne
      obtain ⟨z, hzD, hze, g, hg, hzg⟩ :=
        isPreconnected_closed_iff.mp hc.isConnected.isPreconnected _ _ (hclosed e he) hO hcov
          ⟨x, hsub hx, hx.1⟩ ⟨y, hy, f, hf, hyf⟩
      exact (hD hzD).2 (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hze, hzg⟩)
  refine Subset.antisymm (fun c hc => ?_) ?_
  · obtain ⟨x, hx⟩ := hc.1
    obtain ⟨hxG, hxV⟩ := hc.2.1 hx
    rcases hxG with hx' | ⟨e, he, hxe⟩
    · exact absurd hx' hxV
    · exact ⟨e, he, arcComp_eq_of_mem (hmem e he) hc ⟨hxe, hxV⟩ hx⟩
  · rintro _ ⟨e, he, rfl⟩
    exact hmem e he

end IsGraphD

open IsGraphD in
/-- The drawing of a graph. -/
def _root_.GraphMinor.Surface.IsGraph.toDrawing {V : Set S} {E : Set (Set S)}
  (h : IsGraph V E) : Drawing S where
  U := gr V E
  V := V
  V_subset_U := subset_union_left
  isClosed_U := h.isClosed_gr
  finite_V := h.fin
  finite_edges := by
    rw [arcComponents_eq h]
    exact h.fine.image _
  edge_cond := fun c hc => by
    rw [arcComponents_eq h] at hc
    obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
    refine .inl ⟨u, v, huv, ?_, ?_⟩
    · simp only [closure_diff h he, hi]
    · simp only [closure_diff h he, hl]

open IsGraphD in
/-- **A triangulation as a drawing.** See the module docstring. -/
theorem exists_triang_drawing {S : Type} [TopologicalSpace S] [T2Space S]
  (hT : IsClosedSurface S) [ConnectedSpace S] :
    ∃ H : Drawing S, LoopFree H ∧ (∀ e ∈ H.E, ∀ f ∈ H.E, tilde e = tilde f → e = f) ∧ 3 ≤ H.V.ncard
      ∧ 3 ≤ H.E.ncard ∧ (∀ v ∈ H.V, ConnIn H (H.V \ {v})) ∧
      ∃ κ : ℕ, Nat.card (KCl S K) = 2 ^ κ ∧ (H.E.ncard : ℤ) = 3 * H.V.ncard - 6 + 3 * κ := by
  classical
  obtain ⟨V₁, E₁, 𝓕₁, hdis⟩ := exists_surface_dissection hT.isSurface
  have hne : Nonempty S := ‹ConnectedSpace S›.toNonempty
  obtain ⟨V, E, 𝓕, h, -, -, -⟩ := hdis.exists_triang
  have hg : IsGraph V E := h.dis.graph
  have hE : (hg.toDrawing).E = (fun e => e \ V) '' E := arcComponents_eq hg
  have ht : ∀ e ∈ E, tilde (e \ V) = e ∩ V := fun e he => by
    change closure (e \ V) \ (e \ V) = e ∩ V
    rw [closure_diff hg he]
    ext x
    simp only [mem_sdiff, mem_inter_iff, not_and, not_not]
    exact ⟨fun h' => ⟨h'.1, h'.2 h'.1⟩, fun h' => ⟨h'.1, fun _ => h'.2⟩⟩
  have hinj : InjOn (fun e => e \ V) E := fun e he f hf hef => by
    have h1 : closure (e \ V) = closure (f \ V) := congrArg closure hef
    rwa [closure_diff hg he, closure_diff hg hf] at h1
  have hEn : (hg.toDrawing).E.ncard = E.ncard := by
    rw [hE, hinj.ncard_image]
  have := h.dis.graph.fin.fintype
  have := h.dis.graph.fine.fintype
  have := h.dis.fin.fintype
  obtain ⟨κ, h1, h2⟩ := h.euler_ncard hT
  have h3 := (h.cx hT).three_faces
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq] at h3
  obtain ⟨Φ, hΦ⟩ := h.nonempty_faces
  have hFpos : 0 < 𝓕.ncard := (ncard_pos h.dis.fin).mpr ⟨Φ, hΦ⟩
  have hV3 : 3 ≤ V.ncard := by
    have h4 := h.three Φ hΦ
    have h5 := ncard_le_ncard (inter_subset_right : Φ ∩ V ⊆ V) h.dis.graph.fin
    omega
  refine ⟨hg.toDrawing, ?_, ?_, hV3, ?_, ?_, κ, h1, ?_⟩
  · intro c hc
    rw [hE] at hc
    obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨u, v, huv, hl, hi⟩ := hg.edge e he
    exact ⟨u, v, huv, by rw [ht e he, hi], by rwa [closure_diff hg he]⟩
  · intro c hc d hd hcd
    rw [hE] at hc hd
    obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨f, hf, rfl⟩ := hd
    rw [ht e he, ht f hf] at hcd
    rw [h.simple e he f hf hcd]
  · rw [hEn]
    omega
  · intro v hv Y hY hYne hYc
    have hv' : v ∈ V := hv
    have hsub := h.conn_minus hT hv' (S := Y) (fun e he a ha b hb haw hbw haY => by
      by_cases hab : a = b
      · exact hab ▸ haY
      · refine hYc a haY b ⟨hb.2, hbw⟩ ⟨hab, ha.2, hb.2, e \ V, hE ▸ mem_image_of_mem _ he, ?_, ?_⟩
        · rw [ht e he]
          exact ha
        · rw [ht e he]
          exact hb) (by
      obtain ⟨y, hy⟩ := hYne
      exact ⟨y, hy, hY hy⟩)
    exact Subset.antisymm hY hsub
  · rw [hEn]
    change (E.ncard : ℤ) = 3 * V.ncard - 6 + 3 * κ
    omega

end GraphMinor.GM19
