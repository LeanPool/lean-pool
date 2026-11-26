/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.FlatEdges
public import LeanPool.GraphMinor.GM07.GoodEdge

/-!
# A smallest graph with a flat complement

This file is the middle part of the proof of (4.3) of Graph Minors VII (pages 222 and 223). The
paper takes a maximal flat set `Y`. Here we take instead a smallest subgraph `K` of `G`, avoiding a
given set of vertices, for which the set `offSet K`, the part of the surface off `U(K)` and off
`bd(Σ)`, is flat. Then `offSet K` is the set `Y` of the paper, and maximal `Y` means smallest `K`.

The two facts on `Y` in the paper are `isPreconnected_offSet`, which says that `Y` is connected, and
`disc_subset_offSet`, which says that every closed disc with boundary in `Y` lies in `Y`. For the
first,
an edge with different components of `Y` on its two sides can be added to `Y`, by
`IsFlat.union_bridge`. If there is no such edge, then the components of `Y` extend over the edges to
a partition
of the surface without its vertices and cuffs, and this set is connected. For the second, `Y ∪ Δ` is
flat by (11.3).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- The part of the surface off a graph and off the boundary. -/
def offSet (K : Drawing S) : Set S := (K.U ∪ bd S)ᶜ

theorem mem_offSet {K : Drawing S} {z : S} : z ∈ offSet K ↔ z ∉ K.U ∧ z ∉ bd S := by
  simp [offSet]

theorem isOpen_offSet (hS : IsSurface S) (K : Drawing S) : IsOpen (offSet K) :=
  (K.isClosed_U.union (cuff_statement.{0} S hS).1).isOpen_compl

/-- A connected open set of a surface is path-connected. -/
theorem isPathConnected_of_isOpen (hS : IsSurface S) {Z : Set S} (ho : IsOpen Z)
  (hc : IsConnected Z) : IsPathConnected Z := by
  have ht2 : T2Space S := hS.2.1
  have h := isArcConnected_iff_joinedIn.mp (theorem_11_4_proof hS hc
    (isLocallyArcConnected_of_isOpen hS ho))
  exact isPathConnected_iff.mpr ⟨hc.1, h⟩

/-- A point `p` of an edge `e` of a proper graph `K` lies inside a closed disc that meets `offSet K`
in two path-connected sides `A` and `B`, with `p` in the closure of both. If `offSet K` stays flat
when we add the inside of
the disc, then it also stays flat when we add `e`. For an edge that is a line the disc holds all of
`e`. For a loop the disc holds only a piece of `e`, and we add the rest with `IsFlat.union_loop`. -/
theorem exists_edge_sides (hS : IsSurface S) {K : Drawing S} (hK : K.IsProper) {e : Set S}
  (he : e ∈ K.E) {p : S} (hp : p ∈ e) :
    ∃ Δ A B : Set S, IsClosedDisc Δ ∧ IsOpen (Δ \ discBd Δ) ∧ p ∈ Δ \ discBd Δ ∧ A ⊆ offSet K
      ∧ B ⊆ offSet K ∧ A ⊆ Δ \ discBd Δ ∧ B ⊆ Δ \ discBd Δ ∧
      offSet K ∩ (Δ \ discBd Δ) ⊆ A ∪ B ∧ IsPathConnected A ∧ IsPathConnected B ∧ p ∈ closure A
        ∧ p ∈ closure B ∧
      (IsFlat (offSet K ∪ (Δ \ discBd Δ)) → IsFlat (offSet K ∪ e)) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hdiff : closure e \ K.V = e := K.closure_diff_V he
  have hclU : closure e ⊆ K.U := K.closure_subset_U he
  have hoff : ∀ z ∈ e, z ∉ K.V := fun z hz => by
    have h : z ∈ closure e \ K.V := by
      rw [hdiff]
      exact hz
    exact h.2
  have hinV : ∀ z ∈ closure e, z ∉ e → z ∈ K.V := fun z h1 h2 => by
    by_contra h3
    apply h2
    rw [← hdiff]
    exact ⟨h1, h3⟩
  obtain ⟨R, R', a, b, hl, hR'c, hRu, hRi, hpR, hpa, hpb, hRV, hcase⟩ : ∃ (R R' : Set S)
    (a b : S), IsLineWithEnds R a b ∧ IsClosed R' ∧ R ∪ R' = closure e ∧ R ∩ R' ⊆ {a, b} ∧ p ∈ R
      ∧ p ≠ a ∧ p ≠ b ∧
      R ∩ K.V ⊆ {a, b} ∧ (e ⊆ R \ {a, b} ∨ ∃ u, closure e ∩ K.V = {u} ∧ IsOArc (closure e)) := by
    rcases K.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hcap, hO⟩
    · have hne : ∀ z ∈ e, z ∉ ({u, v} : Set S) := fun z hz h => hoff z hz (hcap.symm.subset h).2
      refine ⟨closure e, ∅, u, v, hl, isClosed_empty, by simp, by simp, subset_closure hp,
        fun h => hne p hp (.inl h), fun h => hne p hp (.inr h), hcap.subset,
        .inl fun z hz => ⟨subset_closure hz, hne z hz⟩⟩
    · have hu : u ∈ closure e ∩ K.V := by
        rw [hcap]
        rfl
      have hup : u ≠ p := fun h => hoff p hp (h ▸ hu.2)
      obtain ⟨P, Q, hP, hQ, hPQ, hPQi⟩ := hO.lines hu.1 (subset_closure hp) hup
      obtain ⟨c, hc⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hP
      obtain ⟨d, hd⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hQ
      obtain ⟨R, R', hR, hR'c, hu', hi, hwR, hxR⟩ := exists_piece_around hO hP hQ hPQ hPQi hc hd
      refine ⟨R, R', c, d, hR, hR'c, hu', hi, hwR, fun h => hc.2 (.inr h.symm),
        fun h => hd.2 (.inr h.symm), fun z hz => ?_, .inr ⟨u, hcap, hO⟩⟩
      have hm : z ∈ closure e ∩ K.V := ⟨hu' ▸ .inl hz.1, hz.2⟩
      rw [hcap] at hm
      obtain rfl : z = u := hm
      exact (hxR hz.1).elim
  have hRs : R ⊆ closure e := hRu ▸ subset_union_left
  have hWc : IsClosed ((K.U \ e) ∪ R') := (isClosed_U_sdiff_edge K he).union hR'c
  have hLW : R ∩ ((K.U \ e) ∪ R') ⊆ {a, b} := by
    rintro z ⟨hz, h | h⟩
    · exact hRV ⟨hz, hinV z (hRs hz) h.2⟩
    · exact hRi ⟨hz, h⟩
  have hLb : R ∩ bd S ⊆ {a, b} := fun z hz => hRV ⟨hz.1, hK ⟨hz.2, hclU (hRs hz.1)⟩⟩
  obtain ⟨Δ, A, B, hΔ, hLD, hDZ, haC, hbC, hDL, hNo, hsub, hAN, hBN, -, hAL, hBL, hAp, hBp, hAc,
    hBc⟩ := exists_line_lens hS hl hWc hLW hLb
  have hends : ∀ z ∈ Δ \ discBd Δ, z ∉ ({a, b} : Set S) := fun z hz h => by
    rcases h with rfl | h
    · exact hz.2 haC
    · exact hz.2 ((mem_singleton_iff.mp h) ▸ hbC)
  have hpN : p ∈ Δ \ discBd Δ := ⟨hLD hpR, fun h => by
    rcases hDL ⟨h, hpR⟩ with h2 | h2
    · exact hpa h2
    · exact hpb h2⟩
  have hinY : ∀ z ∈ Δ \ discBd Δ, z ∉ R → z ∈ offSet K := fun z hz hzR => by
    refine mem_offSet.mpr ⟨fun hU => ?_, fun hb => hends z hz (hDZ ⟨hz.1, .inr hb⟩)⟩
    by_cases hze : z ∈ e
    · have : z ∈ R ∪ R' := hRu ▸ subset_closure hze
      rcases this with h | h
      · exact hzR h
      · exact hends z hz (hDZ ⟨hz.1, .inl (.inr h)⟩)
    · exact hends z hz (hDZ ⟨hz.1, .inl (.inl ⟨hU, hze⟩)⟩)
  have hne : p ∈ R \ {a, b} := ⟨hpR, by simp [hpa, hpb]⟩
  refine ⟨Δ, A, B, hΔ, hNo, hpN, fun z hz => hinY z (hAN hz) (disjoint_left.mp hAL hz), fun z hz
    => hinY z (hBN hz) (disjoint_left.mp hBL hz), hAN, hBN, ?_, hAp, hBp, hAc hne, hBc hne, fun hF
      => ?_⟩
  · rintro z ⟨hz, hzN⟩
    rcases hsub hzN with (h | h) | h
    · exact .inl h
    · exact .inr h
    · exact ((mem_offSet.mp hz).1 (hclU (hRs h))).elim
  · rcases hcase with hs | ⟨u, hcap, hO⟩
    · refine IsFlat.mono hF (union_subset_union_right _ fun z hz => ?_)
      have h2 := hs hz
      refine ⟨hLD h2.1, fun h3 => h2.2 (hDL ⟨h3, h2.1⟩)⟩
    · refine IsFlat.mono (IsFlat.union_loop hS hK hF (fun z h1 h2 => .inl (mem_offSet.mpr ⟨h1,
        h2⟩)) he hcap hO hp (.inr hpN)) ?_
      exact union_subset_union_left _ subset_union_left

/-- **The set `Y` is connected** (Graph Minors VII, page 222). If `offSet K` is flat and cannot take
any edge of `K`, then it is connected. -/
theorem isPreconnected_offSet (hS : IsSurface S) [ConnectedSpace S] {K : Drawing S}
  (hK : K.IsProper) (hY : IsFlat (offSet K)) (hmin : ∀ e ∈ K.E, ¬ IsFlat (offSet K ∪ e)) :
    IsPreconnected (offSet K) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := hS.locallyConnected
  have hYo : IsOpen (offSet K) := isOpen_offSet hS K
  generalize hYdef : offSet K = Y at hY hmin hYo ⊢
  let comp : S → Set S := fun z => connectedComponentIn Y z
  have hco : ∀ z, IsOpen (comp z) := fun z => hYo.connectedComponentIn
  have hcs : ∀ z, comp z ⊆ Y := fun z => connectedComponentIn_subset Y z
  have hself : ∀ z ∈ Y, z ∈ comp z := fun z hz => mem_connectedComponentIn hz
  have hsame : ∀ z w, w ∈ comp z → comp z = comp w := fun z w h => connectedComponentIn_eq h
  have hpcomp : ∀ z ∈ Y, IsPathConnected (comp z) := fun z hz => isPathConnected_of_isOpen hS
    (hco z) ⟨⟨z, hself z hz⟩, isPreconnected_connectedComponentIn⟩
  have hdis : ∀ z w, comp z ≠ comp w → Disjoint (comp z) (comp w) := fun z w hne
    => disjoint_left.mpr fun x h1 h2 => hne ((hsame z x h1).trans (hsame w x h2).symm)
  have hsub : ∀ {A : Set S}, IsPreconnected A → ∀ a ∈ A, A ⊆ Y → A ⊆ comp a := fun hA a ha hs
    => hA.subset_connectedComponentIn ha hs
  have hloc : ∀ p ∈ (bd S)ᶜ \ K.V, (∃ z ∈ Y, ∃ N, IsOpen N ∧ p ∈ N ∧ N ∩ Y ⊆ comp z)
    ∧ p ∈ closure Y := by
    intro p hp
    by_cases hpU : p ∈ K.U
    · obtain ⟨e, he, hpe⟩ : ∃ e ∈ K.E, p ∈ e := by
        rw [K.U_eq] at hpU
        rcases hpU with h | h
        · exact (hp.2 h).elim
        · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp h
          refine ⟨e, he, ?_⟩
          rw [← K.closure_diff_V he]
          exact ⟨hpe, hp.2⟩
      obtain ⟨Δ, A, B, hΔ, hNo, hpN, hAY, hBY, hAN, hBN, hYN, hAp, hBp, hpA, hpB, hflat⟩
        := exists_edge_sides hS hK he hpe
      rw [hYdef] at hAY hBY hYN hflat
      obtain ⟨a, ha⟩ := hAp.nonempty
      obtain ⟨b, hb⟩ := hBp.nonempty
      have hAc := hsub hAp.isConnected.isPreconnected a ha hAY
      have hBc := hsub hBp.isConnected.isPreconnected b hb hBY
      by_cases heq : comp a = comp b
      · refine ⟨⟨a, hAY ha, _, hNo, hpN, fun z hz => ?_⟩, closure_mono hAY hpA⟩
        rcases hYN ⟨hz.2, hz.1⟩ with h | h
        · exact hAc h
        · exact heq ▸ hBc h
      · exfalso
        refine hmin e he (hflat ?_)
        have hd := hdis a b heq
        refine IsFlat.union_bridge hY (hcs a) (hcs b) (hco a) (hco b) (hpcomp a (hAY ha)) (hpcomp b
          (hBY hb)) hd ?_ hΔ hNo hAp hBp ?_ ?_ ?_
        · refine isOpen_iff_forall_mem_open.mpr fun x hx => ⟨comp x, fun y hy => ⟨hcs x hy, ?_⟩,
            hco x, hself x hx.1⟩
          rintro (h | h)
          · exact hx.2 (.inl ((hsame a y h).trans (hsame x y hy).symm ▸ hself x hx.1))
          · exact hx.2 (.inr ((hsame b y h).trans (hsame x y hy).symm ▸ hself x hx.1))
        · refine Subset.antisymm (fun z hz => ⟨hAc hz, hAN hz⟩) fun z hz => ?_
          rcases hYN ⟨hcs a hz.1, hz.2⟩ with h | h
          · exact h
          · exact (disjoint_left.mp hd hz.1 (hBc h)).elim
        · refine Subset.antisymm (fun z hz => ⟨hBc hz, hBN hz⟩) fun z hz => ?_
          rcases hYN ⟨hcs b hz.1, hz.2⟩ with h | h
          · exact (disjoint_left.mp hd (hAc h) hz.1).elim
          · exact h
        · intro z hz
          rcases hYN hz with h | h
          · exact .inl (hAc h)
          · exact .inr (hBc h)
    · have hpY : p ∈ Y := by
        rw [← hYdef]
        exact mem_offSet.mpr ⟨hpU, hp.1⟩
      exact ⟨⟨p, hpY, _, hco p, hself p hpY, inter_subset_left⟩, subset_closure hpY⟩
  rcases Y.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact isPreconnected_empty
  have hYM : Y ⊆ (bd S)ᶜ \ K.V := fun z hz => by
    rw [← hYdef] at hz
    have h := mem_offSet.mp hz
    exact ⟨h.2, fun hv => h.1 (K.V_subset_U hv)⟩
  have hall : ∀ z ∈ Y, comp z = comp z₀ := by
    intro z₁ hz₁
    by_contra hne
    let u : Set S := ⋃₀ {N | IsOpen N ∧ N ∩ Y ⊆ comp z₀}
    let v : Set S := ⋃₀ {N | IsOpen N ∧ ∃ z ∈ Y, comp z ≠ comp z₀ ∧ N ∩ Y ⊆ comp z}
    have huo : IsOpen u := isOpen_sUnion fun N hN => hN.1
    have hvo : IsOpen v := isOpen_sUnion fun N hN => hN.1
    have hcov : (bd S)ᶜ \ K.V ⊆ u ∪ v := fun p hp => by
      obtain ⟨⟨z, hz, N, hNo, hpN, hN⟩, -⟩ := hloc p hp
      by_cases h : comp z = comp z₀
      · exact .inl ⟨N, ⟨hNo, h ▸ hN⟩, hpN⟩
      · exact .inr ⟨N, ⟨hNo, z, hz, h, hN⟩, hpN⟩
    have hz₀u : z₀ ∈ u := ⟨comp z₀, ⟨hco z₀, inter_subset_left⟩, hself z₀ hz₀⟩
    have hz₁v : z₁ ∈ v := ⟨comp z₁, ⟨hco z₁, z₁, hz₁, hne, inter_subset_left⟩, hself z₁ hz₁⟩
    obtain ⟨p, hpM, ⟨N₁, ⟨hN₁o, hN₁⟩, hp₁⟩, ⟨N₂, ⟨hN₂o, z, hz, hc, hN₂⟩, hp₂⟩⟩ :=
      isPreconnected_interior_sdiff_finite hS K.finite_V u v huo hvo hcov ⟨z₀, hYM hz₀, hz₀u⟩ ⟨z₁,
        hYM hz₁, hz₁v⟩
    obtain ⟨y, hy, hyY⟩ := mem_closure_iff.mp (hloc p hpM).2 _ (hN₁o.inter hN₂o) ⟨hp₁, hp₂⟩
    exact hc ((hsame z y (hN₂ ⟨hy.2, hyY⟩)).trans (hsame z₀ y (hN₁ ⟨hy.1, hyY⟩)).symm)
  have heq : Y = comp z₀ := Subset.antisymm (fun z hz => hall z hz ▸ hself z hz) (hcs z₀)
  rw [heq]
  exact isPreconnected_connectedComponentIn

/-- A subgraph of `G` that avoids `X` and has a flat complement. -/
def IsFlatSub (G : Drawing S) (X : Set S) (K : Drawing S) : Prop :=
  K.IsSubdrawing G ∧ Disjoint K.V X ∧ IsFlat (offSet K)

/-- The size of a graph. -/
noncomputable def graphSize (K : Drawing S) : ℕ := K.V.ncard + K.E.ncard

theorem exists_smallest_flatSub {G : Drawing S} {X : Set S} (h : ∃ K, IsFlatSub G X K) : ∃ K,
  IsFlatSub G X K ∧ ∀ K', IsFlatSub G X K' → graphSize K ≤ graphSize K' := by
  classical
  have hex : ∃ n, ∃ K, IsFlatSub G X K ∧ graphSize K = n := by
    obtain ⟨K, hK⟩ := h
    exact ⟨_, K, hK, rfl⟩
  obtain ⟨K, hK, hn⟩ := Nat.find_spec hex
  exact ⟨K, hK, fun K' hK' => hn ▸ Nat.find_min' hex ⟨K', hK', rfl⟩⟩

theorem IsSubdrawing.trans' {A B C : Drawing S} (h : A.IsSubdrawing B)
  (h' : B.IsSubdrawing C) : A.IsSubdrawing C :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- The subgraph of `K` with vertices `V'` and edges `E'`. -/
theorem exists_sub [T1Space S] {K : Drawing S} {V' : Set S} {E' : Set (Set S)} (hV : V' ⊆ K.V)
  (hE : E' ⊆ K.E) (hc : ∀ e ∈ E', closure e ∩ K.V ⊆ V') :
    ∃ K' : Drawing S, K'.IsSubdrawing K ∧ K'.V = V' ∧ K'.E = E' := by
  refine ⟨K.span V' E', K.span_isSubdrawing V' E', ?_, ?_⟩
  · rw [K.span_V]
    unfold Drawing.spanV
    refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset fun e he
      => hc e he.1)) fun z hz => .inl ⟨hz, hV hz⟩
  · rw [K.span_E, inter_eq_left.mpr hE]

/-- A smallest `K` cannot take any edge. -/
theorem not_isFlat_union_edge [T1Space S] {G : Drawing S} {X : Set S} {K : Drawing S}
  (hK : IsFlatSub G X K) (hmin : ∀ K', IsFlatSub G X K' → graphSize K ≤ graphSize K') {e : Set S}
    (he : e ∈ K.E) :
    ¬ IsFlat (offSet K ∪ e) := by
  classical
  intro hF
  obtain ⟨K', hs, hV, hE⟩ := exists_sub (K := K) (V' := K.V) (E' := K.E \ {e}) subset_rfl
    sdiff_subset fun f _ => inter_subset_right
  have hgood : IsFlatSub G X K' := by
    refine ⟨IsSubdrawing.trans' hs hK.1, hV ▸ hK.2.1, IsFlat.mono hF fun z hz => ?_⟩
    have h := mem_offSet.mp hz
    by_cases hzU : z ∈ K.U
    · refine .inr ?_
      rw [K.U_eq] at hzU
      rcases hzU with h1 | h1
      · exact (h.1 (K'.V_subset_U (hV ▸ h1))).elim
      · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp h1
        by_cases hfe : f = e
        · subst hfe
          rw [← K.closure_diff_V hf]
          exact ⟨hzf, fun hv => h.1 (K'.V_subset_U (hV ▸ hv))⟩
        · have hfE : f ∈ K'.E := hE ▸ ⟨hf, hfe⟩
          exact (h.1 (K'.closure_subset_U hfE hzf)).elim
    · exact .inl (mem_offSet.mpr ⟨hzU, h.2⟩)
  have h1 := hmin K' hgood
  have hfin : K.E.Finite := K.finite_edges
  have h2 : K'.E.ncard < K.E.ncard := by
    rw [hE]
    exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h he).2 rfl⟩ hfin
  unfold graphSize at h1
  rw [hV] at h1
  omega

/-- **Every closed disc with boundary in `Y` lies in `Y`** (Graph Minors VII, page 222). -/
theorem disc_subset_offSet (hS : IsSurface S) {G : Drawing S} {X : Set S} {K : Drawing S}
  (hK : IsFlatSub G X K) (hmin : ∀ K', IsFlatSub G X K' → graphSize K ≤ graphSize K') {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hF : discBd Δ ⊆ offSet K) : Δ ⊆ offSet K := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  have hNo : IsOpen (Δ \ discBd Δ) := hΔ.isOpen_discInt hman
  have hΔc : IsClosed Δ := hΔ.isCompact.isClosed
  have hbdΔ : Disjoint Δ (bd S) := disjoint_left.mpr fun z hz hb => by
    by_cases h : z ∈ discBd Δ
    · exact (mem_offSet.mp (hF h)).2 hb
    · exact hb (isInteriorPoint_of_mem_discInt hman hΔ ⟨hz, h⟩)
  have harc : IsArcConnected (offSet K ∩ discBd Δ) := by
    rw [inter_eq_right.mpr hF]
    exact IsOArc.isArcConnected (IsClosedDisc.isOArc_discBd hΔ)
  have hflat : IsFlat (offSet K ∪ Δ) := by
    refine IsFlat.mono ((theorem_11_3_proof hS hΔ harc).2 hK.2.2) (union_subset subset_union_left
      fun z hz => ?_)
    by_cases h : z ∈ discBd Δ
    · exact .inl (hF h)
    · exact .inr ⟨hz, h⟩
  have hV : ∀ v ∈ K.U ∩ Δ, v ∈ Δ \ discBd Δ := fun v hv => ⟨hv.2, fun h => (mem_offSet.mp
    (hF h)).1 hv.1⟩
  obtain ⟨K', hs, hV', hE'⟩ := exists_sub (K := K) (V' := K.V \ Δ) (E' := {f | f ∈ K.E
    ∧ Disjoint f Δ}) sdiff_subset (fun f hf => hf.1) fun f hf v hv => by
    refine ⟨hv.2, fun hvΔ => ?_⟩
    obtain ⟨z, hz, hzf⟩ := mem_closure_iff.mp hv.1 _ hNo (hV v ⟨K.V_subset_U hv.2, hvΔ⟩)
    exact disjoint_left.mp hf.2 hzf hz.1
  have hgood : IsFlatSub G X K' := by
    refine ⟨IsSubdrawing.trans' hs hK.1, hV' ▸ hK.2.1.mono_left sdiff_subset,
      IsFlat.mono hflat fun z hz => ?_⟩
    have h := mem_offSet.mp hz
    by_cases hzU : z ∈ K.U
    · refine .inr ?_
      by_contra hzΔ
      rw [K.U_eq] at hzU
      rcases hzU with h1 | h1
      · exact h.1 (K'.V_subset_U (hV' ▸ ⟨h1, hzΔ⟩))
      · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp h1
        by_cases hd : Disjoint f Δ
        · exact h.1 (K'.closure_subset_U (hE' ▸ ⟨hf, hd⟩) hzf)
        · have hzV : z ∉ K.V := fun hv => h.1 (K'.V_subset_U (hV' ▸ ⟨hv, hzΔ⟩))
          have hzef : z ∈ f := by
            rw [← K.closure_diff_V hf]
            exact ⟨hzf, hzV⟩
          obtain ⟨w, hwf, hwΔ⟩ := not_disjoint_iff.mp hd
          have hfc : IsPreconnected f := isPreconnected_of_edge hf
          have hfU : f ⊆ K.U := fun y hy => K.closure_subset_U hf (subset_closure hy)
          have hcov : f ⊆ (Δ \ discBd Δ) ∪ Δᶜ := fun y hy => by
            by_cases hyΔ : y ∈ Δ
            · exact .inl (hV y ⟨hfU hy, hyΔ⟩)
            · exact .inr hyΔ
          rcases hfc.subset_or_subset hNo hΔc.isOpen_compl (disjoint_left.mpr fun y h1 h2
            => h2 h1.1) hcov with h2 | h2
          · exact hzΔ (h2 hzef).1
          · exact h2 hwf hwΔ
    · exact .inl (mem_offSet.mpr ⟨hzU, h.2⟩)
  by_contra hne
  obtain ⟨z, hzΔ, hzY⟩ := not_subset.mp hne
  have hzU : z ∈ K.U := by
    by_contra h
    exact hzY (mem_offSet.mpr ⟨h, disjoint_left.mp hbdΔ hzΔ⟩)
  have h1 := hmin K' hgood
  have hfV : K.V.Finite := K.finite_V
  have hfE : K.E.Finite := K.finite_edges
  have hle1 : K'.V.ncard ≤ K.V.ncard := by
    rw [hV']
    exact ncard_le_ncard sdiff_subset hfV
  have hle2 : K'.E.ncard ≤ K.E.ncard := by
    rw [hE']
    exact ncard_le_ncard (fun f hf => hf.1) hfE
  unfold graphSize at h1
  have hlt : K'.V.ncard < K.V.ncard ∨ K'.E.ncard < K.E.ncard := by
    rw [K.U_eq] at hzU
    rcases hzU with h2 | h2
    · left
      rw [hV']
      exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h h2).2 hzΔ⟩ hfV
    · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp h2
      by_cases hzV : z ∈ K.V
      · left
        rw [hV']
        exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h hzV).2 hzΔ⟩ hfV
      · right
        have hzef : z ∈ f := by
          rw [← K.closure_diff_V hf]
          exact ⟨hzf, hzV⟩
        rw [hE']
        refine ncard_lt_ncard ⟨fun g hg => hg.1, fun h => ?_⟩ hfE
        exact disjoint_left.mp (h hf).2 hzef hzΔ
  omega

end GraphMinor.GM07
