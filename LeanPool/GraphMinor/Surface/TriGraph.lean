/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TriPath
public import LeanPool.GraphMinor.Surface.TriCohGlue

/-!
# Simple graphs in a surface

A simple graph with at least three edges inside a triangulation has at most `3 |V| - 3 χ` edges,
where `χ` is the value of `|V| - |E| + |F|` on the triangulation (`IsTriang.graph_bound`). This is
the count named in the proof of Graph Minors XIX, (6.5) (page 341). By `IsTriang.euler_eq` the
number `χ` depends only on the surface.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

local notation "K" => ZMod 2

/-- Pull back a set to a subtype and count the elements in the intersection. -/
theorem ncard_coe_preimage {α : Type*} (V A : Set α) :
    ({v : V | v.1 ∈ A}).ncard = (A ∩ V).ncard :=
  ncard_val_preimage V A

variable {X : Type} [TopologicalSpace X] [T2Space X]

namespace IsTriang

variable {V : Set X} {E 𝓕 : Set (Set X)}

theorem euler_ncard (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] :
    ∃ κ : ℕ, Nat.card (KCl X K) = 2 ^ κ ∧ (V.ncard : ℤ) - E.ncard + 𝓕.ncard + κ = 2 := by
  classical
  have := h.dis.graph.fin.fintype
  have := h.dis.graph.fine.fintype
  have := h.dis.fin.fintype
  obtain ⟨κ, h1, h2⟩ := h.euler_eq hT
  refine ⟨κ, h1, ?_⟩
  rw [← Nat.card_coe_set_eq V, ← Nat.card_coe_set_eq E, ← Nat.card_coe_set_eq 𝓕,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact h2

/-- No vertex cuts the graph of a triangulation: a part of the graph without `w`, closed under the
edges that miss `w`, is all of it. The neighbours of `w` lie on one cycle, by `IsTriang.link_conn`.
-/
theorem conn_minus (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {w : X}
  (hw : w ∈ V) {S : Set X}
    (hS : ∀ e ∈ E, ∀ a ∈ e ∩ V, ∀ b ∈ e ∩ V, a ≠ w → b ≠ w → a ∈ S → b ∈ S) (hne : (S ∩
      (V \ {w})).Nonempty) : V \ {w} ⊆ S := by
  classical
  have := h.dis.graph.fin.fintype
  have := h.dis.graph.fine.fintype
  have := h.dis.fin.fintype
  have hF1 : ∀ Φ ∈ 𝓕, ∀ a ∈ Φ ∩ V, ∀ b ∈ Φ ∩ V, a ≠ w → b ≠ w → a ∈ S → b ∈ S
    := fun Φ hΦ a ha b hb haw hbw has => by
    by_cases hab : a = b
    · exact hab ▸ has
    · obtain ⟨e, he, -, hi⟩ := h.face_pair hΦ ha hb hab
      have h1 : a ∈ e ∩ V := hi ▸ .inl rfl
      have h2 : b ∈ e ∩ V := hi ▸ .inr rfl
      exact hS e he a h1 b h2 haw hbw has
  let N : Set X := {y | y ∈ V ∧ y ≠ w ∧ ∃ e ∈ E, w ∈ e ∧ y ∈ e}
  let 𝓐 : Set (Set X) := {Φ | Φ ∈ 𝓕 ∧ w ∈ Φ ∧ ∀ z ∈ Φ ∩ V, z ≠ w → z ∈ S}
  have hmem𝓐 : ∀ Φ ∈ 𝓕, w ∈ Φ → ∀ z ∈ Φ ∩ V, z ≠ w → z ∈ S → Φ ∈ 𝓐 := fun Φ hΦ hwΦ z hz hzw hzS =>
    ⟨hΦ, hwΦ, fun t ht htw => hF1 Φ hΦ z hz t ht hzw htw hzS⟩
  have hall : ∀ x ∈ N, x ∈ S → N ⊆ S := by
    rintro x ⟨hxV, hxw, e₀, he₀, hwe₀, hxe₀⟩ hxS y ⟨hyV, hyw, e₁, he₁, hwe₁, hye₁⟩
    obtain ⟨Φ₀, -, -, hΦ₀, hsub₀, -⟩ := h.exists_edge_face ⟨e₀, he₀⟩
    obtain ⟨Φ₁, -, -, hΦ₁, hsub₁, -⟩ := h.exists_edge_face ⟨e₁, he₁⟩
    have h0 : Φ₀ ∈ 𝓐 := hmem𝓐 Φ₀ hΦ₀ (hsub₀ hwe₀) x ⟨hsub₀ hxe₀, hxV⟩ hxw hxS
    have hl : Φ₁ ∈ 𝓐 := h.link_conn hT hw (𝓐 := 𝓐) (fun Φ hΦ => hΦ.1) (fun Φ hΦ => hΦ.2.1)
      (fun e he hwe Φ hΦ Φ' hΦ' hs hs' => by
      obtain ⟨p, q, hpq, -, hi⟩ := h.dis.graph.edge e he
      have hwi : w ∈ e ∩ V := ⟨hwe, hw⟩
      have hpm : p ∈ e ∩ V := hi ▸ .inl rfl
      have hqm : q ∈ e ∩ V := hi ▸ .inr rfl
      obtain ⟨z, hz, hzw⟩ : ∃ z ∈ e ∩ V, z ≠ w := by
        by_cases hp : p = w
        · exact ⟨q, hqm, fun hq => hpq (hp.trans hq.symm)⟩
        · exact ⟨p, hpm, hp⟩
      exact hmem𝓐 Φ' hΦ' (hs' hwe) z ⟨hs' hz.1, hz.2⟩ hzw (hΦ.2.2 z ⟨hs hz.1, hz.2⟩ hzw)) ⟨Φ₀,
        h0⟩ hΦ₁ (hsub₁ hwe₁)
    exact hl.2.2 y ⟨hsub₁ hye₁, hyV⟩ hyw
  obtain ⟨a₀, ha₀S, ha₀V⟩ := hne
  by_cases hN : (N ∩ S).Nonempty
  · obtain ⟨x, hxN, hxS⟩ := hN
    have hNS := hall x hxN hxS
    have hV : V ⊆ S ∪ {w} := h.graph_conn (S := S ∪ {w}) (fun e he a ha b hb has => by
      by_cases hbw : b = w
      · exact .inr hbw
      by_cases haw : a = w
      · subst haw
        exact .inl (hNS ⟨hb.2, hbw, e, he, ha.1, hb.1⟩)
      · exact .inl (hS e he a ha b hb haw hbw (has.resolve_right haw))) ⟨a₀, .inl ha₀S, ha₀V.1⟩
    exact fun y hy => (hV hy.1).resolve_right hy.2
  · exfalso
    have hV : V ⊆ S \ {w} := h.graph_conn (S := S \ {w}) (fun e he a ha b hb has => by
      have hbw : b ≠ w := fun hbw => hN ⟨a, ⟨ha.2, has.2, e, he, hbw ▸ hb.1, ha.1⟩, has.1⟩
      exact ⟨hS e he a ha b hb has.2 hbw has.1, hbw⟩) ⟨a₀, ⟨ha₀S, ha₀V.2⟩, ha₀V.1⟩
    exact (hV hw).2 rfl

/-- **The edge bound in a surface.** -/
theorem graph_bound (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {V₀ : Set X}
  {E₀ : Set (Set X)}
    (hg : IsGraph V₀ E₀) (hV : V₀ ⊆ V) (hU : ⋃₀ E₀ ⊆ ⋃₀ E) (hs : ∀ e ∈ E₀, ∀ f ∈ E₀, e ∩ V₀
      = f ∩ V₀ → e = f)
    (h3 : 3 ≤ E₀.ncard) : (E₀.ncard : ℤ) ≤ 3 * V₀.ncard - 3 * ((V.ncard : ℤ) - E.ncard + 𝓕.ncard)
      := by
  classical
  have := h.dis.graph.fin.fintype
  have := h.dis.graph.fine.fintype
  have := h.dis.fin.fintype
  have := hg.fine.fintype
  have hne𝓕 := h.nonempty_faces
  have hdata : ∀ i : E₀, ∃ (u v : X) (Y : Set (Set X)), u ≠ v ∧ IsLineWithEnds i.1 u v ∧ i.1 ∩ V₀
    = {u, v} ∧ Y ⊆ E ∧
      (∀ x ∈ Y, x ⊆ i.1) ∧ ⋃₀ Y = i.1 ∧ ((i.1 ∩ V) \ {u, v}).ncard + 1 ≤ Y.ncard ∧
      (∀ w ∈ (i.1 ∩ V) \ {u, v}, {x ∈ Y | w ∈ x}.ncard ≤ 2) ∧ {x ∈ Y | u ∈ x}.ncard = 1
        ∧ {x ∈ Y | v ∈ x}.ncard = 1 := fun i => by
    obtain ⟨u, v, huv, hl, hi⟩ := hg.edge i.1 i.2
    have hu : u ∈ i.1 ∩ V₀ := hi ▸ Or.inl rfl
    have hv : v ∈ i.1 ∩ V₀ := hi ▸ Or.inr rfl
    obtain ⟨Y, h1, h2, h4, h5, h6, h7, h8⟩ := h.dis.graph.exists_subdiv _ rfl hl huv (hV hu.2)
      (hV hv.2)
      (fun y hy => .inr (hU ⟨i.1, i.2, hy⟩))
    exact ⟨u, v, Y, huv, hl, hi, h1, h2, h4, h5, h6, h7, h8⟩
  choose u v Y₀ huv hl hi hYE hYs hYU hYc hYd hYu hYv using hdata
  let Y : E₀ → Set E := fun i => {x | x.1 ∈ Y₀ i}
  let Int : E₀ → Set V := fun i => {w | w.1 ∈ (i.1 ∩ V) \ {u i, v i}}
  let D : E₀ → Set V := fun i => {w | w.1 ∈ i.1 ∩ V₀}
  have hcard : ∀ i, (Int i).ncard + 1 ≤ (Y i).ncard := fun i => by
    have h1 : (Int i).ncard = ((i.1 ∩ V) \ {u i, v i}).ncard := by
      rw [ncard_coe_preimage]
      congr 1
      ext y
      exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.1.2⟩⟩
    have h2 : (Y i).ncard = (Y₀ i).ncard := by
      rw [ncard_coe_preimage, inter_eq_left.mpr (hYE i)]
    rw [h1, h2]
    exact hYc i
  have hne : ∀ i, ∃ x, x ∈ Y₀ i ∧ u i ∈ x := fun i => by
    obtain ⟨x, hx⟩ := ncard_eq_one.mp (hYu i)
    have : x ∈ {x ∈ Y₀ i | u i ∈ x} := hx ▸ rfl
    exact ⟨x, this.1, this.2⟩
  have hcl : ∀ i, ∀ x ∈ Y₀ i, IsClosed x := fun i x hx => by
    obtain ⟨p, q, -, hl', -⟩ := h.dis.graph.edge x (hYE i hx)
    exact hl'.isCompact.isClosed
  have hend : ∀ i j : E₀, i ≠ j → ∀ w ∈ i.1, w ∈ j.1 → w ∈ V₀ := fun i j hij w h1 h2 =>
    hg.disj i.1 i.2 j.1 j.2 (fun h' => hij (Subtype.ext h')) ⟨h1, h2⟩
  have hS : (h.cx hT).Subdiv Y Int D := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      refine Set.disjoint_left.mpr fun x h1 h2 => ?_
      obtain ⟨y, hy, hyV⟩ := h.exists_inner x.2
      exact hyV (hV (hend i j hij y (hYs i _ h1 hy) (hYs j _ h2 hy)))
    · intro i
      obtain ⟨x, hx, -⟩ := hne i
      exact ⟨⟨x, hYE i hx⟩, hx⟩
    · intro i S hSs hSne hSn
      let A : Set (Set X) := Subtype.val '' S
      let B : Set (Set X) := Y₀ i \ A
      have hAs : A ⊆ Y₀ i := by
        rintro _ ⟨x, hx, rfl⟩
        exact hSs hx
      have hfin : (Y₀ i).Finite := h.dis.graph.fine.subset (hYE i)
      have hAc : IsClosed (⋃₀ A) := (hfin.subset hAs).isClosed_sUnion fun x hx => hcl i x (hAs hx)
      have hBc : IsClosed (⋃₀ B) := (hfin.subset sdiff_subset).isClosed_sUnion fun x hx
        => hcl i x hx.1
      have hBne : B.Nonempty := by
        by_contra hc
        rw [not_nonempty_iff_eq_empty] at hc
        apply hSn
        refine Subset.antisymm hSs fun x hx => ?_
        have h1 : x.1 ∈ Y₀ i := hx
        by_contra h2
        have h3 : x.1 ∈ B := ⟨h1, fun ⟨y, hy, h4⟩ => h2 ((Subtype.ext h4 : y = x) ▸ hy)⟩
        rw [hc] at h3
        exact h3
      obtain ⟨x₁, hx₁⟩ := hBne
      obtain ⟨x₀, hx₀⟩ := hSne
      obtain ⟨y₀, hy₀, -⟩ := h.exists_inner x₀.2
      obtain ⟨y₁, hy₁, -⟩ := h.exists_inner (hYE i hx₁.1)
      obtain ⟨z, hz, ⟨a, ha, hza⟩, ⟨b, hb, hzb⟩⟩ := isPreconnected_closed_iff.mp
        (hl i).isPreconnected_self _ _ hAc hBc (fun y hy => by
        have : y ∈ ⋃₀ Y₀ i := by rwa [hYU i]
        obtain ⟨x, hx, hyx⟩ := this
        by_cases hxA : x ∈ A
        · exact .inl ⟨x, hxA, hyx⟩
        · exact .inr ⟨x, ⟨hx, hxA⟩, hyx⟩) ⟨y₀, hYs i _ (hSs hx₀) hy₀, x₀.1, ⟨x₀, hx₀, rfl⟩, hy₀⟩
        ⟨y₁, hYs i _ hx₁.1 hy₁, x₁, hx₁, hy₁⟩
      have hne' : a ≠ b := fun h' => hb.2 (h' ▸ ha)
      have hzV : z ∈ V := h.dis.graph.disj a (hYE i (hAs ha)) b (hYE i hb.1) hne' ⟨hza, hzb⟩
      have huniq : ∀ {c : X}, {x ∈ Y₀ i | c ∈ x}.ncard = 1 → c ≠ z := fun {c} hc hcz => by
        obtain ⟨x, hx⟩ := ncard_eq_one.mp hc
        have h1 : a ∈ {x ∈ Y₀ i | c ∈ x} := ⟨hAs ha, hcz ▸ hza⟩
        have h2 : b ∈ {x ∈ Y₀ i | c ∈ x} := ⟨hb.1, hcz ▸ hzb⟩
        rw [hx] at h1 h2
        exact hne' (h1.trans h2.symm)
      obtain ⟨a', ha', rfl⟩ := ha
      refine ⟨⟨z, hzV⟩, ⟨⟨hz, hzV⟩, ?_⟩, a', ha', ⟨b, hYE i hb.1⟩, ⟨hb.1, fun h' => hb.2 ⟨_, h',
        rfl⟩⟩, hza, hzb⟩
      rintro (h1 | h1)
      · exact huniq (hYu i) h1.symm
      · exact huniq (hYv i) h1.symm
    · intro i w hw
      have hsub : Subtype.val '' {x : E | (∃ j, x ∈ Y j) ∧ w ∈ (h.cx hT).ends x} ⊆ {x ∈ Y₀ i | w.1
        ∈ x} := by
        rintro _ ⟨x, ⟨⟨j, hj⟩, hwx⟩, rfl⟩
        have hwx' : w.1 ∈ x.1 := hwx
        have hji : j = i := by
          by_contra hne'
          have h1 : w.1 ∈ V₀ := hend i j (Ne.symm hne') w.1 hw.1.1 (hYs j _ hj hwx')
          have h2 : w.1 ∈ ({u i, v i} : Set X) := hi i ▸ ⟨hw.1.1, h1⟩
          exact hw.2 h2
        subst hji
        exact ⟨hj, hwx'⟩
      have h1 := ncard_le_ncard hsub ((h.dis.graph.fine.subset (hYE i)).subset fun x hx => hx.1)
      rw [ncard_image_of_injective _ Subtype.val_injective] at h1
      exact h1.trans (hYd i w.1 hw)
    · intro i w hw
      have hE : {x ∈ Y i | w ∈ (h.cx hT).ends x}.ncard = {x ∈ Y₀ i | w.1 ∈ x}.ncard := by
        have h1 := ncard_coe_preimage E {x ∈ Y₀ i | w.1 ∈ x}
        rw [inter_eq_left.mpr fun x (hx : x ∈ {x ∈ Y₀ i | w.1 ∈ x}) => hYE i hx.1] at h1
        exact h1
      rw [hE]
      have h2 : w.1 ∈ ({u i, v i} : Set X) := hi i ▸ hw
      rcases h2 with h2 | h2
      · rw [h2]
        exact hYu i
      · rw [h2]
        exact hYv i
    · intro i j w hw hwn x hx hwx
      exact hwn ⟨hYs j _ hx hwx, hw.2⟩
    · intro i
      have h1 : (D i).ncard = ((i.1 ∩ V₀) ∩ V).ncard := ncard_coe_preimage V (i.1 ∩ V₀)
      have h2 : (i.1 ∩ V₀) ∩ V = i.1 ∩ V₀ := inter_eq_left.mpr fun y hy => hV hy.2
      rw [h1, h2, hi i, ncard_pair (huv i)]
    · intro i j hij
      have hij' : {w : V | w.1 ∈ i.1 ∩ V₀} = {w : V | w.1 ∈ j.1 ∩ V₀} := hij
      refine Subtype.ext (hs i.1 i.2 j.1 j.2 ?_)
      ext y
      constructor
      · intro hy
        have : (⟨y, hV hy.2⟩ : V) ∈ {w : V | w.1 ∈ j.1 ∩ V₀} := hij' ▸ hy
        exact this
      · intro hy
        have : (⟨y, hV hy.2⟩ : V) ∈ {w : V | w.1 ∈ i.1 ∩ V₀} := hij'.symm ▸ hy
        exact this
  have hI : 3 ≤ Fintype.card E₀ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact h3
  have hVne : ({w : V | w.1 ∈ V₀} : Set V).Nonempty := by
    obtain ⟨i⟩ : Nonempty E₀ := Fintype.card_pos_iff.mp (by omega)
    have hu : u i ∈ i.1 ∩ V₀ := hi i ▸ Or.inl rfl
    exact ⟨⟨u i, hV hu.2⟩, hu.2⟩
  have hb := (h.cx hT).edges_le hS hI hVne (fun i x hx w hw => by
    have hw' : w.1 ∈ x.1 := hw
    by_cases h1 : w.1 ∈ ({u i, v i} : Set X)
    · have h2 : w.1 ∈ i.1 ∩ V₀ := (hi i).symm ▸ h1
      exact .inl h2.2
    · exact .inr (mem_iUnion.mpr ⟨i, ⟨hYs i _ hx hw', w.2⟩, h1⟩)) hcard
  have e0 : ({w : V | w.1 ∈ V₀} : Set V).ncard = V₀.ncard := by
    rw [ncard_coe_preimage, inter_eq_left.mpr hV]
  rw [e0] at hb
  rw [← Nat.card_coe_set_eq E₀, ← Nat.card_coe_set_eq V, ← Nat.card_coe_set_eq E,
    ← Nat.card_coe_set_eq 𝓕, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hb

end IsTriang

end GraphMinor.Surface
