/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9f

/-!
# Graph Minors XX, Section 9: the realization

This file proves the rest of the proof of (9.1). For each cell `c'` of `Γ'` outside the image of `ζ`
we
choose `δ_{c'} ∈ Δ'(c')` as in the paper (`exists_delta`), and `H` is the union of these groupings
(`realizationGraph`). Every edge of `H` either joins two nodes of one `ζ(n)`, or joins the two `i`th
terms of
the marches at the ends of a border cell outside the image of `ζ` (`adj_cases`). This gives claims
(8) and
(12). Claims (9), (10) and (11) show that each `η(v)` is connected in `H`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

section Main

variable {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
  {A : Side X F Q} {A' : Side X F Q'} {ζn : X.S → Set X.S} {ζc : Set X.S → Set X.S} {K : ℕ}

/-- The grouping `K` of an internal cell `c'`: two of its nodes are adjacent if they lie in one
`ζ(n)`. -/
def innerGrouping (A : Side X F Q) (A' : Side X F Q') (ζn : X.S → Set X.S) (c' : Set X.S) :
    (⊤ : SimpleGraph α).Subgraph where
  verts := A'.h.node '' tilde c'
  Adj x y := x ≠ y ∧ ∃ n ∈ A.Γ.N, ∃ a ∈ ζn n ∩ tilde c', ∃ b ∈ ζn n ∩ tilde c',
    x = A'.h.node a ∧ y = A'.h.node b
  adj_sub h := h.1
  edge_vert := by
    rintro x y ⟨-, n, -, a, ha, b, -, rfl, -⟩
    exact ⟨a, ha.2, rfl⟩
  symm := ⟨by
    rintro x y ⟨hne, n, hn, a, ha, b, hb, rfl, rfl⟩
    exact ⟨hne.symm, n, hn, b, hb, a, ha, rfl, rfl⟩⟩

variable (H : InflationHyp A A' ζn ζc K)

include H

theorem innerGrouping_mem {c' : Set X.S} (hc' : c' ∈ A'.Γ.C) (hb : ¬ Painting.IsBorder c') :
    innerGrouping A A' ζn c' ∈ Q'.Δ (A'.h.cell c') := by
  have hE := A'.h.cell_bijOn.mapsTo hc'
  have hV : (Q'.Δ (A'.h.cell c')).verts = A'.h.node '' tilde c' := by
    rw [Q'.Δ_verts _ hE]
    exact A'.h.ends_internal c' hc' hb
  refine A'.free_internal c' hc' hb _ ?_ hV.symm
  rw [hV]
  refine isGrouping_iff.mpr ⟨subset_rfl, ?_⟩
  rintro x y z hxz ⟨-, n, hn, a, ha, b, hb₁, rfl, rfl⟩ ⟨-, n₂, hn₂, a₂, ha₂, b₂, hb₂, h₁, rfl⟩
  have hsub := tilde_subset_N A'.Γ hc'
  have heq : b = a₂ := A'.h.node_injOn (hsub hb₁.2) (hsub ha₂.2) h₁
  subst heq
  have hnn : n = n₂ := by
    by_contra hc
    exact Set.disjoint_left.mp (H.infl.node_disjoint _ hn _ hn₂ hc) hb₁.1 ha₂.1
  subst hnn
  exact ⟨hxz, n, hn, a, ha, b₂, hb₂, rfl, rfl⟩

/-- The choice of `δ_{c'}`. -/
theorem exists_delta {c' : Set X.S} (hc' : c' ∈ A'.Γ.C) :
    ∃ δ, δ ∈ Q'.Δ (A'.h.cell c') ∧
      (¬ Painting.IsBorder c' → δ = innerGrouping A A' ζn c') ∧
      (Painting.IsBorder c' → (∀ x y, δ.Adj x y → (A'.M c').Adj x y) ∧
        (∀ x y, (A'.M c').Adj x y → x ∉ A'.h.node '' A'.Γ.N → δ.Adj x y) ∧
        ∀ a b, a ≠ b → a ∈ tilde c' → b ∈ tilde c' → δ.Adj (A'.h.node a) (A'.h.node b) ∨
          ∃ c'' ∈ A'.Γ.C, ¬ Painting.IsBorder c'' ∧ a ∈ tilde c'' ∧ b ∈ tilde c'') := by
  by_cases hb : Painting.IsBorder c'
  · obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
    obtain ⟨m, -, rfl⟩ := (A'.C Θ hΘ).exists_cell c' hc' hcΘ
    have hp := (A'.labelled Θ hΘ).pair m
    have hsym : ∀ a b, a ≠ b → a ∈ tilde ((A'.C Θ hΘ).cell m) → b ∈ tilde ((A'.C Θ hΘ).cell m) →
        (a = (A'.C Θ hΘ).pos m ∧ b = (A'.C Θ hΘ).pos (m + 1)) ∨
          (a = (A'.C Θ hΘ).pos (m + 1) ∧ b = (A'.C Θ hΘ).pos m) := by
      intro a b hne ha hb
      rw [(A'.C Θ hΘ).tilde_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hne
    have hmain : ∀ u v, A'.Γ.γ ((A'.C Θ hΘ).cell m) = [u, v] →
        (u = (A'.C Θ hΘ).pos m ∧ v = (A'.C Θ hΘ).pos (m + 1)) ∨
          (u = (A'.C Θ hΘ).pos (m + 1) ∧ v = (A'.C Θ hΘ).pos m) →
        ∃ δ, δ ∈ Q'.Δ (A'.h.cell ((A'.C Θ hΘ).cell m)) ∧
        (¬ Painting.IsBorder ((A'.C Θ hΘ).cell m) → δ = innerGrouping A A' ζn ((A'.C Θ hΘ).cell m))
          ∧
        (Painting.IsBorder ((A'.C Θ hΘ).cell m) → (∀ x y, δ.Adj x y → (A'.M
          ((A'.C Θ hΘ).cell m)).Adj x y) ∧
        (∀ x y, (A'.M ((A'.C Θ hΘ).cell m)).Adj x y → x ∉ A'.h.node '' A'.Γ.N → δ.Adj x y) ∧
        ∀ a b, a ≠ b → a ∈ tilde ((A'.C Θ hΘ).cell m) → b ∈ tilde ((A'.C Θ hΘ).cell m) →
          δ.Adj (A'.h.node a) (A'.h.node b) ∨
          ∃ c'' ∈ A'.Γ.C, ¬ Painting.IsBorder c'' ∧ a ∈ tilde c'' ∧ b ∈ tilde c'') := by
      intro u v hγ huv
      rcases A'.M_mem _ hc' hb u v hγ with h₁ | ⟨h₁, c'', hc'', hin, hu, hv⟩
      · refine ⟨_, h₁, fun h₂ ↦ absurd hb h₂, fun _ ↦ ⟨fun _ _ h ↦ h, fun _ _ h _ ↦ h, ?_⟩⟩
        intro a b hne ha hb₂
        left
        rcases hsym a b hne ha hb₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hp.adj
        · exact hp.adj.symm
      · refine ⟨_, h₁, fun h₂ ↦ absurd hb h₂, fun _ ↦ ⟨fun _ _ h ↦ h.1, fun x y h hx ↦ ⟨h, ?_⟩, ?_⟩⟩
        · intro hmem
          have h₂ : s(x, y) = s(A'.h.node u, A'.h.node v) := hmem
          have hN : ∀ {n}, n = (A'.C Θ hΘ).pos m ∨ n = (A'.C Θ hΘ).pos (m + 1) →
              A'.h.node n ∈ A'.h.node '' A'.Γ.N := by
            rintro n (rfl | rfl)
            · exact ⟨_, (A'.C Θ hΘ).mem_N _, rfl⟩
            · exact ⟨_, (A'.C Θ hΘ).mem_N _, rfl⟩
          have hu' : A'.h.node u ∈ A'.h.node '' A'.Γ.N :=
            hN (huv.elim (fun h ↦ Or.inl h.1) fun h ↦ Or.inr h.1)
          have hv' : A'.h.node v ∈ A'.h.node '' A'.Γ.N :=
            hN (huv.elim (fun h ↦ Or.inr h.2) fun h ↦ Or.inl h.2)
          rcases Sym2.eq_iff.mp h₂ with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact hx hu'
          · exact hx hv'
        · intro a b hne ha hb₂
          right
          refine ⟨c'', hc'', hin, ?_⟩
          rcases hsym a b hne ha hb₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hu, hv⟩
          · exact ⟨hv, hu⟩
          · exact ⟨hv, hu⟩
          · exact ⟨hu, hv⟩
    rcases (A'.C Θ hΘ).γ_eq m with h₁ | h₁
    · exact hmain _ _ h₁ (Or.inl ⟨rfl, rfl⟩)
    · exact hmain _ _ h₁ (Or.inr ⟨rfl, rfl⟩)
  · exact ⟨_, innerGrouping_mem H hc' hb, fun _ ↦ rfl, fun h₂ ↦ absurd h₂ hb⟩

/-- A cell with two nodes in one `ζ(n)` is not in the image of `ζ`, by the sixth condition of a
linear
inflation. -/
theorem not_image_of_two_nodes {c' : Set X.S} {n a b : X.S} (hn : n ∈ A.Γ.N) (hne : a ≠ b)
    (ha : a ∈ ζn n ∩ tilde c') (hb : b ∈ ζn n ∩ tilde c') : c' ∉ ζc '' A.Γ.C := by
  rintro ⟨c, hc, rfl⟩
  have hc' := H.infl.cell_mem c hc
  have hset := A'.Γ.γ_set _ hc'
  have ha₁ : a ∈ A'.Γ.γ (ζc c) := by
    have : a ∈ {n | n ∈ A'.Γ.γ (ζc c)} := hset ▸ ha.2
    exact this
  have hb₁ : b ∈ A'.Γ.γ (ζc c) := by
    have : b ∈ {n | n ∈ A'.Γ.γ (ζc c)} := hset ▸ hb.2
    exact this
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha₁
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb₁
  have hlen := H.length_γ_image hc
  have hi' : i < (A.Γ.γ c).length := hlen ▸ hi
  have hj' : j < (A.Γ.γ c).length := hlen ▸ hj
  have h₁ := (H.infl.nodes n hn c hc i hi' hi).mpr ha.1
  have h₂ := (H.infl.nodes n hn c hc j hj' hj).mpr hb.1
  have hij : i = j := (A.Γ.γ_nodup c hc).getElem_inj_iff.mp (h₁.trans h₂.symm)
  subst hij
  exact hne rfl

/-- The two kinds of edges of `H`: an edge between two nodes of one `ζ(n)`. -/
def NodeEdge (A : Side X F Q) (A' : Side X F Q') (ζn : X.S → Set X.S) (x y : α) : Prop :=
  ∃ n ∈ A.Γ.N, ∃ a ∈ ζn n, ∃ b ∈ ζn n, x = A'.h.node a ∧ y = A'.h.node b

/-- The two kinds of edges of `H`: an edge between the `i`th terms of the marches at the ends of a
border cell outside the image of `ζ`. -/
def TermEdge (A : Side X F Q) (A' : Side X F Q') (ζc : Set X.S → Set X.S) (x y : α) : Prop :=
  ∃ Θ, ∃ hΘ : Θ ∈ cuffs X.S, ∃ (j i : ℕ), (A'.C Θ hΘ).cell j ∉ ζc '' A.Γ.C ∧
    (((A'.π ((A'.C Θ hΘ).pos j))[i]? = some x ∧ (A'.π ((A'.C Θ hΘ).pos (j + 1)))[i]? = some y) ∨
      ((A'.π ((A'.C Θ hΘ).pos j))[i]? = some y ∧ (A'.π ((A'.C Θ hΘ).pos (j + 1)))[i]? = some x))

/-- An edge of the pairing of a border cell outside the image of `ζ` has one of the two kinds. -/
theorem adj_border {c' : Set X.S} (hc' : c' ∈ A'.Γ.C) (hb : Painting.IsBorder c')
    (hni : c' ∉ ζc '' A.Γ.C) {x y : α} (hadj : (A'.M c').Adj x y) :
    NodeEdge A A' ζn x y ∨ TermEdge A A' ζc x y := by
  obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
  obtain ⟨j, -, rfl⟩ := (A'.C Θ hΘ).exists_cell c' hc' hcΘ
  have hp := (A'.labelled Θ hΘ).pair j
  have hfin := A'.pair_finite hΘ j
  have huniq := ((isPairing_iff hfin).mp hp.isPairing).2
  obtain ⟨n, hn, hsub⟩ := H.infl.border_cell _ hc' hb hni
  set C' := A'.C Θ hΘ
  have h₁ : C'.pos j ∈ ζn n := hsub (A'.mem_tilde_left hΘ j)
  have h₂ : C'.pos (j + 1) ∈ ζn n := hsub (A'.mem_tilde_right hΘ j)
  have hterm : ∀ {u w : α}, (A'.M (C'.cell j)).Adj u w → u ∈ A'.h.border (C'.pos j) →
      w ∈ A'.h.border (C'.pos (j + 1)) →
      ∃ i : ℕ, (A'.π (C'.pos j))[i]? = some u ∧ (A'.π (C'.pos (j + 1)))[i]? = some w := by
    intro u w huw hu hw
    obtain ⟨i, hi⟩ := A'.exists_getElem? hΘ hu
    obtain ⟨y₀, hy₀⟩ := A'.exists_term hΘ (m' := j + 1) hi
    have hl := A'.link_of_ne hΘ (H.cell_ne_cut hΘ hni) hi hy₀
    have hy₀m := A'.mem_of_getElem? hΘ hy₀
    have hv : u ∈ (A'.M (C'.cell j)).verts := (A'.M (C'.cell j)).edge_vert huw
    obtain ⟨z, -, -, hu₂⟩ := hp.existsUnique hfin hv
    have : y₀ = w := (hu₂ y₀ (Or.inl hy₀m) hl).trans (hu₂ w (Or.inl hw) (Or.inr huw)).symm
    subst this
    exact ⟨i, hi, hy₀⟩
  have hvx : x ∈ (A'.M (C'.cell j)).verts := (A'.M (C'.cell j)).edge_vert hadj
  have hvy : y ∈ (A'.M (C'.cell j)).verts := (A'.M (C'.cell j)).edge_vert hadj.symm
  rw [hp.verts_eq] at hvx hvy
  have hnodeL : ∀ {u w : α}, (A'.M (C'.cell j)).Adj u w →
      (u = A'.h.node (C'.pos j) ∨ u = A'.h.node (C'.pos (j + 1))) →
      (u = A'.h.node (C'.pos j) ∧ w = A'.h.node (C'.pos (j + 1))) ∨
        (u = A'.h.node (C'.pos (j + 1)) ∧ w = A'.h.node (C'.pos j)) := by
    rintro u w huw (rfl | rfl)
    · exact Or.inl ⟨rfl, huniq _ _ _ huw hp.adj⟩
    · exact Or.inr ⟨rfl, huniq _ _ _ huw hp.adj.symm⟩
  by_cases hxn : x = A'.h.node (C'.pos j) ∨ x = A'.h.node (C'.pos (j + 1))
  · left
    rcases hnodeL hadj hxn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨n, hn, _, h₁, _, h₂, rfl, rfl⟩
    · exact ⟨n, hn, _, h₂, _, h₁, rfl, rfl⟩
  by_cases hyn : y = A'.h.node (C'.pos j) ∨ y = A'.h.node (C'.pos (j + 1))
  · left
    rcases hnodeL hadj.symm hyn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨n, hn, _, h₂, _, h₁, rfl, rfl⟩
    · exact ⟨n, hn, _, h₁, _, h₂, rfl, rfl⟩
  have hxb : x ∈ A'.h.border (C'.pos j) ∪ A'.h.border (C'.pos (j + 1)) :=
    hvx.resolve_right hxn
  have hyb : y ∈ A'.h.border (C'.pos j) ∪ A'.h.border (C'.pos (j + 1)) :=
    hvy.resolve_right hyn
  right
  refine ⟨Θ, hΘ, j, ?_⟩
  rcases hxb with hx | hx
  · rcases hyb with hy | hy
    · exact absurd (A'.eq_of_linked_right hΘ (Or.inr hadj) hx hy) hadj.ne
    · obtain ⟨i, h₃, h₄⟩ := hterm hadj hx hy
      exact ⟨i, hni, Or.inl ⟨h₃, h₄⟩⟩
  · rcases hyb with hy | hy
    · obtain ⟨i, h₃, h₄⟩ := hterm hadj.symm hy hx
      exact ⟨i, hni, Or.inr ⟨h₃, h₄⟩⟩
    · exact absurd (A'.eq_of_linked_left hΘ (Or.inr hadj) hx hy).symm hadj.ne

/-- The graph `H` of the proof of (9.1), with what we use about it. -/
theorem exists_realization : ∃ R : (⊤ : SimpleGraph α).Subgraph,
    (Q'.deleteEdges (etaEdge A A' ζc '' Q.G.edgeSet)).IsRealization R ∧
    (∀ x y, R.Adj x y → NodeEdge A A' ζn x y ∨ TermEdge A A' ζc x y) ∧
    (∀ n ∈ A.Γ.N, ∀ a ∈ ζn n, ∀ b ∈ ζn n, A'.Γ.sk.Adj a b → R.Adj (A'.h.node a) (A'.h.node b)) ∧
    (∀ c' ∈ A'.Γ.C, Painting.IsBorder c' → c' ∉ ζc '' A.Γ.C → ∀ x y, (A'.M c').Adj x y →
      x ∉ A'.h.node '' A'.Γ.N → R.Adj x y) := by
  classical
  choose! δ hδ₁ hδ₂ hδ₃ using fun c' (hc' : c' ∈ A'.Γ.C) ↦ exists_delta H hc'
  let g : β → (⊤ : SimpleGraph α).Subgraph := fun e ↦ δ (Function.invFunOn A'.h.cell A'.Γ.C e)
  have hg : ∀ {c'}, c' ∈ A'.Γ.C → g (A'.h.cell c') = δ c' := fun {c'} hc' ↦ by
    have h₁ : Function.invFunOn A'.h.cell A'.Γ.C (A'.h.cell c') = c' :=
      A'.h.cell_bijOn.injOn (Function.invFunOn_mem ⟨c', hc', rfl⟩) hc'
        (Function.invFunOn_eq ⟨c', hc', rfl⟩)
    simp only [g, h₁]
  have hedge : ∀ {c'}, c' ∈ A'.Γ.C → c' ∉ ζc '' A.Γ.C →
      A'.h.cell c' ∉ etaEdge A A' ζc '' Q.G.edgeSet := by
    rintro c' hc' hni ⟨e, he, heq⟩
    obtain ⟨c, hc, rfl⟩ := A.h.cell_bijOn.surjOn he
    rw [etaEdge_cell hc] at heq
    exact hni ⟨c, hc, A'.h.cell_bijOn.injOn (H.infl.cell_mem c hc) hc' heq⟩
  have hedge₂ : ∀ {e}, e ∈ Q'.G.edgeSet → e ∉ etaEdge A A' ζc '' Q.G.edgeSet →
      ∃ c' ∈ A'.Γ.C, c' ∉ ζc '' A.Γ.C ∧ A'.h.cell c' = e := by
    intro e he hne
    obtain ⟨c', hc', rfl⟩ := A'.h.cell_bijOn.surjOn he
    refine ⟨c', hc', ?_, rfl⟩
    rintro ⟨c, hc, rfl⟩
    exact hne ⟨A.h.cell c, A.h.cell_bijOn.mapsTo hc, etaEdge_cell hc⟩
  let P₀ := Q'.deleteEdges (etaEdge A A' ζc '' Q.G.edgeSet)
  refine ⟨realizationOf P₀.G.toHypergraph g, ⟨g, ?_, rfl⟩, ?_, ?_, ?_⟩
  · rintro e ⟨he, hne⟩
    obtain ⟨c', hc', -, rfl⟩ := hedge₂ he hne
    rw [hg hc']
    exact hδ₁ c' hc'
  · intro x y hadj
    obtain ⟨e, ⟨he, hne⟩, hxy⟩ := realizationOf_adj.mp hadj
    obtain ⟨c', hc', hni, rfl⟩ := hedge₂ he hne
    rw [hg hc'] at hxy
    by_cases hb : Painting.IsBorder c'
    · exact adj_border H hc' hb hni ((hδ₃ c' hc' hb).1 x y hxy)
    · rw [hδ₂ c' hc' hb] at hxy
      obtain ⟨-, n, hn, a, ha, b, hb₂, rfl, rfl⟩ := hxy
      exact Or.inl ⟨n, hn, a, ha.1, b, hb₂.1, rfl, rfl⟩
  · rintro n hn a ha b hb ⟨hne, haN, hbN, c', hc', hac, hbc⟩
    have hni := not_image_of_two_nodes H hn hne ⟨ha, hac⟩ ⟨hb, hbc⟩
    have hrel : ∀ {c}, c ∈ A'.Γ.C → ¬ Painting.IsBorder c → a ∈ tilde c → b ∈ tilde c →
        (realizationOf P₀.G.toHypergraph g).Adj (A'.h.node a) (A'.h.node b) := by
      intro c hc hbc₂ ha₂ hb₂
      have hni₂ := not_image_of_two_nodes H hn hne ⟨ha, ha₂⟩ ⟨hb, hb₂⟩
      refine realizationOf_adj.mpr ⟨A'.h.cell c, ⟨A'.h.cell_bijOn.mapsTo hc, hedge hc hni₂⟩, ?_⟩
      rw [hg hc, hδ₂ c hc hbc₂]
      exact ⟨fun heq ↦ hne (A'.h.node_injOn haN hbN heq), n, hn, a, ⟨ha, ha₂⟩, b, ⟨hb, hb₂⟩, rfl,
        rfl⟩
    by_cases hbc' : Painting.IsBorder c'
    · rcases (hδ₃ c' hc' hbc').2.2 a b hne hac hbc with h₁ | ⟨c'', hc'', hin, ha₂, hb₂⟩
      · refine realizationOf_adj.mpr ⟨A'.h.cell c', ⟨A'.h.cell_bijOn.mapsTo hc', hedge hc' hni⟩, ?_⟩
        rw [hg hc']
        exact h₁
      · exact hrel hc'' hin ha₂ hb₂
    · exact hrel hc' hbc' hac hbc
  · intro c' hc' hb hni x y hadj hx
    refine realizationOf_adj.mpr ⟨A'.h.cell c', ⟨A'.h.cell_bijOn.mapsTo hc', hedge hc' hni⟩, ?_⟩
    rw [hg hc']
    exact (hδ₃ c' hc' hb).2.1 x y hadj hx

end Main

end GraphMinor.GM20
