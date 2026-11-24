/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9b

/-!
# Graph Minors XX, Section 9: the marches of a hull

This file carries out the first step of the proof of (9.1). In a `(Σ, ρ)`-hulled patchwork, every
border cell `c` with nodes `n₁, n₂` has a pairing `M_c`. Away from the two nodes, `M_c` matches
`β(n₁)`
with `β(n₂)`. So after we order `β(pos 0)` for a cuff `Θ`, we can order `β(pos 1)`, `β(pos 2)`, … in
turn,
such that the `i`th terms of `β(pos m)` and `β(pos (m + 1))` belong to the same component of the
pairing (`exists_cuffLabels`). This can fail only for the last cell, which joins `pos (k - 1)` to
`pos 0`, and this is the cell `c_Θ` of the paper.

`Side` collects all this data for a patchwork.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- `x` and `y` lie in the same component of a pairing. -/
def Linked (M : (⊤ : SimpleGraph α).Subgraph) (x y : α) : Prop := x = y ∨ M.Adj x y

theorem Linked.symm {M : (⊤ : SimpleGraph α).Subgraph} {x y : α} (h : Linked M x y) : Linked M y x
  :=
  h.elim (fun h ↦ Or.inl h.symm) fun h ↦ Or.inr h.symm

section Pairing

variable {X : GradedSurface} {Γ : Painting X.S} {G : Hypergraph α β} {h : Hull Γ G} {n₁ n₂ : X.S}
  {M : (⊤ : SimpleGraph α).Subgraph}

/-- The relation of a pairing does not depend on the order of the two nodes. -/
theorem IsCellPairing.symm (hM : IsCellPairing h n₁ n₂ M) : IsCellPairing h n₂ n₁ M where
  isPairing := hM.isPairing
  verts_eq := by
    rw [hM.verts_eq, Set.union_comm (h.border n₁), Set.pair_comm]
  adj := hM.adj.symm
  components D hD := (hM.components D hD).symm

theorem isPairing_verts_finite (hfin : (h.border n₁).Finite) (hfin' : (h.border n₂).Finite)
    (hM : IsCellPairing h n₁ n₂ M) : M.verts.Finite := by
  rw [hM.verts_eq]
  exact (hfin.union hfin').union (Set.toFinite _)

/-- In a pairing, the component of `x` is `x` and its neighbour. -/
theorem mem_component_iff (hfin : M.verts.Finite) (hp : IsPairing M.verts M) (x : M.verts) (y : α) :
    y ∈ (component M x).verts ↔ y ∈ M.verts ∧ Linked M x.1 y := by
  have huniq := ((isPairing_iff hfin).mp hp).2
  constructor
  · rintro ⟨hy, hr⟩
    refine ⟨hy, ?_⟩
    have key : ∀ b : M.verts, M.coe.Reachable x b → Linked M x.1 b.1 := by
      intro b hb
      rw [SimpleGraph.reachable_iff_reflTransGen] at hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail z w _ hzw ih =>
        rcases ih with hzx | hxz
        · right
          rw [hzx]
          exact hzw
        · left
          exact huniq z.1 x.1 w.1 hxz.symm hzw
    exact key ⟨y, hy⟩ hr
  · rintro ⟨hy, hl⟩
    refine ⟨hy, ?_⟩
    rcases hl with heq | hadj
    · subst heq
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (show M.coe.Adj x ⟨y, hy⟩ from hadj)

/-- Every vertex of the pairing is linked to exactly one vertex of `β(n₂) ∪ {n₂}`. -/
theorem IsCellPairing.existsUnique (hM : IsCellPairing h n₁ n₂ M) (hfin : M.verts.Finite) {x : α}
    (hx : x ∈ M.verts) : ∃ y, y ∈ h.border n₂ ∪ {h.node n₂} ∧ Linked M x y ∧
      ∀ y' ∈ h.border n₂ ∪ {h.node n₂}, Linked M x y' → y' = y := by
  have hp : IsPairing M.verts M := hM.isPairing
  have hD : IsComponent M (component M ⟨x, hx⟩) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp (hM.components _ hD).2
  have hmem : y ∈ (component M ⟨x, hx⟩).verts ∩ (h.border n₂ ∪ {h.node n₂}) := by
    rw [hy]
    exact rfl
  refine ⟨y, hmem.2, ((mem_component_iff hfin hp _ _).mp hmem.1).2, fun y' hy' hl ↦ ?_⟩
  have hv : y' ∈ M.verts := by
    rcases hl with heq | hadj
    · exact heq ▸ hx
    · exact M.edge_vert hadj.symm
  have : y' ∈ (component M ⟨x, hx⟩).verts ∩ (h.border n₂ ∪ {h.node n₂}) :=
    ⟨(mem_component_iff hfin hp _ _).mpr ⟨hv, hl⟩, hy'⟩
  rw [hy] at this
  exact this

open Classical in
/-- The vertex of `B` linked to `x`. -/
noncomputable def partner (M : (⊤ : SimpleGraph α).Subgraph) (B : Set α) (x : α) : α :=
  if h : ∃ y ∈ B, Linked M x y then h.choose else x

theorem partner_spec {B : Set α} {x : α} (hx : ∃ y ∈ B, Linked M x y) :
    partner M B x ∈ B ∧ Linked M x (partner M B x) := by
  classical
  simp only [partner, dite_eq_left hx]
  exact hx.choose_spec

/-- If `x ∈ β(n₁)`, the vertex linked to `x` is not `n₂`, since `n₂` is linked to `n₁`. -/
theorem IsCellPairing.linked_ne (hM : IsCellPairing h n₁ n₂ M) (hfin : M.verts.Finite) {x : α}
    (hx : x ∈ h.border n₁) (hn : h.node n₁ ∉ h.border n₁) (hl : Linked M x (h.node n₂)) : False
      := by
  have hv : h.node n₂ ∈ M.verts := M.edge_vert hM.adj.symm
  obtain ⟨y, -, -, hu⟩ := hM.symm.existsUnique hfin hv
  have h₁ := hu x (Or.inl hx) hl.symm
  have h₂ := hu (h.node n₁) (Or.inr rfl) (Or.inr hM.adj.symm)
  exact hn (h₂.trans h₁.symm ▸ hx)

/-- `M` maps `β(n₁)` onto `β(n₂)`. -/
theorem IsCellPairing.partner_mapsTo (hM : IsCellPairing h n₁ n₂ M) (hfin : M.verts.Finite)
    (hn : h.node n₁ ∉ h.border n₁) {x : α} (hx : x ∈ h.border n₁) :
    partner M (h.border n₂ ∪ {h.node n₂}) x ∈ h.border n₂ ∧
      Linked M x (partner M (h.border n₂ ∪ {h.node n₂}) x) := by
  have hv : x ∈ M.verts := by
    rw [hM.verts_eq]
    exact Or.inl (Or.inl hx)
  obtain ⟨y, hy, hl, -⟩ := hM.existsUnique hfin hv
  obtain ⟨h₁, h₂⟩ := partner_spec (M := M) ⟨y, hy, hl⟩
  refine ⟨h₁.resolve_right fun h₃ ↦ ?_, h₂⟩
  rw [Set.mem_singleton_iff] at h₃
  exact hM.linked_ne hfin hx hn (h₃ ▸ h₂)

theorem IsCellPairing.partner_injOn (hM : IsCellPairing h n₁ n₂ M) (hfin : M.verts.Finite)
    (hn : h.node n₁ ∉ h.border n₁) :
    InjOn (partner M (h.border n₂ ∪ {h.node n₂})) (h.border n₁) := by
  intro x hx x' hx' heq
  have h₁ := (hM.partner_mapsTo hfin hn hx)
  have h₂ := (hM.partner_mapsTo hfin hn hx')
  rw [← heq] at h₂
  have hv : partner M (h.border n₂ ∪ {h.node n₂}) x ∈ M.verts := by
    rw [hM.verts_eq]
    exact Or.inl (Or.inr h₁.1)
  obtain ⟨y, -, -, hu⟩ := hM.symm.existsUnique hfin hv
  rw [hu x (Or.inl hx) h₁.2.symm, hu x' (Or.inl hx') h₂.2.symm]

theorem IsCellPairing.partner_surjOn (hM : IsCellPairing h n₁ n₂ M) (hfin : M.verts.Finite)
    (hn₂ : h.node n₂ ∉ h.border n₂) {y : α} (hy : y ∈ h.border n₂) :
    ∃ x ∈ h.border n₁, partner M (h.border n₂ ∪ {h.node n₂}) x = y := by
  have hv : y ∈ M.verts := by
    rw [hM.verts_eq]
    exact Or.inl (Or.inr hy)
  obtain ⟨x, hx, hl, -⟩ := hM.symm.existsUnique hfin hv
  have hx' : x ∈ h.border n₁ := hx.resolve_right fun h₃ ↦ by
    rw [Set.mem_singleton_iff] at h₃
    exact hM.symm.linked_ne hfin hy hn₂ (h₃ ▸ hl)
  refine ⟨x, hx', ?_⟩
  have hvx : x ∈ M.verts := by
    rw [hM.verts_eq]
    exact Or.inl (Or.inl hx')
  obtain ⟨z, -, -, hu⟩ := hM.existsUnique hfin hvx
  obtain ⟨h₁, h₂⟩ := partner_spec (M := M) (x := x) (B := h.border n₂ ∪ {h.node n₂})
    ⟨y, Or.inl hy, hl.symm⟩
  rw [hu _ h₁ h₂, hu y (Or.inl hy) hl.symm]

end Pairing

/-- The ordering of the sets `β(n)` around a cuff, as in the proof of (9.1). -/
structure IsLabelled {X : GradedSurface} {Γ : Painting X.S} {G : Hypergraph α β} (h : Hull Γ G)
    {Θ : Set X.S} {f : Circle ≃ₜ Θ} (C : CuffCycle Γ f) (ρ : ℕ) (π : X.S → List α)
    (M : Set X.S → (⊤ : SimpleGraph α).Subgraph) : Prop where
  nodup : ∀ m, (π (C.pos m)).Nodup
  set_eq : ∀ m, {x | x ∈ π (C.pos m)} = h.border (C.pos m)
  length_eq : ∀ m, (π (C.pos m)).length = ρ
  pair : ∀ m, IsCellPairing h (C.pos m) (C.pos (m + 1)) (M (C.cell m))
  link : ∀ m, m + 1 < C.k → ∀ (i : ℕ) (x y : α), (π (C.pos m))[i]? = some x → (π (C.pos
    (m + 1)))[i]? = some y →
    Linked (M (C.cell m)) x y

section Labels

variable {X : GradedSurface} {Γ : Painting X.S} {G : Hypergraph α β} (h : Hull Γ G)
  {Θ : Set X.S} {f : Circle ≃ₜ Θ} (C : CuffCycle Γ f)

/-- The march of `β(pos m)`, for the march `l` of `β(pos 0)`. -/
noncomputable def labelSeq (M : Set X.S → (⊤ : SimpleGraph α).Subgraph) (l : List α) : ℕ → List α
  | 0 => l
  | m + 1 => (labelSeq M l m).map
      (partner (M (C.cell m)) (h.border (C.pos (m + 1)) ∪ {h.node (C.pos (m + 1))}))

/-- The orderings around one cuff exist, as a sequence of marches. -/
theorem exists_cuffLabels {ρ : ℕ} (M : Set X.S → (⊤ : SimpleGraph α).Subgraph)
    (hfin : ∀ m, (h.border (C.pos m)).Finite) (hcard : ∀ m, (h.border (C.pos m)).ncard = ρ)
    (hn : ∀ m, h.node (C.pos m) ∉ h.border (C.pos m))
    (hpair : ∀ m, IsCellPairing h (C.pos m) (C.pos (m + 1)) (M (C.cell m))) :
    ∃ s : ℕ → List α, (∀ m, (s m).Nodup) ∧ (∀ m, {x | x ∈ s m} = h.border (C.pos m)) ∧
      (∀ m, (s m).length = ρ) ∧ ∀ m (i : ℕ) (x y : α), (s m)[i]? = some x → (s (m + 1))[i]?
        = some y →
        Linked (M (C.cell m)) x y := by
  classical
  let l := (hfin 0).toFinset.toList
  have hl₀ : {x | x ∈ l} = h.border (C.pos 0) := by
    ext x
    simp [l]
  have hfinM : ∀ m, (M (C.cell m)).verts.Finite := fun m ↦
    isPairing_verts_finite (hfin _) (hfin _) (hpair m)
  have hset : ∀ m, {x | x ∈ labelSeq h C M l m} = h.border (C.pos m) := by
    intro m
    induction m with
    | zero => exact hl₀
    | succ m ih =>
      ext y
      simp only [labelSeq, mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ h.border (C.pos m) := ih ▸ hx
        exact ((hpair m).partner_mapsTo (hfinM m) (hn m) hx').1
      · intro hy
        obtain ⟨x, hx, hxy⟩ := (hpair m).partner_surjOn (hfinM m) (hn _) hy
        have hx' : x ∈ {x | x ∈ labelSeq h C M l m} := ih ▸ hx
        exact ⟨x, hx', hxy⟩
  have hnd : ∀ m, (labelSeq h C M l m).Nodup := by
    intro m
    induction m with
    | zero => exact Finset.nodup_toList _
    | succ m ih =>
      refine ih.map_on fun x hx y hy heq ↦ ?_
      have hx' : x ∈ h.border (C.pos m) := hset m ▸ hx
      have hy' : y ∈ h.border (C.pos m) := hset m ▸ hy
      exact (hpair m).partner_injOn (hfinM m) (hn m) hx' hy' heq
  have hlen : ∀ m, (labelSeq h C M l m).length = ρ := by
    intro m
    have h₁ : {x | x ∈ labelSeq h C M l m} = ↑(labelSeq h C M l m).toFinset := by
      ext x
      simp
    rw [← hcard m, ← hset m, h₁, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd m)]
  refine ⟨labelSeq h C M l, hnd, hset, hlen, fun m i x y hx hy ↦ ?_⟩
  simp only [labelSeq, List.getElem?_map, hx, Option.map_some, Option.some.injEq] at hy
  have hxm : x ∈ h.border (C.pos m) := by
    have : x ∈ labelSeq h C M l m := List.mem_of_getElem? hx
    exact hset m ▸ this
  rw [← hy]
  exact ((hpair m).partner_mapsTo (hfinM m) (hn m) hxm).2

end Labels

/-- A hull for `G` is also a hull for an equal hypergraph. -/
def Hull.transfer {X : GradedSurface} {Γ : Painting X.S} {G G' : Hypergraph α β} (h : Hull Γ G)
    (e : G = G') : Hull Γ G' where
  node := h.node
  cell := h.cell
  border := h.border
  node_injOn := h.node_injOn
  node_mem := by subst e; exact h.node_mem
  cell_bijOn := by subst e; exact h.cell_bijOn
  inc_iff := by subst e; exact h.inc_iff
  border_subset := by subst e; exact h.border_subset
  border_disjoint := h.border_disjoint
  border_ncard := h.border_ncard
  border_cuffs := h.border_cuffs
  vertexSet_eq := by subst e; exact h.vertexSet_eq
  ends_internal := by subst e; exact h.ends_internal
  ends_border := by subst e; exact h.ends_border
  border_order := h.border_order

/-- A cuff of `Σ`, with a parametrization for each one. All the patchworks of the proof of (9.1) use
the same parametrizations. -/
abbrev CuffParam (S : Type) [TopologicalSpace S] := ∀ Θ ∈ cuffs S, Circle ≃ₜ Θ

/-- All that the proof of (9.1) uses about a patchwork `Q` that is an `Ω`-completion of a hulled
patchwork, with the choices of the proof. -/
structure Side {Ω : Type*} (X : GradedSurface) (F : CuffParam X.S) (Q : Patchwork Ω α β) where
  /-- The painting. -/
  Γ : Painting X.S
  /-- The hull. -/
  h : Hull Γ Q.G.toHypergraph
  /-- The pairings `M_c`. -/
  M : Set X.S → (⊤ : SimpleGraph α).Subgraph
  /-- The marches `π(n)`. -/
  π : X.S → List α
  /-- The cycles of nodes and cells around the cuffs. -/
  C : ∀ Θ (hΘ : Θ ∈ cuffs X.S), CuffCycle Γ (F Θ hΘ)
  three_connected : Γ.IsThreeConnected
  free_internal : ∀ c ∈ Γ.C, ¬ Painting.IsBorder c → (Q.Δ (h.cell c)).IsFree
  M_mem : ∀ c ∈ Γ.C, Painting.IsBorder c → ∀ n₁ n₂, Γ.γ c = [n₁, n₂] → (M c ∈ Q.Δ (h.cell c) ∨
    ((M c).deleteEdges {s(h.node n₁, h.node n₂)} ∈ Q.Δ (h.cell c) ∧
      ∃ c' ∈ Γ.C, ¬ Painting.IsBorder c' ∧ n₁ ∈ tilde c' ∧ n₂ ∈ tilde c'))
  roots_nil : Q.G.roots = []
  dom_eq : Q.dom = Q.G.edgeSet
  μ_internal : ∀ c ∈ Γ.C, ¬ Painting.IsBorder c → Q.μ (h.cell c) = (Γ.γ c).map h.node
  labelled : ∀ Θ (hΘ : Θ ∈ cuffs X.S), IsLabelled h (C Θ hΘ) (X.ρ Θ) π M

theorem cuff_eq_of_mem {S : Type} [TopologicalSpace S] {Θ₁ Θ₂ : Set S} (h₁ : Θ₁ ∈ cuffs S)
    (h₂ : Θ₂ ∈ cuffs S) {x : S} (hx₁ : x ∈ Θ₁) (hx₂ : x ∈ Θ₂) : Θ₁ = Θ₂ := by
  obtain ⟨p, hp, rfl⟩ := h₁
  obtain ⟨q, hq, rfl⟩ := h₂
  rw [connectedComponentIn_eq hx₁, connectedComponentIn_eq hx₂]

/-- Each completion of a hulled patchwork has the data of `Side`. -/
theorem exists_side {Ω : Type*} (X : GradedSurface) (F : CuffParam X.S) {P : UnlabeledPatchwork α β}
    {Q : Patchwork Ω α β} (hP : IsHulled X P) (hQ : IsCompletionOf P Q) : Nonempty (Side X F Q)
      := by
  classical
  obtain ⟨Γ, h, hb⟩ := hP
  have hG : P.G.toHypergraph = Q.G.toHypergraph := by rw [hQ.G_eq]
  have hEe : ∀ e ∈ Q.G.edgeSet, e ∈ P.G.edgeSet := fun e he ↦ by
    rw [hQ.G_eq] at he
    exact he
  let h' : Hull Γ Q.G.toHypergraph := h.transfer hG
  have hcell : ∀ c ∈ Γ.C, h'.cell c ∈ Q.G.edgeSet := fun c hc ↦ h'.cell_bijOn.mapsTo hc
  have hΔ : ∀ c ∈ Γ.C, Q.Δ (h.cell c) = P.Δ (h.cell c) := fun c hc ↦
    hQ.Δ_eq (hEe _ (hcell c hc))
  have hpm : ∀ {n₁ n₂ M}, IsCellPairing h n₁ n₂ M → IsCellPairing h' n₁ n₂ M := fun hM ↦
    ⟨hM.isPairing, hM.verts_eq, hM.adj, hM.components⟩
  obtain ⟨C⟩ : Nonempty (∀ Θ (hΘ : Θ ∈ cuffs X.S), CuffCycle Γ (F Θ hΘ)) :=
    ⟨fun Θ hΘ ↦ (exists_cuffCycle Γ hΘ (F Θ hΘ)).some⟩
  have hbΘ : ∀ {Θ}, Θ ∈ cuffs X.S → Θ ⊆ bd X.S := fun hΘ ↦ cuff_subset_bd hΘ
  have hborder : ∀ {Θ} (hΘ : Θ ∈ cuffs X.S) m, Painting.IsBorder ((C Θ hΘ).cell m) := by
    intro Θ hΘ m
    obtain ⟨y, hy, hyΘ⟩ := (C Θ hΘ).meets m
    exact ⟨y, hy, hbΘ hΘ hyΘ⟩
  let R : Set X.S → (⊤ : SimpleGraph α).Subgraph → Prop := fun c M ↦
    ∀ n₁ n₂, Γ.γ c = [n₁, n₂] → IsCellPairing h' n₁ n₂ M ∧ (M ∈ Q.Δ (h.cell c) ∨
    (M.deleteEdges {s(h.node n₁, h.node n₂)} ∈ Q.Δ (h.cell c) ∧
      ∃ c' ∈ Γ.C, ¬ Painting.IsBorder c' ∧ n₁ ∈ tilde c' ∧ n₂ ∈ tilde c'))
  have hR : ∀ c, c ∈ Γ.C ∧ Painting.IsBorder c → ∃ M, R c M := by
    rintro c ⟨hc, hbc⟩
    obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hbc
    obtain ⟨m, -, rfl⟩ := (C Θ hΘ).exists_cell c hc hcΘ
    have hsome : ∃ a b, Γ.γ ((C Θ hΘ).cell m) = [a, b] ∧ a ≠ b ∧
        a ∈ tilde ((C Θ hΘ).cell m) ∧ b ∈ tilde ((C Θ hΘ).cell m) := by
      have h₁ : (C Θ hΘ).pos m ∈ tilde ((C Θ hΘ).cell m) := by
        rw [(C Θ hΘ).tilde_eq]
        exact Or.inl rfl
      have h₂ : (C Θ hΘ).pos (m + 1) ∈ tilde ((C Θ hΘ).cell m) := by
        rw [(C Θ hΘ).tilde_eq]
        exact Or.inr rfl
      have hne := (C Θ hΘ).pos_ne_succ m
      rcases (C Θ hΘ).γ_eq m with h₃ | h₃
      · exact ⟨_, _, h₃, hne, h₁, h₂⟩
      · exact ⟨_, _, h₃, hne.symm, h₂, h₁⟩
    obtain ⟨a, b, hab, hne, ha, hb'⟩ := hsome
    obtain ⟨M, h₁, h₂⟩ := hb.border_pairing _ hc hbc a ha b hb' hne
    refine ⟨M, fun n₁ n₂ hn ↦ ?_⟩
    rw [hab] at hn
    simp only [List.cons.injEq, and_true] at hn
    obtain ⟨rfl, rfl⟩ := hn
    rw [hΔ _ hc]
    exact ⟨hpm h₁, h₂⟩
  choose! M hM using hR
  have hpair : ∀ Θ (hΘ : Θ ∈ cuffs X.S) m, IsCellPairing h' ((C Θ hΘ).pos m) ((C Θ hΘ).pos (m + 1))
      (M ((C Θ hΘ).cell m)) := by
    intro Θ hΘ m
    have h₁ := hM _ ⟨(C Θ hΘ).cell_mem m, hborder hΘ m⟩
    rcases (C Θ hΘ).γ_eq m with h₂ | h₂
    · exact (h₁ _ _ h₂).1
    · exact (h₁ _ _ h₂).1.symm
  have hdisj : ∀ Θ (hΘ : Θ ∈ cuffs X.S) m, h'.node ((C Θ hΘ).pos m) ∉ h'.border ((C Θ hΘ).pos m)
    := by
    intro Θ hΘ m hmem
    have hN := (C Θ hΘ).mem_N m
    exact Set.disjoint_left.mp (h'.border_disjoint _ ⟨hN, hbΘ hΘ ((C Θ hΘ).mem_cuff m)⟩) hmem
      ⟨_, hN, rfl⟩
  have hfin : ∀ Θ (hΘ : Θ ∈ cuffs X.S) m, (h'.border ((C Θ hΘ).pos m)).Finite := fun Θ hΘ m ↦
    Q.G.vertexSet_finite.subset (h'.border_subset _ ⟨(C Θ hΘ).mem_N m, hbΘ hΘ
      ((C Θ hΘ).mem_cuff m)⟩)
  have hseq := fun Θ (hΘ : Θ ∈ cuffs X.S) ↦ exists_cuffLabels (ρ := X.ρ Θ) h' (C Θ hΘ) M (hfin Θ hΘ)
    (fun m ↦ h'.border_ncard Θ hΘ _ ⟨(C Θ hΘ).mem_N m, (C Θ hΘ).mem_cuff m⟩) (hdisj Θ hΘ)
      (hpair Θ hΘ)
  choose s hs₁ hs₂ hs₃ hs₄ using hseq
  let π : X.S → List α := fun n ↦
    if hn : ∃ (Θ : Set X.S) (hΘ : Θ ∈ cuffs X.S) (m : ℕ), m < (C Θ hΘ).k ∧ (C Θ hΘ).pos m = n then
      s hn.choose hn.choose_spec.choose hn.choose_spec.choose_spec.choose else []
  have huniq : ∀ Θ₁ (h₁ : Θ₁ ∈ cuffs X.S) m₁ Θ₂ (h₂ : Θ₂ ∈ cuffs X.S) m₂, m₁ < (C Θ₁ h₁).k →
      m₂ < (C Θ₂ h₂).k → (C Θ₁ h₁).pos m₁ = (C Θ₂ h₂).pos m₂ → s Θ₁ h₁ m₁ = s Θ₂ h₂ m₂ := by
    intro Θ₁ h₁ m₁ Θ₂ h₂ m₂ hm₁ hm₂ heq
    obtain rfl := cuff_eq_of_mem h₁ h₂ ((C Θ₁ h₁).mem_cuff m₁) (heq ▸ (C Θ₂ h₂).mem_cuff m₂)
    rcases lt_trichotomy m₁ m₂ with h₃ | h₃ | h₃
    · exact absurd heq ((C Θ₁ h₁).pos_ne h₃ (by omega))
    · rw [h₃]
    · exact absurd heq.symm ((C Θ₁ h₁).pos_ne h₃ (by omega))
  have hπ : ∀ Θ (hΘ : Θ ∈ cuffs X.S) m, m < (C Θ hΘ).k → π ((C Θ hΘ).pos m) = s Θ hΘ m := by
    intro Θ hΘ m hm
    have hn : ∃ (Θ' : Set X.S) (hΘ' : Θ' ∈ cuffs X.S) (m' : ℕ), m' < (C Θ' hΘ').k ∧
        (C Θ' hΘ').pos m' = (C Θ hΘ).pos m := ⟨Θ, hΘ, m, hm, rfl⟩
    simp only [π, dite_eq_left hn]
    have h₂ := hn.choose_spec.choose_spec.choose_spec
    exact huniq _ _ _ _ _ _ h₂.1 hm h₂.2
  have hπ' : ∀ Θ (hΘ : Θ ∈ cuffs X.S) m, π ((C Θ hΘ).pos m) = s Θ hΘ (m % (C Θ hΘ).k) := by
    intro Θ hΘ m
    rw [← (C Θ hΘ).pos_mod m]
    exact hπ Θ hΘ _ (Nat.mod_lt _ (C Θ hΘ).k_pos)
  refine ⟨⟨Γ, h', M, π, C, hb.three_connected, fun c hc hbc ↦ ?_,
    fun c hc hbc n₁ n₂ hn ↦ (hM c ⟨hc, hbc⟩ n₁ n₂ hn).2,
    ?_, ?_, fun c hc hbc ↦ ?_, fun Θ hΘ ↦ ⟨fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_, hpair Θ hΘ, ?_⟩⟩⟩
  · change (Q.Δ (h.cell c)).IsFree
    rw [hΔ c hc]
    exact hb.free_internal c hc hbc
  · rw [hQ.G_eq]
    exact hb.roots_nil
  · rw [hQ.dom_eq, hb.dom_eq, hQ.G_eq]
  · have hmem : h.cell c ∈ P.dom := by
      rw [hb.dom_eq]
      exact hEe _ (hcell c hc)
    exact (hQ.μ_eq hmem).trans (hb.μ_internal c hc hbc)
  · rw [hπ']
    exact hs₁ Θ hΘ _
  · rw [hπ', hs₂, (C Θ hΘ).pos_mod]
  · rw [hπ']
    exact hs₃ Θ hΘ _
  · intro m hm i x y hx hy
    rw [hπ Θ hΘ m (by omega)] at hx
    rw [hπ Θ hΘ (m + 1) hm] at hy
    exact hs₄ Θ hΘ m i x y hx hy

end GraphMinor.GM20
