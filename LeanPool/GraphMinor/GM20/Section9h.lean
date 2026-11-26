/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9g
public import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors XX, Section 9: the proof of (9.1)

This file proves claims (9), (10), (11) and (12) of the proof of (9.1), and so that `H` realizes
`η`. Then
`P` is simulated in `P'` (`InflationHyp.simulated`), and (9.1) follows from (8.1).
The deductions using other proved results are in `Section9hProved`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v w

variable {α : Type u} {β : Type v}

section Main

variable {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
  {A : Side X F Q} {A' : Side X F Q'} {ζn : X.S → Set X.S} {ζc : Set X.S → Set X.S} {K : ℕ}
  (H : InflationHyp A A' ζn ζc K) {R : (⊤ : SimpleGraph α).Subgraph}
  (hR : (Q'.deleteEdges (etaEdge A A' ζc '' Q.G.edgeSet)).IsRealization R)
  (hadj : ∀ x y, R.Adj x y → NodeEdge A A' ζn x y ∨ TermEdge A A' ζc x y)
  (hnode : ∀ n ∈ A.Γ.N, ∀ a ∈ ζn n, ∀ b ∈ ζn n, A'.Γ.sk.Adj a b →
    R.Adj (A'.h.node a) (A'.h.node b))
  (hterm : ∀ c' ∈ A'.Γ.C, Painting.IsBorder c' → c' ∉ ζc '' A.Γ.C → ∀ x y, (A'.M c').Adj x y →
    x ∉ A'.h.node '' A'.Γ.N → R.Adj x y)

include H in
/-- Claim (12) of the proof of (9.1). -/
theorem claim_12 {x y : α} (h : NodeEdge A A' ζn x y ∨ TermEdge A A' ζc x y) :
    ∃ u, x ∈ etaVert A A' ζn u ∧ y ∈ etaVert A A' ζn u := by
  rcases h with ⟨n, hn, a, ha, b, hb, rfl, rfl⟩ | ⟨Θ, hΘ, j, i, hni, hor⟩
  · exact ⟨A.h.node n, Or.inl ⟨n, hn, rfl, a, ha, rfl⟩, Or.inl ⟨n, hn, rfl, b, hb, rfl⟩⟩
  · obtain ⟨L, -, -, hpos, hstep, -, -⟩ := H.exists_lift' hΘ
    set C := A.C Θ hΘ
    set C' := A'.C Θ hΘ
    have hL : L (j + 1) = L j := by
      rcases hstep j with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact h₁
      · exact absurd ⟨_, C.cell_mem _, h₂⟩ hni
    have hN : C.pos (L j) ∈ A.Γ.N ∩ Θ := ⟨C.mem_N _, C.mem_cuff _⟩
    have h₁ : C'.pos j ∈ ζn (C.pos (L j)) ∩ Θ := ⟨hpos j, C'.mem_cuff _⟩
    have h₂ : C'.pos (j + 1) ∈ ζn (C.pos (L j)) ∩ Θ := ⟨hL ▸ hpos (j + 1), C'.mem_cuff _⟩
    have hterm : ∀ {z : α}, (A'.π (C'.pos j))[i]? = some z →
        ∃ u, (A.π (C.pos (L j)))[i]? = some u := by
      intro z hz
      have hi := (List.getElem?_eq_some_iff.mp hz).1
      rw [(A'.labelled Θ hΘ).length_eq, ← (A.labelled Θ hΘ).length_eq (L j)] at hi
      exact ⟨_, List.getElem?_eq_getElem hi⟩
    rcases hor with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · obtain ⟨u, hu⟩ := hterm h₃
      exact ⟨u, Or.inr ⟨Θ, hΘ, _, hN, _, h₁, i, hu, h₃⟩, Or.inr ⟨Θ, hΘ, _, hN, _, h₂, i, hu, h₄⟩⟩
    · obtain ⟨u, hu⟩ := hterm h₃
      exact ⟨u, Or.inr ⟨Θ, hΘ, _, hN, _, h₂, i, hu, h₄⟩, Or.inr ⟨Θ, hΘ, _, hN, _, h₁, i, hu, h₃⟩⟩

include hR hterm H in
/-- Two `i`th terms at the ends of a border cell outside the image of `ζ` are connected in `H`. -/
theorem same_of_step {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {j i : ℕ}
    (hni : (A'.C Θ hΘ).cell j ∉ ζc '' A.Γ.C) {x y : α}
    (hx : (A'.π ((A'.C Θ hΘ).pos j))[i]? = some x)
    (hy : (A'.π ((A'.C Θ hΘ).pos (j + 1)))[i]? = some y) : sameComponent R x y := by
  have hl := A'.link_of_ne hΘ (H.cell_ne_cut hΘ hni) hx hy
  have hxm := A'.mem_of_getElem? hΘ hx
  rcases hl with rfl | hl
  · have hV : x ∈ R.verts := by
      rw [hR.verts_eq]
      exact A'.h.border_subset _ ⟨(A'.C Θ hΘ).mem_N j, cuff_subset_bd hΘ
        ((A'.C Θ hΘ).mem_cuff j)⟩ hxm
    exact sameComponent_iff.mpr ⟨hV, hV, SimpleGraph.Reachable.refl _⟩
  · refine sameComponent_of_adj (hterm _ ((A'.C Θ hΘ).cell_mem j) (A'.isBorder_cell hΘ j) hni x y
    hl ?_)
    intro hmem
    exact Set.disjoint_left.mp (A'.h.border_disjoint _ ⟨(A'.C Θ hΘ).mem_N j,
      cuff_subset_bd hΘ ((A'.C Θ hΘ).mem_cuff j)⟩) hxm hmem

include hR hterm H in
/-- Claim (9) of the proof of (9.1). -/
theorem claim_9 {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {n n₁' n₂' : X.S} (hn : n ∈ A.Γ.N ∩ Θ)
    (h₁ : n₁' ∈ ζn n ∩ Θ) (h₂ : n₂' ∈ ζn n ∩ Θ) {i : ℕ} {x y : α} (hx : (A'.π n₁')[i]? = some x)
    (hy : (A'.π n₂')[i]? = some y) : sameComponent R x y := by
  obtain ⟨L, -, hmono, hpos, hstep, hlt, -⟩ := H.exists_lift' hΘ
  set C := A.C Θ hΘ
  set C' := A'.C Θ hΘ
  have hchain : ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → L m₁ = L m₂ → ∀ {x y : α},
      (A'.π (C'.pos m₁))[i]? = some x → (A'.π (C'.pos m₂))[i]? = some y → sameComponent R x y := by
    intro m₁ m₂ hm
    induction m₂, hm using Nat.le_induction with
    | base =>
      intro _ x y hx hy
      rw [hx] at hy
      obtain rfl := Option.some.inj hy
      have hV : x ∈ R.verts := by
        rw [hR.verts_eq]
        exact A'.h.border_subset _ ⟨C'.mem_N m₁, cuff_subset_bd hΘ (C'.mem_cuff m₁)⟩
          (A'.mem_of_getElem? hΘ hx)
      exact sameComponent_iff.mpr ⟨hV, hV, SimpleGraph.Reachable.refl _⟩
    | succ m hm ih =>
      intro hL x y hx hy
      have h₃ : L m = L m₁ := le_antisymm (hL ▸ hmono (Nat.le_succ m)) (hmono hm)
      obtain ⟨z, hz⟩ := A'.exists_term hΘ (m' := m) hx
      have hni : C'.cell m ∉ ζc '' A.Γ.C := by
        rcases hstep m with ⟨-, h₄⟩ | ⟨h₄, -⟩
        · exact h₄
        · omega
      exact (ih h₃.symm hx hz).trans (same_of_step H hR hterm hΘ hni hz hy)
  obtain ⟨m₁, hm₁, rfl⟩ := C'.exists_pos n₁' ⟨H.infl.node_subset _ hn.1 h₁.1, h₁.2⟩
  obtain ⟨m₂, hm₂, rfl⟩ := C'.exists_pos n₂' ⟨H.infl.node_subset _ hn.1 h₂.1, h₂.2⟩
  have heq : L m₁ = L m₂ := by
    have h₃ := H.pos_eq_of_mem' hΘ hn.1 h₁.1 (hpos m₁)
    have h₄ := H.pos_eq_of_mem' hΘ hn.1 h₂.1 (hpos m₂)
    have h₅ := C.mod_eq_of_pos_eq (h₃.symm.trans h₄)
    rwa [Nat.mod_eq_of_lt (hlt m₁ hm₁), Nat.mod_eq_of_lt (hlt m₂ hm₂)] at h₅
  rcases le_total m₁ m₂ with h₃ | h₃
  · exact hchain h₃ heq hx hy
  · exact (hchain h₃ heq.symm hy hx).symm

include hR hterm H in
/-- Claim (10) of the proof of (9.1), for all marches around the cuff. -/
theorem claim_10 {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) {n₁ n₂ n₁' n₂' : X.S} (hn₁ : n₁ ∈ A.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ A.Γ.N ∩ Θ) (h₁ : n₁' ∈ ζn n₁ ∩ Θ) (h₂ : n₂' ∈ ζn n₂ ∩ Θ) {i j : ℕ} {v x y : α}
    (hv₁ : (A.π n₁)[i]? = some v) (hv₂ : (A.π n₂)[j]? = some v) (hx : (A'.π n₁')[i]? = some x)
    (hy : (A'.π n₂')[j]? = some y) : sameComponent R x y := by
  set C := A.C Θ hΘ
  set C' := A'.C Θ hΘ
  let G : X.S → Prop := fun n ↦ ∀ n' ∈ ζn n ∩ Θ, ∀ (i : ℕ) (y : α), (A.π n)[i]? = some v →
    (A'.π n')[i]? = some y → sameComponent R x y
  obtain ⟨a, -, rfl⟩ := C.exists_pos n₁ hn₁
  obtain ⟨b, -, rfl⟩ := C.exists_pos n₂ hn₂
  have hb₁ := A.mem_of_getElem? hΘ hv₁
  have hb₂ := A.mem_of_getElem? hΘ hv₂
  have hmem : ∀ m, C.pos m ∈ A.Γ.N ∩ Θ := fun m ↦ ⟨C.mem_N m, C.mem_cuff m⟩
  have hbase : G (C.pos a) := by
    intro n' hn' i₂ y hi₂ hy₂
    obtain rfl := eq_of_getElem?_eq ((A.labelled Θ hΘ).nodup a) hi₂ hv₁
    exact claim_9 H hR hterm hΘ (hmem a) h₁ hn' hx hy₂
  have hG : G (C.pos b) := by
    refine A.walk hΘ G (a := a) ?_ ?_ hb₁ hb₂ hbase
    · intro k hk₁ hk₂ hk n' hn' i₂ y₂ hi₂ hy₂
      obtain ⟨i₁, hi₁⟩ := A.exists_getElem? hΘ hk₁
      obtain ⟨m', hm', hp₁, hp₂⟩ := H.border_cell_facts hΘ k
      obtain ⟨w, hw₁, hw₂⟩ := H.transfer_fwd hΘ hm' hi₁ hi₂
      exact (hk _ ⟨hp₁, C'.mem_cuff m'⟩ i₁ w hi₁ hw₁).trans
        (claim_9 H hR hterm hΘ (hmem _) ⟨hp₂, C'.mem_cuff _⟩ hn' hw₂ hy₂)
    · intro k hk₁ hk₂ hk n' hn' i₁ y₂ hi₁ hy₂
      obtain ⟨i₂, hi₂⟩ := A.exists_getElem? hΘ hk₂
      obtain ⟨m', hm', hp₁, hp₂⟩ := H.border_cell_facts hΘ k
      obtain ⟨w, hw₁, hw₂⟩ := H.transfer_fwd hΘ hm' hi₁ hi₂
      exact (hk _ ⟨hp₂, C'.mem_cuff _⟩ i₂ w hi₂ hw₂).trans
        (claim_9 H hR hterm hΘ (hmem _) ⟨hp₁, C'.mem_cuff m'⟩ hn' hw₁ hy₂)
  exact hG _ h₂ j y hv₂ hy

include hR hnode H in
/-- The nodes of one `ζ(n)` are connected in `H`, which is part of claim (8) of the proof of (9.1).
-/
theorem claim_8 {n a b : X.S} (hn : n ∈ A.Γ.N) (ha : a ∈ ζn n) (hb : b ∈ ζn n) :
    sameComponent R (A'.h.node a) (A'.h.node b) := by
  have key : ∀ w : ζn n, (A'.Γ.sk.induce (ζn n)).Reachable ⟨a, ha⟩ w →
      sameComponent R (A'.h.node a) (A'.h.node w.1) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl =>
      have hV : A'.h.node a ∈ R.verts := by
        rw [hR.verts_eq]
        exact A'.h.node_mem _ (H.infl.node_subset _ hn ha)
      exact sameComponent_iff.mpr ⟨hV, hV, SimpleGraph.Reachable.refl _⟩
    | @tail z w _ hzw ih =>
      exact ih.trans (sameComponent_of_adj (hnode n hn _ z.2 _ w.2 hzw))
  exact key ⟨b, hb⟩ (H.infl.node_connected n hn _ _)

include hR hnode hterm H in
/-- Claim (11) of the proof of (9.1). -/
theorem claim_11 {v : α} (hv : v ∈ Q.G.vertexSet) {a b : α} (ha : a ∈ etaVert A A' ζn v)
    (hb : b ∈ etaVert A A' ζn v) : sameComponent R a b := by
  have hnot : ∀ {n n₀ : X.S} {Θ : Set X.S} {i : ℕ}, Θ ∈ cuffs X.S → n ∈ A.Γ.N → n₀ ∈ A.Γ.N ∩ Θ →
      (A.π n₀)[i]? = some (A.h.node n) → False := by
    intro n n₀ Θ i hΘ hn hn₀ hi
    exact Set.disjoint_left.mp (A.h.border_disjoint _ ⟨hn₀.1, cuff_subset_bd hΘ hn₀.2⟩)
      (A.mem_border_of_term hΘ hn₀ hi) ⟨n, hn, rfl⟩
  rcases ha with ⟨n₁, h₁, rfl, n₁', h₃, rfl⟩ | ⟨Θ₁, hΘ₁, n₁, h₁, n₁', h₃, i, h₅, h₆⟩ <;>
    rcases hb with ⟨n₂, h₁', hv', n₂', h₃', rfl⟩ | ⟨Θ₂, hΘ₂, n₂, h₁', n₂', h₃', j, h₅', h₆'⟩
  · obtain rfl := A.h.node_injOn h₁ h₁' hv'.symm
    exact claim_8 H hR hnode h₁ h₃ h₃'
  · exact (hnot hΘ₂ h₁ h₁' h₅').elim
  · subst hv'
    exact (hnot hΘ₁ h₁' h₁ h₅).elim
  · have hm₁ := A.mem_border_of_term hΘ₁ h₁ h₅
    have hm₂ := A.mem_border_of_term hΘ₂ h₁' h₅'
    by_cases hΘ : Θ₁ = Θ₂
    · subst hΘ
      exact claim_10 H hR hterm hΘ₁ h₁ h₁' h₃ h₃' h₅ h₅' h₆ h₆'
    · exact (Set.disjoint_left.mp (A.h.border_cuffs _ hΘ₁ _ hΘ₂ hΘ _ h₁ _ h₁') hm₁ hm₂).elim

include H in
/-- The main step of the proof of (9.1): `P` is simulated in `P'`. -/
theorem InflationHyp.simulated : Simulated Q Q' := by
  obtain ⟨R, hR, hadj, hnode, hterm⟩ := exists_realization H
  refine ⟨_, _, H.isExpansion, R, hR, fun v hv ↦ ?_⟩
  have hsub : etaVert A A' ζn v ⊆ R.verts := by
    rw [hR.verts_eq]
    exact H.eta_subset v
  refine (exists_isComponent_verts_eq_iff (H.claim_2 hv) hsub).mpr
    ⟨fun a ha b hab ↦ ?_, fun a ha b hb ↦ claim_11 H hR hnode hterm hv ha hb⟩
  obtain ⟨u, h₁, h₂⟩ := claim_12 H (hadj a b hab)
  by_cases huv : u = v
  · exact huv ▸ h₂
  · exact absurd ha (Set.disjoint_left.mp (H.claim_4 huv) h₁)

end Main

/-- Graph Minors XX, (8.1) (page 348), to be derived from (2.1) of Graph Minors XIX: "Let $\Sigma$
be a surface and let $\Omega$ be a well-quasi-order. For each $i \ge 1$ let
$\Gamma_i$ be a 3-connected painting in $\Sigma$ and let $\phi_i : \mathcal{C}(\Gamma_i) \to
E(\Omega)$ be a function. Then there exist $j > i \ge 1$ and a linear inflation $\zeta$ of
$\Gamma_i$ in $\Gamma_j$ such that $\phi_i(c) \le \phi_j(\zeta(c))$ for each $c \in
\mathcal{C}(\Gamma_i)$." -/
def Theorem81Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] {Ω : Type w} [Preorder Ω], IsSurface S → ConnectedSpace S →
    WellQuasiOrderedLE Ω → ∀ (Γ : ℕ → Painting S) (φ : ℕ → Set S → Ω),
    (∀ i, (Γ i).IsThreeConnected) →
    ∃ i j, i < j ∧ ∃ (ζn : S → Set S) (ζc : Set S → Set S), IsLinearInflation (Γ i) (Γ j) ζn ζc ∧
      ∀ c ∈ (Γ i).C, φ i c ≤ φ j (ζc c)

/-- A bound for the marches of border cells. -/
theorem Side.bounded {Ω : Type*} {X : GradedSurface} {F : CuffParam X.S} {Q :
  Patchwork Ω α β}
    (A : Side X F Q) {r : ℕ} (hr : ∀ Θ ∈ cuffs X.S, X.ρ Θ ≤ r) : A.Bounded (2 * r + 2) := by
  intro c hc hb
  obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
  obtain ⟨m, -, rfl⟩ := (A.C Θ hΘ).exists_cell c hc hcΘ
  set C := A.C Θ hΘ
  let l : List α := [A.h.node (C.pos m), A.h.node (C.pos (m + 1))] ++ A.π (C.pos m) ++
    A.π (C.pos (m + 1))
  have hl : l.length = 2 + X.ρ Θ + X.ρ Θ := by
    have h₁ : (A.π (C.pos m)).length = X.ρ Θ := (A.labelled Θ hΘ).length_eq m
    have h₂ : (A.π (C.pos (m + 1))).length = X.ρ Θ := (A.labelled Θ hΘ).length_eq (m + 1)
    simp only [l, List.length_append, List.length_cons, List.length_nil]
    omega
  have hsub : ∀ x ∈ Q.μ (A.h.cell (C.cell m)), x ∈ l := by
    intro x hx
    have hd : A.h.cell (C.cell m) ∈ Q.dom := by
      rw [A.dom_eq]
      exact A.h.cell_bijOn.mapsTo hc
    have h₁ : x ∈ {v | v ∈ Q.μ (A.h.cell (C.cell m))} := hx
    rw [Q.μ_set _ hd, show Q.G.ends (A.h.cell (C.cell m)) = _ from A.h.ends_border _ hc hb,
      C.tilde_eq] at h₁
    have hmem : ∀ k, x ∈ A.h.border (C.pos k) → x ∈ A.π (C.pos k) := fun k hk ↦ by
      rw [← (A.labelled Θ hΘ).set_eq k] at hk
      exact hk
    simp only [l, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases h₁ with ⟨n, hn, rfl⟩ | h₁
    · rcases hn with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inl (Or.inr rfl))
    · simp only [mem_iUnion, exists_prop] at h₁
      obtain ⟨n, hn, hx₂⟩ := h₁
      rcases hn with rfl | rfl
      · exact Or.inl (Or.inr (hmem _ hx₂))
      · exact Or.inr (hmem _ hx₂)
  have := length_le_of_subset (A.μ_nodup hc) hsub
  have h₂ := hr Θ hΘ
  omega


end GraphMinor.GM20
