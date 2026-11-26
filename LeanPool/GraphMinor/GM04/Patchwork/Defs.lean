/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Hypergraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.WellQuasiOrder

/-!
# Patchworks and their containment relation (Graph Minors IV, Sections 6–8)

This file formalizes the definitions of Graph Minors IV, Sections 6, 7 and 8 (pages 240–248):

* `completeSubgraph V` (`K_V`) and `emptySubgraph V` (`N_V`), represented as subgraphs of
  `⊤ : SimpleGraph α`.
* `componentVerts`, `component`, `IsComponent`: connected components of a subgraph `K` of
  `⊤ : SimpleGraph α`, defined via `SimpleGraph.Subgraph.coe` and `SimpleGraph.Reachable`.
* `IsCompleteSubgraph`, `IsGrouping`, `IsPairing`, `Pairs`: groupings, pairings, and when a
  pairing pairs two disjoint vertex sets `X, Y`, together with simpler equivalent characterizations.
* `Patch`: a patch `Δ` with its vertex set `V(Δ)` (`Δ.verts`) and its set of groupings
  (`Δ.groupings`), along with `Patch.IsFree`, `freePatch`, and `Patch.IsRobust`.
* `Patchwork Ω α β`: an `Ω`-patchwork `(G, μ, Δ, φ)` (conditions (i)–(iv) of Section 6) and
  `Patchwork.IsRobust`.
* `realizationOf` and `Patchwork.IsRealization`: realizations of an `Ω`-patchwork.
* `MarchCorresponds`, `marchEquiv`, `marchMapSubgraph`: the march bijection `π → π'` between the
  term sets of two marches of the same length, and the induced map on subgraphs.
* `IsExpansion`: expansions `(ηv, ηe)` of an `Ω`-patchwork `P` in `P'` (conditions (i)–(ix) of
  Section 7).
* `RootedHypergraph.deleteEdges` (`G \ F`), `Patchwork.deleteEdges` (`P \ F`), `Realizes`,
  `IsRealizableExpansion`, and `Simulated`.
* `Patchwork.restrict` (`P | G'`), `Patchwork.IsRemovableEdge`, and `Patchwork.IsRemovable`
  (Section 8).
-/

@[expose] public section

namespace GraphMinor.GM04

open SimpleGraph

variable {Ω α β α' β' : Type*}

/-! ### Complete and edgeless subgraphs `K_V` and `N_V`, and components -/

/-- `K_V`, the complete graph on `V` (Graph Minors IV, Section 6, page 241): "If $V$ is a finite set
we denote by $K_V$ the complete graph on $V$, that is, the simple
graph with vertex set $V$ and edge set the set of all subsets of $V$ of cardinality 2, with
the natural incidence relation." -/
def completeSubgraph (V : Set α) : (⊤ : SimpleGraph α).Subgraph :=
  (⊤ : (⊤ : SimpleGraph α).Subgraph).induce V

@[simp]
theorem completeSubgraph_verts (V : Set α) : (completeSubgraph V).verts = V := rfl

@[simp]
theorem completeSubgraph_adj {V : Set α} {u v : α} :
    (completeSubgraph V).Adj u v ↔ u ∈ V ∧ v ∈ V ∧ u ≠ v := Iff.rfl

@[simp]
theorem le_completeSubgraph_iff {V : Set α} {K : (⊤ : SimpleGraph α).Subgraph} :
    K ≤ completeSubgraph V ↔ K.verts ⊆ V := by
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun u v hadj ↦ ?_⟩⟩
  exact ⟨h (K.edge_vert hadj), h (K.edge_vert hadj.symm), hadj.ne⟩

/-- `N_V`, the graph with vertex set `V` and no edges (Graph Minors IV, Section 6, page 241):
"If $V$ is a finite set, $N_V$ denotes the graph with vertex set $V$ and no edges." -/
def emptySubgraph (V : Set α) : (⊤ : SimpleGraph α).Subgraph where
  verts := V
  Adj _ _ := False
  adj_sub := False.elim
  edge_vert := False.elim

@[simp]
theorem emptySubgraph_verts (V : Set α) : (emptySubgraph V).verts = V := rfl

@[simp]
theorem not_emptySubgraph_adj {V : Set α} {u v : α} : ¬(emptySubgraph V).Adj u v := id

@[simp]
theorem emptySubgraph_le_iff {V : Set α} {K : (⊤ : SimpleGraph α).Subgraph} :
    emptySubgraph V ≤ K ↔ V ⊆ K.verts :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ ↦ False.elim⟩⟩

/-- The vertex set of the component of `K` containing `x : K.verts`: the vertices of `K` that are
reachable from `x` in `K.coe`. -/
def componentVerts (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) : Set α :=
  {w | ∃ hw : w ∈ K.verts, K.coe.Reachable x ⟨w, hw⟩}

@[simp]
theorem mem_componentVerts_iff {K : (⊤ : SimpleGraph α).Subgraph} {x : K.verts} {w : α} :
    w ∈ componentVerts K x ↔ ∃ hw : w ∈ K.verts, K.coe.Reachable x ⟨w, hw⟩ := Iff.rfl

theorem componentVerts_subset (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) :
    componentVerts K x ⊆ K.verts :=
  fun _ ⟨hw, _⟩ ↦ hw

theorem self_mem_componentVerts (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) :
    (x : α) ∈ componentVerts K x :=
  ⟨x.2, Reachable.refl x⟩

theorem componentVerts_eq_iff {K : (⊤ : SimpleGraph α).Subgraph} {x y : K.verts} :
    componentVerts K x = componentVerts K y ↔ K.coe.Reachable x y := by
  constructor
  · intro h
    have hy : (y : α) ∈ componentVerts K x := h ▸ self_mem_componentVerts K y
    obtain ⟨_, hr⟩ := hy
    exact hr
  · intro hxy
    ext w
    simp only [mem_componentVerts_iff]
    exact ⟨fun ⟨hw, hr⟩ ↦ ⟨hw, hxy.symm.trans hr⟩, fun ⟨hw, hr⟩ ↦ ⟨hw, hxy.trans hr⟩⟩

/-- The connected component of `K` containing `x : K.verts`, as an induced subgraph of `K`. -/
def component (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) : (⊤ : SimpleGraph α).Subgraph :=
  K.induce (componentVerts K x)

@[simp]
theorem component_verts (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) :
    (component K x).verts = componentVerts K x := rfl

@[simp]
theorem component_adj {K : (⊤ : SimpleGraph α).Subgraph} {x : K.verts} {u v : α} :
    (component K x).Adj u v ↔
      u ∈ componentVerts K x ∧ v ∈ componentVerts K x ∧ K.Adj u v := Iff.rfl

theorem component_le (K : (⊤ : SimpleGraph α).Subgraph) (x : K.verts) :
    component K x ≤ K := by
  refine ⟨componentVerts_subset K x, fun u v h ↦ h.2.2⟩

theorem component_eq_iff {K : (⊤ : SimpleGraph α).Subgraph} {x y : K.verts} :
    component K x = component K y ↔ K.coe.Reachable x y := by
  refine ⟨fun h ↦ componentVerts_eq_iff.mp (congrArg Subgraph.verts h), fun h ↦ ?_⟩
  have hv : componentVerts K x = componentVerts K y := componentVerts_eq_iff.mpr h
  simp only [component, hv]

/-- `D` is a connected component of `K`: `D` is `component K x` for some vertex `x` of `K`. -/
def IsComponent (K D : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  ∃ x : K.verts, D = component K x

theorem IsComponent.verts_nonempty {K D : (⊤ : SimpleGraph α).Subgraph} (h : IsComponent K D) :
    D.verts.Nonempty := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x.1, self_mem_componentVerts K x⟩

theorem IsComponent.le {K D : (⊤ : SimpleGraph α).Subgraph} (h : IsComponent K D) : D ≤ K := by
  obtain ⟨x, rfl⟩ := h
  exact component_le K x

theorem IsComponent.eq_of_mem {K D₁ D₂ : (⊤ : SimpleGraph α).Subgraph}
    (h₁ : IsComponent K D₁) (h₂ : IsComponent K D₂) {v : α} (hv₁ : v ∈ D₁.verts)
    (hv₂ : v ∈ D₂.verts) : D₁ = D₂ := by
  obtain ⟨x₁, rfl⟩ := h₁
  obtain ⟨x₂, rfl⟩ := h₂
  obtain ⟨hv, hr₁⟩ := hv₁
  obtain ⟨_, hr₂⟩ := hv₂
  exact component_eq_iff.mpr (hr₁.trans hr₂.symm)

theorem IsComponent.disjoint_verts_of_ne {K D₁ D₂ : (⊤ : SimpleGraph α).Subgraph}
    (h₁ : IsComponent K D₁) (h₂ : IsComponent K D₂) (hne : D₁ ≠ D₂) :
    Disjoint D₁.verts D₂.verts :=
  Set.disjoint_left.mpr fun _ hv₁ hv₂ ↦ hne (h₁.eq_of_mem h₂ hv₁ hv₂)

/-! ### Groupings and pairings -/

/-- A subgraph `D` is complete if it equals the complete graph `K_{V(D)}` on its vertex set. -/
def IsCompleteSubgraph (D : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  D = completeSubgraph D.verts

theorem isCompleteSubgraph_iff {D : (⊤ : SimpleGraph α).Subgraph} :
    IsCompleteSubgraph D ↔ ∀ u ∈ D.verts, ∀ v ∈ D.verts, u ≠ v → D.Adj u v := by
  refine ⟨fun h u hu v hv hne ↦ ?_, fun h ↦ ?_⟩
  · rw [h]
    exact ⟨hu, hv, hne⟩
  · ext u v
    · rfl
    · exact ⟨fun hadj ↦ ⟨D.edge_vert hadj, D.edge_vert hadj.symm, hadj.ne⟩,
        fun ⟨hu, hv, hne⟩ ↦ h u hu v hv hne⟩

/-- A grouping in `V` (Graph Minors IV, Section 6, page 241): "A *grouping* in $V$ is a subgraph of
$K_V$ every component of which is complete." -/
def IsGrouping (V : Set α) (K : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  K ≤ completeSubgraph V ∧ ∀ D, IsComponent K D → IsCompleteSubgraph D

/-- A subgraph `K` is a grouping in `V` if and only if `V(K) ⊆ V` and adjacency in `K` is
transitive on distinct vertices. -/
theorem isGrouping_iff {V : Set α} {K : (⊤ : SimpleGraph α).Subgraph} :
    IsGrouping V K ↔ K.verts ⊆ V ∧ ∀ a b c, a ≠ c → K.Adj a b → K.Adj b c → K.Adj a c := by
  constructor
  · rintro ⟨hKV, hcomp⟩
    refine ⟨le_completeSubgraph_iff.mp hKV, fun a b c hac hab hbc ↦ ?_⟩
    have ha : a ∈ K.verts := K.edge_vert hab
    have hb : b ∈ K.verts := K.edge_vert hbc
    have hc : c ∈ K.verts := K.edge_vert hbc.symm
    let x : K.verts := ⟨a, ha⟩
    have hD := isCompleteSubgraph_iff.mp (hcomp (component K x) ⟨x, rfl⟩)
    have haD : a ∈ (component K x).verts := self_mem_componentVerts K x
    have hcD : c ∈ (component K x).verts := by
      refine ⟨hc, ?_⟩
      exact (Adj.reachable hab.coe).trans (Adj.reachable hbc.coe)
    exact (hD a haD c hcD hac).2.2
  · rintro ⟨hKV, htrans⟩
    refine ⟨le_completeSubgraph_iff.mpr hKV, ?_⟩
    rintro D ⟨x, rfl⟩
    rw [isCompleteSubgraph_iff]
    intro u ⟨hu, hxu⟩ v ⟨hv, hxv⟩ huv
    refine ⟨⟨hu, hxu⟩, ⟨hv, hxv⟩, ?_⟩
    have hreach : K.coe.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := hxu.symm.trans hxv
    suffices ∀ (y z : K.verts), K.coe.Reachable y z → y.1 ≠ z.1 → K.Adj y.1 z.1 from
      this ⟨u, hu⟩ ⟨v, hv⟩ hreach huv
    intro y z hr
    rw [reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => intro hne; exact absurd rfl hne
    | @tail w z _ hwz ih =>
      intro hyz
      by_cases hyw : y.1 = w.1
      · rw [hyw]
        exact hwz
      · exact htrans y.1 w.1 z.1 hyz (ih hyw) hwz

/-- A pairing in `V` (Graph Minors IV, Section 6, page 241): "A *pairing* in $V$ is a grouping in
$V$ every component of which has at most two vertices." -/
def IsPairing (V : Set α) (K : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  IsGrouping V K ∧ ∀ D, IsComponent K D → D.verts.encard ≤ 2

/-- For finite `V`, a subgraph `K` is a pairing in `V` if and only if `V(K) ⊆ V` and every vertex
is adjacent to at most one vertex in `K`. -/
theorem isPairing_iff {V : Set α} (hV : V.Finite) {K : (⊤ : SimpleGraph α).Subgraph} :
    IsPairing V K ↔ K.verts ⊆ V ∧ ∀ a b c, K.Adj a b → K.Adj a c → b = c := by
  constructor
  · rintro ⟨⟨hKV, _⟩, hcard⟩
    have hKsub : K.verts ⊆ V := le_completeSubgraph_iff.mp hKV
    refine ⟨hKsub, fun a b c hab hac ↦ ?_⟩
    by_contra hbc
    have ha : a ∈ K.verts := K.edge_vert hab
    have hb : b ∈ K.verts := K.edge_vert hab.symm
    have hc : c ∈ K.verts := K.edge_vert hac.symm
    let x : K.verts := ⟨a, ha⟩
    have hle : (componentVerts K x).ncard ≤ 2 :=
      ((Set.encard_le_coe_iff_finite_ncard_le (k := 2)).mp (hcard (component K x) ⟨x, rfl⟩)).2
    have haD : a ∈ componentVerts K x := self_mem_componentVerts K x
    have hbD : b ∈ componentVerts K x := ⟨hb, Adj.reachable hab.coe⟩
    have hcD : c ∈ componentVerts K x := ⟨hc, Adj.reachable hac.coe⟩
    have hsub : ({a, b, c} : Set α) ⊆ componentVerts K x := by
      intro z hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have h3 : ({a, b, c} : Set α).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hbc]
      simp [hab.ne, hac.ne]
    have hfin : (componentVerts K x).Finite :=
      hV.subset ((componentVerts_subset K x).trans hKsub)
    have hle3 := Set.ncard_le_ncard hsub hfin
    omega
  · rintro ⟨hKV, huniq⟩
    have hgrp : IsGrouping V K := by
      rw [isGrouping_iff]
      refine ⟨hKV, fun a b c hac hab hbc ↦ ?_⟩
      exfalso
      exact hac (huniq b a c hab.symm hbc)
    refine ⟨hgrp, ?_⟩
    rintro D ⟨x, rfl⟩
    have hreach_sub : ∀ y : K.verts, K.coe.Reachable x y →
        y.1 = x.1 ∨ K.Adj x.1 y.1 := by
      intro y hr
      rw [reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => exact Or.inl rfl
      | @tail z w _ hzw ih =>
        rcases ih with hzx | hxz
        · right
          rw [← hzx]
          exact hzw
        · left
          exact (huniq z.1 x.1 w.1 hxz.symm hzw).symm
    by_cases h : ∃ b, K.Adj x.1 b
    · obtain ⟨b, hab⟩ := h
      have hsub : (component K x).verts ⊆ {x.1, b} := by
        rintro w ⟨hw, hr⟩
        rcases hreach_sub ⟨w, hw⟩ hr with hwx | hxw
        · exact Or.inl hwx
        · exact Or.inr (huniq x.1 b w hab hxw).symm
      exact (Set.encard_mono hsub).trans_eq (Set.encard_pair hab.ne)
    · push Not at h
      have hsub : (component K x).verts ⊆ {x.1} := by
        rintro w ⟨hw, hr⟩
        rcases hreach_sub ⟨w, hw⟩ hr with hwx | hxw
        · exact hwx
        · exact (h w hxw).elim
      exact (Set.encard_mono hsub).trans (by simp)

/-- `K` pairs `X, Y` in `V` (Graph Minors IV, Section 6, page 241): "If $K$ is a pairing in $V$, we
say that $K$ *pairs* $X, Y$ if $X, Y \subseteq V$ are
disjoint and (i) every 2-vertex component of $K$ has one vertex in $X$ and the other in $Y$,
and (ii) every vertex of $X \cup Y$ belongs to some 2-vertex component of $K$." -/
structure Pairs (V : Set α) (K : (⊤ : SimpleGraph α).Subgraph) (X Y : Set α) : Prop where
  subset_left : X ⊆ V
  subset_right : Y ⊆ V
  disjoint : Disjoint X Y
  /-- (i) Every 2-vertex component of `K` has one vertex in `X` and the other in `Y`. -/
  two_vert_component : ∀ D, IsComponent K D → D.verts.ncard = 2 →
    (D.verts ∩ X).Nonempty ∧ (D.verts ∩ Y).Nonempty
  /-- (ii) Every vertex of `X ∪ Y` belongs to some 2-vertex component of `K`. -/
  mem_two_vert_component : ∀ v ∈ X ∪ Y, ∃ D, IsComponent K D ∧ D.verts.ncard = 2 ∧ v ∈ D.verts

/-- For a pairing `K` in a finite set `V`, `K` pairs `X, Y` if and only if `X, Y ⊆ V` are disjoint,
every edge of `K` joins a vertex of `X` and a vertex of `Y`, and every vertex of `X ∪ Y` is
incident with an edge of `K`. -/
theorem pairs_iff_of_isPairing {V : Set α} (hV : V.Finite) {K : (⊤ : SimpleGraph α).Subgraph}
    (hK : IsPairing V K) {X Y : Set α} :
    Pairs V K X Y ↔ X ⊆ V ∧ Y ⊆ V ∧ Disjoint X Y ∧
      (∀ u v, K.Adj u v → (u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) ∧
      (∀ v ∈ X ∪ Y, ∃ w, K.Adj v w) := by
  have hKsub : K.verts ⊆ V := le_completeSubgraph_iff.mp hK.1.1
  constructor
  · intro hP
    refine ⟨hP.subset_left, hP.subset_right, hP.disjoint, fun u v huv ↦ ?_, fun v hv ↦ ?_⟩
    · have hu : u ∈ K.verts := K.edge_vert huv
      have hv : v ∈ K.verts := K.edge_vert huv.symm
      let x : K.verts := ⟨u, hu⟩
      have hcomp : IsComponent K (component K x) := ⟨x, rfl⟩
      have huD : u ∈ (component K x).verts := self_mem_componentVerts K x
      have hvD : v ∈ (component K x).verts := ⟨hv, Adj.reachable huv.coe⟩
      have hsub : ({u, v} : Set α) ⊆ (component K x).verts := by
        intro z hz
        rcases hz with rfl | rfl <;> assumption
      have hfin : (component K x).verts.Finite :=
        hV.subset ((componentVerts_subset K x).trans hKsub)
      have h2le : 2 ≤ (component K x).verts.ncard := by
        rw [← Set.ncard_pair huv.ne]
        exact Set.ncard_le_ncard hsub hfin
      have hle2 : (component K x).verts.ncard ≤ 2 :=
        ((Set.encard_le_coe_iff_finite_ncard_le (k := 2)).mp (hK.2 (component K x) hcomp)).2
      have hcard2 : (component K x).verts.ncard = 2 := le_antisymm hle2 h2le
      have hD_eq : (component K x).verts = {u, v} :=
        (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2, Set.ncard_pair huv.ne]) hfin).symm
      obtain ⟨⟨a, haD, haX⟩, ⟨b, hbD, hbY⟩⟩ := hP.two_vert_component (component K x) hcomp hcard2
      rw [hD_eq] at haD hbD
      rcases haD with rfl | rfl <;> rcases hbD with rfl | rfl
      · exact absurd hbY (Set.disjoint_left.mp hP.disjoint haX)
      · exact Or.inl ⟨haX, hbY⟩
      · exact Or.inr ⟨hbY, haX⟩
      · exact absurd hbY (Set.disjoint_left.mp hP.disjoint haX)
    · obtain ⟨D, hD, hcard2, hvD⟩ := hP.mem_two_vert_component v hv
      obtain ⟨a, b, hab, hD_eq⟩ := Set.ncard_eq_two.mp hcard2
      have hcomp := isCompleteSubgraph_iff.mp (hK.1.2 D hD)
      have hvab : v = a ∨ v = b := by
        have : v ∈ ({a, b} : Set α) := hD_eq ▸ hvD
        simpa using this
      rcases hvab with rfl | rfl
      · refine ⟨b, hD.le.2 (hcomp v hvD b ?_ hab)⟩
        rw [hD_eq]; exact Or.inr rfl
      · refine ⟨a, hD.le.2 (hcomp v hvD a ?_ hab.symm)⟩
        rw [hD_eq]; exact Or.inl rfl
  · rintro ⟨hX, hY, hdisj, hadj, hex⟩
    refine ⟨hX, hY, hdisj, fun D hD hcard2 ↦ ?_, fun v hv ↦ ?_⟩
    · obtain ⟨a, b, hab, hD_eq⟩ := Set.ncard_eq_two.mp hcard2
      have haD : a ∈ D.verts := by rw [hD_eq]; exact Or.inl rfl
      have hbD : b ∈ D.verts := by rw [hD_eq]; exact Or.inr rfl
      have hcomp := isCompleteSubgraph_iff.mp (hK.1.2 D hD)
      have hab_adj : K.Adj a b := (hD.le).2 (hcomp a haD b hbD hab)
      rcases hadj a b hab_adj with ⟨haX, hbY⟩ | ⟨haY, hbX⟩
      · exact ⟨⟨a, haD, haX⟩, ⟨b, hbD, hbY⟩⟩
      · exact ⟨⟨b, hbD, hbX⟩, ⟨a, haD, haY⟩⟩
    · obtain ⟨w, hvw⟩ := hex v hv
      have hvK : v ∈ K.verts := K.edge_vert hvw
      have hwK : w ∈ K.verts := K.edge_vert hvw.symm
      let x : K.verts := ⟨v, hvK⟩
      have hcomp : IsComponent K (component K x) := ⟨x, rfl⟩
      have hvD : v ∈ (component K x).verts := self_mem_componentVerts K x
      have hwD : w ∈ (component K x).verts := ⟨hwK, Adj.reachable hvw.coe⟩
      have hsub : ({v, w} : Set α) ⊆ (component K x).verts := by
        intro z hz
        rcases hz with rfl | rfl <;> assumption
      have hfin : (component K x).verts.Finite :=
        hV.subset ((componentVerts_subset K x).trans hKsub)
      have h2le : 2 ≤ (component K x).verts.ncard := by
        rw [← Set.ncard_pair hvw.ne]
        exact Set.ncard_le_ncard hsub hfin
      have hle2 : (component K x).verts.ncard ≤ 2 :=
        ((Set.encard_le_coe_iff_finite_ncard_le (k := 2)).mp (hK.2 (component K x) hcomp)).2
      exact ⟨component K x, hcomp, le_antisymm hle2 h2le, hvD⟩

/-! ### Patches -/

/-- A patch `Δ` (Graph Minors IV, Section 6, page 241): "A *patch* in $V$ is a collection $\Delta$
of groupings in $V$, each with the same vertex set
$V(\Delta) \subseteq V$." -/
@[ext]
structure Patch (α : Type*) where
  /-- The vertex set `V(Δ)` of the patch. -/
  verts : Set α
  /-- The collection of groupings belonging to the patch. -/
  groupings : Set ((⊤ : SimpleGraph α).Subgraph)
  /-- Every member of `Δ` is a grouping in `V(Δ)`. -/
  isGrouping : ∀ δ ∈ groupings, IsGrouping verts δ
  /-- Every member of `Δ` has vertex set `V(Δ)`. -/
  verts_eq : ∀ δ ∈ groupings, δ.verts = verts

instance : Membership ((⊤ : SimpleGraph α).Subgraph) (Patch α) where
  mem Δ δ := δ ∈ Δ.groupings

@[simp]
theorem Patch.mem_iff {Δ : Patch α} {δ : (⊤ : SimpleGraph α).Subgraph} :
    δ ∈ Δ.groupings ↔ δ ∈ Δ := Iff.rfl

/-- `Δ` is a patch in `V` if `V(Δ) ⊆ V`. -/
def Patch.IsIn (V : Set α) (Δ : Patch α) : Prop :=
  Δ.verts ⊆ V

/-- A patch `Δ` is free (Graph Minors IV, Section 6, page 241): "A patch $\Delta$ is *free* if it
contains every grouping in $V$ with vertex set $V(\Delta)$" -/
def Patch.IsFree (Δ : Patch α) : Prop :=
  ∀ δ : (⊤ : SimpleGraph α).Subgraph, IsGrouping Δ.verts δ → δ.verts = Δ.verts → δ ∈ Δ

/-- The free patch on a vertex set `U`: the patch with vertex set `U` containing every grouping in
`U` with vertex set `U`. -/
def freePatch (U : Set α) : Patch α where
  verts := U
  groupings := {δ | IsGrouping U δ ∧ δ.verts = U}
  isGrouping _ h := h.1
  verts_eq _ h := h.2

@[simp]
theorem freePatch_verts (U : Set α) : (freePatch U).verts = U := rfl

@[simp]
theorem mem_freePatch_iff {U : Set α} {δ : (⊤ : SimpleGraph α).Subgraph} :
    δ ∈ freePatch U ↔ IsGrouping U δ ∧ δ.verts = U := Iff.rfl

theorem freePatch_isFree (U : Set α) : (freePatch U).IsFree :=
  fun _ h₁ h₂ ↦ ⟨h₁, h₂⟩

/-- A patch `Δ` on a finite carrier is robust (Graph Minors IV, Section 6, page 241):
"it is *robust* if for every
choice of $X, Y \subseteq V(\Delta)$ with $|X| = |Y|$ and $X
\cap Y = \emptyset$, there is a pairing in $\Delta$ which pairs $X, Y$." -/
structure Patch.IsRobust (Δ : Patch α) : Prop where
  /-- The patch has a finite carrier. -/
  finite_verts : Δ.verts.Finite
  /-- Disjoint equicardinal subsets have a pairing in the patch. -/
  exists_pairing : ∀ X ⊆ Δ.verts, ∀ Y ⊆ Δ.verts, X.ncard = Y.ncard → Disjoint X Y →
    ∃ δ ∈ Δ, IsPairing Δ.verts δ ∧ Pairs Δ.verts δ X Y

/-! ### `Ω`-patchworks and realizations -/

/-- An `Ω`-patchwork `(G, μ, Δ, φ)` (Graph Minors IV, Section 6, page 241):
"Let $\Omega$ be a quasi-order. An $\Omega$-*patchwork* is a quadruple $(G, \mu, \Delta,
\phi)$, where (i) $G$ is a rooted hypergraph (ii) $\mu$ is a function with domain
$\operatorname{dom}(\mu) \subseteq E(G)$; and for each $e \in \operatorname{dom}(\mu)$,
$\mu(e)$ is a march with $\bar{\mu}(e) = V(e)$. (iii) $\Delta$ is a function with domain
$E(G)$, and for each $e \in E(G)$, $\Delta(e)$ is a patch with $V(\Delta(e)) = V(e)$; and
for each $e \in E(G) - \operatorname{dom}(\mu)$, $\Delta(e)$ is free (iv) $\phi$ is a
function from $E(G)$ into $E(\Omega)$." -/
structure Patchwork (Ω α β : Type*) where
  /-- (i) The underlying rooted hypergraph `G`. -/
  G : RootedHypergraph α β
  /-- The domain `dom(μ) ⊆ E(G)`. -/
  dom : Set β
  /-- (ii) The function `μ` assigning a march to each `e ∈ dom(μ)`. -/
  μ : β → List α
  /-- (iii) The function `Δ` assigning a patch to each `e ∈ E(G)`. -/
  Δ : β → Patch α
  /-- (iv) The function `φ` from `E(G)` into `Ω`. -/
  φ : β → Ω
  /-- (ii) `dom(μ) ⊆ E(G)`. -/
  dom_subset : dom ⊆ G.edgeSet
  /-- (ii) For each `e ∈ dom(μ)`, `μ(e)` is a march. -/
  μ_nodup : ∀ e ∈ dom, (μ e).Nodup
  /-- (ii) For each `e ∈ dom(μ)`, `μBar(e) = V(e)`. -/
  μ_set : ∀ e ∈ dom, {v | v ∈ μ e} = G.ends e
  /-- (iii) For each `e ∈ E(G)`, `V(Δ(e)) = V(e)`. -/
  Δ_verts : ∀ e ∈ G.edgeSet, (Δ e).verts = G.ends e
  /-- (iii) For each `e ∈ E(G) - dom(μ)`, `Δ(e)` is free. -/
  Δ_free : ∀ e ∈ G.edgeSet, e ∉ dom → (Δ e).IsFree

/-- An `Ω`-patchwork `(G, μ, Δ, φ)` is robust if each `Δ(e)` (`e ∈ E(G)`) is robust
(Graph Minors IV, Section 6, page 241). -/
def Patchwork.IsRobust (P : Patchwork Ω α β) : Prop :=
  ∀ e ∈ P.G.edgeSet, (P.Δ e).IsRobust

/-- The subgraph `N_{V(G)} ∪ ⋃ (δ_e : e ∈ E(G))` formed from a choice of `δ e` for each edge `e`
of `G`. -/
def realizationOf (G : Hypergraph α β) (δ : β → (⊤ : SimpleGraph α).Subgraph) :
    (⊤ : SimpleGraph α).Subgraph :=
  emptySubgraph G.vertexSet ⊔ ⨆ e ∈ G.edgeSet, δ e

@[simp]
theorem realizationOf_adj {G : Hypergraph α β} {δ : β → (⊤ : SimpleGraph α).Subgraph} {u v : α} :
    (realizationOf G δ).Adj u v ↔ ∃ e ∈ G.edgeSet, (δ e).Adj u v := by
  simp [realizationOf]

/-- A realization of an `Ω`-patchwork `(G, μ, Δ, φ)` (Graph Minors IV, Section 6, page 241):
"a subgraph of $K_{V(G)}$ expressible in the form $$N_{V(G)} \cup \bigcup (\delta_e: e \in
E(G))$$ where $\delta_e \in \Delta(e)$ for each $e \in E(G)$." -/
def Patchwork.IsRealization (P : Patchwork Ω α β) (H : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  ∃ δ : β → (⊤ : SimpleGraph α).Subgraph,
    (∀ e ∈ P.G.edgeSet, δ e ∈ P.Δ e) ∧ H = realizationOf P.G.toHypergraph δ

/-! ### The march bijection `π → π'` -/

/-- Two elements `x` and `y` correspond under the march bijection `π → π'` if they occur at the
same index in `π` and `π'`. -/
def MarchCorresponds (π : List α) (π' : List α') (x : α) (y : α') : Prop :=
  ∃ (i : ℕ) (hi : i < π.length) (hi' : i < π'.length), π[i] = x ∧ π'[i] = y

open Classical in
/-- The march bijection `π → π'` (Graph Minors IV, Section 7, page 244): "If $\pi, \pi'$ are marches
of the same length, we denote by $\pi \to \pi'$ the bijection
from $\bar{\pi}$ onto $\bar{\pi}'$ mapping $\pi$ to $\pi'$." -/
noncomputable def marchEquiv {π : List α} {π' : List α'} (hπ : π.Nodup) (hπ' : π'.Nodup)
    (hlen : π.length = π'.length) : {x // x ∈ π} ≃ {y // y ∈ π'} :=
  (hπ.getEquiv.symm.trans (finCongr hlen)).trans hπ'.getEquiv

theorem marchEquiv_apply_iff {π : List α} {π' : List α'} (hπ : π.Nodup) (hπ' : π'.Nodup)
    (hlen : π.length = π'.length) (x : {x // x ∈ π}) (y : {y // y ∈ π'}) :
    marchEquiv hπ hπ' hlen x = y ↔ MarchCorresponds π π' x.1 y.1 := by
  classical
  constructor
  · intro h
    let i : Fin π.length := hπ.getEquiv.symm x
    have hx : π[i.1] = x.1 := congrArg Subtype.val (hπ.getEquiv.apply_symm_apply x)
    have hy : π'[i.1] = y.1 := by
      have h' := congrArg Subtype.val h
      simpa [marchEquiv, i] using h'
    exact ⟨i.1, i.2, hlen ▸ i.2, hx, hy⟩
  · rintro ⟨i, hi, hi', hx, hy⟩
    apply Subtype.ext
    have hx' : (⟨π[i], List.getElem_mem hi⟩ : {x // x ∈ π}) = x := Subtype.ext hx
    have hidx : hπ.getEquiv.symm x = ⟨i, hi⟩ := by
      rw [← hx']
      apply hπ.getEquiv.injective
      simp [List.Nodup.getEquiv]
    simp [marchEquiv, hidx, hy]

/-- The image of a subgraph `δ` under the march bijection `π → π'`. -/
def marchMapSubgraph (π : List α) (π' : List α') (δ : (⊤ : SimpleGraph α).Subgraph) :
    (⊤ : SimpleGraph α').Subgraph where
  verts := {y | ∃ x ∈ δ.verts, MarchCorresponds π π' x y}
  Adj y₁ y₂ := y₁ ≠ y₂ ∧ ∃ x₁ x₂, MarchCorresponds π π' x₁ y₁ ∧ MarchCorresponds π π' x₂ y₂ ∧
    δ.Adj x₁ x₂
  adj_sub h := h.1
  edge_vert := by
    rintro y₁ y₂ ⟨_, x₁, x₂, hx₁, _, hadj⟩
    exact ⟨x₁, δ.edge_vert hadj, hx₁⟩
  symm := ⟨by
    rintro y₁ y₂ ⟨hne, x₁, x₂, hx₁, hx₂, hadj⟩
    exact ⟨hne.symm, x₂, x₁, hx₂, hx₁, δ.adj_symm hadj⟩⟩

/-! ### Expansions, edge deletion, and simulation (Section 7) -/

/-- `η = (ηv, ηe)` is an expansion of `P` in `P'` (Graph Minors IV, Section 7, page 244):
"Let $P = (G, \mu, \Delta, \phi)$, $P' = (G', \mu', \Delta', \phi')$ be $\Omega$-patchworks.
An *expansion* of $P$ in $P'$ is a function $\eta$ with domain $V(G) \cup E(G)$ such that
(i) for each $v \in V(G)$, $\eta(v)$ is a non-empty subset of $V(G')$, and for each $e \in
E(G)$, $\eta(e) \in E(G')$ (ii) for distinct $v_1, v_2 \in V(G)$, $\eta(v_1) \cap \eta(v_2)
= \emptyset$ (iii) for distinct $e_1, e_2 \in E(G)$, $\eta(e_1) \neq \eta(e_2)$ (iv) for
each $e \in E(G)$, $e \in \operatorname{dom}(\mu)$ if and only if $\eta(e) \in
\operatorname{dom}(\mu')$ (v) for each $e \in E(G) - \operatorname{dom}(\mu)$, if $v$ is an
end of $e$ in $G$ then $\eta(v)$ contains an end of $\eta(e)$ in $G'$ (vi) for each $e \in
\operatorname{dom}(\mu)$, $\mu(e)$ and $\mu'(\eta(e))$ have the same length, $k$, say, and
for $1 \le i \le k$, $\eta(v)$ contains the $i$th term of $\mu'(\eta(e))$ where $v$ is the
$i$th term of $\mu(e)$ (vii) $\pi(G)$ and $\pi(G')$ have the same length, $k$, say, and for
$1 \le i \le k$, $\eta(v)$ contains the $i$th term of $\pi(G')$ where $v$ is the $i$th term
of $\pi(G)$ (viii) for each $e \in \operatorname{dom}(\mu)$, $\mu(e) \to \mu'(\eta(e))$ maps
$\Delta(e)$ to $\Delta'(\eta(e))$ (ix) for each $e \in E(G)$, $\phi(e) \le \phi'(\eta(e))$." -/
structure IsExpansion [Preorder Ω] (P : Patchwork Ω α β) (P' : Patchwork Ω α' β')
    (ηv : α → Set α') (ηe : β → β') : Prop where
  /-- (i) For each `v ∈ V(G)`, `η(v)` is non-empty. -/
  vertex_nonempty : ∀ v ∈ P.G.vertexSet, (ηv v).Nonempty
  /-- (i) For each `v ∈ V(G)`, `η(v) ⊆ V(G')`. -/
  vertex_subset : ∀ v ∈ P.G.vertexSet, ηv v ⊆ P'.G.vertexSet
  /-- (i) For each `e ∈ E(G)`, `η(e) ∈ E(G')`. -/
  edge_mem : ∀ e ∈ P.G.edgeSet, ηe e ∈ P'.G.edgeSet
  /-- (ii) For distinct `v₁, v₂ ∈ V(G)`, `η(v₁) ∩ η(v₂) = ∅`. -/
  vertex_disjoint : ∀ v₁ ∈ P.G.vertexSet, ∀ v₂ ∈ P.G.vertexSet, v₁ ≠ v₂ →
    Disjoint (ηv v₁) (ηv v₂)
  /-- (iii) For distinct `e₁, e₂ ∈ E(G)`, `η(e₁) ≠ η(e₂)`. -/
  edge_injOn : Set.InjOn ηe P.G.edgeSet
  /-- (iv) For each `e ∈ E(G)`, `e ∈ dom(μ)` if and only if `η(e) ∈ dom(μ')`. -/
  mem_dom_iff : ∀ e ∈ P.G.edgeSet, e ∈ P.dom ↔ ηe e ∈ P'.dom
  /-- (v) For each `e ∈ E(G) - dom(μ)`, if `v` is an end of `e` in `G` then `η(v)` contains an end
  of `η(e)` in `G'`. -/
  ends_nonempty : ∀ e ∈ P.G.edgeSet, e ∉ P.dom → ∀ v, P.G.Inc e v →
    ∃ v' ∈ ηv v, P'.G.Inc (ηe e) v'
  /-- (vi) For each `e ∈ dom(μ)`, `μ(e)` and `μ'(η(e))` have the same length. -/
  μ_length : ∀ e ∈ P.dom, (P.μ e).length = (P'.μ (ηe e)).length
  /-- (vi) For each `e ∈ dom(μ)` and `1 ≤ i ≤ k`, `η(v)` contains the `i`th term of `μ'(η(e))`
  where `v` is the `i`th term of `μ(e)`. -/
  μ_mem : ∀ e ∈ P.dom, ∀ (i : ℕ) (hi : i < (P.μ e).length) (hi' : i < (P'.μ (ηe e)).length),
    (P'.μ (ηe e))[i] ∈ ηv (P.μ e)[i]
  /-- (vii) `π(G)` and `π(G')` have the same length. -/
  roots_length : P.G.roots.length = P'.G.roots.length
  /-- (vii) For `1 ≤ i ≤ k`, `η(v)` contains the `i`th term of `π(G')` where `v` is the `i`th term
  of `π(G)`. -/
  roots_mem : ∀ (i : ℕ) (hi : i < P.G.roots.length) (hi' : i < P'.G.roots.length),
    P'.G.roots[i] ∈ ηv P.G.roots[i]
  /-- (viii) For each `e ∈ dom(μ)`, `μ(e) → μ'(η(e))` maps `Δ(e)` to `Δ'(η(e))`: the image of
  every member of `Δ(e)` is a member of `Δ'(η(e))`. The paper uses 'maps ... to' in this sense in
  the proof of (7.1), claim (6): "$\delta_e''$ ... belongs to $\Delta''(e)$ since $\delta_f \in
  \Delta'(f)$ and
  $\mu'(f) \to \mu''(\eta'(f))$ maps $\Delta'(f)$ to $\Delta''(e)$." -/
  maps_Δ : ∀ e ∈ P.dom,
    Set.MapsTo (marchMapSubgraph (P.μ e) (P'.μ (ηe e))) (P.Δ e).groupings (P'.Δ (ηe e)).groupings
  /-- (ix) For each `e ∈ E(G)`, `φ(e) ≤ φ'(η(e))`. -/
  φ_le : ∀ e ∈ P.G.edgeSet, P.φ e ≤ P'.φ (ηe e)

/-- `G \ F` for a rooted hypergraph `G` (Graph Minors IV, Section 7, page 244):
"If $G$ is a rooted hypergraph, $G \setminus F$ denotes $(G^- \setminus F, \pi(G))$." -/
def _root_.GraphMinor.RootedHypergraph.deleteEdges (G : RootedHypergraph α β) (F : Set β) :
    RootedHypergraph α β where
  toHypergraph := G.toHypergraph.deleteEdges F
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset := G.roots_subset

/-- `P \ F` for an `Ω`-patchwork `P` (Graph Minors IV, Section 7, page 244):
"If $P = (G, \mu, \Delta, \phi)$ is an $\Omega$-patchwork and $F \subseteq E(G)$, $P
\setminus F$ denotes the $\Omega$-patchwork $(G \setminus F, \mu', \Delta', \phi')$ where
$\mu', \Delta', \phi'$ are the restrictions of $\mu, \Delta, \phi$ to
$\operatorname{dom}(\mu) \cap E(G \setminus F)$, $E(G \setminus F)$, $E(G \setminus F)$,
respectively." -/
def Patchwork.deleteEdges (P : Patchwork Ω α β) (F : Set β) : Patchwork Ω α β where
  G := P.G.deleteEdges F
  dom := P.dom \ F
  μ := P.μ
  Δ := P.Δ
  φ := P.φ
  dom_subset := Set.sdiff_subset_sdiff P.dom_subset subset_rfl
  μ_nodup e he := P.μ_nodup e he.1
  μ_set e he := by
    rw [P.μ_set e he.1]
    ext v
    exact ⟨fun hv ↦ ⟨hv, he.2⟩, fun hv ↦ hv.1⟩
  Δ_verts e he := by
    rw [P.Δ_verts e he.1]
    ext v
    exact ⟨fun hv ↦ ⟨hv, he.2⟩, fun hv ↦ hv.1⟩
  Δ_free e he hnd := P.Δ_free e he.1 fun hd ↦ hnd ⟨hd, he.2⟩

/-- A realization `H` of `P' \ η(E(G))` realizes `η` (Graph Minors IV, Section 7, page 244):
"A realization $H$ of $P' \setminus \eta(E(G))$ is said to *realize* $\eta$ if for every $v
\in V(G)$, $\eta(v)$ is the vertex set of some component of $H$" -/
def Realizes (P : Patchwork Ω α β) (P' : Patchwork Ω α' β') (ηv : α → Set α') (ηe : β → β')
    (H : (⊤ : SimpleGraph α').Subgraph) : Prop :=
  (P'.deleteEdges (ηe '' P.G.edgeSet)).IsRealization H ∧
    ∀ v ∈ P.G.vertexSet, ∃ D, IsComponent H D ∧ D.verts = ηv v

/-- An expansion `η = (ηv, ηe)` of `P` in `P'` is realizable (Graph Minors IV, Section 7,
page 244): "if there is such a realization, $\eta$ is said to be *realizable*." -/
def IsRealizableExpansion [Preorder Ω] (P : Patchwork Ω α β) (P' : Patchwork Ω α' β')
    (ηv : α → Set α') (ηe : β → β') : Prop :=
  IsExpansion P P' ηv ηe ∧ ∃ H, Realizes P P' ηv ηe H

/-- `P` is simulated in `P'` (Graph Minors IV, Section 7, page 244): "Let us say that $P$ is
*simulated* in $P'$ if there is a realizable expansion of $P$ in
$P'$." -/
def Simulated [Preorder Ω] (P : Patchwork Ω α β) (P' : Patchwork Ω α' β') : Prop :=
  ∃ (ηv : α → Set α') (ηe : β → β'), IsRealizableExpansion P P' ηv ηe

/-! ### Restriction `P | G'` and removable patchworks (Section 8) -/

open Classical in
/-- `P | G'` (Graph Minors IV, Section 8, page 247): "Let $P = (G, \mu, \Delta, \phi)$ be an
$\Omega$-patchwork. If $G'$ is a rooted hypergraph
with $G'^- \subseteq G^-$, and $\mu'$, $\Delta'$, $\phi'$ are the restrictions of $\mu$,
$\Delta$, $\phi$ to $\operatorname{dom}(\mu) \cap E(G')$, $E(G')$, $E(G')$, respectively,
then $(G', \mu', \Delta', \phi')$ is an $\Omega$-patchwork which we denote by $P | G'$." -/
noncomputable def Patchwork.restrict (P : Patchwork Ω α β) (G' : RootedHypergraph α β) :
    Patchwork Ω α β where
  G := G'
  dom := {e ∈ P.dom ∩ G'.edgeSet | G'.ends e = P.G.ends e}
  μ := P.μ
  Δ e := if e ∈ P.G.edgeSet ∧ G'.ends e = P.G.ends e then P.Δ e else freePatch (G'.ends e)
  φ := P.φ
  dom_subset _ he := he.1.2
  μ_nodup e he := P.μ_nodup e he.1.1
  μ_set e he := (P.μ_set e he.1.1).trans he.2.symm
  Δ_verts e he := by
    split_ifs with h
    · exact (P.Δ_verts e h.1).trans h.2.symm
    · rfl
  Δ_free e he hnd := by
    split_ifs with h
    · exact P.Δ_free e h.1 fun hd ↦ hnd ⟨⟨hd, he⟩, h.2⟩
    · exact freePatch_isFree _

@[simp]
theorem Patchwork.restrict_G (P : Patchwork Ω α β) (G' : RootedHypergraph α β) :
    (P.restrict G').G = G' := rfl

@[simp]
theorem Patchwork.restrict_μ (P : Patchwork Ω α β) (G' : RootedHypergraph α β) :
    (P.restrict G').μ = P.μ := rfl

@[simp]
theorem Patchwork.restrict_φ (P : Patchwork Ω α β) (G' : RootedHypergraph α β) :
    (P.restrict G').φ = P.φ := rfl

theorem Patchwork.restrict_dom {P : Patchwork Ω α β} {G' : RootedHypergraph α β}
    (hG' : G'.toHypergraph ≤ P.G.toHypergraph) :
    (P.restrict G').dom = P.dom ∩ G'.edgeSet := by
  ext e
  change (e ∈ P.dom ∧ e ∈ G'.edgeSet) ∧ G'.ends e = P.G.ends e ↔ e ∈ P.dom ∧ e ∈ G'.edgeSet
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (hG'.ends_eq e h.2).symm⟩⟩

theorem Patchwork.restrict_Δ {P : Patchwork Ω α β} {G' : RootedHypergraph α β}
    (hG' : G'.toHypergraph ≤ P.G.toHypergraph) {e : β} (he : e ∈ G'.edgeSet) :
    (P.restrict G').Δ e = P.Δ e := by
  have h : e ∈ P.G.edgeSet ∧ G'.ends e = P.G.ends e :=
    ⟨hG'.edgeSet_subset he, (hG'.ends_eq e he).symm⟩
  simp [Patchwork.restrict, h]

/-- An edge `e ∈ E(G)` of an `Ω`-patchwork `P = (G, μ, Δ, φ)` is removable if `N_{V(e)} ∈ Δ(e)`
(Graph Minors IV, Section 8, page 248). -/
def Patchwork.IsRemovableEdge (P : Patchwork Ω α β) (e : β) : Prop :=
  emptySubgraph (P.G.ends e) ∈ P.Δ e

/-- An `Ω`-patchwork `P = (G, μ, Δ, φ)` is removable if each `e ∈ E(G)` is removable
(Graph Minors IV, Section 8, page 248). -/
def Patchwork.IsRemovable (P : Patchwork Ω α β) : Prop :=
  ∀ e ∈ P.G.edgeSet, P.IsRemovableEdge e

end GraphMinor.GM04
