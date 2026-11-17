/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.SimpleGraphAddVertex

/-!
# Twin vertices

Two vertices of a graph are *twins* if their neighbourhoods agree once each is allowed to ignore
the other. This file defines the general `SimpleGraph.TwinVertices` relation together with its
two standard special cases, *false twins* (non-adjacent twins, `SimpleGraph.FalseTwins`) and
*true twins* (adjacent twins, `SimpleGraph.TrueTwins`), and shows that duplicating a vertex as a
fresh false twin (`SimpleGraph.addFalseTwin`) preserves `n`-clique-freeness exactly, the standard
"independent blow-up vertex" argument in extremal graph theory.

This file imports `LeanPool.FiniteRamsey.SimpleGraphAddVertex` for
`SimpleGraph.addVertex`, on top of which `SimpleGraph.addFalseTwin` is built; in a real PR series
this would instead be an ordinary `Mathlib.Combinatorics.SimpleGraph.AddVertex` import once that
file has landed upstream.

## Main declarations

* `SimpleGraph.TwinVertices`: `v` and `w` are twins.
* `SimpleGraph.FalseTwins`, `SimpleGraph.TrueTwins`: the non-adjacent and adjacent special cases,
  each characterized as `SimpleGraph.TwinVertices` together with the relevant adjacency fact
  (`SimpleGraph.falseTwins_iff`, `SimpleGraph.trueTwins_iff`), each symmetric
  (`SimpleGraph.FalseTwins.symm`, `SimpleGraph.TrueTwins.symm`) and each transporting along a
  graph isomorphism (`SimpleGraph.FalseTwins.map`, `SimpleGraph.TrueTwins.map`).
* `SimpleGraph.addFalseTwin`: duplicate a vertex as a fresh non-adjacent twin.
* `SimpleGraph.cliqueFree_addFalseTwin_iff`: false-twin duplication preserves `n`-clique-freeness
  exactly.
* `SimpleGraph.addTrueTwin`: duplicate a vertex as a fresh adjacent twin, a clique blow-up, the
  opposite extremal move from `addFalseTwin`'s independent-set blow-up, so it does *not* preserve
  clique-freeness.

## Tags

graph theory, combinatorics
-/

@[expose] public section

namespace SimpleGraph

section TwinVertices

variable {V : Type*} (G : SimpleGraph V)

/-- `v` and `w` are twin vertices in `G`: distinct vertices whose neighbourhoods agree once each
is allowed to ignore the other. Covers both the true-twin case (`v ~ w`) and the false-twin case
(`v ≁ w`) below. -/
def TwinVertices (v w : V) : Prop :=
  v ≠ w ∧ G.neighborSet v \ {w} = G.neighborSet w \ {v}

/-- False twins: distinct, non-adjacent vertices with identical open neighbourhoods. The
standard "duplicable independent vertex" relation, witnessed constructively by
`SimpleGraph.addFalseTwin` below. -/
def FalseTwins (v w : V) : Prop :=
  v ≠ w ∧ ¬G.Adj v w ∧ G.neighborSet v = G.neighborSet w

/-- True twins: distinct, adjacent vertices with identical closed neighbourhoods. -/
def TrueTwins (v w : V) : Prop :=
  v ≠ w ∧ G.Adj v w ∧ insert v (G.neighborSet v) = insert w (G.neighborSet w)

/-- Twin-vertex-ness is symmetric. -/
theorem TwinVertices.symm {v w : V} (h : G.TwinVertices v w) : G.TwinVertices w v :=
  ⟨h.1.symm, h.2.symm⟩

theorem twinVertices_comm {v w : V} : G.TwinVertices v w ↔ G.TwinVertices w v :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

/-- False-twin-ness is symmetric. -/
theorem FalseTwins.symm {v w : V} (h : G.FalseTwins v w) : G.FalseTwins w v :=
  ⟨h.1.symm, fun hc ↦ h.2.1 (G.adj_symm hc), h.2.2.symm⟩

/-- True-twin-ness is symmetric. -/
theorem TrueTwins.symm {v w : V} (h : G.TrueTwins v w) : G.TrueTwins w v :=
  ⟨h.1.symm, G.adj_symm h.2.1, h.2.2.symm⟩

theorem FalseTwins.twinVertices {v w : V} (h : G.FalseTwins v w) : G.TwinVertices v w :=
  ⟨h.1, by rw [Set.sdiff_singleton_eq_self (show w ∉ G.neighborSet v from h.2.1),
    Set.sdiff_singleton_eq_self (show v ∉ G.neighborSet w from mt G.adj_symm h.2.1), h.2.2]⟩

theorem TrueTwins.twinVertices {v w : V} (h : G.TrueTwins v w) : G.TwinVertices v w := by
  obtain ⟨hne, hadj, heq⟩ := h
  refine ⟨hne, Set.ext fun x => ?_⟩
  have := Set.ext_iff.mp heq x
  clear heq
  by_cases hxv : x = v <;> by_cases hxw : x = w <;> subst_vars <;> simp_all



/-- **False twins are exactly the non-adjacent twins.** -/
theorem falseTwins_iff {v w : V} : G.FalseTwins v w ↔ G.TwinVertices v w ∧ ¬G.Adj v w :=
  ⟨fun h => ⟨h.twinVertices, h.2.1⟩, fun ⟨⟨hne, heq⟩, hnadj⟩ => ⟨hne, hnadj, by
    rwa [Set.sdiff_singleton_eq_self (show w ∉ G.neighborSet v from hnadj),
      Set.sdiff_singleton_eq_self (show v ∉ G.neighborSet w from mt G.adj_symm hnadj)] at heq⟩⟩



/-- **True twins are exactly the adjacent twins.** -/
theorem trueTwins_iff {v w : V} : G.TrueTwins v w ↔ G.TwinVertices v w ∧ G.Adj v w := by
  refine ⟨fun h => ⟨h.twinVertices, h.2.1⟩, fun ⟨⟨hne, heq⟩, hadj⟩ =>
    ⟨hne, hadj, Set.ext fun x => ?_⟩⟩
  have := Set.ext_iff.mp heq x
  clear heq
  by_cases hxv : x = v <;> by_cases hxw : x = w <;> subst_vars <;> simp_all [G.adj_comm]



/-- Twin-vertex-ness transports along a graph isomorphism. -/
theorem TwinVertices.map {W : Type*} {H : SimpleGraph W} (e : G ≃g H) {v w : V}
    (h : G.TwinVertices v w) : H.TwinVertices (e v) (e w) := by
  obtain ⟨hne, heq⟩ := h
  refine ⟨fun heq' ↦ hne (e.injective heq'), ?_⟩
  rw [← e.image_neighborSet, ← e.image_neighborSet,
    ← Set.image_singleton (f := e) (a := w), ← Set.image_singleton (f := e) (a := v),
    ← Set.image_sdiff e.injective, ← Set.image_sdiff e.injective, heq]

/-- False-twin-ness transports along a graph isomorphism. -/
theorem FalseTwins.map {W : Type*} {H : SimpleGraph W} (e : G ≃g H) {v w : V}
    (h : G.FalseTwins v w) : H.FalseTwins (e v) (e w) := by
  rw [falseTwins_iff] at h ⊢
  exact ⟨h.1.map (e := e), fun hc ↦ h.2 (e.map_adj_iff.mp hc)⟩

/-- True-twin-ness transports along a graph isomorphism. -/
theorem TrueTwins.map {W : Type*} {H : SimpleGraph W} (e : G ≃g H) {v w : V}
    (h : G.TrueTwins v w) : H.TrueTwins (e v) (e w) := by
  rw [trueTwins_iff] at h ⊢
  exact ⟨h.1.map (e := e), e.map_adj_iff.mpr h.2⟩

end TwinVertices

/-! ### False-twin duplication -/

section FalseTwinDuplication

variable {V : Type*} {G : SimpleGraph V}

/-- Duplicate the vertex `u` of `G` as a brand-new non-adjacent twin: extend `G` by one vertex
whose neighbourhood among the old vertices is exactly `u`'s own neighbourhood. The new vertex
`none` and `some u` are, by construction, false twins of the result. -/
def addFalseTwin (G : SimpleGraph V) (u : V) : SimpleGraph (Option V) :=
  G.addVertex (G.neighborSet u)

@[simp]
theorem addFalseTwin_adj_some_some {u a b : V} :
    (G.addFalseTwin u).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem addFalseTwin_adj_some_none {u a : V} :
    (G.addFalseTwin u).Adj (some a) none ↔ G.Adj u a :=
  Iff.rfl

@[simp]
theorem addFalseTwin_adj_none_some {u b : V} :
    (G.addFalseTwin u).Adj none (some b) ↔ G.Adj u b :=
  Iff.rfl

theorem addFalseTwin_not_adj_some_u_none (u : V) : ¬(G.addFalseTwin u).Adj (some u) none := by
  simp [addFalseTwin_adj_some_none]

/-- `some u` and `none` are honest false twins of `G.addFalseTwin u`. -/
theorem falseTwins_addFalseTwin_some_none (u : V) :
    (G.addFalseTwin u).FalseTwins (some u) none := by
  refine ⟨by simp, addFalseTwin_not_adj_some_u_none u, ?_⟩
  ext (_ | a) <;> simp



/-- The retraction collapsing the duplicate vertex `none` back onto `u`, and every other vertex
to itself. -/
private def falseTwinRetract (u : V) : Option V → V
  | none => u
  | some a => a

private theorem falseTwinRetract_not_mem_both {u : V} {K : Finset (Option V)}
    (hK : (G.addFalseTwin u).IsClique (K : Set (Option V))) :
    ¬(none ∈ K ∧ some u ∈ K) := by
  rintro ⟨hnone, hsome⟩
  exact addFalseTwin_not_adj_some_u_none u
    ((G.addFalseTwin u).adj_symm (hK hnone hsome (by simp)))

private theorem falseTwinRetract_injOn {u : V} {K : Finset (Option V)}
    (hK : (G.addFalseTwin u).IsClique (K : Set (Option V))) :
    Set.InjOn (falseTwinRetract u) (K : Set (Option V)) := by
  intro x hx y hy hxy
  match x, y with
  | none, none => rfl
  | none, some b =>
    exact absurd ⟨hx, (show u = b by simpa [falseTwinRetract] using hxy) ▸ hy⟩
      (falseTwinRetract_not_mem_both hK)
  | some a, none =>
    exact absurd ⟨hy, (show a = u by simpa [falseTwinRetract] using hxy) ▸ hx⟩
      (falseTwinRetract_not_mem_both hK)
  | some a, some b => rw [show a = b by simpa [falseTwinRetract] using hxy]

/-- **False-twin duplication never creates a new clique.** Any `n`-clique in `G.addFalseTwin u`
retracts, injectively (the duplicate pair can never both appear in a clique, since they are
non-adjacent), to an `n`-clique in `G`. The standard "independent blow-up vertex" argument. -/
theorem CliqueFree.addFalseTwin {u : V} {n : ℕ} (hG : G.CliqueFree n) :
    (G.addFalseTwin u).CliqueFree n := by
  classical
  intro K hK
  apply hG (K.image (falseTwinRetract u))
  have hinj := falseTwinRetract_injOn (G := G) (u := u) hK.isClique
  refine ⟨fun a ha b hb hab ↦ ?_, by rw [Finset.card_image_of_injOn hinj, hK.card_eq]⟩
  rw [Finset.mem_coe, Finset.mem_image] at ha hb
  obtain ⟨x, hxK, rfl⟩ := ha
  obtain ⟨y, hyK, rfl⟩ := hb
  have hxy : x ≠ y := fun hc ↦ hab (by rw [hc])
  have hadj := hK.isClique hxK hyK hxy
  match x, y with
  | none, none => exact absurd rfl hxy
  | none, some b => simpa [falseTwinRetract] using hadj
  | some a, none => simpa [falseTwinRetract, G.adj_comm] using hadj
  | some a, some b => simpa [falseTwinRetract] using hadj

/-- **False-twin duplication preserves `n`-clique-freeness exactly**: `G` is `n`-clique-free iff
its false-twin duplicate at `u` is. Combines `SimpleGraph.CliqueFree.addFalseTwin` with the
generic deletion direction `SimpleGraph.CliqueFree.of_addVertex`. -/
theorem cliqueFree_addFalseTwin_iff {u : V} {n : ℕ} :
    (G.addFalseTwin u).CliqueFree n ↔ G.CliqueFree n :=
  ⟨CliqueFree.of_addVertex, CliqueFree.addFalseTwin⟩

end FalseTwinDuplication

/-! ### True-twin duplication -/

section TrueTwinDuplication

variable {V : Type*} {G : SimpleGraph V}

/-- Duplicate the vertex `u` of `G` as a brand-new *adjacent* twin: extend `G` by one vertex whose
neighbourhood among the old vertices is `u`'s own neighbourhood together with `u` itself. The new
vertex `none` and `some u` are, by construction, true twins of the result.

Unlike `SimpleGraph.addFalseTwin`, this does **not** preserve `n`-clique-freeness: if `u` belongs
to an `n`-clique of `G`, `some u` and `none` are both adjacent to every other member of its image
and to each other, giving an `(n + 1)`-clique of `G.addTrueTwin u`. True-twin duplication is a
clique-blow-up, the opposite extremal move from the independent-set blow-up `addFalseTwin`. -/
def addTrueTwin (G : SimpleGraph V) (u : V) : SimpleGraph (Option V) :=
  G.addVertex (insert u (G.neighborSet u))

@[simp]
theorem addTrueTwin_adj_some_some {u a b : V} :
    (G.addTrueTwin u).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem addTrueTwin_adj_some_none {u a : V} :
    (G.addTrueTwin u).Adj (some a) none ↔ a = u ∨ G.Adj u a := by
  simp [addTrueTwin, addVertex_adj_some_none]

@[simp]
theorem addTrueTwin_adj_none_some {u b : V} :
    (G.addTrueTwin u).Adj none (some b) ↔ b = u ∨ G.Adj u b := by
  simp [addTrueTwin, addVertex_adj_none_some]

theorem addTrueTwin_adj_some_u_none (u : V) : (G.addTrueTwin u).Adj (some u) none := by
  simp

/-- `some u` and `none` are honest true twins of `G.addTrueTwin u`. -/
theorem trueTwins_addTrueTwin_some_none (u : V) :
    (G.addTrueTwin u).TrueTwins (some u) none := by
  refine ⟨by simp, addTrueTwin_adj_some_u_none u, ?_⟩
  ext x
  cases x with
  | none => simp [or_comm]
  | some a => simp [eq_comm (a := a)]

/-! ### Worked example -/

/-- Concrete instance combining `falseTwins_addFalseTwin_some_none` and
`cliqueFree_addFalseTwin_iff`: duplicating vertex `0` of the two-vertex complete graph as a false
twin gives a graph that is still `3`-clique-free (the original already is, having only two
vertices), in which the new vertex and `0` are honest false twins. -/
theorem addFalseTwin_top_example :
    ((⊤ : SimpleGraph (Fin 2)).addFalseTwin 0).FalseTwins (some 0) none ∧
      ((⊤ : SimpleGraph (Fin 2)).addFalseTwin 0).CliqueFree 3 :=
  ⟨falseTwins_addFalseTwin_some_none 0,
    cliqueFree_addFalseTwin_iff.mpr (cliqueFree_of_card_lt (by simp))⟩

end TrueTwinDuplication

end SimpleGraph
