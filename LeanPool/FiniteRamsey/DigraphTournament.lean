/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.Digraph.Orientation

/-!
# Tournaments, as a predicate on `Digraph`

A *tournament* is an orientation of the complete graph: every pair of distinct vertices is joined
by exactly one directed edge. This file states that directly as a predicate on `Digraph`,
`Digraph.IsTournament`, rather than as a new bundled structure: a tournament is already exactly
"a `Digraph` whose adjacency relation is asymmetric and total off the diagonal", so it reuses all
of `Digraph`'s existing API (`Adj`, transport along an `Equiv`, decidability,
`toSimpleGraphInclusive`) instead of duplicating it under a `beats` field.

## Main declarations

* `Digraph.IsTournament`: `G.Adj` is asymmetric and total on every pair of distinct vertices.
* `Digraph.isTournament_iff_toSimpleGraphInclusive_eq_top`: a `Digraph` is a tournament iff it is
  asymmetric and its orientation-forgetting `SimpleGraph` is complete, the precise sense in which
  a tournament is "an orientation of `K_V`".
* `Digraph.IsTransitiveOn`: a set on which `Adj` is transitive; combined with `IsTournament` this
  makes the set's `Adj`-restriction a strict total order (`Digraph.isStrictTotalOrder_subtype`).
* `Digraph.outSet`/`Digraph.inSet`: the vertices a vertex beats/is beaten by, partitioning
  every other vertex of a tournament.
* `Digraph.linearOrder`, `Digraph.cycle3`: the transitive and the `3`-cycle example tournaments.
* `Digraph.IsTournament.comap`: `IsTournament` transports along a vertex equivalence.

## Implementation notes

`IsTournament`'s asymmetry conjunct is stated via `Std.Asymm` (`Mathlib.Order.Defs.Unbundled`),
matching `SimpleGraph`'s own use of `Std.Symm`/`Std.Irrefl` as field types rather than the older
`Symmetric`/`Irreflexive`/`IsAsymm`-style predicates. Irreflexivity is not a separate conjunct: it
follows from asymmetry alone (`Digraph.IsTournament.irrefl`).

## References

* J. W. Moon, *Topics on Tournaments*, Holt, Rinehart and Winston, New York, 1968.

## Tags

tournament, digraph, combinatorics
-/

@[expose] public section

namespace Digraph

variable {V W : Type*}

/-- **A tournament**: a `Digraph` whose adjacency is asymmetric and total on every pair of
*distinct* vertices — an orientation of the complete graph. -/
def IsTournament (G : Digraph V) : Prop :=
  Std.Asymm G.Adj ∧ ∀ ⦃u v⦄, u ≠ v → G.Adj u v ∨ G.Adj v u

theorem IsTournament.asymm {G : Digraph V} (hT : G.IsTournament) {u v : V} (h : G.Adj u v) :
    ¬G.Adj v u :=
  hT.1.asymm u v h

theorem IsTournament.total_of_ne {G : Digraph V} (hT : G.IsTournament) {u v : V} (huv : u ≠ v) :
    G.Adj u v ∨ G.Adj v u :=
  hT.2 huv

/-- No vertex beats itself: an immediate consequence of asymmetry. -/
theorem IsTournament.irrefl {G : Digraph V} (hT : G.IsTournament) (v : V) : ¬G.Adj v v :=
  fun h => hT.asymm h h

/-- A pair of distinct vertices is decided by `Adj` in exactly one direction. -/
theorem IsTournament.adj_xor {G : Digraph V} (hT : G.IsTournament) {u v : V} (huv : u ≠ v) :
    Xor (G.Adj u v) (G.Adj v u) :=
  (hT.total_of_ne huv).imp (fun h => ⟨h, hT.asymm h⟩) fun h => ⟨h, hT.asymm h⟩

/-- **A tournament is exactly an asymmetric orientation of the complete graph**: `G` is a
tournament iff `G.Adj` is asymmetric and forgetting orientations gives the complete `SimpleGraph`.
This is the precise sense of "an orientation of `K_V`" that motivates the name. -/
theorem isTournament_iff_toSimpleGraphInclusive_eq_top {G : Digraph V} :
    G.IsTournament ↔ Std.Asymm G.Adj ∧ G.toSimpleGraphInclusive = ⊤ := by
  simp only [IsTournament, toSimpleGraphInclusive, SimpleGraph.ext_iff, funext_iff,
    SimpleGraph.fromRel_adj, SimpleGraph.top_adj, eq_iff_iff, and_iff_left_iff_imp]

/-! ### Transitive subsets -/

/-- A set `S` is a *transitive subtournament* of `G` when `Adj`, restricted to `S`, is transitive.
Combined with `IsTournament` (which restricts to `S` automatically), this makes `Adj` a strict
total order on `S` — i.e. `S` can be linearly ordered so every arrow points the same way. -/
def IsTransitiveOn (G : Digraph V) (S : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ ⦃z⦄, z ∈ S → G.Adj x y → G.Adj y z → G.Adj x z

@[simp]
theorem isTransitiveOn_empty (G : Digraph V) : G.IsTransitiveOn (∅ : Set V) :=
  fun x hx => absurd hx (Set.notMem_empty x)

theorem isTransitiveOn_singleton {G : Digraph V} (hT : G.IsTournament) (v : V) :
    G.IsTransitiveOn ({v} : Set V) := fun _ hx _ hy _ _ hxy _ => by
  rw [Set.mem_singleton_iff] at hx hy
  subst hx hy
  exact absurd hxy (hT.irrefl _)

theorem IsTransitiveOn.mono {G : Digraph V} {S S' : Set V} (hS' : S' ⊆ S)
    (h : G.IsTransitiveOn S) : G.IsTransitiveOn S' :=
  fun _x hx _y hy _z hz => h (hS' hx) (hS' hy) (hS' hz)

/-- **Adding a vertex on one side.** A transitive set stays transitive after adding a vertex that
is beaten by all of its members, or that beats all of them. -/
theorem IsTransitiveOn.insert_of_forall_adj {G : Digraph V} (hT : G.IsTournament) {S : Set V}
    {v : V} (h : G.IsTransitiveOn S) (hv : (∀ u ∈ S, G.Adj u v) ∨ ∀ u ∈ S, G.Adj v u) :
    G.IsTransitiveOn (insert v S) := by
  rcases hv with hv | hv <;>
  rintro x (rfl | hx) y (rfl | hy) z (rfl | hz) hxy hyz <;>
  first
    | exact h hx hy hz hxy hyz
    | exact absurd hxy (hT.irrefl _)
    | exact absurd hyz (hT.irrefl _)
    | exact hv _ hx
    | exact hv _ hz
    | exact absurd hxy (hT.asymm (hv _ hy))
    | exact absurd hyz (hT.asymm (hv _ hz))
    | exact absurd hxy (hT.asymm (hv _ hx))
    | exact absurd hyz (hT.asymm (hv _ hy))

/-- The strict total order witnessed by a transitive subtournament: on a transitive-subtournament
subtype of a tournament, `Adj` is trichotomous, transitive and irreflexive, i.e. a genuine
`IsStrictTotalOrder`. This makes precise the "`S` can be linearly ordered so all arrows point the
same way" reading of `IsTransitiveOn`. -/
theorem isStrictTotalOrder_subtype {G : Digraph V} {S : Set V} (hT : G.IsTournament)
    (h : G.IsTransitiveOn S) : IsStrictTotalOrder S (fun a b : S => G.Adj a.1 b.1) where
  trichotomous _ _ hab hba := Subtype.ext (by_contra fun hne => (hT.total_of_ne hne).elim hab hba)
  trans a b c hab hbc := h a.2 b.2 c.2 hab hbc
  irrefl a := hT.irrefl a.1

/-! ### Out-set and in-set -/

/-- The vertices `v` beats. -/
def outSet (G : Digraph V) (v : V) : Set V :=
  {w | G.Adj v w}

/-- The vertices that beat `v`. -/
def inSet (G : Digraph V) (v : V) : Set V :=
  {w | G.Adj w v}

@[simp] theorem mem_outSet {G : Digraph V} {v w : V} : w ∈ G.outSet v ↔ G.Adj v w := Iff.rfl
@[simp] theorem mem_inSet {G : Digraph V} {v w : V} : w ∈ G.inSet v ↔ G.Adj w v := Iff.rfl

/-- **Every other vertex of a tournament is on exactly one side of `v`**: it either beats `v` or
is beaten by `v`, never both. -/
theorem outSet_disjoint_inSet {G : Digraph V} (hT : G.IsTournament) (v : V) :
    Disjoint (G.outSet v) (G.inSet v) :=
  Set.disjoint_left.mpr fun _ hout hin => hT.asymm hout hin

theorem outSet_union_inSet_eq {G : Digraph V} (hT : G.IsTournament) (v : V) :
    G.outSet v ∪ G.inSet v = {v}ᶜ := by
  ext w
  simp only [Set.mem_union, mem_outSet, mem_inSet, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨by rintro (h | h) rfl <;> exact hT.irrefl _ h, fun hne => hT.total_of_ne (Ne.symm hne)⟩

/-! ### Example tournaments -/

/-- The transitive "linear order" tournament on `Fin n`: `i` beats `j` iff `i < j`. -/
def linearOrder (n : Nat) : Digraph (Fin n) where
  Adj i j := i < j

theorem isTournament_linearOrder (n : Nat) : (linearOrder n).IsTournament :=
  ⟨⟨fun _ _ h => not_lt.mpr h.le⟩, fun _ _ h => lt_or_gt_of_ne h⟩

theorem isTransitiveOn_linearOrder_univ (n : Nat) :
    (linearOrder n).IsTransitiveOn (Set.univ : Set (Fin n)) :=
  fun _ _ _ _ _ _ hxy hyz => hxy.trans hyz

/-- The `3`-cycle tournament on `Fin 3`: `i` beats `i + 1 (mod 3)`. -/
def cycle3 : Digraph (Fin 3) where
  Adj i j := j = i + 1

instance : DecidableRel cycle3.Adj := fun _ _ => inferInstanceAs (Decidable (_ = _))

theorem isTournament_cycle3 : cycle3.IsTournament :=
  ⟨⟨by decide⟩, by decide⟩

/-! ### Transport along an equivalence -/

/-- Transport a `Digraph` along a bijection: `G.comap e` is the digraph on `W` obtained by
relabelling `G`'s vertices via `e : V ≃ W`. -/
def comap (G : Digraph V) (e : V ≃ W) : Digraph W where
  Adj w₁ w₂ := G.Adj (e.symm w₁) (e.symm w₂)

@[simp]
theorem comap_adj (G : Digraph V) (e : V ≃ W) (w₁ w₂ : W) :
    (G.comap e).Adj w₁ w₂ ↔ G.Adj (e.symm w₁) (e.symm w₂) := Iff.rfl

@[simp]
theorem comap_refl (G : Digraph V) : G.comap (Equiv.refl V) = G := rfl

@[simp]
theorem comap_comap (G : Digraph V) (e : V ≃ W) {X : Type*} (f : W ≃ X) :
    (G.comap e).comap f = G.comap (e.trans f) := rfl

/-- `IsTournament` transports along a graph vertex equivalence. -/
theorem IsTournament.comap {G : Digraph V} (hT : G.IsTournament) (e : V ≃ W) :
    (G.comap e).IsTournament :=
  ⟨⟨fun _ _ h => hT.asymm h⟩, fun _ _ huv => hT.total_of_ne (e.symm.injective.ne huv)⟩

/-- Transport of `IsTransitiveOn` along an equivalence: a transitive subtournament of `G` maps to
a transitive subtournament, of the corresponding image set, of the transported digraph. -/
theorem IsTransitiveOn.comap {G : Digraph V} {S : Set V} (h : G.IsTransitiveOn S) (e : V ≃ W) :
    (G.comap e).IsTransitiveOn (e '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz
  simp only [comap_adj, Equiv.symm_apply_apply] at hxy hyz ⊢
  exact h hx hy hz hxy hyz

/-! ### Worked example -/

/-- Forgetting the orientation of the `3`-cycle tournament gives the complete graph on `Fin 3`:
the concrete instance, on the smallest genuinely non-transitive tournament, of
`isTournament_iff_toSimpleGraphInclusive_eq_top`. -/
theorem cycle3_toSimpleGraphInclusive_eq_top :
    cycle3.toSimpleGraphInclusive = (⊤ : SimpleGraph (Fin 3)) :=
  (isTournament_iff_toSimpleGraphInclusive_eq_top.mp isTournament_cycle3).2

end Digraph
