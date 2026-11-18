/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import LeanPool.FiniteRamsey.ArrowNumber
import LeanPool.FiniteRamsey.RamseyNumber

/-!
# The graph-target Ramsey number `R(G, H)`

The classical two-colour Ramsey arrow `n → (r, s)` asks for a monochromatic clique, `K_r` or
`K_s`, inside every red/blue colouring of `K_n`'s edges. Dropping the restriction to complete
targets gives the graph Ramsey number of Chvátal-Harary-style generalized Ramsey theory: given
finite graphs `G` and `H`, `n` arrows `(G, H)` if every red/blue colouring of `K_n`'s edges
contains a red copy of `G` or a blue copy of `H`. Cliques are graphs too, so `R(K_r, K_s)`
recovers the classical Ramsey number exactly (`graphArrow_completeGraph_iff`).

`R(G, H)` is the arrow number (`arrowNumber`) of the two-colour target family
`pairTargets G H` (colour `true` asks for `G`, colour `false` for `H`), so it is a specialisation
of the single primitive in `ArrowNumber.lean`, and it exists for all finite `G`, `H` by
`exists_arrow` (Ramsey's theorem).

## Main declarations

* `SimpleGraph.GraphArrow n G H`: `n` arrows `(G, H)`, i.e. every red/blue edge-colouring of `K_n`
  contains a red copy of `G` or a blue copy of `H`.
* `SimpleGraph.graphArrow_comm`: `GraphArrow` is symmetric in its two targets.
* `SimpleGraph.GraphArrow.mono_graphs`/`mono_vertices`: monotonicity in the targets and in the
  host size.
* `SimpleGraph.graphArrow_completeGraph_iff`: `GraphArrow` specialised to complete-graph targets
  is definitionally the classical clique arrow relation.
* `SimpleGraph.graphArrow_iff_arrow`: `GraphArrow` is `Arrow` for the family `pairTargets`.
* `SimpleGraph.exists_graphArrow`: unconditional existence for finite targets.
* `SimpleGraph.graphRamseyNumber`: the least `n` such that `n` arrows `(G, H)`, with its
  least-number API (`graphRamseyNumber_spec`, `graphRamseyNumber_le_of_graphArrow`,
  `graphArrow_iff_graphRamseyNumber_le`, `lt_graphRamseyNumber_of_not_graphArrow`).
* `SimpleGraph.isContained_completeGraph_two_of_adj`,
  `SimpleGraph.graphRamseyNumber_completeGraph_two_pathGraph_three`: a worked instance,
  `R(K_2, P_3) = 3`, for a target that is not a clique.

## Implementation notes

`GraphArrow` is kept as a readable two-colour interface (`true` for the first colour, `false` for
the second) and is identified with the generic `Arrow` by `graphArrow_iff_arrow`. The number itself
is defined through `arrowNumber`, so no existence proof appears in its statement. The two vertex
types share a universe because the target family `pairTargets` is indexed by `Bool`.

## References

* V. Chvátal, F. Harary, *Generalized Ramsey theory for graphs*, Bull. Amer. Math. Soc. 78 (1972),
  423-426.

## Tags

ramsey theory, graph theory, combinatorics
-/

@[expose] public section

namespace SimpleGraph

universe u

variable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}

/-- **The graph-target Ramsey arrow relation.** `GraphArrow n G H` means: every red/blue
colouring of the edges of the complete graph on `n` vertices (colour `true` for "red", `false`
for "blue") contains a red copy of `G` or a blue copy of `H`. The natural generalisation of the
classical clique arrow `n → (r, s)` from complete-graph targets to arbitrary finite graph
targets. -/
def GraphArrow (n : Nat) (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∀ C : (⊤ : SimpleGraph (Fin n)).EdgeLabeling Bool,
    G ⊑ C.labelGraph true ∨ H ⊑ C.labelGraph false

/-- Recolouring a labelling by swapping the two colours (`Bool.not`) swaps which colour's
label-graph you get. The key computation behind colour symmetry (`graphArrow_comm`) below. -/
private theorem labelGraph_compRight_not {n : Nat} (C : (⊤ : SimpleGraph (Fin n)).EdgeLabeling Bool)
    (b : Bool) : (C.compRight Bool.not).labelGraph b = C.labelGraph !b := by
  ext; cases b <;> simp

/-- **Colour symmetry.** Swapping which target is asked for in which colour preserves
arrowability, by swapping `true`/`false` throughout the colouring. -/
theorem GraphArrow.symm {n : Nat} (h : GraphArrow n G H) : GraphArrow n H G := fun C => by
  simpa [labelGraph_compRight_not, or_comm] using h (C.compRight Bool.not)

/-- **Colour symmetry.** `GraphArrow` is symmetric in its two graph targets. -/
theorem graphArrow_comm {n : Nat} : GraphArrow n G H ↔ GraphArrow n H G :=
  ⟨.symm, .symm⟩

/-- **Target antitonicity.** `GraphArrow` persists if either target is replaced by a graph it
already contains — an easier target to find. Stated with fully independent vertex types for the
replacement targets, since `⊑` (`IsContained`) already works across different types. -/
theorem GraphArrow.mono_graphs {α' β' : Type*} {G' : SimpleGraph α'} {H' : SimpleGraph β'}
    {n : Nat} (hG : G' ⊑ G) (hH : H' ⊑ H) (h : GraphArrow n G H) :
    GraphArrow n G' H' :=
  fun C => (h C).imp hG.trans hH.trans

/-- **Host monotonicity.** Enlarging the host complete graph can only help find the targets. -/
theorem GraphArrow.mono_vertices {n m : Nat} (hnm : n ≤ m) (h : GraphArrow n G H) :
    GraphArrow m G H := fun C =>
  (h (C.pullback (Embedding.completeGraph (Fin.castLEEmb hnm)).toHom)).imp
    (·.trans (C.labelGraph_pullback_isContained _ true))
    (·.trans (C.labelGraph_pullback_isContained _ false))

/-- **Validation against the classical clique case.** `GraphArrow` specialised to complete-graph
targets on both sides is, definitionally, the classical clique-arrow relation `n → (r, s)`. -/
theorem graphArrow_completeGraph_iff {n r s : Nat} :
    GraphArrow n (completeGraph (Fin r)) (completeGraph (Fin s)) ↔
      ∀ C : (⊤ : SimpleGraph (Fin n)).EdgeLabeling Bool,
        completeGraph (Fin r) ⊑ C.labelGraph true ∨ completeGraph (Fin s) ⊑ C.labelGraph false :=
  Iff.rfl

section GraphRamseyNumber

variable {α β : Type u} {G : SimpleGraph α} {H : SimpleGraph β}

/-- The two-colour target family `(G, H)`: colour `true` asks for a copy of `G`, colour `false`
for a copy of `H`. -/
def pairTargets (G : SimpleGraph α) (H : SimpleGraph β) : (b : Bool) → SimpleGraph (cond b α β)
  | true => G
  | false => H

/-- `GraphArrow` is the generic `Arrow` relation for the target family `pairTargets G H`. -/
theorem graphArrow_iff_arrow {n : ℕ} :
    GraphArrow n G H ↔ (⊤ : SimpleGraph (Fin n)).Arrow (pairTargets G H) :=
  forall_congr' fun _ => ⟨(·.elim (⟨true, ·⟩) (⟨false, ·⟩)), fun ⟨b, hb⟩ => by
    cases b
    exacts [.inr hb, .inl hb]⟩

instance [Finite α] [Finite β] (b : Bool) : Finite (cond b α β) := by
  cases b <;> assumption

/-- **Unconditional existence.** For finite `G` and `H`, some complete graph arrows `(G, H)`. -/
theorem exists_graphArrow [Finite α] [Finite β] : ∃ n, GraphArrow n G H :=
  (exists_arrow _).imp fun _ => graphArrow_iff_arrow.mpr

/-- **The graph Ramsey number `R(G, H)`**: the least `n` such that every red/blue colouring of the
edges of `K_n` contains a red copy of `G` or a blue copy of `H`. -/
noncomputable def graphRamseyNumber (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  arrowNumber (pairTargets G H)

/-- Any arrowing host size bounds `R(G, H)` from above. -/
theorem graphRamseyNumber_le_of_graphArrow {n : ℕ} (h : GraphArrow n G H) :
    graphRamseyNumber G H ≤ n :=
  arrowNumber_le_of_arrow (graphArrow_iff_arrow.mp h)

variable [Finite α] [Finite β]

/-- **The least-number characterisation** of `R(G, H)`. -/
theorem graphArrow_iff_graphRamseyNumber_le {n : ℕ} :
    GraphArrow n G H ↔ graphRamseyNumber G H ≤ n :=
  graphArrow_iff_arrow.trans (arrow_iff_arrowNumber_le (exists_arrow _))

/-- The complete graph on `graphRamseyNumber G H` vertices arrows `(G, H)`. -/
theorem graphRamseyNumber_spec : GraphArrow (graphRamseyNumber G H) G H :=
  graphArrow_iff_graphRamseyNumber_le.mpr le_rfl

/-- Failure of the arrow gives a strict lower bound on `R(G, H)`. -/
theorem lt_graphRamseyNumber_of_not_graphArrow {n : ℕ} (h : ¬ GraphArrow n G H) :
    n < graphRamseyNumber G H :=
  not_le.mp (mt graphArrow_iff_graphRamseyNumber_le.mpr h)

end GraphRamseyNumber

section Example

/-- A graph with at least one edge contains a copy of the two-vertex complete graph `K_2`: send
the edge's endpoints to the two vertices of `K_2`. Used by
`graphRamseyNumber_completeGraph_two_pathGraph_three` below to build a red copy of `K_2` out of
any red edge. -/
theorem isContained_completeGraph_two_of_adj {V : Type*} {B : SimpleGraph V} {x y : V}
    (hxy : B.Adj x y) : completeGraph (Fin 2) ⊑ B :=
  (not_cliqueFree_iff_top_isContained 2).mp (cliqueFree_two.not.mpr
    (ne_bot_iff_exists_adj.mpr ⟨x, y, hxy⟩))

/-- **A worked instance for a non-clique target: `R(K_2, P_3) = 3`.** Every red/blue colouring of
`K_3`'s edges contains a red edge or a blue copy of the 3-vertex path `P_3`: if some edge is red,
`isContained_completeGraph_two_of_adj` gives the red `K_2` directly; otherwise every edge of `K_3`
is blue, so the blue label graph is all of `K_3`, which already contains `P_3`. At `n = 2` this
fails: colouring `K_2`'s single edge blue leaves no red edge and only two vertices, too few for a
blue `P_3`. This shows `graphRamseyNumber` behaves correctly on a target that is not a complete
graph, unlike `graphArrow_completeGraph_iff`'s reduction to the classical clique case. -/
theorem graphRamseyNumber_completeGraph_two_pathGraph_three :
    graphRamseyNumber (completeGraph (Fin 2)) (pathGraph 3) = 3 := by
  have hle : graphRamseyNumber (completeGraph (Fin 2)) (pathGraph 3) ≤ 3 := by
    refine graphRamseyNumber_le_of_graphArrow fun C => ?_
    by_cases hred : ∃ x y : Fin 3, (C.labelGraph true).Adj x y
    · obtain ⟨x, y, hxy⟩ := hred
      exact .inl (isContained_completeGraph_two_of_adj hxy)
    push Not at hred
    refine .inr (.of_le fun x y hxy => ?_)
    have h := hred x y
    rw [EdgeLabeling.labelGraph_adj] at h ⊢
    exact ⟨hxy.ne, by simpa using fun e => h ⟨hxy.ne, e⟩⟩
  have hlt : 2 < graphRamseyNumber (completeGraph (Fin 2)) (pathGraph 3) :=
    lt_graphRamseyNumber_of_not_graphArrow fun h => (h fun _ => false).elim
      (fun ⟨f⟩ => by
        simpa [EdgeLabeling.labelGraph] using
          f.toHom.map_rel (show (completeGraph (Fin 2)).Adj 0 1 by decide))
      (fun ⟨f⟩ => by simpa using Fintype.card_le_of_injective _ f.injective)
  omega

end Example

end SimpleGraph
