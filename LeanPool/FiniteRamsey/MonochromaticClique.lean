/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Monochromatic cliques under an `EdgeLabeling`

Every declaration is stated for an arbitrary edge-labelling `C : G.EdgeLabeling K` of an arbitrary
host graph `G` by an arbitrary (not just two-element) colour type `K`; it does not mention `Bool`
or any complete-graph host. Depends only on mathlib's `SimpleGraph.EdgeLabeling` and
`SimpleGraph.IsNClique`/`CliqueFree`.

## Main declarations

* `SimpleGraph.EdgeLabeling.colorNeighborSet C k v`: the set of `v`'s neighbours reached by a
  colour-`k` edge.
* `SimpleGraph.EdgeLabeling.MonochromaticClique C k n s`: `s` is an `n`-element clique all of
  whose edges have colour `k`.
* `SimpleGraph.EdgeLabeling.HasMonochromaticClique C k n`: some such clique exists.
* `SimpleGraph.hasNClique_mono_size`/`SimpleGraph.EdgeLabeling.hasMonochromaticClique_mono_size`:
  a clique of size `n` gives one of every smaller size, plainly and under a colour.
* `SimpleGraph.EdgeLabeling.monochromaticClique_insert_of_subset_colorNeighbor`: extending a
  monochromatic clique by one vertex adjacent, in the same colour, to every existing member.
* Transport along a vertex embedding into a `TopEdgeLabeling`'s host (`colorGraph_pullback_map_le`,
  `monochromaticClique_map_pullback`, `hasMonochromaticClique_map_pullback`, and their
  contrapositive
  "not" forms): a monochromatic clique of a pulled-back colouring pushes forward to one of the
  original colouring, of the same size — the key one-vertex-extension step a recursive Ramsey
  bound is built from.

## Design notes

`SimpleGraph.EdgeLabeling.labelGraph` (mathlib) is already "the graph of colour-`k` edges";
`MonochromaticClique C k n s` below is nothing more than `(C.labelGraph k).IsNClique n s` under a
more Ramsey-flavoured name, kept as a named abbreviation rather than inlined everywhere because it
reads better in downstream Ramsey statements. All content in this file specialises, without
change, to the two-colour case: a classical red/blue Ramsey clique predicate's `RedClique`/
`BlueClique` are exactly `MonochromaticClique` at colours `true`/`false`.

## Tags

ramsey theory, clique, graph coloring
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A clique of size `n` gives one of every smaller size. Pure `IsNClique`/`CliqueFree`
content, with no dependency on `EdgeLabeling`; the fact
`EdgeLabeling.hasMonochromaticClique_mono_size`
below specialises to a single colour's label graph. -/
theorem hasNClique_mono_size {G : SimpleGraph V} {m n : ℕ} (hmn : m ≤ n)
    (h : ∃ s : Finset V, G.IsNClique n s) : ∃ s : Finset V, G.IsNClique m s :=
  let ⟨t, ht⟩ := h; not_forall_not.mp fun hm => CliqueFree.mono hmn hm t ht

namespace EdgeLabeling

variable {G : SimpleGraph V} {K : Type*}

/-- The set of `v`'s neighbours reached by a colour-`k` edge. -/
def colorNeighborSet (C : G.EdgeLabeling K) (k : K) (v : V) : Set V :=
  (C.labelGraph k).neighborSet v

@[simp]
theorem mem_colorNeighborSet_iff {C : G.EdgeLabeling K} {k : K} {v w : V} :
    w ∈ colorNeighborSet C k v ↔ (C.labelGraph k).Adj v w :=
  Iff.rfl

/-- `s` is an `n`-element clique all of whose edges have colour `k`. -/
def MonochromaticClique (C : G.EdgeLabeling K) (k : K) (n : ℕ) (s : Finset V) : Prop :=
  (C.labelGraph k).IsNClique n s

/-- Some colour-`k` monochromatic `n`-clique exists somewhere in `C`. -/
def HasMonochromaticClique (C : G.EdgeLabeling K) (k : K) (n : ℕ) : Prop :=
  ∃ s : Finset V, MonochromaticClique C k n s

theorem monochromaticClique_isClique {C : G.EdgeLabeling K} {k : K} {n : ℕ} {s : Finset V}
    (h : MonochromaticClique C k n s) : (C.labelGraph k).IsClique s :=
  SimpleGraph.IsNClique.isClique h

theorem monochromaticClique_card_eq {C : G.EdgeLabeling K} {k : K} {n : ℕ} {s : Finset V}
    (h : MonochromaticClique C k n s) : s.card = n :=
  SimpleGraph.IsNClique.card_eq h

/-- A monochromatic `n`-clique gives one of every smaller size. -/
theorem hasMonochromaticClique_mono_size {C : G.EdgeLabeling K} {k : K} {m n : ℕ} (hmn : m ≤ n) :
    HasMonochromaticClique C k n → HasMonochromaticClique C k m :=
  hasNClique_mono_size hmn

/-- Extending a monochromatic clique by one vertex. If a new vertex `v` is, in colour `k`,
adjacent to every member of an existing monochromatic clique, adjoining it gives a monochromatic
clique one larger. -/
theorem monochromaticClique_insert_of_subset_colorNeighbor [DecidableEq V]
    {C : G.EdgeLabeling K} {k : K} {n : ℕ} {s : Finset V} {v : V}
    (hclique : MonochromaticClique C k n s)
    (hneighbor : (s : Set V) ⊆ colorNeighborSet C k v) :
    MonochromaticClique C k (n + 1) (insert v s) :=
  hclique.insert fun _ hw => hneighbor hw

section Pullback

variable {W : Type*}

/-- Pulling back a `TopEdgeLabeling` along an embedding never creates new edges outside the
original label graph's image: the pulled-back colour-`k` label graph, pushed forward along the
same embedding, sits inside the original colour-`k` label graph. -/
theorem colorGraph_pullback_map_le (C : SimpleGraph.TopEdgeLabeling W K) (f : V ↪ W) (k : K) :
    ((C.pullback f).labelGraph k).map f ≤ C.labelGraph k := by
  rintro _ _ ⟨-, u, w, huw, rfl, rfl⟩
  rw [TopEdgeLabeling.labelGraph_adj] at huw ⊢
  exact ⟨f.injective.ne huw.1, huw.2⟩

/-- A monochromatic clique of a pulled-back `TopEdgeLabeling` pushes forward, along the same
embedding, to a monochromatic clique of the original labelling of the same size. -/
theorem monochromaticClique_map_pullback (C : SimpleGraph.TopEdgeLabeling W K) (f : V ↪ W)
    (k : K) {n : ℕ} {s : Finset V}
    (h : MonochromaticClique (C.pullback f) k n s) :
    MonochromaticClique C k n (s.map f) :=
  (SimpleGraph.IsNClique.map h (f := f)).mono (colorGraph_pullback_map_le C f k)

/-- The pushed-forward existence form of `monochromaticClique_map_pullback`. -/
theorem hasMonochromaticClique_map_pullback (C : SimpleGraph.TopEdgeLabeling W K) (f : V ↪ W)
    (k : K) {n : ℕ} (h : HasMonochromaticClique (C.pullback f) k n) :
    HasMonochromaticClique C k n :=
  let ⟨_, hs⟩ := h; ⟨_, monochromaticClique_map_pullback C f k hs⟩

/-- Contrapositive form. If the original labelling has no colour-`k` `n`-clique, neither does any
pullback of it: pulling back along an embedding can only lose structure, never create it. -/
theorem not_hasMonochromaticClique_pullback_of_not_hasMonochromaticClique
    (C : SimpleGraph.TopEdgeLabeling W K) (f : V ↪ W) (k : K) {n : ℕ}
    (hno : ¬ HasMonochromaticClique C k n) :
    ¬ HasMonochromaticClique (C.pullback f) k n :=
  mt (hasMonochromaticClique_map_pullback C f k) hno

end Pullback

end EdgeLabeling

/-- The single-colour edge-labelling of the complete graph on `Fin 3`, used only by the worked
instance below: every edge gets the unique colour `0 : Fin 1`. -/
def oneColorLabeling : (⊤ : SimpleGraph (Fin 3)).EdgeLabeling (Fin 1) :=
  EdgeLabeling.mk (fun _ _ _ => 0) (fun _ _ _ => rfl)

/-- A worked instance: with a single colour, every vertex set of the complete graph on `Fin 3` is
a monochromatic clique of that colour, since the unique colour's label graph is the whole host. -/
example : EdgeLabeling.MonochromaticClique oneColorLabeling 0 3 Finset.univ := by
  have heq : oneColorLabeling.labelGraph 0 = ⊤ := by
    ext; simp [Subsingleton.elim _ (0 : Fin 1)]
  change (oneColorLabeling.labelGraph 0).IsNClique 3 _
  simp [heq, isNClique_iff]

end SimpleGraph
