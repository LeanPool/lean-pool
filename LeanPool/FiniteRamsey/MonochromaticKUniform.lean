/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.MonochromaticClique
public import LeanPool.FiniteRamsey.HypergraphRamsey

/-!
# Monochromatic `u`-uniform cliques, directly on `Finset V → K`

`InfiniteRamseyKUniform.lean` proves the infinite pigeonhole theorem for a colouring of arbitrary
`k`-element `Finset`s, stated with no `SimpleGraph`/`Hypergraph` vocabulary at all — just
`Finset V → K`. This file gives that same bare vocabulary a *finite* home:
`MonochromaticKUniformClique`
is the natural finite analogue (a `Finset` all of whose `u`-element subsets share a colour), and it
turns out to be the common generalisation this series' two existing finite "monochromatic clique"
notions were independently reinventing:

* At `u = 2`, it is `EdgeLabeling.MonochromaticClique` (`MonochromaticClique.lean`) — an ordinary
  graph clique, monochromatic under a `TopEdgeLabeling` — via the pair-colouring bridge
  `pairColouring`/`pairColouring_eq` (`hasMonochromaticKUniformClique_two_iff`).
* At `u = k` and a complete `k`-uniform host, it is `Hypergraph.EdgeColoring.MonochromaticClique`
  (`HypergraphRamsey.lean`) via the analogous bridge `Hypergraph.toFinsetColouring`
  (`Hypergraph.hasMonochromaticKUniformClique_toFinsetColouring_iff`).

Neither existing file's own definition is touched — both stay exactly as they were, and gain a
proven connection to this shared foundation rather than being rewritten to use it directly, the
same "additive, not a rewrite" choice made for `RamseyProperty`'s connection to `Arrow`
(`MulticolorRamseyUnconditional.lean`). `pairColouring`/`get_eq_get_of_pair_eq`/`pairColouring_eq`
live here, rather than in `InfiniteRamsey.lean`, because the bridge is independent of whether the
vertex set is finite.

## Main declarations

* `SimpleGraph.MonochromaticKUniformClique C col u s`: every `u`-element subset of `s` is coloured
  `col` under `C : Finset V → K`.
* `SimpleGraph.HasMonochromaticKUniformClique C col u n`: some size-`n` such clique exists.
* `SimpleGraph.hasMonochromaticKUniformClique_mono_size`: antitonicity in the requested size.
* `SimpleGraph.pairColouring`, `SimpleGraph.pairColouring_eq`: a `TopEdgeLabeling` as a colouring
  of pairs, agreeing with `EdgeLabeling.get` on every genuine pair.
* `SimpleGraph.hasMonochromaticKUniformClique_two_iff`: the `u = 2` case coincides with
  `EdgeLabeling.HasMonochromaticClique`.
* `Hypergraph.toFinsetColouring`, `Hypergraph.hasMonochromaticKUniformClique_toFinsetColouring_iff`:
  the `u = k`, complete-host case coincides with `Hypergraph.EdgeColoring.HasMonochromaticClique`.
-/

@[expose] public section

namespace SimpleGraph

variable {V K : Type*}

/-! ### Bridge: `TopEdgeLabeling` as a colouring of pairs -/

/-- **A `TopEdgeLabeling` repackaged as a colouring of pairs.** Agrees with `C.get` on every
genuine pair (`pairColouring_eq`); takes the arbitrary placeholder value `col0` on every `Finset`
that is not a pair, where it is never consulted by the theorems below. -/
noncomputable def pairColouring [DecidableEq V] (C : TopEdgeLabeling V K) (col0 : K) :
    Finset V → K :=
  fun s => if h : s.card = 2 then
      C.get (Finset.card_eq_two.mp h).choose (Finset.card_eq_two.mp h).choose_spec.choose
        (Finset.card_eq_two.mp h).choose_spec.choose_spec.1
    else col0

/-- **A `TopEdgeLabeling`'s colour of a pair depends only on the pair, not on which two names it
is presented as.** The genuinely reusable content behind `pairColouring_eq`: proved for ordinary
bound variables `a, b, c, d` (so the `rfl`-substitution case split below is unproblematic), then
applied at the opaque `Finset.card_eq_two`-witnesses inside `pairColouring` — applying an already
generic lemma at a stuck term needs no further substitution. -/
theorem get_eq_get_of_pair_eq [DecidableEq V] (C : TopEdgeLabeling V K) {a b c d : V}
    (hab : a ≠ b) (hcd : c ≠ d) (h : ({a, b} : Finset V) = ({c, d} : Finset V)) :
    C.get a b hab = C.get c d hcd := by
  rcases Set.pair_eq_pair_iff.mp (by simpa using congrArg (fun t : Finset V => (t : Set V)) h) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [rfl, EdgeLabeling.get_comm _ _ _]

/-- **`pairColouring` agrees with `C.get` on pairs.** The `Finset.card_eq_two` witnesses used
inside `pairColouring` need not literally be `x, y` in that order — only that `{x, y}` equals the
pair they extract — so this goes through `get_eq_get_of_pair_eq` to cover both orderings. -/
theorem pairColouring_eq [DecidableEq V] (C : TopEdgeLabeling V K) (col0 : K) {x y : V}
    (hxy : x ≠ y) : pairColouring C col0 ({x, y} : Finset V) = C.get x y hxy := by
  have hcard : ({x, y} : Finset V).card = 2 := Finset.card_pair_eq_two_iff.mpr hxy
  rw [pairColouring, dite_eq_left hcard]
  exact get_eq_get_of_pair_eq C (Finset.card_eq_two.mp hcard).choose_spec.choose_spec.1 hxy
    (Finset.card_eq_two.mp hcard).choose_spec.choose_spec.2.symm

/-! ### `u`-uniform monochromatic cliques -/

/-- **`s` is a monochromatic `u`-uniform clique of colour `col`.** Every `u`-element subset of `s`
is coloured `col` under `C`. -/
def MonochromaticKUniformClique (C : Finset V → K) (col : K) (u : ℕ) (s : Finset V) : Prop :=
  ∀ t ∈ s.powersetCard u, C t = col

/-- Some size-`n` vertex subset is a monochromatic `u`-uniform clique of colour `col`. -/
def HasMonochromaticKUniformClique (C : Finset V → K) (col : K) (u n : ℕ) : Prop :=
  ∃ s : Finset V, s.card = n ∧ MonochromaticKUniformClique C col u s

/-- A monochromatic `u`-uniform clique restricts to one on any subset: the subset's `u`-subsets
are among the original clique's. -/
theorem monochromaticKUniformClique_mono_subset {C : Finset V → K} {col : K} {u : ℕ}
    {s s' : Finset V} (hsub : s ⊆ s') (h : MonochromaticKUniformClique C col u s') :
    MonochromaticKUniformClique C col u s :=
  fun t ht => h t (Finset.powersetCard_mono hsub ht)

/-- **Antitonicity of `HasMonochromaticKUniformClique` in the requested clique size.** -/
theorem hasMonochromaticKUniformClique_mono_size {C : Finset V → K} {col : K} {u m n : ℕ}
    (hmn : m ≤ n) (h : HasMonochromaticKUniformClique C col u n) :
    HasMonochromaticKUniformClique C col u m :=
  let ⟨s, hcard, hmono⟩ := h
  let ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (hcard ▸ hmn : m ≤ s.card)
  ⟨t, htcard, monochromaticKUniformClique_mono_subset hts hmono⟩

/-! ### Bridge to `MonochromaticClique.lean` (pairs, `u = 2`) -/

/-- **The `u = 2` case is an ordinary monochromatic clique.** A `pairColouring`-monochromatic
`2`-uniform clique is exactly a clique of `C.labelGraph col` in the usual `SimpleGraph` sense. -/
theorem monochromaticKUniformClique_two_iff [DecidableEq V] {C : TopEdgeLabeling V K}
    {col0 col : K} {s : Finset V} :
    MonochromaticKUniformClique (pairColouring C col0) col 2 s ↔
      (C.labelGraph col).IsClique (s : Set V) := by
  refine ⟨fun h x hx y hy hxy => ?_, fun h t ht => ?_⟩
  · have hval := h {x, y} (Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩,
        Finset.card_pair_eq_two_iff.mpr hxy⟩)
    rw [pairColouring_eq C col0 hxy] at hval
    exact (TopEdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hval⟩
  · obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    rw [pairColouring_eq C col0 hxy]
    exact ((TopEdgeLabeling.labelGraph_adj x y).mp (h (hsub (by simp)) (hsub (by simp)) hxy)).2

/-- **The `u = 2`, sized case coincides with `EdgeLabeling.HasMonochromaticClique`.** -/
theorem hasMonochromaticKUniformClique_two_iff [DecidableEq V] {C : TopEdgeLabeling V K}
    (col0 col : K) (n : ℕ) :
    HasMonochromaticKUniformClique (pairColouring C col0) col 2 n ↔
      EdgeLabeling.HasMonochromaticClique C col n :=
  ⟨fun ⟨s, hcard, hmono⟩ => ⟨s, monochromaticKUniformClique_two_iff.mp hmono, hcard⟩,
    fun ⟨s, hs⟩ => ⟨s, hs.card_eq, monochromaticKUniformClique_two_iff.mpr hs.isClique⟩⟩

end SimpleGraph

/-! ### Bridge to `HypergraphRamsey.lean` (constant uniformity `k`, complete host) -/

namespace Hypergraph

variable {n k : ℕ} {Color : Type*}

/-- **A `Hypergraph.EdgeColoring` of the complete `k`-uniform host repackaged as a
`Finset (Fin n) → Color` colouring.** Every `k`-element `Finset (Fin n)` is an edge of
`completeKUniform n k` by definition, so this simply repackages `C`'s value there, with an
arbitrary placeholder `col0` on every `Finset` that is not `k`-element. -/
noncomputable def toFinsetColouring (C : (completeKUniform n k).EdgeColoring Color) (col0 : Color) :
    Finset (Fin n) → Color :=
  fun s => if h : s.card = k then
      C ⟨(s : Set (Fin n)), by rw [mem_completeKUniform_edgeSet, Set.ncard_coe_finset]; exact h⟩
    else col0

/-- **The `u = k` case, on a complete `k`-uniform host, is a `Hypergraph.EdgeColoring`-monochromatic
clique.** -/
theorem monochromaticKUniformClique_toFinsetColouring_iff
    (C : (completeKUniform n k).EdgeColoring Color) (col0 col : Color) {s : Finset (Fin n)} :
    SimpleGraph.MonochromaticKUniformClique (toFinsetColouring C col0) col k s ↔
      EdgeColoring.MonochromaticClique C col k s := by
  unfold SimpleGraph.MonochromaticKUniformClique EdgeColoring.MonochromaticClique
  refine ⟨fun h => ⟨Set.subset_univ _, fun e he => ?_⟩, fun h e he => ?_⟩
  · have hval := h e he
    rw [toFinsetColouring, dite_eq_left (Finset.mem_powersetCard.mp he).2] at hval
    exact ⟨_, hval⟩
  · rw [toFinsetColouring, dite_eq_left (Finset.mem_powersetCard.mp he).2]
    exact (h.2 e he).2



/-- **The `u = k`, sized case coincides with `Hypergraph.EdgeColoring.HasMonochromaticClique`.** -/
theorem hasMonochromaticKUniformClique_toFinsetColouring_iff
    (C : (completeKUniform n k).EdgeColoring Color) (col0 col : Color) (m : ℕ) :
    SimpleGraph.HasMonochromaticKUniformClique (toFinsetColouring C col0) col k m ↔
      EdgeColoring.HasMonochromaticClique C col k m :=
  exists_congr fun _ => and_congr_right fun _ =>
    monochromaticKUniformClique_toFinsetColouring_iff C col0 col

end Hypergraph
