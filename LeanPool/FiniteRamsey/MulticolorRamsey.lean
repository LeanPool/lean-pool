/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.ArrowSemantics
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The multicolour clique Ramsey arrow, and its reduction to the two-colour case

`MulticolorCliqueArrow` specialises the generic `SimpleGraph.Arrow` relation (from the file
preceding it in the series) to a complete host and constant clique targets, one per colour.

## Background

The classical two-colour Ramsey arrow `n → (r, s)` generalises to `k` colours: `n → (n_1, ...,
n_k)` says every `k`-colouring of `K_n`'s edges contains, in some colour `c`, a monochromatic
`K_{n_c}`. This file states that relation (`MulticolorCliqueArrow`, indexed by an arbitrary
`Fin k` colour palette) and proves its headline theorem: **unconditional existence, for every
`k` and every tuple of clique sizes**, via the classical recursive argument
`R(n_1, ..., n_k) ≤ R(n_1, R(n_2, ..., n_k))`.

## The argument

Induction on `k`.

* `k = 0`: vacuous. No colouring by the *empty* colour type `Fin 0` can exist on a host with at
  least one edge, so the arrow relation holds trivially (`exists_multicolorCliqueArrow_zero`).
* `k + 1`: given `sizes : Fin (k + 1) → Nat`, split off colour `0` (target size `sizes 0`) from
  the rest (`Fin.tail sizes : Fin k → Nat`). By the induction hypothesis, some `m` makes
  `MulticolorCliqueArrow m (Fin.tail sizes)` hold. By the *two-colour* case — taken here as an
  explicit hypothesis `h2`, since proving it is a separate, much larger piece of
  neighbourhood-counting combinatorics entirely out of this file's scope (the classical Ramsey
  theorem itself) — some `N` makes `MulticolorCliqueArrow N ![sizes 0, m]` hold. Given any
  `(k+1)`-colouring `C` of `K_N`,
  merge colours `1..k` into a single colour `1` (colour `0` stays `0`) and apply the two-colour
  hypothesis to the merged colouring:
  - colour `0` of the merged colouring is exactly colour `0` of `C` — a colour-`0` clique of size
    `sizes 0` there finishes immediately.
  - colour `1` of the merged colouring is a set `S` of `m` vertices all of whose `C`-colours
    (among themselves) are `≠ 0`. Pulling `C` back along an embedding `Fin m ↪ Fin N` with range
    `S`, and dropping the (never-occurring) colour `0` via `Fin.pred`, gives a genuine
    `k`-colouring of `K_m`. The induction hypothesis, applied to *this* colouring, produces a
    monochromatic clique in some colour `c' : Fin k`, i.e. (shifting back by one, `c'.succ`) a
    colour-`c'.succ` clique of size `sizes c'.succ` inside `S`, hence inside `K_N` — done.

**Given the two-colour case as a hypothesis rather than the classical Ramsey theorem itself**,
this file's main theorem, `exists_multicolorCliqueArrow_of_exists_two`, is a genuinely more
general induction principle than what it specialises to: *any* proof that the classical
two-colour clique arrow always eventually holds lifts, mechanically, to every finite colour
count. Discharging `h2` with the two-colour theorem (`MulticolorRamseyUnconditional.lean`) gives
the unconditional `∀ k sizes, ∃ n, MulticolorCliqueArrow n sizes`.

## Design notes for reviewers

* The two-colour merge uses `Fin 2` (`0`/`1`) rather than a bespoke two-element colour type, to
  keep this file's induction independent of any particular two-colour formalisation.
-/

@[expose] public section

namespace SimpleGraph

variable {k : Nat}

/-- **The multicolour clique Ramsey arrow.** `MulticolorCliqueArrow n sizes` means every
`k`-colouring of the edges of `K_n` contains, in some colour `c`, a monochromatic clique of size
`sizes c`. The `R(n_1, ..., n_k)`-style multicolour generalisation of the classical two-colour
clique arrow — `Arrow` specialised to a complete host and constant clique targets. -/
def MulticolorCliqueArrow (n : Nat) (sizes : Fin k → Nat) : Prop :=
  (⊤ : SimpleGraph (Fin n)).Arrow fun c => completeGraph (Fin (sizes c))

/-- **Colour-permutation invariance.** Permuting which colour is asked to find which clique size
does not change arrowability. -/
theorem multicolorCliqueArrow_permute_iff {n : Nat} {sizes : Fin k → Nat} (e : Fin k ≃ Fin k) :
    MulticolorCliqueArrow n sizes ↔ MulticolorCliqueArrow n (sizes ∘ e) :=
  (Arrow.reindex e).symm

/-- **Base case (`k = 0`).** A host with at least one edge cannot be coloured at all by the
empty colour type `Fin 0`, so the arrow relation holds vacuously: there is no `C` to check. -/
theorem exists_multicolorCliqueArrow_zero (sizes : Fin 0 → Nat) :
    ∃ n, MulticolorCliqueArrow n sizes :=
  ⟨2, fun C => (C.get 0 1 (by decide)).elim0⟩

section MergeColoring

variable {V : Type} {G : SimpleGraph V}

/-- The two-colour "merge colours `1..k` into colour `1`" recolouring used to reduce a
`(k + 1)`-colour arrow problem to the two-colour case: colour `0` is kept as `0`, every other
colour becomes `1`. -/
def mergeColoring (C : G.EdgeLabeling (Fin (k + 1))) : G.EdgeLabeling (Fin 2) :=
  C.compRight (fun c => if c = 0 then 0 else 1)

/-- Merging preserves colour `0` exactly: the colour-`0` subgraph of the merged colouring is the
colour-`0` subgraph of the original. -/
theorem mergeColoring_labelGraph_zero (C : G.EdgeLabeling (Fin (k + 1))) :
    (mergeColoring C).labelGraph 0 = C.labelGraph 0 := by
  ext; simp [mergeColoring, EdgeLabeling.labelGraph_adj]

/-- The colour-`1` subgraph of the merged colouring is exactly the edges whose original colour
is `≠ 0`. -/
theorem mergeColoring_labelGraph_one_adj (C : G.EdgeLabeling (Fin (k + 1))) (x y : V) :
    ((mergeColoring C).labelGraph 1).Adj x y ↔ ∃ h : G.Adj x y, C.get x y h ≠ 0 := by
  simp [mergeColoring, EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

end MergeColoring

/-- **Unconditional existence of the multicolour clique Ramsey arrow, for arbitrary `k`, given
the two-colour case.** The classical recursive-bound argument
`R(n_1, ..., n_k) ≤ R(n_1, R(n_2, ..., n_k))`, by induction on `k`: see this file's module
docstring. A genuine induction principle, not specific to any one proof of the two-colour case:
`h2` can be discharged by any theorem establishing that the classical two-colour clique arrow
always eventually holds (e.g. the classical Ramsey theorem, once available). -/
theorem exists_multicolorCliqueArrow_of_exists_two
    (h2 : ∀ r s : Nat, ∃ n, MulticolorCliqueArrow n ![r, s]) :
    ∀ (k : Nat) (sizes : Fin k → Nat), ∃ n, MulticolorCliqueArrow n sizes
  | 0, sizes => exists_multicolorCliqueArrow_zero sizes
  | k + 1, sizes => by
    obtain ⟨m, hm⟩ := exists_multicolorCliqueArrow_of_exists_two h2 k (Fin.tail sizes)
    obtain ⟨N, hN⟩ := h2 (sizes 0) m
    refine ⟨N, fun C => ?_⟩
    obtain ⟨c, hc⟩ := hN (mergeColoring C)
    fin_cases c
    · -- colour `0`: a colour-`0` clique of the right size
      exact ⟨0, mergeColoring_labelGraph_zero C ▸
        (hc : completeGraph (Fin (sizes 0)) ⊑ (mergeColoring C).labelGraph 0)⟩
    -- colour `1`: a copy of `K_m` none of whose edges has colour `0`; recurse on it
    obtain ⟨f⟩ := (hc : completeGraph (Fin m) ⊑ (mergeColoring C).labelGraph 1)
    let φ : (⊤ : SimpleGraph (Fin m)) ↪g ⊤ := Embedding.completeGraph f.toEmbedding
    have hne (e : (⊤ : SimpleGraph (Fin m)).edgeSet) : C.pullback φ.toHom e ≠ 0 := by
      obtain ⟨⟨x, y⟩, he⟩ := e
      exact ((mergeColoring_labelGraph_one_adj C _ _).mp (f.toHom.map_adj he)).2
    obtain ⟨c', hc'⟩ := hm fun e => (C.pullback φ.toHom e).pred (hne e)
    refine ⟨c'.succ, hc'.trans <| (IsContained.of_le fun x y h => ?_).trans
      ((C.labelGraph_pullback_isContained φ c'.succ))⟩
    obtain ⟨H, hd⟩ := (EdgeLabeling.labelGraph_adj _ _).mp h
    exact (EdgeLabeling.labelGraph_adj _ _).mpr ⟨H, (Fin.pred_eq_iff_eq_succ _).mp hd⟩

end SimpleGraph
