/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import LeanPool.FiniteRamsey.MonochromaticClique

/-!
# The two-colour Ramsey property: definition, symmetry, monotonicity

For a two-colouring of the edges of a complete graph on `n` vertices, the Ramsey property
`RamseyProperty n r s` says every such colouring contains a red `r`-clique or a blue `s`-clique.
This file gives the property itself, colour-swap symmetry, monotonicity in both the clique-size
parameters and the host size, and the degenerate base cases (`R(1, s) = 1`, `R(r, 1) = 1`,
`R(2, s) = s`, `R(r, 2) = r`) that anchor the recursive existence argument.

This file covers only the property's basic algebra; Ramsey's theorem itself (existence, the
recursive/binomial bound) and the least-Ramsey-number API built on top of existence are separate.
It builds on `MonochromaticClique.lean` for the pullback-transport lemma monotonicity in the host
size needs.

## Main declarations

* `SimpleGraph.RamseyProperty n r s`: every two-colouring of `K_n`'s edges contains a red
  `r`-clique or a blue `s`-clique.
* `SimpleGraph.ramseyProperty_swap`/`_comm`: swapping "red" and "blue" throughout swaps `r`
  and `s`.
* `SimpleGraph.ramseyProperty_mono_cliqueSizes`/`_mono_vertices`: `RamseyProperty` is monotone
  in the clique-size parameters (larger targets are harder to avoid) and in the host size
  (a larger host only makes the property easier to satisfy).
* `SimpleGraph.not_ramseyProperty_zero_of_pos`: an empty host cannot satisfy the property for
  any positive clique sizes.
* Degenerate base cases: `ramseyProperty_one_red`/`_one_blue` (a single vertex trivially has a
  monochromatic 1-clique) and `ramseyProperty_two_left`/`_two_right` (`R(2, s) = s`,
  `R(r, 2) = r`: with clique target `2`, either every edge is the other colour, or some edge
  gives the target directly).

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.

## Tags

ramsey theory, combinatorics, graph coloring, extremal graph theory
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- **A two-colouring of the edges of the complete graph on `V`.** `Bool` is used as the
two-element colour type: `true` plays the role of "red", `false` the role of "blue". -/
abbrev TwoColoring (V : Type*) : Type _ :=
  SimpleGraph.TopEdgeLabeling V Bool

/-- `s` is a red `n`-clique of the two-colouring `C`. -/
abbrev RedClique (C : TwoColoring V) (n : ℕ) (s : Finset V) : Prop :=
  (C.labelGraph true).IsNClique n s

/-- `s` is a blue `n`-clique of the two-colouring `C`. -/
abbrev BlueClique (C : TwoColoring V) (n : ℕ) (s : Finset V) : Prop :=
  (C.labelGraph false).IsNClique n s

/-- `C` has a red `n`-clique somewhere. -/
abbrev HasRedClique (C : TwoColoring V) (n : ℕ) : Prop :=
  ∃ s, RedClique C n s

/-- `C` has a blue `n`-clique somewhere. -/
abbrev HasBlueClique (C : TwoColoring V) (n : ℕ) : Prop :=
  ∃ s, BlueClique C n s

/-- **The two-colour Ramsey property**, i.e. the `n → (r, s)` Ramsey arrow statement: every
two-colouring of the edges of `K_n` contains a red `r`-clique or a blue `s`-clique. -/
def RamseyProperty (n r s : ℕ) : Prop :=
  ∀ C : TwoColoring (Fin n), HasRedClique C r ∨ HasBlueClique C s

/-! ### Swapping red and blue -/

/-- Swap the two colours of a two-colouring: what was red becomes blue and vice versa. -/
def swapColoring (C : TwoColoring V) : TwoColoring V :=
  C.compRight not

@[simp]
theorem colorGraph_swapColoring_red (C : TwoColoring V) :
    (swapColoring C).labelGraph true = C.labelGraph false := by
  ext; simp [swapColoring]

@[simp]
theorem colorGraph_swapColoring_blue (C : TwoColoring V) :
    (swapColoring C).labelGraph false = C.labelGraph true := by
  ext; simp [swapColoring]

theorem hasRedClique_swapColoring_iff (C : TwoColoring V) (n : ℕ) :
    HasRedClique (swapColoring C) n ↔ HasBlueClique C n :=
  exists_congr fun _ => by simp [RedClique, BlueClique]

theorem hasBlueClique_swapColoring_iff (C : TwoColoring V) (n : ℕ) :
    HasBlueClique (swapColoring C) n ↔ HasRedClique C n :=
  exists_congr fun _ => by simp [RedClique, BlueClique]

/-- **Symmetry.** Swapping the colours of every colouring swaps `r` and `s`. -/
theorem ramseyProperty_swap {n r s : ℕ} (h : RamseyProperty n r s) : RamseyProperty n s r :=
  fun C => (h (swapColoring C)).symm.imp (hasBlueClique_swapColoring_iff C s).mp
    (hasRedClique_swapColoring_iff C r).mp

/-- **`RamseyProperty` is symmetric in its two clique-size arguments.** -/
theorem ramseyProperty_comm {n r s : ℕ} : RamseyProperty n r s ↔ RamseyProperty n s r :=
  ⟨ramseyProperty_swap, ramseyProperty_swap⟩

/-! ### Monotonicity -/

/-- **Monotonicity in the clique-size parameters.** A host satisfying the property for larger
clique targets also satisfies it for any smaller ones (a smaller monochromatic clique is easier
to find than a larger one). -/
theorem ramseyProperty_mono_cliqueSizes {n redSmall redLarge blueSmall blueLarge : ℕ}
    (hred : redSmall ≤ redLarge) (hblue : blueSmall ≤ blueLarge)
    (h : RamseyProperty n redLarge blueLarge) : RamseyProperty n redSmall blueSmall :=
  fun C => (h C).imp (hasNClique_mono_size hred) (hasNClique_mono_size hblue)

/-- A monochromatic clique of a pulled-back colouring, along an embedding, pushes forward to a
monochromatic clique of the original colouring of the same size. The two-colour specialisation of
`SimpleGraph.EdgeLabeling.monochromaticClique_map_pullback`. -/
theorem monochromaticClique_map_pullback {W : Type*} (C : TwoColoring W) (f : V ↪ W) (k : Bool)
    {n : ℕ} {s : Finset V} (h : ((C.pullback f).labelGraph k).IsNClique n s) :
    (C.labelGraph k).IsNClique n (s.map f) :=
  EdgeLabeling.monochromaticClique_map_pullback C f k h

/-- **Monotonicity in the host size.** If `RamseyProperty` holds at host size `n`, it holds at
every larger host size `m`: a larger complete graph contains the smaller one, so any
monochromatic clique found inside it (via the canonical inclusion `Fin n ↪ Fin m`) is genuinely
present in the larger host too. -/
theorem ramseyProperty_mono_vertices {n m redSize blueSize : ℕ} (hmn : n ≤ m)
    (h : RamseyProperty n redSize blueSize) : RamseyProperty m redSize blueSize :=
  fun C => (h (C.pullback (Fin.castLEEmb hmn))).imp
    (EdgeLabeling.hasMonochromaticClique_map_pullback C _ true)
    (EdgeLabeling.hasMonochromaticClique_map_pullback C _ false)

theorem not_ramseyProperty_of_le_vertices {n m redSize blueSize : ℕ} (hmn : m ≤ n)
    (hnot : ¬ RamseyProperty n redSize blueSize) : ¬ RamseyProperty m redSize blueSize :=
  mt (ramseyProperty_mono_vertices hmn) hnot

/-! ### Degenerate base cases -/

theorem not_hasMonochromaticClique_of_card_lt {W : Type*} [Fintype W] {k : Bool}
    (C : TwoColoring W) {n : ℕ} (hn : Fintype.card W < n) :
    ¬ ∃ s : Finset W, (C.labelGraph k).IsNClique n s :=
  fun ⟨s, hs⟩ => hn.not_ge (hs.card_eq ▸ s.card_le_univ)

/-- **An empty host cannot arrow any positive pair of clique sizes.** -/
theorem not_ramseyProperty_zero_of_pos {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ¬ RamseyProperty 0 r s := fun h =>
  (h fun _ => true).elim (not_hasMonochromaticClique_of_card_lt _ (by simpa))
    (not_hasMonochromaticClique_of_card_lt _ (by simpa))

theorem ramseyProperty_one_red (s : ℕ) : RamseyProperty 1 1 s := fun _ =>
  Or.inl ⟨{0}, by simp⟩

theorem ramseyProperty_one_blue (r : ℕ) : RamseyProperty 1 r 1 := fun _ =>
  Or.inr ⟨{0}, by simp⟩

/-- **`R(2, s) = s`, existence half.** With red target `2`, either the whole host is an
independent set in red (so it is entirely blue, giving a blue `s`-clique on all `s` vertices), or
some red edge already gives the red `2`-clique. -/
theorem ramseyProperty_two_left (s : ℕ) : RamseyProperty s 2 s := by
  intro C
  by_cases hfree : (C.labelGraph true).CliqueFree 2
  · refine Or.inr ⟨Finset.univ, fun v _ w _ hvw => ?_, by simp⟩
    have : ¬ (C.labelGraph true).Adj v w := by simp [cliqueFree_two.mp hfree]
    simpa [hvw] using this
  · exact Or.inl (not_forall_not.mp hfree)

/-- **`R(r, 2) = r`, existence half.** The colour-swapped mirror of `ramseyProperty_two_left`. -/
theorem ramseyProperty_two_right (r : ℕ) : RamseyProperty r r 2 :=
  ramseyProperty_swap (ramseyProperty_two_left r)

/-! ### A worked example -/

/-- A concrete instance: monotonicity in the host size lifts `ramseyProperty_two_left`'s
`RamseyProperty 3 2 3` up to a `5`-vertex host, i.e. `RamseyProperty 5 2 3` holds. -/
theorem ramseyProperty_five_two_three : RamseyProperty 5 2 3 :=
  ramseyProperty_mono_vertices (by omega) (ramseyProperty_two_left 3)

end SimpleGraph
