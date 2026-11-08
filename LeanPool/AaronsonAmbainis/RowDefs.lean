/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import LeanPool.AaronsonAmbainis.Statements

/-!
# Interface for the proof of the row bound

The row bound of Agarwal and Ben-David (`RowBound` in `Statements.lean`) enters `Chain.lean`
as a named hypothesis. This file states the links of the proof of the row bound of the paper
(Section 6: cost at most `π² d²` for functions with values in `[-1,1]`, where the bound of
Agarwal and Ben-David gives `π² d² / 2`), which has no hypothesis:

* `MarkovEndpoint`  — A. A. Markov's inequality at an endpoint of the interval `[0,2]`
                      (Lemma 6.1);
* `BlockInequality` — the block inequality for a family of blocks in which every coordinate
                      lies in at most `N` blocks (Lemma 6.4);
* `PackingBound`    — the packing bound, for fractional packings (Lemma 6.5);
* `CoverDuality`    — linear-programming duality between packings and rows
                      (Proposition 6.7);
* `RowBoundPM`      — the row bound (Theorem 6.8).

Chain: `MarkovEndpoint → BlockInequality → PackingBound`, then
`PackingBound → CoverDuality → RowBoundPM`. The block inequality also gives `SensitivityBound`
(`Statements.lean`), and `RowBoundPM` and `SensitivityBound` enter the main theorem
(`MainTheorem.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- Markov's inequality at an endpoint: a real polynomial of degree at most `D` which is bounded
by `1` in absolute value on `[0,2]` has `|p'(0)| ≤ D²`. -/
def MarkovEndpoint : Prop :=
  ∀ (D : ℕ) (p : Polynomial ℝ), p.natDegree ≤ D →
    (∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) → |p.derivative.eval 0| ≤ (D : ℝ) ^ 2

/-- The block inequality. `f` is bounded by `1` and has degree at most `d`; `S b` (`b : β`) is a
finite family of blocks such that every coordinate lies in at most `N` blocks; `m ≥ 1` satisfies
`N (1 - cos (π / m)) ≤ 2`. Then `∑_b |f(x) - f(x^{S b})| ≤ 4 d² m²`. -/
def BlockInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ), 0 < m →
    (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
    (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2

/-- The packing bound. `f` is bounded by `1` and has degree at most `d`. If `κ ≥ 0` and
`∑_{S ∋ i} κ_S ≤ 1` for every coordinate `i`, then `∑_S κ_S |f(x) - f(x^S)| ≤ π² d²`. -/
def PackingBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (κ : Finset ι → ℝ), (∀ S, 0 ≤ κ S) →
    (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
    ∑ S, κ S * |f x - f (flipSet x S)| ≤ Real.pi ^ 2 * (d : ℝ) ^ 2

/-- Duality between packings and rows: if every fractional packing `κ` has `∑_S κ_S t_S ≤ K`,
then there is a vector `a ≥ 0` of total mass at most `K` with `t_S ≤ a(S)` for every `S`.
(The hypotheses `0 ≤ K` and `t ∅ ≤ 0` follow from the hypothesis on packings: take `κ = 0`,
and take `κ` with `κ_∅` arbitrarily large and `κ_S = 0` for `S ≠ ∅`.) -/
def CoverDuality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : Finset ι → ℝ) (K : ℝ), 0 ≤ K → t ∅ ≤ 0 →
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) →
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i

/-- The row bound (Theorem 6.8 of the paper): a function with values in `[-1,1]` and of
degree at most `d` has, at every point, a row of cost at most `π² d²`. -/
def RowBoundPM : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i

end AaronsonAmbainis
