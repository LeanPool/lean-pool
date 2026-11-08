/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import LeanPool.AaronsonAmbainis.Statements

/-!
# Interface for the proof of the two-sided inequality from the antipodal inequality

`AllPairsInequality` is the all-pairs inequality (the inequality of Proposition 5.2 of the paper:
the sum over all pairs of a one and a zero of `g`), multiplied by `2` so that `2^(n-1)` does not
appear.

It splits the proof of `AntipodalInequality → TwoSidedInequality` into two independent parts:

* `AntipodalInequality → AllPairsInequality` — apply the antipodal inequality (Theorem 4.3) on
  every subcube and add up (Section 5.1);
* `AllPairsInequality → TwoSidedInequality` — the overlap lemma (Lemma 4.1) and the
  Cauchy–Schwarz inequality (Section 5.2).

The all-pairs inequality is also the starting point of the statements on real functions:
applied to the level functions `1_{f > t}` of a real function `f` and integrated over the level
`t`, it gives the integrated all-pairs inequality (`Level/Integrated.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper, multiplied by `2`).
For every Boolean `g`, all positive weights `w` and every row field `lam`:
`2 · ∑_{x : g x = true} ∑_{y : g y = false} 1 / (∑_{j ∈ Δ(x,y)} w_j lam^x_j lam^y_j)
  ≤ 2^n · ∑_j b_j(g) / w_j`. -/
def AllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    2 * ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j

end AaronsonAmbainis
