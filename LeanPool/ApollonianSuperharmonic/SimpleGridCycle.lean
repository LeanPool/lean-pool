/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: SimpleGridCycle]

/-!
# SimpleGridCycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A finite grid graph $(V,E)$ is a *simple grid cycle* when its vertices
have a cyclic listing $p_0,\ldots,p_{n-1}$ without repetition, with
$n\geq4$, every consecutive pair (including $p_{n-1},p_0$) is
four-neighbor adjacent, and $E$ consists exactly of those consecutive
unordered pairs.
-/
def SimpleGridCycle (V : Set GaussianInt)
    (E : Set (Finset GaussianInt)) : Prop :=
-- BODY
  ∃ p : List GaussianInt, ∃ x y : GaussianInt,
    p.Nodup ∧ 4 ≤ p.length ∧
    p.head? = some x ∧ p.getLast? = some y ∧
    V = (p.toFinset : Set GaussianInt) ∧
    FourNeighborAdjacent y x ∧
    (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) ∧
    ∀ e, e ∈ E ↔ e = {y, x} ∨
      ∃ a b : GaussianInt, ∃ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}

end ApollonianSuperharmonic

end
