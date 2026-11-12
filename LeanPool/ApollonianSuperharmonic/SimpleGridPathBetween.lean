/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: SimpleGridPathBetween]

/-!
# SimpleGridPathBetween

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A footprint graph $(V,E)$ is a simple nontrivial grid path from $x$ to $y$
when one list $p_0,\ldots,p_n$ without repeated vertices, with $n\geq1$,
simultaneously satisfies $p_0=x$, $p_n=y$, has vertex set exactly $V$, and
has edge set exactly the unordered pairs $\{p_j,p_{j+1}\}$.  Every
consecutive pair differs by one of $\pm1,\pm i$.
-/
def SimpleGridPathBetween (V : Set GaussianInt)
    (E : Set (Finset GaussianInt)) (x y : GaussianInt) : Prop :=
-- BODY
  ∃ p : List GaussianInt, p.Nodup ∧ 2 ≤ p.length ∧
    p.head? = some x ∧ p.getLast? = some y ∧
    V = (p.toFinset : Set GaussianInt) ∧
    (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ →
        b = a + 1 ∨ b = a - 1 ∨
          b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) ∧
    ∀ e, e ∈ E ↔ ∃ a b : GaussianInt, ∃ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}

end ApollonianSuperharmonic

end
