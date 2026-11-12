/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: SimpleGridPath]

/-!
# SimpleGridPath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A footprint graph $(V,E)$ is a simple nontrivial grid path when its vertices
can be listed without repetition as $p_0,\ldots,p_n$ with $n\geq1$, and its
edges are exactly the unordered pairs $\{p_j,p_{j+1}\}$ of consecutive
vertices.  Every consecutive pair must differ by one of $\pm1,\pm i$, so
each displayed pair is an actual unit edge of the Gaussian-integer lattice.
-/
def SimpleGridPath (V : Set GaussianInt)
    (E : Set (Finset GaussianInt)) : Prop :=
-- BODY
  ∃ p : List GaussianInt, p.Nodup ∧ 2 ≤ p.length ∧
    V = (p.toFinset : Set GaussianInt) ∧
    (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ →
        b = a + 1 ∨ b = a - 1 ∨
          b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) ∧
    ∀ e, e ∈ E ↔ ∃ a b : GaussianInt, ∃ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}

end ApollonianSuperharmonic

end
