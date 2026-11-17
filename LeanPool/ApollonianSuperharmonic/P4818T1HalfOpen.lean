/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains

-- [TABLET NODE: P4818T1HalfOpen]

/-!
# P4818T1HalfOpen

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a positive integer $k$, let $T_k$ be the closed lattice domain of
`DiamondVertexDomains`. Set
$$
\begin{aligned}
 U_a&=\{(r,2k):-1\le r\le1,\ r\in\mathbb Z\},\\
 U_b&=\{(k+1-j,k+j):1\le j\le k\}
       \cup\{(k-j,k+j):0\le j<k\},\\
 U_c&=\{(j-k-1,k+j-1):1\le j\le k\}
       \cup\{(j-k-1,k+j):1\le j\le k\}.
\end{aligned}
$$
Define $H_k=T_k\setminus(U_a\cup U_b\cup U_c)$.
All indices in these sets are integers.
-/
def P4818T1HalfOpen (K : DiamondParameter) : Set GaussianInt :=
-- BODY
  let k : Int := K.1
  {x | x ∈ DiamondVertexDomains K false ∧
    ¬ (x.im = 2 * k ∧ -1 ≤ x.re ∧ x.re ≤ 1) ∧
    ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨k + 1 - j, k + j⟩) ∨
       (∃ j : Int, 0 ≤ j ∧ j < k ∧ x = ⟨k - j, k + j⟩)) ∧
    ¬ ((∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨j - k - 1, k + j - 1⟩) ∨
       (∃ j : Int, 1 ≤ j ∧ j ≤ k ∧ x = ⟨j - k - 1, k + j⟩))}

end ApollonianSuperharmonic

end
