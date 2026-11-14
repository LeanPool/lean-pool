/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Data.EReal.Operations

-- [TABLET NODE: P3832T1ConeCollapse]

/-!
# P3832T1ConeCollapse

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $I=[0,1]$ and let
$K=\{(r,b)\in I^2:b\leq r\}$, both with their subspace topologies.
The collapsed-cone projection is
$$
q:I^2\longrightarrow K,\qquad q(r,t)=(r,rt).
$$
This is well-defined because $0\leq rt\leq r\leq1$.
It identifies the entire side $\{0\}\times I$ with the cone vertex.
-/
def P3832T1ConeCollapse :
    Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 →
      {z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 // (z.2 : ℝ) ≤ z.1} :=
-- BODY
  fun z =>
    ⟨⟨z.1, ⟨(z.1 : ℝ) * z.2,
      mul_nonneg z.1.2.1 z.2.2.1,
      (mul_le_mul_of_nonneg_left z.2.2.2 z.1.2.1).trans (by simpa using z.1.2.2)⟩⟩,
      by simpa using mul_le_mul_of_nonneg_left z.2.2.2 z.1.2.1⟩

end ApollonianSuperharmonic

end
