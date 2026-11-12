/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Analysis.Complex.Basic
public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: SymmetricMatrixCoordinates]

/-!
# SymmetricMatrixCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a real $2\times2$ matrix $A$, define its spatial coordinates by
$$
 \operatorname{coord}(A)=(x,r),\qquad
 x=(A_{00}-A_{11})+2A_{01}i,\qquad r=\operatorname{trace}(A).
$$
When $A$ is symmetric these are the $(x_1,x_2,r)$ coordinates used in the
paper, with $x=x_1+ix_2$.
-/
noncomputable def SymmetricMatrixCoordinates
    (A : Matrix (Fin 2) (Fin 2) Real) : Complex × Real :=
-- BODY
  (⟨A 0 0 - A 1 1, 2 * A 0 1⟩, Matrix.trace A)

end ApollonianSuperharmonic

end
