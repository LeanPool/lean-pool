/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircleEuclideanData

-- [TABLET NODE: CircleMatrix]

/-!
# CircleMatrix

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a positive-curvature band circle $C$, let
$E=(z,r)=\operatorname{circ}(C)$ be its Euclidean circle datum from
`BandCircleEuclideanData`, and write $z=x_1+ix_2$.  Define
$$
 A_C=\frac12
 \begin{pmatrix}r+x_1&x_2\\ x_2&r-x_1\end{pmatrix}.
$$
No matrix is assigned to a curvature-zero line.
-/
noncomputable def CircleMatrix (C : BandCircle) : Matrix (Fin 2) (Fin 2) ℝ :=
-- BODY
  let E := BandCircleEuclideanData C
  (2 : ℝ)⁻¹ •
    ![![E.radius + E.center.re, E.center.im],
      ![E.center.im, E.radius - E.center.re]]

end ApollonianSuperharmonic

end
