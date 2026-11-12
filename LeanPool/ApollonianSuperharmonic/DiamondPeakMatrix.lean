/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondParameter

-- [TABLET NODE: DiamondPeakMatrix]

/-!
# DiamondPeakMatrix

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For the positive diamond parameter $k$, the exceptional peak matrix is
$$
 A_k=\frac12\begin{pmatrix}k/(k+1)&1\\1&(1-k)/k\end{pmatrix}.
$$
Positivity of $k$ makes both displayed denominators nonzero.
-/
noncomputable def DiamondPeakMatrix (K : DiamondParameter) :
    Matrix (Fin 2) (Fin 2) Real :=
-- BODY
  let k : Real := K.1
  (1 / 2 : Real) • ![![k / (k + 1), 1], ![1, (1 - k) / k]]

end ApollonianSuperharmonic

end
