/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: FordPeakMatrix]

/-!
# FordPeakMatrix

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For relatively prime $q$ and $|p|$, with $q>0$, the exceptional peak
matrix of the Ford circle $C_{p,q}$ is
$$
 A_{p,q}=\frac1{q^2}\begin{pmatrix}1&pq\\pq&0\end{pmatrix}.
$$
This definition is made only for $q>0$ Ford circles; it assigns no matrix
to the curvature-zero line parent.
-/
noncomputable def FordPeakMatrix (p : Int) (q : Nat) (_q_pos : 0 < q)
    (_reduced : Nat.Coprime q p.natAbs) : Matrix (Fin 2) (Fin 2) Real :=
-- BODY
  (1 / ((q : Real) ^ 2)) • ![![(1 : Real), (p : Real) * (q : Real)],
    ![(p : Real) * (q : Real), (0 : Real)]]

end ApollonianSuperharmonic

end
