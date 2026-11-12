/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: P4630T1RingIndex]

/-!
# P4630T1RingIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The twelve exterior periodic indices, in cyclic order for each parent,
are the entries of the following array. The row index is in
$\{0,1,2\}$ and the column index is in $\{0,1,2,3\}$.
$$
\begin{pmatrix}
A_{-1,-1}&A_{0,-1}&B_{1,1}&B_{0,1}\\
C_{1,0}&C_{1,1}&D_{-1,0}&D_{-1,-1}\\
E_{0,1}&E_{-1,0}&F_{0,-1}&F_{1,0}
\end{pmatrix}.
$$
These are indices, not identifications of prototile records.
-/
def P4630T1RingIndex : Fin 3 → Fin 4 → PeriodicSubtileIndex :=
-- BODY
  ![![⟨.A, -1, -1⟩, ⟨.A, 0, -1⟩, ⟨.B, 1, 1⟩, ⟨.B, 0, 1⟩],
    ![⟨.C, 1, 0⟩, ⟨.C, 1, 1⟩, ⟨.D, -1, 0⟩, ⟨.D, -1, -1⟩],
    ![⟨.E, 0, 1⟩, ⟨.E, -1, 0⟩, ⟨.F, 0, -1⟩, ⟨.F, 1, 0⟩]]

end ApollonianSuperharmonic

end
