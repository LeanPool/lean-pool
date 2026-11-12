/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileFaceIndex
public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: SixSubtileFaceVertices]

/-!
# SixSubtileFaceVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The three vertices of each translated face in the six-occurrence layout are
the following periodic subtile indices:
$$
\begin{array}{c|c@{\qquad}c|c}
I_1&(A,B,C)&I_2&(A,B,D)\\
I_3&(A,C,F)&I_4&(B,D,E)\\
J_1&(A,B_{0,1},E_{0,1})&J_2&(A,B_{0,1},F)\\
J_3&(A,B_{1,1},C_{1,1})&J_4&(A,B_{1,1},D)\\
J_5&(A,C_{1,1},E_{0,1})&J_6&(B,D_{-1,-1},F_{0,-1})\\
J_7&(C,D_{-1,0},E_{-1,0})&J_8&(C,D_{-1,0},F).
\end{array}
$$
For the face indexed by $(H,m,n)$, $(m,n)$ is added to every subscript in
the row.  Thus translation acts on the entire face rather than on one
displayed vertex.
-/
def SixSubtileFaceVertices (f : PeriodicSubtileFaceIndex) :
    Fin 3 -> PeriodicSubtileIndex :=
-- BODY
  let m := f.first
  let n := f.second
  match f.label with
  | .I1 => ![⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩]
  | .I2 => ![⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.D, m, n⟩]
  | .I3 => ![⟨.A, m, n⟩, ⟨.C, m, n⟩, ⟨.F, m, n⟩]
  | .I4 => ![⟨.B, m, n⟩, ⟨.D, m, n⟩, ⟨.E, m, n⟩]
  | .J1 => ![⟨.A, m, n⟩, ⟨.B, m, n + 1⟩, ⟨.E, m, n + 1⟩]
  | .J2 => ![⟨.A, m, n⟩, ⟨.B, m, n + 1⟩, ⟨.F, m, n⟩]
  | .J3 => ![⟨.A, m, n⟩, ⟨.B, m + 1, n + 1⟩,
      ⟨.C, m + 1, n + 1⟩]
  | .J4 => ![⟨.A, m, n⟩, ⟨.B, m + 1, n + 1⟩, ⟨.D, m, n⟩]
  | .J5 => ![⟨.A, m, n⟩, ⟨.C, m + 1, n + 1⟩, ⟨.E, m, n + 1⟩]
  | .J6 => ![⟨.B, m, n⟩, ⟨.D, m - 1, n - 1⟩, ⟨.F, m, n - 1⟩]
  | .J7 => ![⟨.C, m, n⟩, ⟨.D, m - 1, n⟩, ⟨.E, m - 1, n⟩]
  | .J8 => ![⟨.C, m, n⟩, ⟨.D, m - 1, n⟩, ⟨.F, m, n⟩]

end ApollonianSuperharmonic

end
