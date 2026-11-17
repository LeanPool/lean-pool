/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1DualEdges
public import LeanPool.ApollonianSuperharmonic.P3776T1TileContractions
public import LeanPool.ApollonianSuperharmonic.StandardSimplex

-- [TABLET NODE: P3776T1SectorMaps]

/-!
# P3776T1SectorMaps

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given contractions $H$ from `P3776T1TileContractions` and edge
halves $E$ from `P3776T1DualEdges`, a sector-map family assigns
a continuous map $M_f$ from the standard two-simplex to the real plane
for every numbered face $f$. Its value belongs to a tile at a vertex
whose coordinate is positive. At simplex vertex $i$ its value is
$c_{a_i}$, where $a_i$ is the numbered primal vertex. On the simplex edge
with coordinates $s_i=r$, $s_j=1-r$ and the other coordinate zero,
its value is
$$
\begin{cases}
H_{a_j}(2r,m_{a_i a_j}),&0\leq r\leq1/2,\\
H_{a_i}(2(1-r),m_{a_i a_j}),&1/2<r\leq1.
\end{cases}
$$
Finally $M_{u+f}(s)=M_f(s)+[u]$. These are parameter triangles, not an
assertion that the fixed embedded face closures are affine triangles.
-/
structure P3776T1SectorMaps {ι : Type} (P : PeriodicTileCore ι)
    (H : P3776T1TileContractions P) (E : P3776T1DualEdges P) where
-- BODY
  /-- The continuous map from each parameter simplex into its three incident tiles. -/
  faceMap : P.plane.Face → C(StandardSimplex (Fin 3), Real × Real)
  support : ∀ f s, ∃ i : Fin 3,
    0 < s.1 i ∧ faceMap f s ∈ TileRealization (P.tile (P.plane.faceVertex f i))
  vertex : ∀ f i (s : StandardSimplex (Fin 3)),
    (∀ j, s.1 j = if j = i then 1 else 0) →
      faceMap f s = H.center (P.plane.faceVertex f i)
  edge : ∀ f (i j : Fin 3), i ≠ j → ∀ r : Set.Icc (0 : Real) 1,
    ∀ s : StandardSimplex (Fin 3),
    (∀ k, s.1 k = if k = i then (r : Real) else if k = j then 1 - (r : Real) else 0) →
      faceMap f s =
        if (r : Real) ≤ 1 / 2 then
          H.homotopy (P.plane.faceVertex f j) (2 * (r : Real))
            (E.port (P.plane.faceVertex f i) (P.plane.faceVertex f j))
        else
          H.homotopy (P.plane.faceVertex f i) (2 * (1 - (r : Real)))
            (E.port (P.plane.faceVertex f i) (P.plane.faceVertex f j))
  periodic : ∀ u : P.lattice, ∀ f s,
    faceMap (P.faceShift u f) s = faceMap f s + GaussianRealPoint u

end ApollonianSuperharmonic

end
