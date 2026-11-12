/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeRow
public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingData

-- [TABLET NODE: P4733T1FacePairOrbit]

/-!
# P4733T1FacePairOrbit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For drawing data $D$ and a triple $(r,w,s)$ consisting of a row
$r\in\{0,\ldots,17\}$, $w\in L$, and a Boolean $s$, let
$N_D(r,w,\mathrm{true})=(w\cdot f_r,w\cdot g_r)$ and
$N_D(r,w,\mathrm{false})=(w\cdot g_r,w\cdot f_r)$.
Here $w\cdot f$ is the drawing's face translation, and the two faces
come from the original-footprint edge row.
-/
def P4733T1FacePairOrbit {u v : GaussianInt} {L : AddSubgroup GaussianInt}
    (D : P4677T2DrawingData u v L) (t : Fin 18 × L × Bool) :
    PeriodicSubtileFaceIndex × PeriodicSubtileFaceIndex :=
-- BODY
  let faces := (P4733T1EdgeRow t.1).2
  if t.2.2 then (D.faceShift t.2.1 faces.1, D.faceShift t.2.1 faces.2)
  else (D.faceShift t.2.1 faces.2, D.faceShift t.2.1 faces.1)

end ApollonianSuperharmonic

end
