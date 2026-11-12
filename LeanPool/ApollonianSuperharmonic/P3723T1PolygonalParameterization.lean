/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Segment

-- [TABLET NODE: P3723T1PolygonalParameterization]

/-!
# P3723T1PolygonalParameterization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $g:[0,1]\to\mathbb R^2$, a polygonal parametrization certificate
consists of an integer $m>0$, a strictly increasing sequence
$0=\tau_0<\cdots<\tau_m=1$, and, for each $i<m$, plane vectors
$A_i,B_i$ such that $g(s)=A_i+sB_i$ whenever
$\tau_i\le s\le\tau_{i+1}$. The certificate does not by itself assert
injectivity. Its affine pieces include their endpoints.
-/
structure P3723T1PolygonalParameterization
    (g : Set.Icc (0 : Real) 1 → Real × Real) where
-- BODY
  /-- The positive number of affine parameter intervals. -/
  count : Nat
  positive : 0 < count
  /-- The strictly increasing subdivision times, including zero and one. -/
  time : Fin (count + 1) → Real
  strict : StrictMono time
  start : time 0 = 0
  finish : time (Fin.last count) = 1
  affine_on : ∀ i : Fin count, ∃ A B : Real × Real,
    ∀ s : Set.Icc (0 : Real) 1,
      time i.castSucc ≤ (s : Real) → (s : Real) ≤ time i.succ →
        g s = A + (s : Real) • B

end ApollonianSuperharmonic

end
