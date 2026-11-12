/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import LeanPool.ApollonianSuperharmonic.P4828T1Root

-- [TABLET NODE: P4828T1Evaluate]

/-!
# P4828T1Evaluate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $z\in\mathbb Z[i]$, a side $e\in\{-,+\}$, and a finite word $w$
over $\mathbb Z/3\mathbb Z$, define $E(z,e,[]) = F(z,e)$ and
$$
 E(z,e,w b)=S(R_b E(z,e,w)).
$$
Thus letters are read from left to right; $w b$ means appending one letter.
This evaluation is denoted by `P4828T1Evaluate`.
-/
def P4828T1Evaluate (z : GaussianInt) (side : Bool)
    (word : List (Fin 3)) : Fin 4 → CircleCoordinates :=
-- BODY
  word.foldl (fun q b => P4828T1Step (P4828T1Rotate q b))
    (P4828T1Root z side)

end ApollonianSuperharmonic

end
