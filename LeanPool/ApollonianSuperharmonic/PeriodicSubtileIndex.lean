/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Order.Ring.Int

public import LeanPool.ApollonianSuperharmonic.SixSubtileLabel

-- [TABLET NODE: PeriodicSubtileIndex]

/-!
# PeriodicSubtileIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A periodic labeled-subtile index is a triple $(X,m,n)$ with
$X\in\{A,B,C,D,E,F\}$ and $(m,n)\in\mathbb Z^2$.  It denotes the translate
$X_{m,n}$ in the periodic six-type layout.
-/
structure PeriodicSubtileIndex where
-- BODY
  /-- The orbit label preserved by all period translations. -/
  label : SixSubtileLabel
  /-- The integral coordinate along the first period vector. -/
  first : Int
  /-- The integral coordinate along the second period vector. -/
  second : Int
  deriving DecidableEq

end ApollonianSuperharmonic

end
