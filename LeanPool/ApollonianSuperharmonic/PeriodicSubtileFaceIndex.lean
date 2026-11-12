/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceLabel

-- [TABLET NODE: PeriodicSubtileFaceIndex]

/-!
# PeriodicSubtileFaceIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A periodic face index is a triple $(H,m,n)$, where $H$ is one of the twelve
labels of `SixSubtileFaceLabel` and $(m,n)\in\mathbb Z^2$.  It
denotes the translate by $mu+nv$ of the entire labelled face, including its
three tile occurrences and its selected common point.
-/
structure PeriodicSubtileFaceIndex where
-- BODY
  /-- The orbit label preserved by all period translations. -/
  label : SixSubtileFaceLabel
  /-- The integral coordinate along the first period vector. -/
  first : Int
  /-- The integral coordinate along the second period vector. -/
  second : Int
  deriving DecidableEq

end ApollonianSuperharmonic

end
