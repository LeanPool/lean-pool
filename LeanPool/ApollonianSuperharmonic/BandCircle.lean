/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandGeneralCircle

-- [TABLET NODE: BandCircle]

/-!
# BandCircle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A band circle is an element $C=(c,w)$ of $\mathcal B^{\rm gen}$ with
$c>0$.  The notation $\mathcal B$ below always means this
positive-curvature subtype.  The oriented lines remain available only
through $\mathcal B^{\rm gen}$ for Descartes recursion.
-/
def BandCircle : Type :=
-- BODY
  {C : BandGeneralCircle // 0 < C.1.1}

end ApollonianSuperharmonic

end
