/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: GaussianTranslation]

/-!
# GaussianTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Gaussian integer $u$, translation by $u$ is the grid map
$\tau_u(z)=z+u$.  It acts on cell basepoints, footprint vertices, and the
assigned anchor of an empty prototile by the same formula.
-/
def GaussianTranslation (u z : GaussianInt) : GaussianInt :=
-- BODY
  z + u

end ApollonianSuperharmonic

end
