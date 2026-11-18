/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondOdometerExistsUnique

-- [TABLET NODE: DiamondOdometer]

/-!
# DiamondOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The diamond odometer $g_k:\mathbb Z^2\to\mathbb Z$ is the unique function
selected by `DiamondOdometerExistsUnique` for the positive parameter
$k$.
-/
noncomputable def DiamondOdometer (K : DiamondParameter) : IntegerLatticeFunction :=
-- BODY
  Classical.choose (DiamondOdometerExistsUnique K)

end ApollonianSuperharmonic

end
