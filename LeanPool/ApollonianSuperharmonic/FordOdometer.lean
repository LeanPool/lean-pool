/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordOdometerFamilyExistsUnique

-- [TABLET NODE: FordOdometer]

/-!
# FordOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The Ford odometer $g_{p,q}:\mathbb Z^2\to\mathbb Z$ is the component at
the Ford--Farey parameter $(p,q)$ of the unique family constructed in
`FordOdometerFamilyExistsUnique`.
-/
noncomputable def FordOdometer (P : FordFareyParameter) : IntegerLatticeFunction :=
-- BODY
  Classical.choose FordOdometerFamilyExistsUnique P

end ApollonianSuperharmonic

end
