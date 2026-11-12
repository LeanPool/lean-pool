/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init


-- [TABLET NODE: SixSubtileFaceLabel]

/-!
# SixSubtileFaceLabel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The fixed six-occurrence periodic layout has twelve face-orbit labels.  The
four inner labels are $I_1,I_2,I_3,I_4$, and the eight outer labels are
$J_1,\ldots,J_8$.  In particular, $J_5$ is the face called `F10`
in the coverage audit.
-/
inductive SixSubtileFaceLabel : Type where
-- BODY
  | I1 | I2 | I3 | I4
  | J1 | J2 | J3 | J4 | J5 | J6 | J7 | J8
  deriving DecidableEq

end ApollonianSuperharmonic

end
