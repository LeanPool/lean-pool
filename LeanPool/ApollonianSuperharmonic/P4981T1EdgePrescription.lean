/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation

-- [TABLET NODE: P4981T1EdgePrescription]

/-!
# P4981T1EdgePrescription

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A prescription on a primitive coordinate edge is one of the following data:
the line edge $((0,-1),(0,1))$; a Gaussian parameter $z$ for the edge
$((0,1),(1,1+2z+2i))$; a parameter $z$ for
$((0,-1),(1,1+2z+2i))$; a parameter $z$ for
$((1,1+2z+2i),(1,1+2z))$; or a proper quadruple $q$ together
with a parent slot $j\in\mathbb Z/3\mathbb Z$, prescribing the edge
$(q_{j+1},q_0)$. These are data indexed by the actual coordinate edge,
not an identification of different presentations.
-/
inductive P4981T1EdgePrescription :
    CircleCoordinates × CircleCoordinates → Type where
-- BODY
  | line : P4981T1EdgePrescription ((0, -1), (0, 1))
  | left (z : GaussianInt) : P4981T1EdgePrescription
      ((0, 1), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)))
  | right (z : GaussianInt) : P4981T1EdgePrescription
      ((0, -1), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)))
  | unit (z : GaussianInt) : P4981T1EdgePrescription
      ((1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (1, 1 + 2 * z))
  | proper (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
      (j : Fin 3) : P4981T1EdgePrescription (q j.succ, q 0)

end ApollonianSuperharmonic

end
