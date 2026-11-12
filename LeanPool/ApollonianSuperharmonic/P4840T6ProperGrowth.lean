/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: P4840T6ProperGrowth]

/-!
# P4840T6ProperGrowth

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4840T6ProperGrowth (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    1 < (q 0).1 ∧
      (q 0).1 < 2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1 := by
-- BODY
  obtain ⟨hpos, hn, hz⟩ := ProperBandCurvatureStructure q hq
  have h1 : (q 1).1 < (q 0).1 := hq.2 0
  have h2 : (q 2).1 < (q 0).1 := hq.2 1
  have n1 : 0 ≤ (q 1).1 := hn 0
  have n2 : 0 ≤ (q 2).1 := hn 1
  have n3 : 0 ≤ (q 3).1 := hn 2
  constructor
  · by_contra h
    have z1 : (q 1).1 = 0 := by omega
    have z2 : (q 2).1 = 0 := by omega
    have bad := hz 0 1 z1 z2
    norm_num at bad
  · omega

end ApollonianSuperharmonic

end
