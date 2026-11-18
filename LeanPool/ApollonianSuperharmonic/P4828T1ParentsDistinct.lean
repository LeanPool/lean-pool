/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity

-- [TABLET NODE: P4828T1ParentsDistinct]

/-!
# P4828T1ParentsDistinct

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1ParentsDistinct (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) : Function.Injective (fun j : Fin 3 => q j.succ) := by
-- BODY
  intro i j hij
  change q i.succ = q j.succ at hij
  by_contra hne
  have ht := TangencyCoordinateIdentity q hq.1 i.succ j.succ
    (fun h => hne (Fin.succ_inj.mp h))
  have hn := (ProperBandCurvatureStructure q hq).2.1 i
  rw [hij] at ht hn
  simp at ht
  have hz : (q j.succ).1 = 0 := by nlinarith [sq_nonneg ((q j.succ).1)]
  exact hne ((ProperBandCurvatureStructure q hq).2.2 i j (by simpa [hij] using hz) hz)

end ApollonianSuperharmonic

end
