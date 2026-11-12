/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: CurvatureOneBandPrototileSingleton]

/-!
# CurvatureOneBandPrototileSingleton

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CurvatureOneBandPrototileSingleton (C : BandCircle) (base : ProtoTile)
    (hcurv : C.1.1.1 = 1) (hbase : BandPrototile C.1.1 base) :
    ∃ x : GaussianInt, base.cells = {x} := by
-- BODY
  have aux : ∀ (c : CircleCoordinates) (T : ProtoTile),
      BandPrototile c T → c.1 = 1 → ∃ x : GaussianInt, T.cells = {x} := by
    intro c T h
    induction h with
    | line w x hw =>
        intro hc
        norm_num at hc
    | unit z x anchor =>
        intro hc
        exact ⟨x, rfl⟩
    | @decompose q hq S T hS hcells hfoot hcentroid ih =>
        intro hc
        have hs := ProperBandCurvatureStructure q hq
        have hz : ∀ i : Fin 3, (q i.succ).1 = 0 := by
          intro i
          have hlt := hq.2 i
          have hn := hs.2.1 i
          omega
        have heq := hs.2.2 (0 : Fin 3) (1 : Fin 3) (hz 0) (hz 1)
        norm_num at heq
  exact aux C.1.1 base hbase hcurv

end ApollonianSuperharmonic

end
