/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototile

/-!
# Nonempty positive-curvature band prototiles

Shared from the nonemptiness arguments in Wesley Pegden’s Apache-2.0 formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic.BandPrototileNonempty

/-- A band prototile of positive curvature contains a lattice cell. -/
theorem positive (D : CircleCoordinates) (V : ProtoTile)
    (hD : 0 < D.1) (hV : BandPrototile D V) : V.cells.Nonempty := by
  classical
  induction hV with
  | line w x hw => simp at hD
  | unit z x anchor => simp
  | @decompose q hq S V hS hcells hfoot hcentroid ih =>
      have facts := ProperBandCurvatureStructure q hq
      have hp : ∃ i : Fin 3, 0 < (q i.succ).1 := by
        by_cases h0 : 0 < (q (0 : Fin 3).succ).1
        · exact ⟨0, h0⟩
        by_cases h1 : 0 < (q (1 : Fin 3).succ).1
        · exact ⟨1, h1⟩
        have n0 := facts.2.1 (0 : Fin 3)
        have n1 := facts.2.1 (1 : Fin 3)
        have z0 : (q (0 : Fin 3).succ).1 = 0 := by omega
        have z1 : (q (1 : Fin 3).succ).1 = 0 := by omega
        exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
      rcases hp with ⟨i, hi⟩
      rcases ih i false hi with ⟨x, hx⟩
      exact ⟨x, (hcells x).mpr ⟨i, false, hx⟩⟩

end ApollonianSuperharmonic.BandPrototileNonempty

end
