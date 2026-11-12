/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile

-- [TABLET NODE: P4638T1EmptyCurvature]

/-!
# P4638T1EmptyCurvature

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4638T1EmptyCurvature (C : CircleCoordinates) (T : ProtoTile)
    (hT : BandPrototile C T) (hempty : T.cells = ∅) : C.1 = 0 := by
-- BODY
  induction hT with
  | line w x hw => rfl
  | unit z x anchor => simp at hempty
  | @decompose q hq S U hS hcells hfoot hcent ih =>
      have children : ∀ i s, (S i s).cells = ∅ := by
        intro i s
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have hu := (hcells a).mpr ⟨i, s, ha⟩
        rw [hempty] at hu
        exact Finset.notMem_empty a hu
      have h0 := ih 0 true (children 0 true)
      have h1 := ih 1 true (children 1 true)
      have bad := (ProperBandCurvatureStructure q hq).2.2 0 1 h0 h1
      exact False.elim (by simp at bad)

end ApollonianSuperharmonic

end
