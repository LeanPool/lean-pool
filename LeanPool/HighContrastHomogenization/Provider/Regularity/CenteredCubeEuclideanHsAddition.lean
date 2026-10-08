/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsConstantMatrix

/-!
# High-contrast homogenization: Provider.Regularity.CenteredCubeEuclideanHsAddition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Addition on the physical centered-cube Euclidean Hs carrier

This module packages pointwise addition on the proof-carrying physical
Euclidean `L2` carrier.  The elementary squared triangle estimate gives a
dimension-free bound for the literal centered-cube Gagliardo energy, and hence
addition preserves `MemCenteredCubeEuclideanHs`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- Pointwise addition, packaged as a centered-cube Euclidean `L2` field. -/
@[expose]
noncomputable def centeredCubeEuclideanL2FieldAdd
    (F G : CenteredCubeEuclideanL2Field d m) :
    CenteredCubeEuclideanL2Field d m where
  toField := fun x ↦ F x + G x
  euclideanMemL2 := by
    have h := F.euclideanMemL2.add G.euclideanMemL2
    convert h using 1
    funext x
    simp only [Pi.add_apply, ← HilbertVec.ofVecL_apply]
    exact (HilbertVec.ofVecL d).map_add _ _

@[simp] theorem centeredCubeEuclideanL2FieldAdd_apply
    (F G : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    centeredCubeEuclideanL2FieldAdd F G x = F x + G x :=
  rfl

end

end HighContrast
end HCPolySupport
