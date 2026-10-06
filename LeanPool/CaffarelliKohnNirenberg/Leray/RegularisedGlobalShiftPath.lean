/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild

/-!
# Finite shifts of the global real mild curve

The global mild trajectory restricts continuously to every finite
interval after a nonnegative start time.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The global real mild curve viewed from a later start time. -/
@[expose]
def regularizedGlobalMildCurve_shiftPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) : C(RegularizedMildTimeInterval T, RealVectorL2) :=
  ⟨fun q => regularizedGlobalMildCurve ρ ε hε b₀ hbJ (a + q.1),
    (regularizedGlobalMildCurve_continuous ρ ε hε b₀ hbJ).comp
      (continuous_const.add continuous_subtype_val)⟩

end CKN.Leray

end
