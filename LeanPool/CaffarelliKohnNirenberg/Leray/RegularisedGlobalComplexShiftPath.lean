/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification

/-!
# Time shifts of the global complex mild curve

Every nonnegative start time gives a continuous bounded complex L²
coefficient path for the uniform complete Sobolev continuation equation.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complex global mild curve shifted to a nonnegative start time. -/
@[expose]
def regularisedGlobalComplexShiftPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) :
    C(RegularizedMildTimeInterval T, ComplexVectorL2) :=
  ⟨fun q => complexifyVectorL2
      (regularizedGlobalMildCurve ρ ε hε b₀ hbJ (a + q.1)),
    complexifyVectorL2.continuous.comp
      ((regularizedGlobalMildCurve_continuous ρ ε hε b₀ hbJ).comp
        (continuous_const.add continuous_subtype_val))⟩

/-- Every nonnegative shift has the same global physical L² bound. -/
theorem regularisedGlobalComplexShiftPath_norm_le_initial
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) (ha : 0 ≤ a)
    (q : RegularizedMildTimeInterval T) :
    ‖regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T q‖ ≤ ‖b₀‖ := by
  change ‖complexifyVectorL2
      (regularizedGlobalMildCurve ρ ε hε b₀ hbJ (a + q.1))‖ ≤ ‖b₀‖
  exact (complexifyVectorL2_norm_le _).trans
    (regularizedGlobalMildCurve_norm_le_initial
      ρ ε hε b₀ hbJ (a + q.1) (add_nonneg ha q.2.1))

end CKN.Leray

end
