/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalVelocityLp
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds

/-!
# Stability Local Gradient Lp

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The gradient of a suitable solution is square integrable on each local
box, as required when passing the weak-gradient term to the limit. -/
theorem stability_gradient_memLp_two_on_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolution Ω I q u Du p 0)
    (hbox : CKN.localBox Ω I Ω' J) :
    MemLp Du 2 (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
  have hdata := (CKN.isSuitableWeakSolution_iff_integrable.mp hsol).toData
  have hmeas := hdata.aestronglyMeasurable_gradient hbox
  have hlt : (∫⁻ z in CKN.spaceTimeSet Ω' J, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl)
      (hdata.energy_lintegral_lt_top hbox)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hmeas]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

end CKN
