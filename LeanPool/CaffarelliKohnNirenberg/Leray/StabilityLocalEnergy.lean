/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Stability Local Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Local `L³` velocity and `L²` gradient bounds supply the joint energy
integrability in (S1) of `def:sws` (`thm:stability`). -/
theorem stability_local_energy_lintegral_lt_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hu : MemLp u 3 (volume.restrict (CKN.spaceTimeSet Ω' J)))
    (hDu : MemLp Du 2 (volume.restrict (CKN.spaceTimeSet Ω' J))) :
    (∫⁻ z in CKN.spaceTimeSet Ω' J,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let μ := volume.restrict (CKN.spaceTimeSet Ω' J)
  have hfinite : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hu2 : MemLp u 2 μ :=
    @MemLp.mono_exponent _ _ _ μ u _ _ 2 3 hfinite hu (by norm_num)
  have huInt : (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hu2.eLpNorm_lt_top
    norm_num at h ⊢
    exact h
  have hDuInt : (∫⁻ z, ‖Du z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hDu.eLpNorm_lt_top
    norm_num at h ⊢
    exact h
  have hmeas : AEMeasurable (fun z => ‖u z‖ₑ ^ (2 : ℝ)) μ :=
    hu2.aestronglyMeasurable.enorm.pow_const (2 : ℝ)
  change (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤
  rw [lintegral_add_left' hmeas]
  exact ENNReal.add_lt_top.mpr ⟨huInt, hDuInt⟩

end CKN
