/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialErrorLimits
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleIntegration

/-!
# Quadratic energy on the normalized cylinder

Finite weak derivative data give an integrable quadratic energy for the
Gaussian unique continuation argument.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Finite quadratic weak derivative data give an integrable normalized
field and spatial gradient energy. -/
theorem uc_normalized_energy_integrable
    {ρ : ℝ} {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2) (ucCylinder ρ) volume ∧
    IntegrableOn (fun z => spatialGradientSq v Dv z) (ucCylinder ρ) volume := by
  let S := ucCylinder ρ
  have hvfin : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact (le_add_right le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl))
  have hDvfin : (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    exact (le_add_left le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl))
  have hvInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      S volume :=
    uc_squared_norm_integrable_on_subset S S v hweak.1 hvfin Subset.rfl
  have hDvmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => spatialGradientSq v Dv z)
      (volume.restrict S) := by
    have hcont : Continuous
        (fun u : Fin 3 → Vec3 =>
          ∑ i : Fin 3, ∑ j : Fin 3, (u i j) ^ (2 : ℕ)) := by
      fun_prop
    simpa only [S, ucCylinder, spatialGradientSq] using
      hcont.comp_aestronglyMeasurable hweak.2.1.aestronglyMeasurable
  have hDvlin : (∫⁻ z in S,
      ENNReal.ofReal (spatialGradientSq v Dv z)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S, 9 * ‖Dv z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun z => CKN.ofReal_spatialGradientSq_le_nine_mul v Dv z)
      _ = 9 * ∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' 9 _ (by norm_num)]
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hDvfin
  have hDvInt : IntegrableOn (fun z => spatialGradientSq v Dv z)
      S volume :=
    (lintegral_ofReal_ne_top_iff_integrable hDvmeas
      (Filter.Eventually.of_forall (fun z => by
        dsimp [spatialGradientSq]
        positivity))).mp hDvlin.ne
  exact ⟨hvInt, hDvInt⟩

end ESS
