/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.PeriodicTimeEnergy

/-! Time differentiation of the periodic quadratic energy. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Section4

/-- Joint time-space domain with strictly positive time. -/
def classicalPositiveTimeDomain : Set (ℝ × Vec 2) :=
  AVenhance.Infra.Classical.classicalPositiveTimeDomain

theorem ThetaTimeEnergy.thetaTime_unitCube_subset_closedCell :
    AVenhance.unitCube ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem ThetaTimeEnergy.isCompact_closedUnitCell :
    IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) := by
  exact AVenhance.Infra.Classical.TimeEnergy.isCompact_closedUnitCell

theorem thetaTime_integrableOn_unitCube {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.unitCube) := by
  simpa only [IntegrableOn, Measure.restrict_congr_set unitCell_ae_eq_unitCube] using
    (AVenhance.Infra.Classical.continuous_integrableOn_unitCell hf)

theorem thetaTime_measurableSet_unitCube : MeasurableSet AVenhance.unitCube := by
  change MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

/-- Pure time direction in the temperature energy calculation. -/
def ThetaTimeEnergy.timeVector : ℝ × Vec 2 :=
  AVenhance.Infra.Classical.TimeEnergy.timeVector

/-- Time partial derivative obtained from the joint Fréchet derivative of the temperature. -/
def classicalTimePartial (u : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  AVenhance.Infra.Classical.classicalTimePartial u p

theorem ThetaTimeEnergy.partialTime_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain) :
    ContinuousOn (classicalTimePartial u) classicalPositiveTimeDomain := by
  exact AVenhance.Infra.Classical.TimeEnergy.partialTime_continuousOn hu

theorem classicalTimeSection_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => u s x) (classicalTimePartial u (t, x)) t := by
  exact AVenhance.Infra.Classical.classicalTimeSection_hasDerivAt hu ht x

/-- The joint smooth representative's time partial is the ordinary derivative of a fixed spatial
section at every positive time. -/
theorem classicalTimePartial_eq_deriv {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    classicalTimePartial u (t, x) = deriv (fun s => u s x) t := by
  exact AVenhance.Infra.Classical.classicalTimePartial_eq_deriv hu ht x

theorem classicalTimePartial_continuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (fun x => classicalTimePartial u (t, x)) := by
  exact AVenhance.Infra.Classical.classicalTimePartial_continuous_slice hu ht

theorem classicalSmooth_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  exact AVenhance.Infra.Classical.classicalSmooth_slice hu ht

theorem classicalSmooth_slice_nonneg {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  exact AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hu ht

theorem classicalContinuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (u t) := by
  exact AVenhance.Infra.Classical.classicalContinuous_slice hu ht

/-- The unit-cell quadratic energy is differentiable at every positive time, with the expected
pointwise time derivative under the integral. -/
theorem theta_energy_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in AVenhance.unitCube, (u s x) ^ 2)
      (∫ x in AVenhance.unitCube, 2 * u t x * classicalTimePartial u (t, x)) t := by
  simpa only [classicalTimePartial, Measure.restrict_congr_set unitCell_ae_eq_unitCube] using
    (AVenhance.Infra.Classical.unitCell_energy_hasDerivAt hu ht)

/-- The cell energy is continuous down to the initial time for a jointly smooth function on the
closed nonnegative time half-space. -/
theorem theta_energy_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x in AVenhance.unitCube, (u t x) ^ 2) (Set.Icc (0 : ℝ) T) := by
  simpa only [Measure.restrict_congr_set unitCell_ae_eq_unitCube] using
    (AVenhance.Infra.Classical.unitCell_energy_continuousOn hu hT)

end AVenhance.Infra.Section4

end
