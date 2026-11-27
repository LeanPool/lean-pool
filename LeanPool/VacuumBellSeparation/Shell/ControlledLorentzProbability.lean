/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.SmoothBallProbability
public import LeanPool.VacuumBellSeparation.Shell.LorentzParameterContinuity

/-!
# Smooth parameter probabilities on controlled proper Lorentz families

Both genuine Euclidean operator norms are bounded on a closed parameter
ball. The normalized bump gives a probability supported in this ball.
This constructs a smooth parameter density, without asserting a smooth
Haar density on the Lorentz group.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped Topology

/-- Continuous linear equivalence for the prefixed Lorentz family, of type `Spacetime ≃L[ℝ]
Spacetime`. -/
noncomputable def prefixedLorentzFamily (Λ : Spacetime ≃L[ℝ] Spacetime)
    (s : Fin 6 → ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  (lorentzParameterFamily s).trans Λ

theorem prefixedLorentzFamily_zero (Λ : Spacetime ≃L[ℝ] Spacetime) :
    prefixedLorentzFamily Λ 0 = Λ := by
  unfold prefixedLorentzFamily
  rw [lorentzParameterFamily_zero]
  rfl

theorem continuous_prefixedLorentzFamily_apply (Λ : Spacetime ≃L[ℝ] Spacetime)
    (x : Spacetime) : Continuous (fun s => prefixedLorentzFamily Λ s x) :=
  Λ.continuous.comp (continuous_lorentzParameterFamily_apply x)

theorem prefixedLorentzFamily_isProper {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsProperLorentzMap Λ) (s : Fin 6 → ℝ) :
    IsProperLorentzMap (prefixedLorentzFamily Λ s) :=
  (lorentzParameterFamily_isProper s).trans hΛ

theorem prefixedLorentzFamily_isOrthochronous {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfΛ : IsOrthochronousMap Λ) (s : Fin 6 → ℝ) :
    IsOrthochronousMap (prefixedLorentzFamily Λ s) :=
  IsOrthochronousMap.trans (lorentzParameterFamily_isProper s).1 hΛ
    (lorentzParameterFamily_isOrthochronous s) hfΛ

theorem prefixedLorentzFamily_controlled_ball {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) {R : ℝ}
    (hn : spacetimeEuclideanOperatorNorm Λ < R)
    (hi : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ ρ > 0, ∀ s : Fin 6 → ℝ, ‖s‖ ≤ ρ →
      spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s) < R ∧
      spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s).symm < R := by
  have hc := continuous_spacetimeEuclideanOperatorNorm_family
    (prefixedLorentzFamily Λ) (continuous_prefixedLorentzFamily_apply Λ)
  have hci := continuous_lorentzInverse_operatorNorm_family
    (prefixedLorentzFamily Λ) (fun s => (lorentzParameterFamily_isProper s).1.trans hΛ)
    (continuous_prefixedLorentzFamily_apply Λ)
  have hn0 : spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ 0) < R := by
    rwa [prefixedLorentzFamily_zero]
  have hi0 : spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ 0).symm < R := by
    rwa [prefixedLorentzFamily_zero]
  have hall : ∀ᶠ s in 𝓝 (0 : Fin 6 → ℝ),
      spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s) < R ∧
      spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s).symm < R :=
    (hc.continuousAt.eventually_lt continuousAt_const hn0).and
      (hci.continuousAt.eventually_lt continuousAt_const hi0)
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r / 2, half_pos hr, fun s hs => hh ?_⟩
  simpa only [dist_zero_right] using hs.trans_lt (half_lt_self hr)

theorem smoothBallProbability_ae_norm_lt (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ s ∂smoothBallProbability (Fin 6 → ℝ) ρ hρ, ‖s‖ < ρ := by
  rw [ae_iff]
  simpa only [Metric.ball, dist_zero_right, Set.compl_ofPred] using
    smoothBallProbability_compl_ball (Fin 6 → ℝ) ρ hρ

theorem exists_controlledLorentz_probability {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) {R : ℝ}
    (hn : spacetimeEuclideanOperatorNorm Λ < R)
    (hi : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ∀ᵐ s ∂smoothBallProbability (Fin 6 → ℝ) ρ hρ,
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s) < R ∧
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s).symm < R := by
  obtain ⟨ρ, hρ, hball⟩ := prefixedLorentzFamily_controlled_ball hΛ hn hi
  exact ⟨ρ, hρ, (smoothBallProbability_ae_norm_lt ρ hρ).mono
    (fun s hs => hball s hs.le)⟩

end VacuumBellSeparation
