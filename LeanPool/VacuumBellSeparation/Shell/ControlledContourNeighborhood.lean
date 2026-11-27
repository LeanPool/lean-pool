/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.FullContourParameters
public import LeanPool.VacuumBellSeparation.Shell.LorentzParameterContinuity

/-!
# Actual open control of the full contour parameters

A strict bound at the constructed preimage persists on a genuine open
parameter ball, simultaneously for energy and both Euclidean operator
norms. This includes the varying mass coordinate and stays inside the
actual inverse-function chart.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

/-- Full contour Lorentz map of type `Spacetime ≃L[ℝ] Spacetime`. -/
noncomputable def fullContourLorentzMap (Λ : Spacetime ≃L[ℝ] Spacetime)
    (q : ShellContourParameters) : Spacetime ≃L[ℝ] Spacetime :=
  (lorentzParameterFamily (fullContourLorentzParameters q)).trans Λ

theorem fullContourLorentzMap_zero (Λ : Spacetime ≃L[ℝ] Spacetime) :
    fullContourLorentzMap Λ 0 = Λ := by
  have hp : fullContourLorentzParameters 0 = 0 := by ext i; fin_cases i <;> rfl
  unfold fullContourLorentzMap
  rw [hp, lorentzParameterFamily_zero]
  rfl

theorem fullContourLorentzMap_isProper {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsProperLorentzMap Λ) (q : ShellContourParameters) :
    IsProperLorentzMap (fullContourLorentzMap Λ q) :=
  (lorentzParameterFamily_isProper _).trans hΛ

theorem fullContourLorentzMap_isOrthochronous {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfΛ : IsOrthochronousMap Λ) (q : ShellContourParameters) :
    IsOrthochronousMap (fullContourLorentzMap Λ q) :=
  IsOrthochronousMap.trans (lorentzParameterFamily_isProper _).1 hΛ
    (lorentzParameterFamily_isOrthochronous _) hfΛ

theorem continuous_fullContourLorentzMap_apply (Λ : Spacetime ≃L[ℝ] Spacetime)
    (x : Spacetime) : Continuous (fun q => fullContourLorentzMap Λ q x) := by
  have hp : Continuous fullContourLorentzParameters := by
    unfold fullContourLorentzParameters
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun q : ShellContourParameters => q.1 0)
      fun_prop
    · change Continuous (fun q : ShellContourParameters => q.1 1)
      fun_prop
    · change Continuous (fun q : ShellContourParameters => q.1 2)
      fun_prop
    · change Continuous (fun q : ShellContourParameters => q.1 3)
      fun_prop
    · change Continuous (fun q : ShellContourParameters => q.1 4)
      fun_prop
    · change Continuous (fun q : ShellContourParameters => q.2.2 0)
      fun_prop
  exact Λ.continuous.comp ((continuous_lorentzParameterFamily_apply x).comp hp)

theorem controlledContour_parameter_ball {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (m : ℝ) {B θ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (henergy : radialShellEnergy m B 0 < R)
    (hnorm : spacetimeEuclideanOperatorNorm Λ < R)
    (hinv : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ r > 0, ∀ q : ShellContourParameters, ‖q‖ < r →
      q ∈ (fullContourLocalCoordinates m hB hθ).source ∧
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q) < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q).symm < R := by
  have he := (contDiffAt_fullContourEnergy hB m).continuousAt
  have h0 : 0 < fullContourEnergy m B 0 := by
    rw [fullContourEnergy_zero]
    exact radialShellEnergy_pos hB m
  have hE : fullContourEnergy m B 0 < R := by
    rwa [fullContourEnergy_zero]
  have hne := continuous_spacetimeEuclideanOperatorNorm_family
    (fullContourLorentzMap Λ) (continuous_fullContourLorentzMap_apply Λ)
  have hni := continuous_lorentzInverse_operatorNorm_family
    (fullContourLorentzMap Λ)
    (fun q => (lorentzParameterFamily_isProper _).1.trans hΛ)
    (continuous_fullContourLorentzMap_apply Λ)
  have hn0 : spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ 0) < R := by
    rwa [fullContourLorentzMap_zero]
  have hi0 : spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ 0).symm < R := by
    rwa [fullContourLorentzMap_zero]
  have hs := (fullContourLocalCoordinates m hB hθ).open_source.mem_nhds
    (zero_mem_fullContourLocalCoordinates m hB hθ)
  have hall : ∀ᶠ q : ShellContourParameters in 𝓝 0,
      q ∈ (fullContourLocalCoordinates m hB hθ).source ∧
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q) < R ∧
      spacetimeEuclideanOperatorNorm (fullContourLorentzMap Λ q).symm < R := by
    filter_upwards [hs, continuousAt_const.eventually_lt he h0,
      he.eventually_lt continuousAt_const hE,
      hne.continuousAt.eventually_lt continuousAt_const hn0,
      hni.continuousAt.eventually_lt continuousAt_const hi0] with q hq he0 heR hn hi
    exact ⟨hq, he0, heR, hn, hi⟩
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨r, hr, fun q hq => hh (by simpa only [dist_zero_right] using hq)⟩

end VacuumBellSeparation
