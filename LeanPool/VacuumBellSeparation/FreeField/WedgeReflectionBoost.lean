/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeReflection
public import LeanPool.VacuumBellSeparation.FreeField.WedgeGaussianAverage

/-! # The actual wedge reflection commutes with real boosts and their Gaussian averages -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate

theorem axisReflection_e₁ : axisReflection e₁ = e₁ := by
  rw [axisReflection_apply, inner_e₁_self]
  module

theorem axisReflection_shellBoost (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    axisReflection (shellBoost m η p) = shellBoost m η (axisReflection p) := by
  simp only [shellBoost, map_add, map_smul, axisReflection_e₁,
    dispersion_linearIsometryEquiv, inner_e₁_axisReflection]

theorem physicalWedgeReflection_boost {m : ℝ} (hm : 0 < m) (η : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm (oneParticleBoost hm η ψ) =
      oneParticleBoost hm η (physicalWedgeReflection hm ψ) := by
  apply Lp.ext
  have h₁ := (measurePreserving_massShell_rotation hm
    axisReflection).quasiMeasurePreserving.ae_eq_comp
    (oneParticleBoostIsometry_ae hm η ψ)
  have h₂ := (measurePreserving_shellBoost hm (-η)).quasiMeasurePreserving.ae_eq_comp
    (physicalWedgeReflection_ae hm ψ)
  filter_upwards [physicalWedgeReflection_ae hm (oneParticleBoost hm η ψ), h₁,
    oneParticleBoostIsometry_ae hm η (physicalWedgeReflection hm ψ), h₂]
    with p hj hU hUj hJ
  simp only [Function.comp_apply] at hU hJ hUj
  rw [hj]
  change conj ((oneParticleBoostIsometry hm η ψ) (axisReflection p)) =
    (oneParticleBoostIsometry hm η (physicalWedgeReflection hm ψ)) p
  rw [hU, hUj, hJ, axisReflection_shellBoost]

theorem physicalWedgeReflection_gaussianBoostAverage {m : ℝ} (hm : 0 < m) (ε : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm (gaussianBoostAverage hm ε ψ) =
      gaussianBoostAverage hm ε (physicalWedgeReflection hm ψ) := by
  rw [gaussianBoostAverage_apply, gaussianBoostAverage_apply,
    ← (physicalWedgeReflection hm).integral_comp_comm (integrable_gaussian_boost hm ε ψ)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => physicalWedgeReflection_boost hm (ε * t) ψ

end VacuumBellSeparation
