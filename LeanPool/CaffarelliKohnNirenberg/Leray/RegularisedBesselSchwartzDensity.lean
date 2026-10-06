/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatRealization

/-!
# Schwartz density in complete Bessel spaces

The Bessel/L² isometry transports density of Schwartz fields in L²
to every complete Sobolev order.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Sobolev lifts of Schwartz L² fields are dense in every complete
Bessel potential space. -/
theorem regularisedBesselSchwartzLift_denseRange (s : ℝ) :
    DenseRange (fun φ : 𝓢(L2Vec3, ComplexVec3) =>
      BesselPotentialSpace.ofLp s (φ.toLp 2)) := by
  let e := BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 s 2
  have hSchwartz : DenseRange
      (SchwartzMap.toLpCLM ℝ (E := L2Vec3) ComplexVec3 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (E := L2Vec3)
      (F := ComplexVec3) (μ := volume) ENNReal.ofNat_ne_top
  have h := e.symm.surjective.denseRange.comp hSchwartz
    e.symm.continuous
  convert h using 1
  funext φ
  apply e.injective
  simp only [e, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply,
    BesselPotentialSpace.toLpₗᵢ_apply, BesselPotentialSpace.toLp_ofLp,
    SchwartzMap.toLpCLM_apply]

/-- Lifting a Schwartz L² field into Hˢ still represents a Schwartz
field: the inverse Bessel operator preserves Schwartz decay. -/
theorem regularisedBesselSchwartzLift_hasSchwartzRepresentative
    (s : ℝ) (φ : 𝓢(L2Vec3, ComplexVec3)) :
    ∃ ψ : 𝓢(L2Vec3, ComplexVec3),
      (BesselPotentialSpace.ofLp s (φ.toLp 2)).toDistr =
        (ψ : 𝓢'(L2Vec3, ComplexVec3)) := by
  let weight : L2Vec3 → ℂ := fun ξ =>
    (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)
  have hweight : weight.HasTemperateGrowth := by
    dsimp [weight]
    fun_prop
  refine ⟨SchwartzMap.fourierMultiplierCLM ComplexVec3 weight φ, ?_⟩
  rw [BesselPotentialSpace.toDistr_ofLp,
    Lp.toTemperedDistribution_toLp_eq]
  change TemperedDistribution.fourierMultiplierCLM ComplexVec3 weight
    (φ : 𝓢'(L2Vec3, ComplexVec3)) = _
  exact TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    hweight φ

end CKN.Leray

end
