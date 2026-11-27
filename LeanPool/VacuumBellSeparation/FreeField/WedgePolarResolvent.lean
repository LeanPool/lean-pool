/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgePhysicalResolvent
public import LeanPool.VacuumBellSeparation.FreeField.SourceModularResolvent

/-!
# The original wedge source Gram resolvent in physical and Fourier coordinates

Only the actual polar factorization κ=U sqrt(G) is used. The full
unitary exists by proved source injectivity and density; no inverse of
sqrt(G) as a bounded operator is introduced.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m)

theorem leftWedgeSourceMap_adjoint (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (complexSourceMap hm (leftWedgeTimeZero 0)).adjoint ψ =
      CFC.sqrt (sourceGram hm (leftWedgeTimeZero 0))
        ((leftWedgeSourcePolarUnitary hm 0).symm ψ) := by
  apply ext_inner_right ℂ
  intro z
  rw [(complexSourceMap hm (leftWedgeTimeZero 0)).adjoint_inner_left]
  rw [← leftWedgeSourcePolarUnitary_factorization hm 0 z]
  have hi := (leftWedgeSourcePolarUnitary hm 0).inner_map_map
    ((leftWedgeSourcePolarUnitary hm 0).symm ψ)
    (CFC.sqrt (sourceGram hm (leftWedgeTimeZero 0)) z)
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [hi]
  exact ((CFC.sqrt_nonneg (sourceGram hm (leftWedgeTimeZero 0))).isSelfAdjoint.isSymmetric _ _).symm

theorem leftWedgeSourcePolar_resolvent :
    (leftWedgeSourcePolarUnitary hm 0).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero 0)) =
        sourcePhysicalResolvent hm (leftWedgeTimeZero 0) := by
  apply ContinuousLinearMap.ext
  intro ψ
  change leftWedgeSourcePolarUnitary hm 0
    ((1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero 0)
      ((leftWedgeSourcePolarUnitary hm 0).symm ψ)) =
      (1 / 2 : ℝ) • complexSourceMap hm (leftWedgeTimeZero 0)
        ((complexSourceMap hm (leftWedgeTimeZero 0)).adjoint ψ)
  have hsmul := (leftWedgeSourcePolarUnitary hm 0).toLinearEquiv.toLinearMap.map_smul_of_tower
    (1 / 2 : ℝ) (sourceGram hm (leftWedgeTimeZero 0)
      ((leftWedgeSourcePolarUnitary hm 0).symm ψ))
  change leftWedgeSourcePolarUnitary hm 0
    ((1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero 0)
      ((leftWedgeSourcePolarUnitary hm 0).symm ψ)) =
        (1 / 2 : ℝ) • leftWedgeSourcePolarUnitary hm 0
          (sourceGram hm (leftWedgeTimeZero 0)
            ((leftWedgeSourcePolarUnitary hm 0).symm ψ)) at hsmul
  rw [hsmul, leftWedgeSourceMap_adjoint,
    ← leftWedgeSourcePolarUnitary_factorization]
  congr 2
  exact (congrArg (fun A : ComplexSourceHilbert hm (leftWedgeTimeZero 0) →L[ℂ]
      ComplexSourceHilbert hm (leftWedgeTimeZero 0) =>
      A ((leftWedgeSourcePolarUnitary hm 0).symm ψ))
    (CFC.sqrt_mul_sqrt_self (sourceGram hm (leftWedgeTimeZero 0))
      (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm (leftWedgeTimeZero 0))))).symm

/-- Linear isometry equivalence for the left wedge source Fourier unitary, of type
`ComplexSourceHilbert hm (leftWedgeTimeZero 0) ≃ₗᵢ[ℂ] RapidityL2`. -/
noncomputable def leftWedgeSourceFourierUnitary :
    ComplexSourceHilbert hm (leftWedgeTimeZero 0) ≃ₗᵢ[ℂ] RapidityL2 :=
  (leftWedgeSourcePolarUnitary hm 0).trans (oneParticleRapidityFourier hm)

theorem leftWedgeSourceFourier_resolvent :
    (leftWedgeSourceFourierUnitary hm).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero 0)) =
        exponentialResolvent rapidityMeasure (rapidityFrequencyExponent 1)
          (measurable_rapidityFrequencyExponent 1) := by
  rw [leftWedgeSourceFourierUnitary, LinearIsometryEquiv.conjStarAlgEquiv_trans]
  change (oneParticleRapidityFourier hm).conjStarAlgEquiv
    ((leftWedgeSourcePolarUnitary hm 0).conjStarAlgEquiv
      (sourceModularResolvent hm (leftWedgeTimeZero 0))) = _
  rw [leftWedgeSourcePolar_resolvent]
  apply ContinuousLinearMap.ext
  intro f
  change oneParticleRapidityFourier hm (sourcePhysicalResolvent hm (leftWedgeTimeZero 0)
    ((oneParticleRapidityFourier hm).symm f)) = _
  rw [leftWedgePhysicalResolvent_fourier, LinearIsometryEquiv.apply_symm_apply]

theorem leftWedgeSourceModularResolvent_injective :
    Function.Injective (sourceModularResolvent hm (leftWedgeTimeZero 0)) := by
  have hG : Function.Injective (sourceGram hm (leftWedgeTimeZero 0)) :=
    (complexSourceMap hm (leftWedgeTimeZero 0)).adjoint_comp_self_injective_iff.mpr
      (complexSourceMap_injective_leftWedgeTimeZero hm 0)
  intro x y hxy
  apply hG
  change (1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero 0) x =
    (1 / 2 : ℝ) • sourceGram hm (leftWedgeTimeZero 0) y at hxy
  exact (smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) hxy

end VacuumBellSeparation
