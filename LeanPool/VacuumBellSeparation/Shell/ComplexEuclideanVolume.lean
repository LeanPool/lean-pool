/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixGaussianIntegral
public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCoordinates

/-!
# Complex coordinate volume and genuine real Euclidean volume

The real orthonormal basis consisting of 1 and i in each coordinate
identifies complex Euclidean space with real Euclidean space of twice
the dimension. Its volume preservation, followed by the already proved
complex-plane product coordinate formula, proves the complex toLp/ofLp
volume bridge. The real-only pinned PiLp theorem is used only on real
coordinates.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- Identify complex Euclidean coordinates with their real and imaginary coordinate pairs. -/
noncomputable def complexEuclideanRealIsometry (n : ℕ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
  (Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd (Fin n) (Fin 2)))

theorem complexEuclideanRealIsometry_coordinates (n : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) :
    WithLp.ofLp (complexEuclideanRealIsometry n z) =
      Gaussian.complexRealCoordinates n (WithLp.ofLp z) := by
  funext j
  rcases j with ⟨i, k⟩
  fin_cases k <;> rfl

theorem complexEuclidean_volume_preserving_ofLp (n : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin n → ℂ)) := by
  have h := (Gaussian.complexRealCoordinates_measurePreserving n).symm.comp
    ((PiLp.volume_preserving_ofLp (Fin n × Fin 2)).comp
      (complexEuclideanRealIsometry n).measurePreserving)
  have heq : (fun z : EuclideanSpace ℂ (Fin n) =>
      (Gaussian.complexRealCoordinates n).symm
        (WithLp.ofLp (complexEuclideanRealIsometry n z))) = WithLp.ofLp := by
    funext z
    apply (Gaussian.complexRealCoordinates n).injective
    rw [MeasurableEquiv.apply_symm_apply]
    exact complexEuclideanRealIsometry_coordinates n z
  change MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) =>
    (Gaussian.complexRealCoordinates n).symm
      (WithLp.ofLp (complexEuclideanRealIsometry n z))) at h
  rw [heq] at h
  exact h

theorem complexEuclidean_volume_preserving_toLp (n : ℕ) :
    MeasurePreserving (@WithLp.toLp 2 (Fin n → ℂ)) := by
  have h : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm
      (volume : Measure (EuclideanSpace ℂ (Fin n))) (volume : Measure (Fin n → ℂ)) := by
    simpa only [MeasurableEquiv.coe_toLp_symm] using
      complexEuclidean_volume_preserving_ofLp n
  simpa only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp] using h.symm

theorem shellEuclideanCoordinates_measurePreserving :
    MeasurePreserving shellEuclideanCoordinates :=
  complexEuclidean_volume_preserving_ofLp 3

theorem shellEuclideanCoordinates_symm_measurePreserving :
    MeasurePreserving shellEuclideanCoordinates.symm :=
  complexEuclidean_volume_preserving_toLp 3

end VacuumBellSeparation
