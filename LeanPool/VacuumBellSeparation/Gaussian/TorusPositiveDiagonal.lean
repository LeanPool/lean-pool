/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.TorusCoherentExpansion
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-!
# Angular integration of an actual positive coherent form

Scalar torus Parseval is applied to the actual sqrt(A) basis coordinates.
Nonnegative Tonelli and Hilbert-space Parseval then isolate the positive
number-state diagonal. This identity precedes, and does not assume,
construction of an inverse sandwich extension or its trace class.
Torus measure has total mass one; radial/polar conversion is separate.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate ENNReal

/-- Measure-space instance for `UnitAddCircle`. -/
local instance torusPositiveDiagonalMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusPositiveDiagonalProbabilityMeasure : IsProbabilityMeasure
  (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Positive torus coherent diagonal. -/
def positiveTorusCoherentDiagonal {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (a : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) : ℝ :=
  let v := multiExponentialVector (fun j => conj (torusCoherentLabel a θ j))
  (inner ℂ v (A v)).re

theorem positiveTorusCoherentDiagonal_nonneg {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (a : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) :
    0 ≤ positiveTorusCoherentDiagonal A a θ :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _

theorem tsum_torusCoherent_sqrt_basis {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (a : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) :
    (∑' k, ENNReal.ofReal (‖torusCoherentFunction a
      (CFC.sqrt A (multiModeNumberBasis m k)) θ‖ ^ 2)) =
        ENNReal.ofReal (positiveTorusCoherentDiagonal A a θ) := by
  let S := CFC.sqrt A
  let v := multiExponentialVector (fun j => conj (torusCoherentLabel a θ j))
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hn (k : Fin m → ℕ) : ‖inner ℂ v (S (multiModeNumberBasis m k))‖ =
      ‖inner ℂ (multiModeNumberBasis m k) (S v)‖ := by
    rw [← S.adjoint_inner_left, hS.adjoint_eq, norm_inner_symm]
  change (∑' k, ENNReal.ofReal (‖inner ℂ v (S (multiModeNumberBasis m k))‖ ^ 2)) = _
  simp_rw [hn]
  rw [tsum_basis_inner_norm_sq (multiModeNumberBasis m)]
  exact congrArg ENNReal.ofReal (sqrt_norm_sq_eq_diagonal hA v)

/-- Angular integration gives the actual full diagonal series. Neither
finite trace nor existence of a bounded inverse sandwich is assumed. -/
theorem lintegral_positiveTorusCoherentDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (a : Fin m → ℂ) :
    (∫⁻ θ : UnitAddTorus (Fin m), ENNReal.ofReal (positiveTorusCoherentDiagonal A a θ)) =
      ∑' k, ENNReal.ofReal (‖multiCoherentCoefficient a k‖ ^ 2 *
        (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re) := by
  let S := CFC.sqrt A
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  let f : (Fin m → ℕ) → UnitAddTorus (Fin m) → ℝ := fun j θ =>
    ‖torusCoherentFunction a (S (multiModeNumberBasis m j)) θ‖ ^ 2
  have hint (j : Fin m → ℕ) : Integrable (f j) := integrable_torusCoherentFunction_norm_sq _ _
  have heval (j : Fin m → ℕ) :
      (∫⁻ θ, ENNReal.ofReal (f j θ)) =
        ∑' k, ENNReal.ofReal (‖S (multiModeNumberBasis m j) k‖ ^ 2 *
          ‖multiCoherentCoefficient a k‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint j)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    rw [show (∫ θ, f j θ) = ∑' k, ‖S (multiModeNumberBasis m j) k‖ ^ 2 *
      ‖multiCoherentCoefficient a k‖ ^ 2 from integral_torusCoherentFunction_norm_sq _ _]
    exact ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (by simpa only [norm_mul, mul_pow] using
        summable_torusCoherentCoefficients a (S (multiModeNumberBasis m j)))
  have hnorm (j k : Fin m → ℕ) : ‖S (multiModeNumberBasis m j) k‖ =
      ‖inner ℂ (multiModeNumberBasis m j) (S (multiModeNumberBasis m k))‖ := by
    rw [← multiModeNumberBasis_inner, ← S.adjoint_inner_left, hS.adjoint_eq, norm_inner_symm]
  calc
    _ = ∫⁻ θ, ∑' j, ENNReal.ofReal (f j θ) := by
      apply lintegral_congr
      intro θ
      exact (tsum_torusCoherent_sqrt_basis hA a θ).symm
    _ = ∑' j, ∫⁻ θ, ENNReal.ofReal (f j θ) :=
      lintegral_tsum (fun j => (hint j).aemeasurable.ennreal_ofReal)
    _ = ∑' j, ∑' k, ENNReal.ofReal (‖S (multiModeNumberBasis m j) k‖ ^ 2 *
        ‖multiCoherentCoefficient a k‖ ^ 2) := tsum_congr heval
    _ = ∑' k, ∑' j, ENNReal.ofReal (‖S (multiModeNumberBasis m j) k‖ ^ 2 *
        ‖multiCoherentCoefficient a k‖ ^ 2) := tsum_comm
    _ = _ := by
      apply tsum_congr
      intro k
      simp_rw [hnorm, ENNReal.ofReal_mul (sq_nonneg _)]
      rw [ENNReal.tsum_mul_right, tsum_basis_inner_norm_sq (multiModeNumberBasis m),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      change ENNReal.ofReal (‖CFC.sqrt A (multiModeNumberBasis m k)‖ ^ 2 *
        ‖multiCoherentCoefficient a k‖ ^ 2) = _
      have hsq : ‖CFC.sqrt A (multiModeNumberBasis m k)‖ ^ 2 =
          (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re :=
        sqrt_norm_sq_eq_diagonal hA (multiModeNumberBasis m k)
      rw [hsq, mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]

end VacuumBellSeparation.Gaussian
