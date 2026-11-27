/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSMatrixCoefficients

/-!
# The actual GNS map induced by positive-functional domination

For positive functionals psi <= C phi, the identity on the original algebra
extends from the two original pre-GNS seminorms to a bounded map of their
completed GNS Hilbert spaces. The map intertwines the actual representations.
No representation equivalence, normality or vector-state realization is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ ψ : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
variable (hdom : ∀ a : A, 0 ≤ a → ψ a ≤ C • φ a)

include hC hdom in
theorem norm_dominated_preGNS_le (x : φ.PreGNS) :
    ‖ψ.toPreGNS (φ.ofPreGNS x)‖ ≤ Real.sqrt C * ‖x‖ := by
  have hd : (ψ (star (φ.ofPreGNS x) * φ.ofPreGNS x)).re ≤
      C * (φ (star (φ.ofPreGNS x) * φ.ofPreGNS x)).re := by
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      (hdom _ (star_mul_self_nonneg _)).1
  calc
    ‖ψ.toPreGNS (φ.ofPreGNS x)‖ =
        Real.sqrt (ψ (star (φ.ofPreGNS x) * φ.ofPreGNS x)).re := by
      rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS]
    _ ≤ Real.sqrt (C * (φ (star (φ.ofPreGNS x) * φ.ofPreGNS x)).re) :=
      Real.sqrt_le_sqrt hd
    _ = Real.sqrt C * ‖x‖ := by
      rw [Real.sqrt_mul hC, PositiveLinearMap.preGNS_norm_def]

/-- Dominated pre GNS map of type `φ.PreGNS →L[ℂ] ψ.PreGNS`. -/
def dominatedPreGNSMap : φ.PreGNS →L[ℂ] ψ.PreGNS :=
  (ψ.toPreGNS.toLinearMap.comp φ.ofPreGNS.toLinearMap).mkContinuous
    (Real.sqrt C) (norm_dominated_preGNS_le φ ψ C hC hdom)

@[simp] theorem dominatedPreGNSMap_apply (x : φ.PreGNS) :
    dominatedPreGNSMap φ ψ C hC hdom x = ψ.toPreGNS (φ.ofPreGNS x) := rfl

/-- Dominated GNS map of type `φ.GNS →L[ℂ] ψ.GNS`. -/
def dominatedGNSMap : φ.GNS →L[ℂ] ψ.GNS :=
  (dominatedPreGNSMap φ ψ C hC hdom).completion

@[simp] theorem dominatedGNSMap_coe (x : φ.PreGNS) :
    dominatedGNSMap φ ψ C hC hdom (x : φ.GNS) =
      ((ψ.toPreGNS (φ.ofPreGNS x) : ψ.PreGNS) : ψ.GNS) := by
  exact ContinuousLinearMap.completion_apply_coe _ x

theorem dominatedGNSMap_norm_apply_le (x : φ.GNS) :
    ‖dominatedGNSMap φ ψ C hC hdom x‖ ≤ Real.sqrt C * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih x =>
    rw [dominatedGNSMap_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact norm_dominated_preGNS_le φ ψ C hC hdom x

theorem norm_dominatedGNSMap_le : ‖dominatedGNSMap φ ψ C hC hdom‖ ≤ Real.sqrt C :=
  (dominatedGNSMap φ ψ C hC hdom).opNorm_le_bound (Real.sqrt_nonneg C)
    (dominatedGNSMap_norm_apply_le φ ψ C hC hdom)

@[simp] theorem dominatedGNSMap_unitVector :
    dominatedGNSMap φ ψ C hC hdom (gnsUnitVector φ) = gnsUnitVector ψ := by
  change dominatedGNSMap φ ψ C hC hdom ((φ.toPreGNS 1 : φ.PreGNS) : φ.GNS) =
    ((ψ.toPreGNS 1 : ψ.PreGNS) : ψ.GNS)
  rw [dominatedGNSMap_coe, PositiveLinearMap.ofPreGNS_toPreGNS]

theorem dominatedGNSMap_apply_unitVector (a : A) :
    dominatedGNSMap φ ψ C hC hdom (φ.gnsStarAlgHom a (gnsUnitVector φ)) =
      ψ.gnsStarAlgHom a (gnsUnitVector ψ) := by
  simp only [gns_apply_unitVector, dominatedGNSMap_coe,
    PositiveLinearMap.ofPreGNS_toPreGNS]

/-- The genuine bounded map intertwines every algebra element on every
vector of the completion, not only on the cyclic algebraic core. -/
theorem dominatedGNSMap_intertwines (a : A) :
    (dominatedGNSMap φ ψ C hC hdom).comp (φ.gnsStarAlgHom a) =
      (ψ.gnsStarAlgHom a).comp (dominatedGNSMap φ ψ C hC hdom) := by
  apply ContinuousLinearMap.ext
  have he := (gnsUnitVector_dense_orbit φ).equalizer
    ((dominatedGNSMap φ ψ C hC hdom).continuous.comp (φ.gnsStarAlgHom a).continuous)
    ((ψ.gnsStarAlgHom a).continuous.comp (dominatedGNSMap φ ψ C hC hdom).continuous)
    (by
      funext b
      change dominatedGNSMap φ ψ C hC hdom
          (φ.gnsStarAlgHom a (φ.gnsStarAlgHom b (gnsUnitVector φ))) =
        ψ.gnsStarAlgHom a
          (dominatedGNSMap φ ψ C hC hdom (φ.gnsStarAlgHom b (gnsUnitVector φ)))
      rw [← mul_apply_eq_comp, ← map_mul, dominatedGNSMap_apply_unitVector,
        dominatedGNSMap_apply_unitVector, map_mul, mul_apply_eq_comp])
  intro x
  exact congrFun he x

end VacuumBellSeparation
