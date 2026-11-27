/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSDominatedTransport
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Bounded Radon--Nikodym operator in the actual GNS commutant

The operator is J*J for the constructed domination map, not supplied as
an assumption. Its positive square root gives an actual representing vector
for every dominated positive functional. No assertion about arbitrary
undominated normal functionals or the GNS image being a VNA is made.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ ψ : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
variable (hdom : ∀ a : A, 0 ≤ a → ψ a ≤ C • φ a)

/-- Continuous linear map for the dominated GNS radon nikodym, of type `φ.GNS →L[ℂ] φ.GNS`. -/
def dominatedGNSRadonNikodym : φ.GNS →L[ℂ] φ.GNS :=
  (dominatedGNSMap φ ψ C hC hdom).adjoint.comp (dominatedGNSMap φ ψ C hC hdom)

theorem dominatedGNSRadonNikodym_nonneg : 0 ≤ dominatedGNSRadonNikodym φ ψ C hC hdom :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self _)

theorem norm_dominatedGNSRadonNikodym_le : ‖dominatedGNSRadonNikodym φ ψ C hC hdom‖ ≤ C := by
  rw [dominatedGNSRadonNikodym, ContinuousLinearMap.norm_adjoint_comp_self]
  have h := norm_dominatedGNSMap_le φ ψ C hC hdom
  nlinarith [Real.sq_sqrt hC, norm_nonneg (dominatedGNSMap φ ψ C hC hdom),
    Real.sqrt_nonneg C]

/-- The actual Radon--Nikodym operator lies in the literal order interval [0,C]. -/
theorem dominatedGNSRadonNikodym_le :
    dominatedGNSRadonNikodym φ ψ C hC hdom ≤
      algebraMap ℝ (φ.GNS →L[ℂ] φ.GNS) C :=
  (CStarAlgebra.norm_le_iff_le_algebraMap _ hC
    (dominatedGNSRadonNikodym_nonneg φ ψ C hC hdom)).mp
      (norm_dominatedGNSRadonNikodym_le φ ψ C hC hdom)

theorem dominatedGNSRadonNikodym_commute (a : A) :
    Commute (dominatedGNSRadonNikodym φ ψ C hC hdom) (φ.gnsStarAlgHom a) := by
  let J := dominatedGNSMap φ ψ C hC hdom
  have hj : J.comp (φ.gnsStarAlgHom a) = (ψ.gnsStarAlgHom a).comp J :=
    dominatedGNSMap_intertwines φ ψ C hC hdom a
  have hja : (φ.gnsStarAlgHom a).comp J.adjoint =
      J.adjoint.comp (ψ.gnsStarAlgHom a) := by
    have h := congrArg ContinuousLinearMap.adjoint
      (dominatedGNSMap_intertwines φ ψ C hC hdom (star a))
    simpa only [ContinuousLinearMap.adjoint_comp, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h
  change (J.adjoint.comp J).comp (φ.gnsStarAlgHom a) =
    (φ.gnsStarAlgHom a).comp (J.adjoint.comp J)
  rw [ContinuousLinearMap.comp_assoc, hj, ← ContinuousLinearMap.comp_assoc,
    ← hja, ContinuousLinearMap.comp_assoc]

theorem dominatedGNSRadonNikodym_expectation (a : A) :
    inner ℂ (gnsUnitVector φ)
      (dominatedGNSRadonNikodym φ ψ C hC hdom
        (φ.gnsStarAlgHom a (gnsUnitVector φ))) = ψ a := by
  change inner ℂ (gnsUnitVector φ)
    ((dominatedGNSMap φ ψ C hC hdom).adjoint
      (dominatedGNSMap φ ψ C hC hdom (φ.gnsStarAlgHom a (gnsUnitVector φ)))) = ψ a
  rw [ContinuousLinearMap.adjoint_inner_right, dominatedGNSMap_unitVector,
    dominatedGNSMap_apply_unitVector, gnsUnitVector_expectation]

/-- Dominated GNS vector defined as `CFC.sqrt (dominatedGNSRadonNikodym φ ψ C hC hdom)
(gnsUnitVector φ)`. -/
def dominatedGNSVector : φ.GNS :=
  CFC.sqrt (dominatedGNSRadonNikodym φ ψ C hC hdom) (gnsUnitVector φ)

/-- The domination hypothesis constructs a vector in the original completed
GNS Hilbert space representing psi on every element of the original algebra. -/
theorem dominatedGNSVector_expectation (a : A) :
    inner ℂ (dominatedGNSVector φ ψ C hC hdom)
      (φ.gnsStarAlgHom a (dominatedGNSVector φ ψ C hC hdom)) = ψ a := by
  let R := dominatedGNSRadonNikodym φ ψ C hC hdom
  let Q := CFC.sqrt R
  have hQ : Q.adjoint = Q := by
    exact (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hQQ : Q * Q = R := CFC.sqrt_mul_sqrt_self R
    (dominatedGNSRadonNikodym_nonneg φ ψ C hC hdom)
  have hcomm : Commute Q (φ.gnsStarAlgHom a) :=
    (dominatedGNSRadonNikodym_commute φ ψ C hC hdom a).cfcₙ_nnreal NNReal.sqrt
  have hmove : φ.gnsStarAlgHom a (Q (gnsUnitVector φ)) =
      Q (φ.gnsStarAlgHom a (gnsUnitVector φ)) := by
    exact congrArg (fun T : φ.GNS →L[ℂ] φ.GNS => T (gnsUnitVector φ)) hcomm.eq.symm
  change inner ℂ (Q (gnsUnitVector φ))
    (φ.gnsStarAlgHom a (Q (gnsUnitVector φ))) = ψ a
  rw [hmove, ← ContinuousLinearMap.adjoint_inner_right, hQ,
    ← mul_apply_eq_comp, hQQ]
  exact dominatedGNSRadonNikodym_expectation φ ψ C hC hdom a

theorem dominatedGNSVector_norm :
    ‖dominatedGNSVector φ ψ C hC hdom‖ = Real.sqrt (ψ 1).re := by
  have h := dominatedGNSVector_expectation φ ψ C hC hdom (1 : A)
  simp only [map_one, one_apply_eq_self] at h
  rw [← h]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

theorem dominatedGNSVector_norm_one (hψ : ψ 1 = 1) :
    ‖dominatedGNSVector φ ψ C hC hdom‖ = 1 := by
  rw [dominatedGNSVector_norm, hψ, Complex.one_re, Real.sqrt_one]

end VacuumBellSeparation
