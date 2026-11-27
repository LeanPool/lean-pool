/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialKernelCoefficients

/-!
# The manuscript alpha, beta coefficient indexing

This is an actual equivalence between all six natural coordinates and
the two full triples. Coefficients, degrees and monomials are reindexed
without truncation, factorial factors or multiplicities.
-/

@[expose] public section

open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

/-- Spatial multi index equivalence. -/
def spatialMultiIndexEquiv : ((Fin 3 → ℕ) × (Fin 3 → ℕ)) ≃ (Fin 6 → ℕ) where
  toFun k := Fin.append k.1 k.2
  invFun k := (fun j => k (Fin.castAdd 3 j), fun j => k (Fin.natAdd 3 j))
  left_inv k := by ext j <;> simp only [Fin.append_left, Fin.append_right]
  right_inv k := Fin.append_castAdd_natAdd

theorem spatialMultiIndex_degree (α β : Fin 3 → ℕ) :
    (∑ j : Fin 6, Fin.append α β j) = (∑ j, α j) + ∑ j, β j := by
  rw [Fin.sum_univ_add (a := 3) (b := 3)]
  simp only [Fin.append_left, Fin.append_right]

theorem spatialMultiIndex_monomial (x y : Fin 3 → ℂ) (α β : Fin 3 → ℕ) :
    (∏ j : Fin 6, Fin.append x y j ^ Fin.append α β j) =
      (∏ j, x j ^ α j) * ∏ j, y j ^ β j := by
  rw [Fin.prod_univ_add (a := 3) (b := 3)]
  simp only [Fin.append_left, Fin.append_right]

theorem spatialSixPair_append (x y : EuclideanSpace ℂ (Fin 3)) :
    spatialSixPair (Fin.append (fun j => x j) (fun j => y j)) = (x, y) := by
  apply Prod.ext
  · ext j
    change Fin.append (fun j => x j) (fun j => y j) (Fin.castAdd 3 j) = x j
    exact Fin.append_left _ _ j
  · ext j
    change Fin.append (fun j => x j) (fun j => y j) (Fin.natAdd 3 j) = y j
    exact Fin.append_right _ _ j

/-- Spatial field multi coefficient obtained from `spatialFieldCoefficient`. -/
noncomputable def spatialFieldMultiCoefficient (μ s R : ℝ)
    (α β : Fin 3 → ℕ) : ℂ := spatialFieldCoefficient μ s R (Fin.append α β)

/-- Spatial momentum multi coefficient obtained from `spatialMomentumCoefficient`. -/
noncomputable def spatialMomentumMultiCoefficient (μ s R : ℝ)
    (α β : Fin 3 → ℕ) : ℂ := spatialMomentumCoefficient μ s R (Fin.append α β)

theorem spatialFieldMultiCoefficient_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (α β : Fin 3 → ℕ) :
    ‖spatialFieldMultiCoefficient μ s R α β‖ ≤
      spatialFieldPolydiscBound μ s R * R⁻¹ ^ ((∑ j, α j) + ∑ j, β j) := by
  simpa only [spatialFieldMultiCoefficient, spatialMultiIndex_degree] using
    spatialFieldCoefficient_norm_le hμ hs hR hsep (Fin.append α β)

theorem spatialMomentumMultiCoefficient_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (α β : Fin 3 → ℕ) :
    ‖spatialMomentumMultiCoefficient μ s R α β‖ ≤
      spatialMomentumPolydiscBound μ s R * R⁻¹ ^ ((∑ j, α j) + ∑ j, β j) := by
  simpa only [spatialMomentumMultiCoefficient, spatialMultiIndex_degree] using
    spatialMomentumCoefficient_norm_le hμ hs hR hsep (Fin.append α β)

theorem spatialFieldMultiCoefficient_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (x y : EuclideanSpace ℂ (Fin 3))
    (hx : ∀ j, ‖x j‖ < R) (hy : ∀ j, ‖y j‖ < R) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialFieldMultiCoefficient μ s R k.1 k.2 * (∏ j, x j ^ k.1 j) * ∏ j, y j ^ k.2 j)
        (spatialPairFieldKernel μ s (x, y)) ∧
      Summable (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
        ‖spatialFieldMultiCoefficient μ s R k.1 k.2 * (∏ j, x j ^ k.1 j) * ∏ j, y j ^ k.2 j‖) := by
  have hz : ∀ j : Fin 6, ‖Fin.append (fun j => x j) (fun j => y j) j‖ < R := by
    intro j
    refine Fin.addCases (motive := fun k : Fin (3 + 3) =>
      ‖Fin.append (fun i => x i) (fun i => y i) k‖ < R)
      (fun i : Fin 3 => ?_) (fun i : Fin 3 => ?_) j
    · simpa only [Fin.append_left] using hx i
    · simpa only [Fin.append_right] using hy i
  have h := spatialFieldCoefficient_expansion hμ hs hR hsep
    (Fin.append (fun j => x j) (fun j => y j)) hz
  constructor
  · simpa only [Function.comp_def, spatialMultiIndexEquiv, Equiv.coe_fn_mk,
      spatialMultiIndex_monomial, ← mul_assoc, spatialFieldMultiCoefficient,
      spatialSixFieldKernel, spatialSixPair_append] using spatialMultiIndexEquiv.hasSum_iff.mpr h.1
  · simpa only [Function.comp_def, spatialMultiIndexEquiv, Equiv.coe_fn_mk,
      spatialMultiIndex_monomial, ← mul_assoc, spatialFieldMultiCoefficient] using
      h.2.comp_injective spatialMultiIndexEquiv.injective

theorem spatialMomentumMultiCoefficient_expansion {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (x y : EuclideanSpace ℂ (Fin 3))
    (hx : ∀ j, ‖x j‖ < R) (hy : ∀ j, ‖y j‖ < R) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialMomentumMultiCoefficient μ s R k.1 k.2 * (∏ j, x j ^ k.1 j) * ∏ j, y j ^ k.2 j)
        (spatialPairMomentumKernel μ s (x, y)) ∧
      Summable (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
        ‖spatialMomentumMultiCoefficient μ s R k.1 k.2 * (∏ j, x j ^ k.1 j) * ∏ j,
          y j ^ k.2 j‖) := by
  have hz : ∀ j : Fin 6, ‖Fin.append (fun j => x j) (fun j => y j) j‖ < R := by
    intro j
    refine Fin.addCases (motive := fun k : Fin (3 + 3) =>
      ‖Fin.append (fun i => x i) (fun i => y i) k‖ < R)
      (fun i : Fin 3 => ?_) (fun i : Fin 3 => ?_) j
    · simpa only [Fin.append_left] using hx i
    · simpa only [Fin.append_right] using hy i
  have h := spatialMomentumCoefficient_expansion hμ hs hR hsep
    (Fin.append (fun j => x j) (fun j => y j)) hz
  constructor
  · simpa only [Function.comp_def, spatialMultiIndexEquiv, Equiv.coe_fn_mk,
      spatialMultiIndex_monomial, ← mul_assoc, spatialMomentumMultiCoefficient,
      spatialSixMomentumKernel, spatialSixPair_append] using
        spatialMultiIndexEquiv.hasSum_iff.mpr h.1
  · simpa only [Function.comp_def, spatialMultiIndexEquiv, Equiv.coe_fn_mk,
      spatialMultiIndex_monomial, ← mul_assoc, spatialMomentumMultiCoefficient] using
      h.2.comp_injective spatialMultiIndexEquiv.injective

end VacuumBellSeparation.Gaussian
