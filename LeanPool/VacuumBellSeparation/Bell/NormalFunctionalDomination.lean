/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSDominatedCommutant
public import LeanPool.VacuumBellSeparation.Bell.GNSNormalDirectedSuprema

/-!
# Positive domination preserves full order normality

The bounded Radon--Nikodym construction gives an actual vector in GNS(phi).
Normality of its pulled-back vector functional proves normality of psi.
Neither faithfulness nor unit normalization nor normality of psi is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isNormalFunctional_of_positive_domination (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ X : M.toStarSubalgebra, 0 ≤ X → ψ X ≤ C • φ X) :
    IsNormalFunctional M ψ := by
  have h := gns_vectorFunctional_isNormal M φ hn (dominatedGNSVector φ ψ C hC hdom)
  simpa only [IsNormalFunctional, dominatedGNSVector_expectation] using h

/-- The same result in the original continuous dual, with positivity proved
from the literal inequality on positive observables. -/
theorem isNormalFunctional_of_dual_domination (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (f : StrongDual ℂ M.toStarSubalgebra)
    (hf : ∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ X : M.toStarSubalgebra, 0 ≤ X → f X ≤ C • φ X) :
    IsNormalFunctional M f := by
  let ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ := {
    toLinearMap := f.toLinearMap
    monotone' := by
      intro X Y hXY
      change f X ≤ f Y
      have h := hf (Y - X) (sub_nonneg.mpr hXY)
      simpa only [map_sub, sub_nonneg] using h }
  exact isNormalFunctional_of_positive_domination M φ ψ hn C hC hdom

end VacuumBellSeparation.Bipartite
