/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteGaussianPairModel
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSourceLocality
public import LeanPool.VacuumBellSeparation.Bell.CommutingEffects
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiConsequences

/-!
# Both actual Rényi effect inequalities in the original physical vacuum

The constructed reference is fixed for the two source systems before the
effects or Rényi order are chosen. Its full regional marginals identify the
reference joint effect expectation with the product of physical probabilities.
These estimates retain the true Rényi quantities.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace ENNReal

variable {m : ℝ} {hm : 0 < m} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : FreeFieldVacuum m H} {S T : Submodule ℝ TimeZeroSource}

omit [CompleteSpace H] in
theorem inner_product_real_of_nonneg {A B : H →L[ℂ] H}
    (hA : 0 ≤ A) (v : H) :
    (⟪v, A v⟫_ℂ * ⟪v, B v⟫_ℂ).re = (⟪v, A v⟫_ℂ).re * (⟪v, B v⟫_ℂ).re := by
  have hAi : (⟪v, A v⟫_ℂ).im = 0 := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp
      hA).toLinearMap.isSymmetric.im_inner_self_apply v
  simp only [Complex.mul_re, hAi, zero_mul, sub_zero]

namespace FiniteGaussianPairModel

variable (X : FiniteGaussianPairModel hm V S T)

theorem effect_renyi_bounds {r : ℝ} (hr : 1 < r)
    {A B : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S)
    (hB : B ∈ canonicalSourceAlgebra V hm T)
    (hA₀ : 0 ≤ A) (hA₁ : A ≤ 1) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1)
    (hAB : A * B = B * A) :
    (ENNReal.ofReal (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ r ≤
      sandwichedRenyiQuantity X.density X.reference r *
        ENNReal.ofReal ((⟪V.vacuum, A V.vacuum⟫_ℂ).re *
          (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ (r - 1)) ∧
    (ENNReal.ofReal ((⟪V.vacuum, A V.vacuum⟫_ℂ).re *
        (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ r ≤
      sandwichedRenyiQuantity X.reference X.density r *
        ENNReal.ofReal (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ (r - 1)) := by
  have hAS := canonicalSourceAlgebra_mono V hm (show S ≤ S ⊔ T from le_sup_left) hA
  have hBT := canonicalSourceAlgebra_mono V hm (show T ≤ S ⊔ T from le_sup_right) hB
  have hprod := commuting_effect_product hA₀ hA₁ hB₀ hB₁ hAB
  have hρ := X.vacuum_expectation (A * B) ((canonicalSourceAlgebra V hm (S ⊔ T)).mul_mem hAS hBT)
  have hσ := X.product_expectation A hA B hB
  have hσre : (densityExpectation (multiModeNumberBasis X.modes) X.reference
      (X.toOperator (A * B))).re =
        (⟪V.vacuum, A V.vacuum⟫_ℂ).re * (⟪V.vacuum, B V.vacuum⟫_ℂ).re := by
    rw [hσ, inner_product_real_of_nonneg hA₀]
  constructor
  · have he := faithful_sandwichedRenyi_density_effect_bound (multiModeNumberBasis X.modes)
      X.faithful_density.isPositiveTraceClass X.faithful_reference hr
      (X.map_nonneg _ hprod.1) (X.map_le_one _ hprod.2)
    rwa [← hρ, hσre] at he
  · have he := faithful_sandwichedRenyi_density_effect_bound (multiModeNumberBasis X.modes)
      X.faithful_reference.isPositiveTraceClass X.faithful_density hr
      (X.map_nonneg _ hprod.1) (X.map_le_one _ hprod.2)
    rwa [← hρ, hσre] at he

end FiniteGaussianPairModel

/-- A single actual model gives both bounds for all physical local effects
and all Rényi orders greater than one. No existence premise remains. -/
theorem exists_finite_physical_renyi_effect_bounds
    (hm : 0 < m) (V : FreeFieldVacuum m H) (S T : Submodule ℝ TimeZeroSource)
    {U W : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : Bornology.IsBounded U) (hW : Bornology.IsBounded W) (hUW : Disjoint U W)
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T) :
    ∃ X : FiniteGaussianPairModel hm V S T, ∀ r : ℝ, 1 < r →
      ∀ A ∈ canonicalSourceAlgebra V hm S, ∀ B ∈ canonicalSourceAlgebra V hm T,
        0 ≤ A → A ≤ 1 → 0 ≤ B → B ≤ 1 →
          (ENNReal.ofReal (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ r ≤
            sandwichedRenyiQuantity X.density X.reference r *
              ENNReal.ofReal ((⟪V.vacuum, A V.vacuum⟫_ℂ).re *
                (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ (r - 1)) ∧
          (ENNReal.ofReal ((⟪V.vacuum, A V.vacuum⟫_ℂ).re *
              (⟪V.vacuum, B V.vacuum⟫_ℂ).re) ^ r ≤
            sandwichedRenyiQuantity X.reference X.density r *
              ENNReal.ofReal (⟪V.vacuum, (A * B) V.vacuum⟫_ℂ).re ^ (r - 1)) := by
  obtain ⟨X⟩ := nonempty_finiteGaussianPairModel hm V S T hU hW hUW hS hT
  refine ⟨X, ?_⟩
  intro r hr A hA B hB hA₀ hA₁ hB₀ hB₁
  exact X.effect_renyi_bounds hr hA hB hA₀ hA₁ hB₀ hB₁
    (commuting_canonicalSourceAlgebras hm V S T
      (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) A hA B hB)

end VacuumBellSeparation
