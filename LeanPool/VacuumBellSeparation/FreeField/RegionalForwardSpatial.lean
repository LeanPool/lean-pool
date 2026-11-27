/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalForwardSpatial
public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalEventBounds
public import LeanPool.VacuumBellSeparation.FreeField.RegionalEventExtension
public import LeanPool.VacuumBellSeparation.FreeField.RegionalForwardContractions

/-!
# Genuine forward estimates on the full physical regional algebras

Uniform actual finite Gaussian estimates are passed through the proved
canonical exhaustion. All local effects, their actual event constant,
and all complex contractions are included. No finite-dimensionality or
approximation premise is imposed on the local algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal InnerProductSpace

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regional_forward_effects_of_finite_ennreal
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3))) (hUW : Disjoint U W)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ E ∈ canonicalSourceAlgebra V hm S, ∀ P ∈ canonicalSourceAlgebra V hm T,
        0 ≤ E → E ≤ 1 → 0 ≤ P → P ≤ 1 →
        ENNReal.ofReal (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ r ≤
          ENNReal.ofReal K * ENNReal.ofReal
            ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (r - 1))
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ r ≤
      K * ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (r - 1) := by
  apply canonical_forward_event_bound_extends_to_local V hm U W hr _ hE hP
  intro S T hS hT E hE P hP
  have hE₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hE.2.1
  have hE₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hE.2.2)
  have hP₀ := ContinuousLinearMap.nonneg_iff_isPositive.mpr hP.2.1
  have hP₁ := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hP.2.2)
  have hcomm := commuting_canonicalSourceAlgebras hm V S T
    (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) E hE.1 P hP.1
  have hprod := commuting_effect_product hE₀ hE₁ hP₀ hP₁ hcomm
  have hw := (ContinuousLinearMap.nonneg_iff_isPositive.mp hprod.1).re_inner_nonneg_right V.vacuum
  have hp := mul_nonneg (hE.2.1.re_inner_nonneg_right V.vacuum)
    (hP.2.1.re_inner_nonneg_right V.vacuum)
  exact real_event_bound_of_ennreal hw hp hK hr
    (hfinite S T hS hT E hE.1 P hP.1 hE₀ hE₁ hP₀ hP₁)

/-- Constants are fixed before the mass, physical representation, regions,
and effects or contractions. The original infinite-dimensional algebras
are used in every conclusion. -/
theorem exists_uniform_regional_forward (n : ℕ) :
    ∃ Sgeo A Q₀ : ℝ, 0 < Sgeo ∧ 0 < A ∧ 0 < Q₀ ∧
      ∀ (m : ℝ) (hm : 0 < m) (s : ℝ), Sgeo ≤ s →
        A / s ^ 2 ≤ 1 / (8 * ((n + 2 : ℕ) : ℝ)) →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H) (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 → Disjoint U W →
          (∀ E ∈ effects (timeZeroLocalAlgebra V hm U), ∀ P ∈ effects (timeZeroLocalAlgebra V hm W),
            (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ ((n + 2 : ℕ) : ℝ) ≤
              Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2)) *
                ((⟪V.vacuum, E V.vacuum⟫_ℂ).re *
                  (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (((n + 2 : ℕ) : ℝ) - 1)) ∧
          eventConstPlus (vectorState V.vacuum V.vacuum_norm)
            (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) ((n + 2 : ℕ) : ℝ) ≤
              ENNReal.ofReal (Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2))) ∧
          (∀ A₀ ∈ timeZeroLocalAlgebra V hm U, ∀ B₀ ∈ timeZeroLocalAlgebra V hm W,
            ‖A₀‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖vacuumComplexCovariance V.vacuum A₀ B₀‖ ≤ Q₀ / s) := by
  obtain ⟨Sgeo, A, Q₀, hSgeo, hA, hQ₀, hfinite⟩ := exists_uniform_finite_physical_forward n
  refine ⟨Sgeo, A, 4 * Q₀, hSgeo, hA, by positivity, ?_⟩
  intro m hm s hs hsmall H _ _ _ V U W hU hW hUW
  have hr : 1 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n + 2 by omega)
  have hfin := hfinite m hm s hs hsmall H V U W hU hW hUW
  have heffects : ∀ E ∈ effects (timeZeroLocalAlgebra V hm U),
      ∀ P ∈ effects (timeZeroLocalAlgebra V hm W),
        (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ ((n + 2 : ℕ) : ℝ) ≤
          Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2)) *
            ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^
              (((n + 2 : ℕ) : ℝ) - 1) := by
    intro E hE P hP
    exact regional_forward_effects_of_finite_ennreal V hm U W hUW hr (Real.exp_nonneg _)
      (fun S T hS hT => (hfin S T hS hT).1) hE hP
  refine ⟨heffects, ?_, ?_⟩
  · exact eventConstPlus_le_of_effect_bound (vectorState V.vacuum V.vacuum_norm)
      (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) heffects
  · intro A₀ hA₀ B₀ hB₀ hAn hBn
    have h := canonical_covariance_bound_extends_to_all_local_contractions V hm U W (Q₀ / s)
      (fun S T hS hT => (hfin S T hS hT).2) hA₀ hB₀ hAn hBn
    simpa only [mul_div_assoc] using h

end VacuumBellSeparation
