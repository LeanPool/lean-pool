/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalEventBounds
public import LeanPool.VacuumBellSeparation.FreeField.RegionalEventExtension
public import LeanPool.VacuumBellSeparation.FreeField.CanonicalContractionExhaustion

/-!
# Passage of actual finite Gaussian comparisons to the full local algebras

The remaining finite hypotheses specify upper bounds on the real constructed
Gaussian quantities. Representation, product-reference marginals, positivity,
and canonical exhaustion are all supplied by proved earlier modules.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace ENNReal

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H) (hm : 0 < m)
  (U W : Set (EuclideanSpace ℝ (Fin 3)))

theorem regional_forward_events_of_finite_gaussian (hUW : Disjoint U W)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∃ X : FiniteGaussianPairModel hm V S T,
        sandwichedRenyiQuantity X.density X.reference r ≤ ENNReal.ofReal K)
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ r ≤
      K * ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (r - 1) := by
  apply canonical_forward_event_bound_extends_to_local V hm U W hr _ hE hP
  intro S T hS hT E hE P hP
  obtain ⟨X, hQ⟩ := hfinite S T hS hT
  exact X.forward_event_bound hr hK hQ hE hP
    (commuting_canonicalSourceAlgebras hm V S T
      (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) E hE.1 P hP.1)

theorem regional_reverse_events_of_finite_gaussian (hUW : Disjoint U W)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∃ X : FiniteGaussianPairModel hm V S T,
        sandwichedRenyiQuantity X.reference X.density r ≤ ENNReal.ofReal K)
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ r ≤
      K * (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ (r - 1) := by
  apply canonical_reverse_event_bound_extends_to_local V hm U W hr _ hE hP
  intro S T hS hT E hE P hP
  obtain ⟨X, hQ⟩ := hfinite S T hS hT
  exact X.reverse_event_bound hr hK hQ hE hP
    (commuting_canonicalSourceAlgebras hm V S T
      (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) E hE.1 P hP.1)

theorem regional_eventConstPlus_le_of_finite_gaussian (hUW : Disjoint U W)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∃ X : FiniteGaussianPairModel hm V S T,
        sandwichedRenyiQuantity X.density X.reference r ≤ ENNReal.ofReal K) :
    eventConstPlus (vectorState V.vacuum V.vacuum_norm)
      (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) r ≤ ENNReal.ofReal K := by
  apply eventConstPlus_le_of_effect_bound _ _ _
  intro E hE P hP
  exact regional_forward_events_of_finite_gaussian V hm U W hUW hr hK hfinite hE hP

theorem regional_eventConstMinus_le_of_finite_gaussian (hUW : Disjoint U W)
    {r K : ℝ} (hr : 1 < r) (hK : 0 ≤ K)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∃ X : FiniteGaussianPairModel hm V S T,
        sandwichedRenyiQuantity X.reference X.density r ≤ ENNReal.ofReal K) :
    eventConstMinus (vectorState V.vacuum V.vacuum_norm)
      (timeZeroLocalAlgebra V hm U) (timeZeroLocalAlgebra V hm W) r ≤ ENNReal.ofReal K := by
  apply eventConstMinus_le_of_effect_bound _ _ _ hK
  intro E hE P hP
  exact regional_reverse_events_of_finite_gaussian V hm U W hUW hr hK hfinite hE hP

theorem regional_covariance_le_of_finite_gaussian
    {r C : ℝ} (hr : 2 ≤ r) (hC : 0 ≤ C)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∃ X : FiniteGaussianPairModel hm V S T,
        (sandwichedRenyiQuantity X.density X.reference r ^ (1 / (r - 1)) - 1) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal C)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions (timeZeroLocalAlgebra V hm U))
    (hB : B ∈ saContractions (timeZeroLocalAlgebra V hm W)) :
    ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C := by
  apply canonical_covariance_bound_extends_to_local V hm U W C _ hA hB
  intro S T hS hT A hA B hB
  obtain ⟨X, hQ⟩ := hfinite S T hS hT
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp
    ((X.contraction_covariance_le_renyi hr hA.1 hB.1 hA.2.2 hB.2.2).trans hQ)

end VacuumBellSeparation
