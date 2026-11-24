/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedMongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence

/-!
# The bounded mixed product of a smooth tuple is its smooth density measure

The Bedford–Taylor tower is built from weak limits of the smooth mixed density
measures, and every statement about it is a statement about those limits. This
module supplies the base case that anchors the tower: on a relatively compact
open set where the tuple is already smooth, the canonical bounded mixed
measure *is* the smooth density measure. Nothing in the theory can therefore
be vacuous by the canonical measure secretly being zero — on a smooth patch it
is `mixedDensity` against Lebesgue measure.

The proof is the constant approximation: a smooth tuple approximates itself
decreasingly, so the defining testing relation applies to a constant sequence
and identifies the two measures against every test function.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open BedfordTaylor

variable {n : ℕ}

/-- The smooth mixed density measure is finite on compact subsets of its
domain: the density is continuous there, hence bounded on a compact set. -/
theorem smoothMixedMeasure_finiteOnCompacts {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsSmoothMixedPshOn U u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ (U : Set (ComplexModel n))) :
    smoothMixedMeasure U u hu K < ⊤ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_mixedDensity fun i => (hu.component i).1).mono hKU)
  have hbound : ∀ z ∈ K, ENNReal.ofReal (mixedDensity u z) ≤ ENNReal.ofReal C := fun z hz =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz))
  rw [smoothMixedMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (mixedDensity u z)
        ∂(volume.restrict (U : Set (ComplexModel n)))
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂(volume.restrict (U : Set (ComplexModel n))) :=
        setLIntegral_mono' hK.measurableSet hbound
    _ = ENNReal.ofReal C * (volume.restrict (U : Set (ComplexModel n))) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top)

/-- **The canonical bounded mixed Bedford–Taylor measure of a smooth tuple.**
On a relatively compact open set where the tuple is smooth, the canonical
measure restricts to the honest smooth density measure. -/
theorem canonicalMixedBedfordTaylorMeasure_restrict_smooth {Ω U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (hU : RelativelyCompactIn U Ω) (hsm : IsSmoothMixedPshOn U u) :
    (canonicalMixedBedfordTaylorMeasure Ω u hu).restrict (U : Set (ComplexModel n)) =
      smoothMixedMeasure U u hsm := by
  have hUΩ : (U : Set (ComplexModel n)) ⊆ (Ω : Set (ComplexModel n)) := subset_closure.trans hU.2
  have hconst : IsDecreasingMixedApproximation U u (fun _ => u) := hsm.constantApproximation
  have htend := canonicalMixedBedfordTaylorMeasure_tendsto hu hU hconst
  have heq : ∀ φ : 𝓓(U, ℝ),
      ∫ z, φ z ∂(canonicalMixedBedfordTaylorMeasure Ω u hu) =
        ∫ z, φ z ∂(smoothMixedMeasure U u hsm) := by
    intro φ
    -- the approximating sequence is constant, so its smooth measures are one measure
    have h := htend φ φ.continuous φ.hasCompactSupport φ.tsupport_subset
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hres := restrict_eq_of_testFunction_integral_eq (U := U)
    (fun K hK hKU => canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hu hK (hKU.trans hUΩ))
    (fun K hK hKU => smoothMixedMeasure_finiteOnCompacts hsm hK hKU) heq
  rw [hres, smoothMixedMeasure_restrict le_rfl u hsm hsm]

end SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
