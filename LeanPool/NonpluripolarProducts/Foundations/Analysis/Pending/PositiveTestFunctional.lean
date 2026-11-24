/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PositiveDistributionMeasure

/-!
# Measures representing positive linear functionals on test functions

A linear functional on smooth test functions of an open set which is
nonnegative on nonnegative tests is integration against a regular locally
finite measure on the open set. No continuity is assumed: positivity and the
order-cofinality of smooth tests among compactly supported continuous functions
suffice for the M. Riesz extension, and Riesz–Markov–Kakutani gives the measure.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions CompactlySupported

namespace SGPT.Foundations.Analysis.Pending

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ω : Opens E}

theorem exists_positiveLinearMap_of_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ) :
    ∃ Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ,
      ∀ φ : 𝓓(Ω, ℝ), Λ (testFunctionToCompactlySupportedLM Ω φ) = T φ := by
  let i := testFunctionToCompactlySupportedLM Ω
  let e := LinearEquiv.ofInjective i testFunctionToCompactlySupportedLM_injective
  let p : C_c(Ω, ℝ) →ₗ.[ℝ] ℝ := ⟨i.range, T.comp e.symm.toLinearMap⟩
  let s : PointedCone ℝ C_c(Ω, ℝ) :=
    { carrier := {f | ∀ x, 0 ≤ f x}
      zero_mem' := fun _ => le_rfl
      add_mem' := fun hf hg x => add_nonneg (hf x) (hg x)
      smul_mem' := fun c _ hf x => mul_nonneg c.property (hf x) }
  have hp : ∀ x : p.domain, (x : C_c(Ω, ℝ)) ∈ s → 0 ≤ p x := by
    intro x hx
    change 0 ≤ T (e.symm x)
    apply hT
    intro z
    by_cases hz : z ∈ Ω
    · have hi : i (e.symm x) = (x : C_c(Ω, ℝ)) := LinearEquiv.ofInjective_symm_apply i x
      have hxz : 0 ≤ (x : C_c(Ω, ℝ)) ⟨z, hz⟩ := hx ⟨z, hz⟩
      rw [← hi] at hxz
      exact hxz
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((e.symm x).tsupport_subset h))]
  have hcofinal : ∀ y : C_c(Ω, ℝ), ∃ x : p.domain, (x : C_c(Ω, ℝ)) + y ∈ s := by
    intro y
    obtain ⟨φ, _, hφ⟩ := exists_nonneg_testFunction_abs_le y
    refine ⟨⟨i φ, ⟨φ, rfl⟩⟩, ?_⟩
    change ∀ z : Ω, 0 ≤ φ z + y z
    intro z
    have := (neg_le_abs (y z)).trans (hφ z)
    linarith
  obtain ⟨g, hgp, hgn⟩ := riesz_extension s p hp hcofinal
  let Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := g.map_smul
      monotone' := by
        intro f₁ f₂ hf
        have := hgn (f₂ - f₁) (fun x => sub_nonneg.mpr (hf x))
        rw [g.map_sub] at this
        exact sub_nonneg.mp this }
  refine ⟨Λ, fun φ => ?_⟩
  calc
    Λ (i φ) = T (e.symm (e φ)) := hgp (e φ)
    _ = T φ := by rw [e.symm_apply_apply]

variable [MeasurableSpace E] [BorelSpace E]

/-- A positive linear functional on test functions is integration against a
regular locally finite measure on the open set. -/
theorem exists_regular_measure_of_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ) :
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) = T φ := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨Λ, hΛ⟩ := exists_positiveLinearMap_of_testFunctional T hT
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, inferInstance, fun φ => ?_⟩
  exact (RealRMK.integral_rieszMeasure Λ (testFunctionToCompactlySupportedLM Ω φ)).trans (hΛ φ)

end SGPT.Foundations.Analysis.Pending
