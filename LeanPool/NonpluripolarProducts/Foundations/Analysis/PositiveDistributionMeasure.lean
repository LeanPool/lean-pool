/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.RegularDistribution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Measures representing positive distributions

A positive distribution on an open subset of a finite-dimensional real vector
space is represented by a regular, locally finite Borel measure on that open
subset. Smooth test functions form an order-cofinal subspace of the compactly
supported continuous functions: this follows from a genuine compactly supported
smooth majorant construction. The M. Riesz extension theorem and the
Riesz–Markov–Kakutani theorem then give the representing measure.

The measure lives on the open subset. No local finiteness of its pushforward
across the boundary, and no uniqueness of the representing measure, is asserted.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions CompactlySupported

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- Restriction embeds actual smooth test functions into the continuous
compactly supported functions on the open domain itself. -/
def testFunctionToCompactlySupportedLM (Ω : Opens E) :
    𝓓(Ω, ℝ) →ₗ[ℝ] C_c(Ω, ℝ) where
  toFun φ :=
    ⟨⟨fun x => φ x, φ.continuous.comp continuous_subtype_val⟩, by
      have hK : IsCompact ((Subtype.val : Ω → E) ⁻¹' tsupport φ) :=
        Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
          φ.hasCompactSupport (by
            intro x hx
            exact ⟨⟨x, φ.tsupport_subset hx⟩, rfl⟩)
      exact hK.of_isClosed_subset isClosed_closure
        (closure_minimal (fun x hx => subset_tsupport φ hx)
          (isClosed_closure.preimage continuous_subtype_val))⟩
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

@[simp]
theorem testFunctionToCompactlySupportedLM_apply (φ : 𝓓(Ω, ℝ)) (x : Ω) :
    testFunctionToCompactlySupportedLM Ω φ x = φ x := rfl

theorem testFunctionToCompactlySupportedLM_injective :
    Injective (testFunctionToCompactlySupportedLM Ω) := by
  intro φ ψ h
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ Ω
  · exact congrArg (fun f : C_c(Ω, ℝ) => f ⟨x, hx⟩) h
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.tsupport_subset h))]

variable [FiniteDimensional ℝ E]

/-- A compact subset of the open domain admits a nonnegative smooth test
function which is at least one on that compact set. -/
theorem exists_nonneg_testFunction_one_le_on_compact {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) ∧ ∀ x ∈ K, 1 ≤ φ x := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · subst K
    exact ⟨0, fun _ => le_rfl, by simp⟩
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hgs, hgd, hgr⟩ := hVo.exists_contDiff_support_eq (n := ⊤)
  have hgn : ∀ x, 0 ≤ g x := fun x => (hgr (mem_range_self x)).1
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKn hgd.continuous.continuousOn
  have hga : 0 < g a := by
    refine lt_of_le_of_ne (hgn a) (Ne.symm ?_)
    have : a ∈ support g := hgs.symm ▸ hKV ha
    exact this
  let φ : 𝓓(Ω, ℝ) :=
    ⟨g, hgd, by simpa only [HasCompactSupport, tsupport, hgs] using hVc,
      by simpa only [tsupport, hgs] using hVΩ⟩
  refine ⟨(g a)⁻¹ • φ, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hga.le) (hgn x)
  · intro x hx
    change 1 ≤ (g a)⁻¹ * g x
    calc
      1 = (g a)⁻¹ * g a := (inv_mul_cancel₀ hga.ne').symm
      _ ≤ (g a)⁻¹ * g x := mul_le_mul_of_nonneg_left (hmin hx) (inv_nonneg.mpr hga.le)

/-- Every compactly supported continuous function on the domain has a
nonnegative smooth test function dominating its absolute value. -/
theorem exists_nonneg_testFunction_abs_le (f : C_c(Ω, ℝ)) :
    ∃ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) ∧ ∀ x : Ω, |f x| ≤ φ x := by
  let K : Set E := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hKΩ : K ⊆ Ω := by rintro x ⟨y, _, rfl⟩; exact y.property
  obtain ⟨χ, hχn, hχK⟩ := exists_nonneg_testFunction_one_le_on_compact hK hKΩ
  let M : ℝ := ‖f.toBoundedContinuousFunction‖
  have hMn : 0 ≤ M := norm_nonneg _
  refine ⟨M • χ, fun x => mul_nonneg hMn (hχn x), ?_⟩
  intro x
  change |f x| ≤ M * χ x
  by_cases hx : x ∈ tsupport f
  · calc
      |f x| ≤ M := by
        change ‖f.toBoundedContinuousFunction x‖ ≤ ‖f.toBoundedContinuousFunction‖
        exact f.toBoundedContinuousFunction.norm_coe_le_norm x
      _ ≤ M * χ x := le_mul_of_one_le_right hMn (hχK x ⟨x, hx, rfl⟩)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact mul_nonneg hMn (hχn x)

/-- A nonnegative linear functional on smooth tests extends to compactly supported
continuous functions by the Riesz extension theorem. -/
theorem exists_positiveLinearMap_of_nonneg_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
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

/-- A positive distribution extends to a positive functional on continuous tests. -/
theorem PositiveDistribution.exists_positiveLinearMap {T : 𝓓'(Ω, ℝ)}
    (hT : PositiveDistribution T) :
    ∃ Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ,
      ∀ φ : 𝓓(Ω, ℝ), Λ (testFunctionToCompactlySupportedLM Ω φ) = T φ :=
  exists_positiveLinearMap_of_nonneg_testFunctional T.toLinearMap hT

variable [MeasurableSpace E] [BorelSpace E]

/-- A positive linear functional on test functions is integration against a
regular locally finite measure on the open set. -/
theorem exists_regular_measure_of_nonneg_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ) :
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) = T φ := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨Λ, hΛ⟩ := exists_positiveLinearMap_of_nonneg_testFunctional T hT
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, inferInstance, fun φ => ?_⟩
  exact (RealRMK.integral_rieszMeasure Λ (testFunctionToCompactlySupportedLM Ω φ)).trans (hΛ φ)

/-- A positive distribution is integration against a regular, locally finite
Borel measure on its open domain. This is an existence statement only. -/
theorem PositiveDistribution.exists_regular_measure {T : 𝓓'(Ω, ℝ)}
    (hT : PositiveDistribution T) :
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) = T φ :=
  exists_regular_measure_of_nonneg_testFunctional T.toLinearMap hT

end SGPT.Foundations.Analysis
