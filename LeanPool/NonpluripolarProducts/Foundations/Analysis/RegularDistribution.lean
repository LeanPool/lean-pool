/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Regular distributions and distributional Levi operators

These are genuine continuous linear functionals on smooth compactly supported
test functions. Constructing a regular distribution requires an explicit local
integrability proof; no assertion that arbitrary PSH functions are locally
integrable is built into these definitions.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- Positivity is tested against every nonnegative smooth test function. -/
def PositiveDistribution (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ

theorem PositiveDistribution.add {S T : 𝓓'(Ω, ℝ)}
    (hS : PositiveDistribution S) (hT : PositiveDistribution T) :
    PositiveDistribution (S + T) := by
  intro φ hφ
  exact add_nonneg (hS φ hφ) (hT φ hφ)

theorem PositiveDistribution.smul {T : 𝓓'(Ω, ℝ)} (hT : PositiveDistribution T)
    {c : ℝ} (hc : 0 ≤ c) : PositiveDistribution (c • T) := by
  intro φ hφ
  exact mul_nonneg hc (hT φ hφ)

section Regular

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The distribution induced by a real locally integrable density. The proof
argument rules out mathlib's zero fallback for a nonintegrable density. -/
def regularDistribution (μ : Measure E) (u : E → ℝ)
    (_hu : LocallyIntegrableOn u Ω μ) : 𝓓'(Ω, ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ u

theorem regularDistribution_apply (μ : Measure E) (u : E → ℝ)
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) :
    regularDistribution μ u hu φ = ∫ x, φ x * u x ∂μ :=
  TestFunction.integralAgainstBilinCLM_eq_integral hu

theorem regularDistribution_congr_ae {μ : Measure E} {u w : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (heq : u =ᵐ[μ] w) : regularDistribution μ u hu = regularDistribution μ w hw := by
  ext φ
  rw [regularDistribution_apply, regularDistribution_apply]
  exact integral_congr_ae (heq.mono (fun x hx => congrArg (φ x * ·) hx))

/-- A nonnegative locally integrable density defines a positive distribution. -/
theorem positive_regularDistribution {μ : Measure E} {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ u x) :
    PositiveDistribution (regularDistribution μ u hu) := by
  intro φ hφ
  rw [regularDistribution_apply]
  exact integral_nonneg_of_ae (hpos.mono (fun x hx => mul_nonneg (hφ x) hx))

end Regular

section Levi

variable [NormedSpace ℂ E]

/-- The real directional Levi operator on distributions, with the same factor
one quarter as the classical real-Hessian definition. The derivatives have
order parameter `⊤`, so no finite-order fallback can occur. -/
def distributionalLeviCLM (v : E) : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ) :=
  (1 / 4 : ℝ) •
    ((Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v).comp
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v) +
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v)).comp
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v)))

/-- Two distributional derivatives cancel the two integration-by-parts signs. -/
theorem distributionalLeviCLM_apply (T : 𝓓'(Ω, ℝ)) (v : E) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM v T φ = (1 / 4 : ℝ) *
      (T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)) +
       T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v)
         (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Complex.I • v) φ))) := by
  simp [distributionalLeviCLM, Distribution.lineDerivCLM_apply, mul_add]

/-- Nonnegativity of every constant complex-direction Levi distribution.
The equivalence with a canonical PSH representative remains a separate theorem. -/
def HasNonnegativeDistributionalLevi (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ v, PositiveDistribution (distributionalLeviCLM v T)

/-- The Levi operator is quadratic in the direction. -/
theorem distributionalLeviCLM_smul_apply (T : 𝓓'(Ω, ℝ)) (c : ℝ) (v : E) (φ : 𝓓(Ω, ℝ)) :
    distributionalLeviCLM (c • v) T φ = c ^ 2 * distributionalLeviCLM v T φ := by
  have hI : Complex.I • (c • v) = c • (Complex.I • v) := smul_comm _ _ _
  rw [distributionalLeviCLM_apply, distributionalLeviCLM_apply, hI,
    TestFunction.lineDerivCLM_smul, TestFunction.lineDerivCLM_smul]
  simp only [smul_apply, map_smul, smul_eq_mul]
  ring

/-- Unit-direction tests suffice by the quadratic homogeneity of the Levi operator. -/
theorem hasNonnegativeDistributionalLevi_of_unit (T : 𝓓'(Ω, ℝ))
    (hunit : ∀ a : E, ‖a‖ = 1 → ∀ φ : 𝓓(Ω, ℝ),
      (∀ z, 0 ≤ φ z) → 0 ≤ distributionalLeviCLM a T φ) :
    HasNonnegativeDistributionalLevi T := by
  intro v φ hφ
  by_cases hv : v = 0
  · have h0 : v = (0 : ℝ) • v := by rw [hv, smul_zero]
    rw [h0, distributionalLeviCLM_smul_apply]
    simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hva : v = ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) := by
      rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
    have ha : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hvn.ne']
    rw [hva, distributionalLeviCLM_smul_apply]
    exact mul_nonneg (sq_nonneg _) (hunit _ ha φ hφ)

theorem HasNonnegativeDistributionalLevi.add {S T : 𝓓'(Ω, ℝ)}
    (hS : HasNonnegativeDistributionalLevi S)
    (hT : HasNonnegativeDistributionalLevi T) :
    HasNonnegativeDistributionalLevi (S + T) := by
  intro v
  rw [map_add]
  exact (hS v).add (hT v)

theorem HasNonnegativeDistributionalLevi.smul {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) {c : ℝ} (hc : 0 ≤ c) :
    HasNonnegativeDistributionalLevi (c • T) := by
  intro v
  rw [map_smul]
  exact (hT v).smul hc

end Levi

end SGPT.Foundations.Analysis
