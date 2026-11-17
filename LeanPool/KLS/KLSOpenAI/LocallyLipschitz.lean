/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.KLSOpenAI.Bridge
public import LeanPool.KLS.FunctionalInequalities.Poincare.LocalSlope.Gradient

/-!
# The KLS density bound for locally Lipschitz L2 tests

Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 1.1, tests locally Lipschitz
functions in L2. This frontend retains the pinned OpenAI model's density and
coordinate-isotropy assumptions and enlarges its test class to that of the paper.
The gradient energy is an extended nonnegative integral, including infinity.
The original OpenAI model and its smooth compactly supported statement are unchanged.

The bridge is conditional on `FunctionalInequalities.KLS.Conjecture`; this module
does not import a proof of KLS. The closed endpoint is in `KLSOpenAI.Target`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open OAI.LeanBlast.KLS FunctionalInequalities

namespace KLSOpenAI

/-- The Euclidean carrier of the OpenAI model is complete.

`gradient` takes this instance as an argument. Left to instance synthesis, its proof is a
compound term that Lean abstracts into a generated auxiliary theorem whose name depends on
the surrounding module, so the same source can elaborate to different terms in the Palomar
challenge and in its solution. `LocallyLipschitzBound` names this theorem instead. It is not
an instance. -/
theorem completeSpace_space (n : ℕ) : CompleteSpace (Space n) := by
  infer_instance

/-- The direct Poincare bound on the paper's locally Lipschitz L2 test class.
The variance is the ordinary centered-square integral. Its nonnegative extended
value is compared with the squared-gradient energy, which may be infinite. -/
def LocallyLipschitzBound {n : ℕ} (μ : Measure (Space n)) (C : ℝ) : Prop :=
  letI := completeSpace_space n
  ∀ f : Space n → ℝ, LocallyLipschitz f → MemLp f 2 μ →
    ENNReal.ofReal (OAI.LeanBlast.KLS.variance μ f) ≤
      ENNReal.ofReal C * ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂μ

/-- BKL Theorem 1.1 in ordinary density coordinates: one positive constant before
all positive dimensions, isotropic log-concave densities and locally Lipschitz L2 tests. -/
def LocallyLipschitzStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
      LocallyLipschitzBound (densityMeasure ρ) C

/-- For an absolutely continuous law, a smooth-test Poincaré bound with a positive constant
bounds the extended variance of every locally Lipschitz function by its squared-gradient
`lintegral`; infinite energy makes the bound trivial. -/
private theorem locallyLipschitz_of_smooth {n : ℕ} (μ : ProbabilityMeasure (Space n))
    (hac : (μ : Measure (Space n)) ≪ volume) (C : NNReal) (hC : 0 < C)
    (h : Poincare.SmoothTest.Holds (μ : Measure (Space n)) (C : ℝ))
    (f : Space n → ℝ) (hf : LocallyLipschitz f) :
    evariance f (μ : Measure (Space n)) ≤
      (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(μ : Measure (Space n)) := by
  have hlit : Poincare.LocalSlope.Holds μ C :=
    (Poincare.SmoothTest.holds_iff_localSlope μ volume hac C).mp h
  have heq := Energy.LocalSlope.energy_eq_lintegral_gradient μ volume hac f hf
  by_cases htop : (∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2
      ∂(μ : Measure (Space n))) = ⊤
  · have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hC
    rw [htop, ENNReal.mul_top hC0]
    exact le_top
  · have hfin : Energy.LocalSlope.energy μ f ≠ ⊤ := by rwa [heq]
    have hbound := hlit f ⟨hf, hlit.memLp_two hf hfin, hfin⟩
    rwa [heq] at hbound

/-- The covariance-normalized KLS theorem implies the full locally Lipschitz L2
density formulation, with no additional density regularity or finite-energy premise. -/
theorem locallyLipschitz_of_conjecture (hKLS : KLS.Conjecture) :
    LocallyLipschitzStatement := by
  obtain ⟨C, hC⟩ := hKLS
  let D : NNReal := C + 1
  have hD : 0 < D := by simp [D]
  refine ⟨(D : ℝ), by exact_mod_cast hD, ?_⟩
  intro n _ ρ hρ hi f hf hL2
  let μ : ProbabilityMeasure (Space n) := ⟨densityMeasure ρ, hρ.probability⟩
  have hsmooth : Poincare.SmoothTest.Holds (densityMeasure ρ) (D : ℝ) :=
    (smoothTest_holds_of_localSlope_le_covariance hρ hi
      (hC n μ (logConcave hρ) (isotropic hρ hi).memLp_two)).mono (by simp [D])
  have hlocal : evariance f (densityMeasure ρ) ≤
      (D : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂densityMeasure ρ :=
    locallyLipschitz_of_smooth μ (withDensity_absolutelyContinuous volume _) D hD hsmooth f hf
  have : IsProbabilityMeasure (densityMeasure ρ) := hρ.probability
  have hvariance : OAI.LeanBlast.KLS.variance (densityMeasure ρ) f =
      ProbabilityTheory.variance f (densityMeasure ρ) := by
    rw [ProbabilityTheory.variance_eq_integral hL2.aemeasurable]
    rfl
  rw [hvariance, ProbabilityTheory.ofReal_variance hL2, ENNReal.ofReal_coe_nnreal]
  exact hlocal

end KLSOpenAI
