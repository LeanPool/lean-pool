/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactTestCoefficients.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactStoppedSelection
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoCoefficientBounds

/-! Actual local C² gradient and Hessian coefficients of compact adapted configuration paths. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactProcess_scalar_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → Configuration n) (hX : StronglyAdapted F X)
    (K : Set (Configuration n)) (hRange : ∀ t ω, X t ω ∈ K)
    (g : Configuration n → ℝ) (hg : ContinuousOn g K) :
    StronglyAdapted F (fun t ω => g (X t ω)) := by
  intro t
  have hm : @Measurable Ω K (F t) _ (fun ω => ⟨X t ω, hRange t ω⟩) := (hX t).measurable.subtype_mk
  exact hg.domRestrict.comp_stronglyMeasurable hm.stronglyMeasurable

theorem ginibreCompactProcess_test_coefficients {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → Configuration n) (hX : StronglyAdapted F X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ i : Fin n × Fin 2,
        StronglyAdapted F (fun t ω => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)) ∧
        (∀ ω, Continuous (fun t => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i))) ∧
        ∀ t ω, ‖fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)‖ ≤ C) ∧
      ∀ i j : Fin n × Fin 2,
        StronglyAdapted F (fun t ω => itoConfigurationHessianEntry f (X t ω) i j) ∧
        (∀ ω, Continuous (fun t => itoConfigurationHessianEntry f (X t ω) i j)) ∧
        ∀ t ω, ‖itoConfigurationHessianEntry f (X t ω) i j‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ := itoConfigurationCoefficients_exists_bound f U K hU hf hK hKU
  refine ⟨C, hC,?_,?_⟩
  · intro i
    have hg := itoConfigurationGradientEntry_continuousOn f U hU hf i
    exact ⟨ginibreCompactProcess_scalar_stronglyAdapted n F X hX K hRange _ (hg.mono hKU),
      fun ω => hg.comp_continuous (hCont ω) (fun t => hKU (hRange t ω)),
      fun t ω => (hBound _ (hRange t ω)).1 i⟩
  · intro i j
    have hg := itoConfigurationHessianEntry_continuousOn f U hU hf i j
    exact ⟨ginibreCompactProcess_scalar_stronglyAdapted n F X hX K hRange _ (hg.mono hKU),
      fun ω => hg.comp_continuous (hCont ω) (fun t => hKU (hRange t ω)),
      fun t ω => (hBound _ (hRange t ω)).2 i j⟩

end
end GinibrePoincare
