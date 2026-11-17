/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation

/-!
# Stein identity extension to locally Lipschitz L2 tests

The Stein integration-by-parts identity extends to locally Lipschitz L2 tests.
-/

@[expose] public section

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace Topology ContDiff Matrix.Norms.Frobenius

section

namespace FunctionalInequalities.Probability.Stein


/--
**Letwin A.7 (identity)**: for `μ ≪ volume` with finite second moment, the Stein identity extends to
every locally Lipschitz `f ∈ L²(μ)` with `∇f ∈ L²(μ)`, by `C_c^∞` approximation in the graph norm.
-/
theorem extended_identity_of_ac {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) (hK : IsSteinKernel μ τ)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    (hμ2 :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hSym : SymmetricAE μ τ)
    (hHS : MemLp (fun x => hsNorm (τ x)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgrad : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, ⟪action (τ x) v, gradient f x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hgradId :
    MemLp (fun x => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (gradient f x)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [ContinuousLinearMap.id_apply] using hgrad
  obtain ⟨seq, hs, hval, hder⟩ :=
    exists_smooth_weighted_L2 μ volume hac (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      f hf hf2 hgradId
  have hsval (j : ℕ) : MemLp (seq j) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := (hs j).2.2.1
  have hsgrad (j : ℕ) : MemLp (gradient (seq j)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [ContinuousLinearMap.id_apply] using (hs j).2.2.2
  have hder' :
    Tendsto
      (fun j =>
        eLpNorm (fun x => gradient (seq j) x - gradient f x) 2
          (μ : Measure (EuclideanSpace ℝ (Fin n))))
      atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.id_apply] using hder
  have hlinear :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, v⟫) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [id_eq] using hμ2.inner_const (𝕜 := ℝ) v
  have hleft :
    Tendsto (fun j => ∫ x, ⟪x, v⟫ * seq j x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [Real.inner_apply] using
      L2.tendsto_integral_inner_of_eLpNorm_sub hlinear hf2 hsval hval
  have hτv := action_memLp hK.measurable_entries hHS v
  have hright := L2.tendsto_integral_inner_of_eLpNorm_sub hτv hgrad hsgrad hder'
  have heq (j : ℕ) :
    (∫ x, ⟪x, v⟫ * seq j x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, ⟪action (τ x) v, gradient (seq j) x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    compact_directional_identity μ τ hK hμ2 hSym hHS (seq j) (hs j).1 (hs j).2.1 v
  have hright' :
    Tendsto (fun j => ∫ x, ⟪x, v⟫ * seq j x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, ⟪action (τ x) v, gradient f x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) :=
    hright.congr' (Filter.Eventually.of_forall fun j => (heq j).symm)
  exact tendsto_nhds_unique hleft hright'

/-- **Letwin A.7 (bound)**: `|∫ ⟪x, v⟫ f dμ| ≤ (∫ ‖τ(x) v‖² dμ)^{1/2} (∫ ‖∇f‖² dμ)^{1/2}`. -/
theorem extended_abs_bound_of_ac {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) (hK : IsSteinKernel μ τ)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    (hμ2 :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hSym : SymmetricAE μ τ)
    (hHS : MemLp (fun x => hsNorm (τ x)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgrad : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    |∫ x, ⟪x, v⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| ≤
      Real.sqrt (∫ x, ‖action (τ x) v‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  rw [extended_identity_of_ac μ τ hK hac hμ2 hSym hHS f hf hf2 hgrad v]
  have hτv := action_memLp hK.measurable_entries hHS v
  rw [L2.sqrt_integral_norm_sq_eq hτv, L2.sqrt_integral_norm_sq_eq hgrad]
  exact L2.abs_integral_inner_le hτv hgrad

end FunctionalInequalities.Probability.Stein

end
