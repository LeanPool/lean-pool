/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConfigurationHessianSum.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticFamilyQuadraticSum
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactHessianCorrection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianCoordinates

/-! Exact coordinate expansion of the actual paper-normalized Brownian Hessian sum. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationBrownianNoise_increment_coordinate {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω)
    (s t : ℝ≥0) (p : Fin n × Fin 2) :
    configurationEuclideanLinearEquiv n
      (ginibreConfigurationBrownianNoise n B α ω t -
        ginibreConfigurationBrownianNoise n B α ω s) p =
      Real.sqrt (2*α/(n : ℝ)^2)*(B p t ω-B p s ω) := by
  rcases p with ⟨i, j⟩
  fin_cases j <;> simp [configurationEuclideanLinearEquiv,
    ginibreConfigurationBrownianNoise, Complex.mul_re, Complex.mul_im] <;> ring

/-- The sum of directional Hessians `∑ D²f(X tₗ)(ΔₗW, ΔₗW)` of `f` along `X` in the directions of
the configuration Brownian increments, over the uniform partition of `[0, T]` into `k + 1`
steps. -/
def ginibreConfigurationBrownianHessianSum {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ l : Fin (k+1), itoDirectionalHessian f (X (ginibreUniformBrownianTime T k l) ω)
    (ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (l.val+1))-
      ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k l))

theorem ginibreConfigurationBrownianHessianSum_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianHessianSum n B α X f T k ω =
      (Real.sqrt (2*α/(n : ℝ)^2))^2*
        ginibreBrownianAugmentedWeightedHessian B T
          (fun i j t ω => itoConfigurationHessianEntry f (X t ω) i j) k ω := by
  classical
  unfold ginibreBrownianAugmentedWeightedHessian
  rw [Fintype.sum_prod_type]
  simp only [ginibreConfigurationBrownianHessianSum, itoConfigurationHessian_coordinate_sum,
    ginibreConfigurationBrownianNoise_increment_coordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring
theorem ginibreCompactProcess_configuration_hessian_correction {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0) :
    TendstoInMeasure P (ginibreConfigurationBrownianHessianSum n B α X f T) atTop
      (fun ω => (2*(α : ℝ)/(n : ℝ)^2)*
        ∫ s in (0 : ℝ)..T, configurationLaplacian f (X s.toNNReal ω)) := by
  have h := ginibreCompactProcess_hessian_correction n B P hB hind X hX hCont
    f U K hU hf hK hKU hRange T
  have hs : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2=2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  have hh := ginibre_tendstoInMeasure_const_mul P _ _ (2*(α : ℝ)/(n : ℝ)^2) h
  convert! hh using 1
  funext k ω
  rw [ginibreConfigurationBrownianHessianSum_eq, hs]

/-- The sum over all real coordinates of the squared configuration Brownian increments along the
uniform partition of `[0, T]` into `k + 1` steps. -/
def ginibreConfigurationBrownianCoordinateQuadraticSum {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ p : Fin n × Fin 2, ∑ l : Fin (k+1),
    (configurationEuclideanLinearEquiv n
      (ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (l.val+1))-
        ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k l)) p)^2

theorem ginibreConfigurationBrownianCoordinateQuadraticSum_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ≥0) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianCoordinateQuadraticSum n B α T k ω =
      (2*(α : ℝ)/(n : ℝ)^2)*ginibreBrownianFamilyQuadraticSum B T k ω := by
  simp only [ginibreConfigurationBrownianCoordinateQuadraticSum,
    ginibreConfigurationBrownianNoise_increment_coordinate, mul_pow,
    Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ 2*(α : ℝ)) (sq_nonneg (n : ℝ))),
    ginibreBrownianFamilyQuadraticSum, Finset.mul_sum]

theorem ginibreConfigurationBrownianCoordinateQuadraticSum_tendstoInProbability
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (T : ℝ≥0) :
    TendstoInMeasure P (ginibreConfigurationBrownianCoordinateQuadraticSum n B α T) atTop
      (fun _ => (2*(α : ℝ)/(n : ℝ)^2)*((2*n : ℕ) : ℝ)*(T : ℝ)) := by
  have h := ginibre_tendstoInMeasure_const_mul P _ _ (2*(α : ℝ)/(n : ℝ)^2)
    (ginibreBrownianFamilyQuadraticSum_tendstoInProbability B P hB hind T)
  convert! h using 1
  · funext k ω
    exact ginibreConfigurationBrownianCoordinateQuadraticSum_eq n B α T k ω
  · funext ω
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring

end
end GinibrePoincare
