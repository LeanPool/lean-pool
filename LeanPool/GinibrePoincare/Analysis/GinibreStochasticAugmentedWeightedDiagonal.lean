/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedWeightedDiagonal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedQuadraticVariation
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConvergenceInMeasure

/-! Actual adapted continuous weighted Brownian quadratic variation converges to its time integral.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The weighted quadratic sum `∑ A tᵢ (B tᵢ₊₁ - B tᵢ)²` over the uniform partition of `[0, t]`
into `n + 1` steps, with the weight process `A` sampled at left endpoints. -/
def ginibreBrownianAugmentedWeightedDiagonal {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n+1), A (ginibreUniformBrownianTime t n i) ω*
    (B (ginibreUniformBrownianTime t n (i.val+1)) ω-B (ginibreUniformBrownianTime t n i) ω)^2

theorem ginibreBrownianAugmentedWeightedDiagonal_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (t : ℝ≥0) (A : ℝ≥0 → Ω → ℝ)
    (hA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) A)
    (hc : ∀ᵐ ω ∂P, Continuous (fun s => A s ω))
    (C : ℝ) (hbound : ∀ s ω, ‖A s ω‖ ≤ C) :
    TendstoInMeasure P (ginibreBrownianAugmentedWeightedDiagonal (B j) t A) atTop
      (fun ω => ∫ s in (0 : ℝ)..t, A s.toNNReal ω) := by
  have := Fintype.ofFinite ι
  let F := fun (n : ℕ) (i : Fin (n+1)) => A (ginibreUniformBrownianTime t n i)
  have hF (n : ℕ) (i : Fin (n+1)) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (ginibreUniformBrownianTime t n i)) _ (F n i) :=
          (hA _).measurable
  let E := fun n => ginibreBrownianAugmentedQuadraticError (B j) t n (F n)
  have hE := ginibreBrownianAugmentedQuadraticError_tendstoInProbability B P hB hind j t F hF C
    (fun n i ω => hbound _ ω)
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) P :=
    (ginibreBrownianAugmentedQuadraticError_memLp_two B P hB hind j t n (F n) (hF n) C
      (fun i ω => hbound _ ω)).aestronglyMeasurable
  let R := fun (n : ℕ) (ω : Ω) => ∑ i : Fin (n+1), F n i ω*((t : ℝ)/((n : ℝ)+1))
  have hRm (n : ℕ) : AEStronglyMeasurable (R n) P := by
    have hEach (i : Fin (n+1)) : AEStronglyMeasurable (fun ω => F n i ω*((t : ℝ)/((n : ℝ)+1))) P :=
      ((hA _).mono ((ginibreBrownianAugmentedFiltration B P hB).le
          _)).aestronglyMeasurable.mul_const _
    convert! Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hEach i) using 1
    ext ω
    simp [R]
  have hR : TendstoInMeasure P R atTop (fun ω => ∫ s in (0 : ℝ)..t, A s.toNNReal ω) := by
    apply tendstoInMeasure_of_tendsto_ae hRm
    filter_upwards [hc] with ω hω
    have h := itoContinuousScalarRiemann_fin_tendsto (fun s : ℝ => A s.toNNReal ω) t
      (hω.comp continuous_real_toNNReal).continuousOn
    simpa only [Real.toNNReal_coe] using h
  have hSum := itoTendstoInMeasure_add P E R (fun _ => 0) _ hEm hRm hE hR
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun ω => zero_add _)) hSum
  intro n
  apply Eventually.of_forall
  intro ω
  dsimp only [E, R, F, ginibreBrownianAugmentedQuadraticError,
      ginibreBrownianAugmentedWeightedDiagonal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end GinibrePoincare
