/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedWeightedHessian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedWeightedDiagonal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedMixedVariation

/-! Actual full finite-dimensional predictable Hessian correction, including all off-diagonal terms.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The Hessian-type sum `∑ₚ ∑ₗ A p.1 p.2 tₗ (ΔₗB p.1) (ΔₗB p.2)` of a family of processes `B`
over the uniform partition of `[0, t]` into `n + 1` steps, with the matrix weight `A` sampled at
left endpoints. -/
def ginibreBrownianAugmentedWeightedHessian {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (A : ι → ι → ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ p : ι × ι, ∑ l : Fin (n+1), A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
    ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.1 (ginibreUniformBrownianTime t n l)
        ω)*
      (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.2 (ginibreUniformBrownianTime t n l)
          ω))

theorem ginibreBrownianAugmentedWeightedHessian_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (t : ℝ≥0) (A : ι → ι → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i j, StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) (A i j))
    (hc : ∀ i j, ∀ᵐ ω ∂P, Continuous (fun s => A i j s ω))
    (C : ℝ) (hbound : ∀ i j s ω, ‖A i j s ω‖ ≤ C) :
    TendstoInMeasure P (ginibreBrownianAugmentedWeightedHessian B t A) atTop
      (fun ω => ∑ i, ∫ s in (0 : ℝ)..t, A i i s.toNNReal ω) := by
  classical
  let W := fun (p : ι × ι) (n : ℕ) (ω : Ω) => ∑ l : Fin (n+1),
    A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
      ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω -
          B p.1 (ginibreUniformBrownianTime t n l) ω) *
        (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω -
          B p.2 (ginibreUniformBrownianTime t n l) ω))
  let L := fun (p : ι × ι) (ω : Ω) =>
    if p.1=p.2 then ∫ s in (0 : ℝ)..t, A p.1 p.2 s.toNNReal ω else 0
  have hBm (i : ι) (s : ℝ≥0) : Measurable (B i s) :=
    aemeasurable_iff_measurable.mp ((hB i).aemeasurable s)
  have hWm (p : ι × ι) (n : ℕ) : AEStronglyMeasurable (W p n) P := by
    have hEach (l : Fin (n+1)) : AEStronglyMeasurable (fun ω =>
        A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
          ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω -
              B p.1 (ginibreUniformBrownianTime t n l) ω) *
            (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω -
              B p.2 (ginibreUniformBrownianTime t n l) ω))) P :=
      (((hA _ _ _).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le _)).aestronglyMeasurable).mul
        (((hBm _ _).sub (hBm _ _)).mul ((hBm _ _).sub (hBm _ _))).aestronglyMeasurable
    convert! Finset.aestronglyMeasurable_sum Finset.univ (fun l _ => hEach l) using 1
    ext ω
    simp [W]
  have hW (p : ι × ι) : TendstoInMeasure P (W p) atTop (L p) := by
    rcases p with ⟨i, j⟩
    by_cases hij : i=j
    · subst j
      convert! ginibreBrownianAugmentedWeightedDiagonal_tendstoInProbability B P hB hind i t (A i i)
          (hA i i) (hc i i) C (hbound i i) using 1
      · funext n ω
        simp [W, ginibreBrownianAugmentedWeightedDiagonal, pow_two]
      · funext ω
        simp [L]
    · convert! ginibreBrownianAugmentedMixedError_tendstoInProbability B P hB hind i j hij t
        (fun n l => A i j (ginibreUniformBrownianTime t n l))
        (fun n l => (hA _ _ _).measurable) C (fun n l ω => hbound _ _ _ ω) using 1
      all_goals simp [L, hij]
  have h := itoTendstoInMeasure_finset_sum P Finset.univ W L hWm hW
  convert! h using 1
  ext ω
  simp [L, Fintype.sum_prod_type]

end
end GinibrePoincare
