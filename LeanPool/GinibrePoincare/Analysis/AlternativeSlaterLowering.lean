/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterLowering.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterOrbits

/-!
# Alternative Slater lowering

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `dbarComponent_slaterDeterminant`, `slaterPermutedIndex_totalAntiDegree`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Leibniz expansion of the actual normalized Slater determinant. -/
theorem slaterDeterminant_signed_tensor_sum {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (z : Configuration n) :
    slaterDeterminant hn pq z = (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
      ∑ σ : ParticlePermutation n, permutationSign σ *
        multivariateNormalized n hn (slaterPermutedIndex σ pq).1
          (slaterPermutedIndex σ pq).2 z := by
  unfold slaterDeterminant
  congr 1
  rw [Matrix.det_apply' (M := fun i j : Fin n => normalizedEval n hn (pq.1 i) (pq.2 i) (z j))]
  let f : ParticlePermutation n → ℂ := fun σ => permutationSign σ *
    ∏ j, normalizedEval n hn (pq.1 (σ j)) (pq.2 (σ j)) (z j)
  calc
    _ = ∑ σ, f σ := by simp [f, permutationSign]
    _ = ∑ σ, f ((Equiv.inv (ParticlePermutation n)) σ) :=
      (Equiv.sum_comp (Equiv.inv (ParticlePermutation n)) f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [f, permutationSign, Equiv.Perm.sign_inv, slaterPermutedIndex, multivariateNormalized]

/-- Literal ordinary Wirtinger lowering of a Slater determinant. The derivative
lowers the orbital at the differentiated particle in every permutation term,
with exactly the paper's factor `sqrt(n b)`. -/
theorem dbarComponent_slaterDeterminant {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (j : Fin n) (z : Configuration n) :
    dbarComponent (slaterDeterminant hn pq) j z =
      (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
        ∑ σ : ParticlePermutation n, permutationSign σ *
          ((Real.sqrt (n * (slaterPermutedIndex σ pq).2 j : ℕ) : ℂ) *
            multivariateNormalized n hn (slaterPermutedIndex σ pq).1
              (Function.update (slaterPermutedIndex σ pq).2 j
                ((slaterPermutedIndex σ pq).2 j - 1)) z) := by
  have hd (σ : ParticlePermutation n) : Differentiable ℝ
      (multivariateNormalized n hn (slaterPermutedIndex σ pq).1 (slaterPermutedIndex σ pq).2) :=
    (contDiff_multivariateNormalized_real n hn _ _).differentiable (by norm_num)
  have hs : Differentiable ℝ (fun w : Configuration n =>
      ∑ σ : ParticlePermutation n, permutationSign σ *
        multivariateNormalized n hn (slaterPermutedIndex σ pq).1 (slaterPermutedIndex σ pq).2 w) :=
            by
    apply Differentiable.fun_sum
    intro σ hσ
    exact (hd σ).const_mul _
  rw [show slaterDeterminant hn pq = fun w =>
    (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
      ∑ σ : ParticlePermutation n, permutationSign σ *
        multivariateNormalized n hn (slaterPermutedIndex σ pq).1 (slaterPermutedIndex σ pq).2 w by
    funext w; exact slaterDeterminant_signed_tensor_sum hn pq w]
  rw [dbarComponent_const_mul _ _ hs,
    dbarComponent_finset_sum _ _ (fun σ _ => (hd σ).const_mul _)]
  simp_rw [dbarComponent_const_mul _ _ (hd _) j z, dbarComponent_multivariateNormalized]
  rfl

/-- Permuting labels leaves the Slater total antiholomorphic degree unchanged. -/
theorem slaterPermutedIndex_totalAntiDegree {n : ℕ} (pq : HermiteMultiIndex n)
    (σ : ParticlePermutation n) : totalAntiDegree (slaterPermutedIndex σ pq) = totalAntiDegree pq :=
        by
  change (∑ i, pq.2 (σ.symm i)) = ∑ i, pq.2 i
  exact Equiv.sum_comp σ.symm pq.2

end
end GinibrePoincare

