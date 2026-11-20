/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticBoundedFactorization.lean.
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

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Bounded factorization through an actual derivative range
A coercive estimate supplies an actual bounded vector-valued inverse on the
closed derivative range, extended to the whole Hilbert space by projection. -/

@[expose] public section
open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- A genuine vector norm estimate gives a bounded linear factorization,
without any completeness or topology assumptions on the test domain. -/
theorem exists_bounded_hilbert_factor
    {𝕜 D H : Type*} [RCLike 𝕜] [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A B : D →ₗ[𝕜] H) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖B x‖ ≤ C * ‖A x‖) :
    ∃ T : H →L[𝕜] H, ‖T‖ ≤ C ∧ ∀ x, T (A x) = B x := by
  let K := A.range.topologicalClosure
  let : CompleteSpace K := A.range.isClosed_topologicalClosure.completeSpace_coe
  let : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  let e : D →ₗ[𝕜] K := (Submodule.inclusion A.range.le_topologicalClosure).comp A.rangeRestrict
  have hd : DenseRange e := by
    have hi : DenseRange (Submodule.inclusion A.range.le_topologicalClosure) := by
      exact (denseRange_inclusion_iff A.range.le_topologicalClosure).mpr (by exact Set.Subset.refl
                                                                               _)
    exact hi.comp A.surjective_rangeRestrict.denseRange (continuous_inclusion
        A.range.le_topologicalClosure)
  have he (x : D) : ‖e x‖ = ‖A x‖ := rfl
  have hb' (x : D) : ‖B x‖ ≤ C * ‖e x‖ := by rw [he]; exact hb x
  let S : K →L[𝕜] H := B.extendOfNorm e
  have hS : ‖S‖ ≤ C := LinearMap.opNorm_extendOfNorm_le hd hC hb'
  let T := S.comp K.orthogonalProjectionOnto
  refine ⟨T, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hS K.orthogonalProjectionOnto_norm_le (norm_nonneg _) hC).trans_eq (mul_one C))
  · intro x
    change S (K.orthogonalProjectionOnto (A x)) = B x
    have hp : K.orthogonalProjectionOnto (A x) = e x := by
      exact K.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
    rw [hp]
    exact LinearMap.extendOfNorm_eq hd ⟨C, hb'⟩ x
end
end GinibrePoincare
