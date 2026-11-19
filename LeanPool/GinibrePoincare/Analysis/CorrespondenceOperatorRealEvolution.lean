/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorRealEvolution.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorEvolution
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupRealInvariant
/-!
# Correspondence operator real evolution

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorEvolution_ofReal`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped Topology NNReal
theorem correspondenceOperatorCfc_im_zero (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (correspondenceOperatorComplexResolvent n hn)))
    (u : GinibreFullComplexL2 n) (hu : ginibreFullComplexIm n u = 0) :
    ginibreFullComplexIm n (resolventRealCfc (correspondenceOperatorComplexResolvent n hn) f u) = 0
        := by
  let M := (ginibreFullComplexIm n).ker
  have hm : IsClosed (M : Set (GinibreFullComplexL2 n)) :=
    (ginibreFullComplexIm n).isClosed_ker
  have hr : ∀ x ∈ M, correspondenceOperatorComplexResolvent n hn x ∈ M := by
    intro x hx
    change ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn x) = 0
    rw [correspondenceOperatorComplexResolvent_im, show ginibreFullComplexIm n x = 0 from hx,
        map_zero]
  exact cfc_real_preserves_closed_submodule _ (correspondenceOperatorComplexResolvent_isSelfAdjoint
      n hn)
    M hm hr f hf u hu

/-- The full diffusion preserves actual real-valued observables. -/
theorem correspondenceOperatorEvolution_im_zero (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : GinibreFullComplexL2 n) (hu : ginibreFullComplexIm n u = 0) :
    ginibreFullComplexIm n (correspondenceOperatorEvolution n hn t u) = 0 :=
  correspondenceOperatorCfc_im_zero n hn _ (resolventEvolutionMultiplier_continuous _).continuousOn
      u hu

/-- The real full diffusion, on the actual symmetric real weighted L² space. -/
def correspondenceOperatorRealEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  (ginibreFullComplexRe n).comp
    (((correspondenceOperatorEvolution n hn t).restrictScalars ℝ).comp (ginibreFullComplexOfReal n))

/-- Complex evolution of an actual real input agrees with its real restriction. -/
theorem correspondenceOperatorEvolution_ofReal (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : GinibreFullValueL2 n) :
    correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u) =
      ginibreFullComplexOfReal n (correspondenceOperatorRealEvolution n hn t u) := by
  rw [← ginibreFullComplex_decomposition n
    (correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u))]
  have hz := correspondenceOperatorEvolution_im_zero n hn t (ginibreFullComplexOfReal n u)
    (ginibreFullComplexIm_ofReal n u)
  have hzv : ginibreFullComplexIm n
      (correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u)) = 0 :=
    hz
  rw [hzv, map_zero, smul_zero, add_zero]
  rfl

end
end GinibrePoincare
