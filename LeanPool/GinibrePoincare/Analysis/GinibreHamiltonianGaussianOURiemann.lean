/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOURiemann.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOULimit
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUConvolution
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Ginibre Hamiltonian Gaussian OU riemann

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianOURiemann_isGaussianProcess`,
`ginibreBrownianOURiemann_second_moment`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianOURiemann_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate : ℝ≥0) (m : ℕ) :
    IsGaussianProcess (fun t ω => ginibreBrownianOURiemannSum B rate t m ω) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  let I : Finset ℝ≥0 :=
    (Finset.univ.image (fun i : Fin (m+1) => ginibreUniformBrownianTime t m (i.val+1))) ∪
      (Finset.univ.image (fun i : Fin (m+1) => ginibreUniformBrownianTime t m i.val))
  have hS (i : Fin (m+1)) : ginibreUniformBrownianTime t m (i.val+1) ∈ I :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hP (i : Fin (m+1)) : ginibreUniformBrownianTime t m i.val ∈ I :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let L : (I → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (m+1), ginibreOUStochasticWeight rate t (ginibreUniformTime t m i) •
      (ContinuousLinearMap.proj ⟨_, hS i⟩-ContinuousLinearMap.proj ⟨_, hP i⟩)
  refine ⟨I, L,?_⟩
  intro ω
  simp [L, ginibreBrownianOURiemannSum, Finset.restrict_def, smul_eq_mul]

theorem ginibreBrownianOURiemann_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate t : ℝ≥0) (m : ℕ) :
    (∫ ω, (ginibreBrownianOURiemannSum B rate t m ω)^2 ∂P) =
      (ginibreBrownianOURiemannVariance rate t m : ℝ) := by
  have hL := ginibreBrownianOURiemannSum_hasLaw B P hB rate t m
  have hmean : (∫ ω, ginibreBrownianOURiemannSum B rate t m ω ∂P)=0 := by
    simpa using hL.integral_eq
  have hv : variance (ginibreBrownianOURiemannSum B rate t m) P =
      (ginibreBrownianOURiemannVariance rate t m : ℝ) := by
    simpa [id_def] using hL.variance_eq
  rw [variance_eq_integral hL.aemeasurable, hmean] at hv
  simpa using hv

end
end GinibrePoincare
