/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupRealInvariant.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Closed real invariant subspaces of the full spectral evolution -/

@[expose] public section
open Filter
open scoped NNReal Topology ContinuousFunctionalCalculus
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real spectral calculus on a complex Hilbert space, bundled before instantiation. -/
def resolventRealCfc (R : H →L[ℂ] H) (f : ℝ → ℝ) : H →L[ℂ] H := cfc f R

/-- Real continuous functional calculus preserves every closed real invariant subspace. -/
theorem cfc_real_preserves_closed_submodule (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (hRM : ∀ x ∈ M, R x ∈ M) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    ∀ x ∈ M, cfc f R x ∈ M := by
  have hall : ∀ g : C(spectrum ℝ R, ℝ), ∀ x ∈ M, cfcHom hR g x ∈ M := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      intro x hx
      change (cfcHom hR (algebraMap ℝ C(spectrum ℝ R, ℝ) r)) x ∈ M
      rw [AlgHomClass.commutes]
      exact M.smul_mem r hx
    | id =>
      rw [cfcHom_id hR]
      exact hRM
    | star_id =>
      rw [map_star, cfcHom_id hR, hR.star_eq]
      exact hRM
    | add g h hg hh =>
      intro x hx
      rw [map_add, add_apply]
      exact M.add_mem (hg x hx) (hh x hx)
    | mul g h hg hh =>
      intro x hx
      rw [map_mul]
      exact hg _ (hh x hx)
    | frequently g hg =>
      intro x hx
      apply hM.mem_of_frequently_of_tendsto (hg.mono (fun h hh => hh x hx))
      exact ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
        ((cfcHom_continuous hR).tendsto g)
  rw [cfc_apply f R hR hf]
  exact hall _

/-- Every real continuous spectral multiplier preserves actual real observables. -/
theorem ginibreFullCfc_im_zero (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (ginibreFullComplexResolvent n hn)))
    (u : ginibreSymmetricL2 n) (hu : ginibreFullSymmetricIm n u = 0) :
    ginibreFullSymmetricIm n (resolventRealCfc (ginibreFullComplexResolvent n hn) f u) = 0 := by
  let M := (ginibreFullSymmetricIm n).ker
  have hm : IsClosed (M : Set (ginibreSymmetricL2 n)) :=
    (ginibreFullSymmetricIm n).isClosed_ker
  have hr : ∀ x ∈ M, ginibreFullComplexResolvent n hn x ∈ M := by
    intro x hx
    change ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn x) = 0
    rw [ginibreFullComplexResolvent_im, show ginibreFullSymmetricIm n x = 0 from hx, map_zero]
  exact cfc_real_preserves_closed_submodule _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    M hm hr f hf u hu

/-- The full diffusion preserves actual real-valued observables. -/
theorem ginibreFullEvolution_im_zero (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreSymmetricL2 n) (hu : ginibreFullSymmetricIm n u = 0) :
    ginibreFullSymmetricIm n (ginibreFullEvolution n hn t u) = 0 :=
  ginibreFullCfc_im_zero n hn _ (resolventEvolutionMultiplier_continuous _).continuousOn u hu

/-- The real full diffusion, on the actual symmetric real weighted L² space. -/
def ginibreFullRealEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  (ginibreFullSymmetricRe n).comp
    (((ginibreFullEvolution n hn t).restrictScalars ℝ).comp (ginibreFullSymmetricOfReal n))

/-- Complex evolution of an actual real input agrees with its real restriction. -/
theorem ginibreFullEvolution_ofReal (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreFullSymmetricValues n) :
    ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u) =
      ginibreFullSymmetricOfReal n (ginibreFullRealEvolution n hn t u) := by
  apply Subtype.ext
  rw [← ginibreFullComplex_decomposition n
    (ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u)).val]
  have hz := ginibreFullEvolution_im_zero n hn t (ginibreFullSymmetricOfReal n u)
    (ginibreFullSymmetricIm_ofReal n u)
  have hzv : ginibreFullComplexIm n
      (ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u)).val = 0 :=
    congrArg Subtype.val hz
  rw [hzv, map_zero, smul_zero, add_zero]
  rfl

end
end GinibrePoincare
