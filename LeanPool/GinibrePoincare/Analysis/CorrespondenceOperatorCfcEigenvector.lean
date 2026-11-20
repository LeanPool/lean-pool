/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorCfcEigenvector.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupRealInvariant
/-!
# Correspondence operator cfc eigenvector

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_eigenvalue_mem_spectrum`,
`correspondenceOperator_cfc_eigenvector`.
-/

@[expose] public section
open Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
theorem correspondenceOperator_eigenvalue_mem_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : H →L[ℂ] H) (r : ℝ) (x : H) (hx0 : x ≠ 0) (hx : R x = r • x) :
    r∈spectrum ℝ R := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hz : (u : H→L[ℂ]H) x=0 := by
    rw [hu, Algebra.algebraMap_eq_smul_one]
    simp [hx]
  have he := congrArg (fun A : H→L[ℂ]H=>A x) u.inv_val
  have hxzero : x=0 := by
    change ((↑u⁻¹ : H→L[ℂ]H) ((u : H→L[ℂ]H) x))=x at he
    rw [hz, map_zero] at he
    exact he.symm
  exact hx0 hxzero
/-- Continuous spectral calculus acts on eigenvectors by literal evaluation;
no differentiability assumption on the spectral multiplier is needed. -/
theorem correspondenceOperator_cfc_eigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (r : ℝ) (hr : r ∈ spectrum ℝ R)
    (x : H) (hx : R x = r • x) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    cfc f R x=f r • x := by
  have hall : ∀g : C(spectrum ℝ R, ℝ), cfcHom hR g x=g ⟨r, hr⟩ • x := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const a =>
      change (cfcHom hR (algebraMap ℝ C(spectrum ℝ R, ℝ) a)) x=a • x
      rw [AlgHomClass.commutes]
      rfl
    | id =>
      rw [cfcHom_id hR]
      exact hx
    | star_id =>
      rw [map_star, cfcHom_id hR, hR.star_eq]
      simpa using hx
    | add g h hg hh =>
      rw [map_add, add_apply, hg, hh]
      exact (add_smul _ _ _).symm
    | mul g h hg hh =>
      rw [map_mul]
      change (cfcHom hR g) ((cfcHom hR h) x)=(g*h) ⟨r, hr⟩ • x
      rw [hh, ContinuousLinearMap.map_smul_of_tower, hg, smul_smul]
      simp [mul_comm]
    | frequently g hg =>
      have hEval : Continuous (fun h : C(spectrum ℝ R, ℝ)=>h ⟨r, hr⟩) := continuous_eval_const _
      have hclosed : IsClosed {h : C(spectrum ℝ R, ℝ) | cfcHom hR h x=h ⟨r, hr⟩ • x} :=
        isClosed_eq ((ContinuousLinearMap.apply ℂ H x).continuous.comp (cfcHom_continuous hR))
          (hEval.smul continuous_const)
      exact hclosed.mem_of_frequently_of_tendsto hg tendsto_id
  rw [cfc_apply f R hR hf]
  exact hall _
end
end GinibrePoincare
