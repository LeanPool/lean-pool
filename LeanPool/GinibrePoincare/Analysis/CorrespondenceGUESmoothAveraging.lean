/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESmoothAveraging.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEPermutationMeasure
/-!
# Correspondence GUE smooth averaging

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueSmoothAverage_contDiff`, `gueSmoothAverage_compact`,
`gueSmoothAverage_eq_of_symmetric`, `gueSmoothAverage_gradient`.
-/

@[expose] public section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The symmetrization of `f`: the average of `f ∘ guePermute n σ` over all permutations `σ`. -/
def gueSmoothAverage (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ
    :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹*∑σ : Equiv.Perm (Fin n), f (guePermute n σ x)

theorem gueSmoothAverage_symmetric (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    gueSmoothAverage n f (guePermute n τ x)=gueSmoothAverage n f x := by
  unfold gueSmoothAverage
  simp_rw [guePermute_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => f (guePermute n σ x))

theorem gueSmoothAverage_contDiff (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gueSmoothAverage n f) := by
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro σ hσ
  exact hf.comp (guePermuteIsometry n σ).contDiff

theorem gueSmoothAverage_compact (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (gueSmoothAverage n f) := by
  have hsum (s : Finset (Equiv.Perm (Fin n))) : HasCompactSupport (fun x => ∑σ∈s, f (guePermute n σ
      x)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : EuclideanSpace ℝ (Fin n)→ℝ)
      exact HasCompactSupport.zero
    | @insert σ s hσ ih =>
      simp_rw [Finset.sum_insert hσ]
      exact (hf.comp_homeomorph (guePermuteIsometry n σ).toHomeomorph).add ih
  exact (hsum Finset.univ).mul_left

theorem gueSmoothAverage_eq_of_symmetric (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ σ x, f (guePermute n σ x) = f x) : gueSmoothAverage n f=f := by
  funext x
  unfold gueSmoothAverage
  simp_rw [hf]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem guePermute_gradient (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (f ∘ guePermute n σ) x=guePermute n σ.symm (gradient f (guePermute n σ x)) := by
  have hd := (hf.differentiable (by norm_num) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  apply PiLp.ext
  intro i
  rw [gue_gradient_coordinate, hd.fderiv, ContinuousLinearMap.comp_apply]
  have he := congrArg (fderiv ℝ f (guePermute n σ x)) (guePermute_basis n σ i)
  exact he.trans (gue_gradient_coordinate f (guePermute n σ x) (σ.symm i)).symm

theorem gueSmoothAverage_gradient (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (gueSmoothAverage n f) x=
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ •∑σ : Equiv.Perm (Fin n),
        guePermute n σ.symm (gradient f (guePermute n σ x)) := by
  have hd σ := (hf.differentiable (by simp) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) (fun σ hσ => hd σ)).const_mul
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  simp only [Function.comp_apply] at hs
  unfold gradient gueSmoothAverage
  rw [hs.fderiv, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  have hgrad := guePermute_gradient n σ f (hf.of_le (by simp)) x
  unfold gradient at hgrad
  rw [(hd σ).fderiv] at hgrad
  exact hgrad

end
end GinibrePoincare
