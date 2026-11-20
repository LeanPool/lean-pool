/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEEndpoints.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEC1H1Membership
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUELSIWitness
/-!
# Correspondence GUE endpoints

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFull_C1_H1_inequalities`, `gueCenterCoordinate_H1`, `gueLSIWitness_H1`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem gueCenterCoordinate_symmetric (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : gueCenterCoordinate n (guePermute n σ x)=gueCenterCoordinate n
        x := by
  rw [gueCenterCoordinate_eq, gueCenterCoordinate_eq]
  congr 1
  exact Equiv.sum_comp σ (fun i => x i)

theorem gueLSIWitness_symmetric (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : gueLSIWitness n (guePermute n σ x)=gueLSIWitness n x := by
  unfold gueLSIWitness
  rw [gueCenterCoordinate_symmetric]

theorem gueFull_C1_H1_inequalities {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x)
    (hv : MemLp f 2 (gueFullMeasure n)) (hg : MemLp (gradient f) 2 (gueFullMeasure n)) :
    Integrable (fun x => f x^2*Real.log (f x^2)) (gueFullMeasure n) ∧
    squareEntropy (gueFullMeasure n) f≤(2/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueFullMeasure n ∧
    (∫x, f x^2 ∂gueFullMeasure n)-(∫x, f x ∂gueFullMeasure n)^2≤
      (1/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueFullMeasure n := by
  have hp := gueSymmetric_C1_pair_mem_H1Completion hn f hf hs hv hg
  obtain ⟨hlog, hLSI⟩ := gueSymmetricH1Completion_square_lsi hn _ hp
  have hPI := gueSymmetricH1Completion_poincare hn _ hp
  have he : ‖hg.toLp (gradient f)‖^2=(∫x, ‖gradient f x‖^2 ∂gueFullMeasure n) := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun y => ‖y‖^2))
  refine ⟨?_,?_,?_⟩
  · exact hlog.congr (hv.coeFn_toLp.fun_comp (fun t => t^2*Real.log (t^2)))
  · rwa [squareEntropy_congr_ae _ hv.coeFn_toLp, he] at hLSI
  · have hsq : (∫x, (hv.toLp f) x^2 ∂gueFullMeasure n)=(∫x, f x^2 ∂gueFullMeasure n) := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx]
    simp only [] at hPI
    rwa [hsq, integral_congr_ae hv.coeFn_toLp, he] at hPI

theorem gueCenterCoordinate_H1 {n : ℕ} (hn : 0 < n) :
    ((gueCenterCoordinate_memLp hn).toLp (gueCenterCoordinate n),
      (gueCenterCoordinate_gradient_memLp hn).toLp (gradient (gueCenterCoordinate
          n)))∈gueSymmetricH1Completion n :=
  gueSymmetric_C1_pair_mem_H1Completion hn _ ((gueCenterCoordinate_contDiff n).of_le (by simp))
    (gueCenterCoordinate_symmetric n) (gueCenterCoordinate_memLp hn)
        (gueCenterCoordinate_gradient_memLp hn)

theorem gueLSIWitness_H1 {n : ℕ} (hn : 0 < n) :
    ((gueLSIWitness_memLp hn).toLp (gueLSIWitness n),
      (gueLSIWitness_gradient_memLp hn).toLp (gradient (gueLSIWitness n)))∈gueSymmetricH1Completion
          n :=
  gueSymmetric_C1_pair_mem_H1Completion hn _ ((gueLSIWitness_contDiff n).of_le (by simp))
    (gueLSIWitness_symmetric n) (gueLSIWitness_memLp hn) (gueLSIWitness_gradient_memLp hn)

end
end GinibrePoincare
