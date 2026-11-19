/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESymmetricInequalities.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEPermutationGradient
/-!
# Correspondence GUE symmetric inequalities

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFullMeasure_symmetric_square_lsi_compactC1`,
`gueFullMeasure_symmetric_poincare_compactC1`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem gueFullMeasure_symmetric_compact_integral {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x) :
    (∫x, f x ∂gueFullMeasure n)=(∫x, f x ∂gueOrderedMeasure n) := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact gueFullMeasure_symmetric_integral hn f hf hs C (fun x => hC (mem_range_self x))

theorem gueFullMeasure_symmetric_square_lsi_compactC1 {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x) :
    squareEntropy (gueFullMeasure n) f ≤ (2/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueFullMeasure n := by
  have hf2 : HasCompactSupport (fun x => f x^2) := hc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have he := gueFullMeasure_symmetric_compact_integral hn
    (fun x => f x^2*Real.log (f x^2)) (continuous_square_mul_log hf.continuous)
    (compactSupport_square_mul_log hc) (by intros σ x; rw [hs])
  have h2 := gueFullMeasure_symmetric_compact_integral hn (fun x => f x^2) (hf.continuous.pow 2)
    hf2 (by intros σ x; rw [hs])
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgc : HasCompactSupport (fun x => ‖gradient f x‖^2) :=
    ((hc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm)
      (map_zero _)).comp_left (g := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖^2) (by simp)
  have hge := gueFullMeasure_symmetric_compact_integral hn (fun x => ‖gradient f x‖^2)
    (hg.norm.pow 2) hgc (gueSymmetric_gradient_norm_sq n f hf hs)
  unfold squareEntropy
  rw [he, h2, hge]
  exact gueOrderedMeasure_square_lsi hn f hf hc

theorem gueFullMeasure_symmetric_poincare_compactC1 {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x) :
    (∫x, f x^2 ∂gueFullMeasure n)-(∫x, f x ∂gueFullMeasure n)^2 ≤
      (1/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueFullMeasure n := by
  have hf2 : HasCompactSupport (fun x => f x^2) := hc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have h2 := gueFullMeasure_symmetric_compact_integral hn (fun x => f x^2) (hf.continuous.pow 2)
    hf2 (by intros σ x; rw [hs])
  have h1 := gueFullMeasure_symmetric_compact_integral hn f hf.continuous hc hs
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgc : HasCompactSupport (fun x => ‖gradient f x‖^2) :=
    ((hc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm)
      (map_zero _)).comp_left (g := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖^2) (by simp)
  have hge := gueFullMeasure_symmetric_compact_integral hn (fun x => ‖gradient f x‖^2)
    (hg.norm.pow 2) hgc (gueSymmetric_gradient_norm_sq n f hf hs)
  rw [h1, h2, hge]
  exact gueOrderedMeasure_poincare_compactC1 hn f hf hc

end
end GinibrePoincare
