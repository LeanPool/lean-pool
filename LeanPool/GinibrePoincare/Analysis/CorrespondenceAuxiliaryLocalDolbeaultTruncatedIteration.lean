/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultTruncatedIteration.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultTruncation

/-!
# Correspondence auxiliary local Dolbeault truncated iteration

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `truncatedDolbeaultPrimitive_smooth_compact`, `dolbeaultPrimitiveLp_ae`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The composition along a list of coordinates of the truncated operators
`dolbeaultTruncatedCutoff j R (planarDbar (χ j))`, applied to `a`. -/
def truncatedDolbeaultBoundaryComposition {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ) :
    List (Fin n) → (Configuration n → ℂ) → Configuration n → ℂ
  | [], a => a
  | j::l, a => dolbeaultTruncatedCutoff j R (planarDbar (χ j))
      (truncatedDolbeaultBoundaryComposition R χ l a)

/-- The truncated Dolbeault primitive along a list of coordinates: for `j :: l`, the primitive
for `l` plus `dolbeaultTruncatedCutoff j R (χ j)` of the truncated boundary composition along `l`
applied to `α j`. -/
def truncatedDolbeaultPrimitive {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ)
    (α : Fin n → Configuration n → ℂ) : List (Fin n) → Configuration n → ℂ
  | [] => 0
  | j::l => truncatedDolbeaultPrimitive R χ α l + dolbeaultTruncatedCutoff j R (χ j)
      (truncatedDolbeaultBoundaryComposition R χ l (α j))

theorem truncatedDolbeaultBoundaryComposition_smooth_compact {n : ℕ} (R : ℝ)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (l : List (Fin n)) (a : Configuration n → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ContDiff ℝ ∞ (truncatedDolbeaultBoundaryComposition R χ l a) ∧
      HasCompactSupport (truncatedDolbeaultBoundaryComposition R χ l a) := by
  induction l with
  | nil => exact ⟨ha, hc⟩
  | cons j l ih =>
    exact dolbeaultTruncatedCutoff_smooth_compact j R _ _
      (planarDbar_contDiff_infty _ (hχ j)) ih.1 ih.2

theorem truncatedDolbeaultPrimitive_smooth_compact {n : ℕ} (R : ℝ)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (hc : ∀ j, HasCompactSupport (α j)) (l : List (Fin n)) :
    ContDiff ℝ ∞ (truncatedDolbeaultPrimitive R χ α l) ∧
      HasCompactSupport (truncatedDolbeaultPrimitive R χ α l) := by
  induction l with
  | nil => exact ⟨contDiff_const, by simp [HasCompactSupport, truncatedDolbeaultPrimitive]⟩
  | cons j l ih =>
    have hb := truncatedDolbeaultBoundaryComposition_smooth_compact R χ hχ l _ (hα j) (hc j)
    have ht := dolbeaultTruncatedCutoff_smooth_compact j R _ _ (hχ j) hb.1 hb.2
    exact ⟨ih.1.add ht.1, ih.2.add ht.2⟩

theorem dolbeaultBoundaryLpComposition_ae {n : ℕ} (R : ℝ)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hcχ : ∀ j, HasCompactSupport (χ j)) (l : List (Fin n))
    (a : Configuration n → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    (dolbeaultBoundaryLpComposition R χ hχ hcχ l
      ((ha.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc).toLp a)
        : Configuration n → ℂ) =ᵐ[volume] truncatedDolbeaultBoundaryComposition R χ l a := by
  induction l with
  | nil => exact (ha.continuous.memLp_of_hasCompactSupport hc).coeFn_toLp
  | cons j l ih =>
    have hb := truncatedDolbeaultBoundaryComposition_smooth_compact R χ hχ l a ha hc
    let f := truncatedDolbeaultBoundaryComposition R χ l a
    let hmf := hb.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hb.2
    have he : dolbeaultBoundaryLpComposition R χ hχ hcχ l
        ((ha.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc).toLp a) =
          hmf.toLp f := by
      apply Lp.ext
      exact ih.trans hmf.coeFn_toLp.symm
    change (dolbeaultCutoffLpOperator j R (planarDbar (χ j))
      (planarDbar_contDiff_infty _ (hχ j)).continuous (planarDbar_compact _ (hcχ j))
        (dolbeaultBoundaryLpComposition R χ hχ hcχ l _)
          : Configuration n → ℂ) =ᵐ[volume] _
    rw [he]
    exact dolbeaultCutoffLpOperator_smooth_representative j R _ f
      (planarDbar_contDiff_infty _ (hχ j)) (planarDbar_compact _ (hcχ j)) hb.1 hb.2

theorem dolbeaultPrimitiveLp_ae {n : ℕ} (R : ℝ)
    (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hcχ : ∀ j, HasCompactSupport (χ j))
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (hcα : ∀ j, HasCompactSupport (α j)) (l : List (Fin n)) :
    (dolbeaultPrimitiveLp R χ hχ hcχ
      (fun j => ((hα j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hcα j)).toLp
          (α j)) l
        : Configuration n → ℂ) =ᵐ[volume] truncatedDolbeaultPrimitive R χ α l := by
  induction l with
  | nil => exact Lp.coeFn_zero ℂ 2 volume
  | cons j l ih =>
    have hb := truncatedDolbeaultBoundaryComposition_smooth_compact R χ hχ l _ (hα j) (hcα j)
    let f := truncatedDolbeaultBoundaryComposition R χ l (α j)
    let hmf := hb.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hb.2
    have he : dolbeaultBoundaryLpComposition R χ hχ hcχ l
        (((hα j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hcα j)).toLp (α j)) =
          hmf.toLp f := by
      apply Lp.ext
      exact (dolbeaultBoundaryLpComposition_ae R χ hχ hcχ l _ (hα j) (hcα j)).trans
          hmf.coeFn_toLp.symm
    have ht := dolbeaultCutoffLpOperator_smooth_representative j R (χ j) f
      (hχ j) (hcχ j) hb.1 hb.2
    rw [← he] at ht
    filter_upwards [Lp.coeFn_add
      (dolbeaultPrimitiveLp R χ hχ hcχ
        (fun j => ((hα j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hcα j)).toLp
            (α j)) l)
      (dolbeaultCutoffLpOperator j R (χ j) (hχ j).continuous (hcχ j)
        (dolbeaultBoundaryLpComposition R χ hχ hcχ l
          (((hα j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hcα j)).toLp (α
              j)))),
      ih, ht] with p h1 h2 h3
    change _ = truncatedDolbeaultPrimitive R χ α l p + dolbeaultTruncatedCutoff j R (χ j) f p
    simpa only [Pi.add_apply, h2, h3, dolbeaultPrimitiveLp] using! h1

end
end GinibrePoincare
