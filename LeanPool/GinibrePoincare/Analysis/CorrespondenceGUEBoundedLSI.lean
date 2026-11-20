/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEBoundedLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEOrderedLSI
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBoundedLSIClosure
/-!
# Correspondence GUE bounded LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledOrderedMeasure_boundedC1_square_lsi`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

theorem gueDoubledOrderedMeasure_boundedC1_square_lsi {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hK : LipschitzWith K f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy (gueDoubledOrderedMeasure n) f ≤
      (2/(n : ℝ))*∫ x, ‖gradient f x‖^2 ∂gueDoubledOrderedMeasure n := by
  let := gueDoubledOrderedMeasure_probability hn
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n×Fin 2))
  have hc : ∀g : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ,
      ContDiff ℝ 1 g → HasCompactSupport g →
      squareEntropy (gueDoubledOrderedMeasure n) g ≤
        (2/(n : ℝ))*∫ x, directionalEnergy b g x ∂gueDoubledOrderedMeasure n := by
    intro g hg hs
    simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using
      gueDoubledOrderedMeasure_square_lsi hn g hg hs
  have h := bakryEmery_boundedC1_lsi_of_compact
    (EuclideanSpace ℝ (Fin n×Fin 2)) (gueDoubledOrderedMeasure n) b _ hc f hf K hK C hC
  simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using h

end
end GinibrePoincare
