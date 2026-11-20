/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultInterior
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMollifier
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiCompactGraphApproximation

/-!
# Correspondence auxiliary local Dolbeault approximation

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `ordinaryDolbeaultPiMollification_closed_ball`.
-/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

theorem ordinaryDolbeaultPiMollification_eq {n : ℕ}
    (φ : ContDiffBump (0 : ℂ)) (a : Configuration n → ℂ) :
    ordinaryDolbeaultMollify (fun p => Complex.ofReal (piPlanarBump n φ p)) a =
      piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a := by
  funext p
  unfold ordinaryDolbeaultMollify convolution
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp [Complex.real_smul])

theorem ordinaryDolbeaultPiMollification_closed_ball {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, MemLp (α j) 2 volume)
    (x : Configuration n) (R : ℝ)
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ ball x R → ∀ j k,
        (∫ y, dbarComponent θ k y * α j y) = ∫ y, dbarComponent θ j y * α k y)
    (φ : ContDiffBump (0 : ℂ)) (p : Configuration n)
    (hp : φ.rOut + dist p x < R) (j k : Fin n) :
    dbarComponent (piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] α j) k p =
      dbarComponent (piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] α k) j p := by
  rw [← ordinaryDolbeaultPiMollification_eq φ (α j),← ordinaryDolbeaultPiMollification_eq φ (α k)]
  exact ordinaryDolbeaultMollify_closed_on (ball x R) α
    (fun t => (hα t).locallyIntegrable (by norm_num)) hclosed _
    (Complex.ofRealCLM.contDiff.comp (dolbeaultPiBump_contDiff n φ))
    ((piPlanarBump_compact n φ).comp_left Complex.ofReal_zero) p
    (dolbeaultBump_translated_tsupport_interior φ x p R hp) j k

end
end GinibrePoincare
