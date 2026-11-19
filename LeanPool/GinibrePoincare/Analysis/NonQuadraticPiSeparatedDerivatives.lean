/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiSeparatedDerivatives.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticFiniteDerivativeConvolution
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiTensorConvolution
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Non quadratic pi separated derivatives

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piSeparated_dbar`, `piComplexDbar_continuous`, `piComplexDbar_compact`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The Wirtinger derivative `∂̄_i f = (∂_{x_i} f + i ∂_{y_i} f) / 2` in the `i`-th complex
coordinate. -/
def piComplexDbar {d : ℕ} (i : Fin d) (f : Configuration d → ℂ) (x : Configuration d) : ℂ :=
  finiteComplexDbar (Pi.single i 1) (Pi.single i Complex.I) f x

theorem piSeparated_fderiv_single {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (x : Configuration d) (i : Fin d) (v : ℂ) :
    fderiv ℝ (fun z : Configuration d => ∏ j, φ j (z j)) x (Pi.single i v) =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) * fderiv ℝ (φ i) (x i) v := by
  have hd := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ =>
    (hφ j (x j)).hasFDerivAt.comp x ((ContinuousLinearMap.proj j :
      Configuration d →L[ℝ] ℂ).hasFDerivAt))
  change HasFDerivAt (fun z : Configuration d => ∏ j, φ j (z j)) _ x at hd
  rw [hd.fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem piSeparated_dbar {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (x : Configuration d) (i : Fin d) :
    piComplexDbar i (fun z : Configuration d => ∏ j, φ j (z j)) x =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) * planarDbar (φ i) (x i) := by
  unfold piComplexDbar finiteComplexDbar planarDbar
  rw [piSeparated_fderiv_single φ hφ x i 1, piSeparated_fderiv_single φ hφ x i Complex.I]
  ring

theorem piComplexDbar_continuous {d : ℕ} (i : Fin d) (f : Configuration d → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (piComplexDbar i f) := by
  unfold piComplexDbar finiteComplexDbar
  exact continuous_const.mul (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
    (continuous_const.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem piComplexDbar_compact {d : ℕ} (i : Fin d) (f : Configuration d → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (piComplexDbar i f) :=
  ((hc.fderiv_apply ℝ _).add ((hc.fderiv_apply ℝ _).mul_left)).mul_left
end
end GinibrePoincare
