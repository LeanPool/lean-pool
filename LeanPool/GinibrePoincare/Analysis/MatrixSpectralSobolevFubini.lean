/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevFubini.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevFTC
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Distributional derivative transport from actual spectral line slices -/

@[expose] public section
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

/-- Actual continuous line slices with integrable derivatives off finitely many
points imply the ordinary distributional test identity under product measure. -/
theorem product_weak_derivative_identity_of_finite_crossings
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (f g ψ ψ' : ℝ × Y → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hψ : ∀ y, ContDiff ℝ 1 (fun t => ψ (t, y)))
    (hψ' : ∀ t y, deriv (fun s => ψ (s, y)) t = ψ' (t, y))
    (hsupp : ∀ y, tsupport (fun t => ψ (t, y)) ⊆ Set.Ioo a b)
    (hslice : ∀ᵐ y ∂ν, Continuous (fun t => f (t, y)) ∧
      LocallyIntegrable (fun t => g (t, y)) volume ∧
      ∃ S : Finset ℝ, ∀ t, t ∉ S →
        HasDerivAt (fun s => f (s, y)) (g (t, y)) t)
    (hgi : Integrable (fun z => g z * ψ z) ((volume : Measure ℝ).prod ν))
    (hfi : Integrable (fun z => f z * ψ' z) ((volume : Measure ℝ).prod ν)) :
    (∫ z, g z * ψ z ∂((volume : Measure ℝ).prod ν)) =
      -(∫ z, f z * ψ' z ∂((volume : Measure ℝ).prod ν)) := by
  rw [integral_prod_symm _ hgi, integral_prod_symm _ hfi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hslice] with y hy
  obtain ⟨hf, hg, S, hd⟩ := hy
  have h := weak_derivative_test_identity_off_finite S (fun t => f (t, y))
    (fun t => g (t, y)) (fun t => ψ (t, y)) hf hg hd (hψ y) a b hab (hsupp y)
  simpa only [hψ'] using h

end
end GinibrePoincare
