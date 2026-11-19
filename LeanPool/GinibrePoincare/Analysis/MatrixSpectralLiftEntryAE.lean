/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftEntryAE.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp

/-!
# Matrix spectral lift entry AE

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixEntryGaussian_ae_iff_volume`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- Actual positive Gaussian entry density makes weighted and ordinary volume
almost-everywhere representatives identical. -/
theorem matrixEntryGaussian_ae_iff_volume {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (p : Configuration m → Prop) :
    (∀ᵐ x ∂matrixEntryGaussianMeasure e, p x) ↔ ∀ᵐ x ∂volume, p x := by
  rw [matrixEntryGaussianMeasure_eq_real_density e,
    ae_withDensity_iff (matrixEntryGaussianDensityReal_continuous e).measurable.ennreal_ofReal]
  have hpos : ∀ x, ENNReal.ofReal (matrixEntryGaussianDensityReal e x) ≠ 0 :=
    fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (matrixEntryGaussianDensityReal_pos hn e x))
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx (hpos x)
  · intro h
    filter_upwards [h] with x hx
    exact fun _ => hx

end
end GinibrePoincare
