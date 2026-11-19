/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurProductIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAngularDensity

/-!
# Matrix Schur product integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchur_product_integral_of_injective` and its existence form
`matrixSchur_product_integral`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- On a measurable angular domain where the sorted Schur chart is injective, the chart
separates the angular integral from the spectral and strict upper integral for every
measurable unitary-conjugation-invariant observable. -/
theorem matrixSchur_product_integral_of_injective (n : ℕ)
    (V : Set (SchurLowerIndex n → ℂ)) (hV : MeasurableSet V)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n)
        ℂ))
      (V ×ˢ matrixSchurSortedUpperDomain n))
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hg : Measurable g)
    (hInv : ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ) ''
        (V ×ˢ matrixSchurSortedUpperDomain n), g A =
      (∫⁻ x in V, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            g (schurUpperCombination y) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hs : MeasurableSet (V ×ˢ matrixSchurSortedUpperDomain n) :=
    hV.prod (measurableSet_matrixSchurSortedUpperDomain n)
  have hi := matrixSchurChart_lintegral_of_injOn (0 : Matrix (Fin n) (Fin n) ℂ)
    (by intros; rfl) (V ×ˢ matrixSchurSortedUpperDomain n) hs hinj g
  rw [hi]
  have hfun : (fun p : SchurCoordinates n =>
      ENNReal.ofReal (vandermondeWeight (fun i => ((0 : Matrix (Fin n) (Fin n) ℂ) +
          schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
        g (matrixSchurFrameChart (matrixSchurExponentialFrame n) 0 p)) =
      (fun p => ENNReal.ofReal (matrixSchurAngularDensity n p.1) *
        (ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination p.2 i i)) *
          g (schurUpperCombination p.2))) := by
    funext p
    simp only [zero_add, matrixSchurFrameChart]
    rw [hInv _ (matrixSchurExponentialFrame_unitary n p.1),
      ENNReal.ofReal_mul (vandermondeWeight_nonneg _)]
    ac_rfl
  rw [hfun, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hU : Measurable (schurUpperCombination (n := n)) := by
    have he : (schurUpperCombination (n := n)) = schurUpperCLM n :=
      funext fun y => (schurUpperCLM_apply n y).symm
    rw [he]
    exact (schurUpperCLM n).continuous.measurable
  have hv : Measurable (fun y : SchurUpperIndex n → ℂ =>
      vandermondeWeight (fun i => schurUpperCombination y i i)) := by
    have hd : Measurable (fun y : SchurUpperIndex n → ℂ =>
        fun i : Fin n => schurUpperCombination y i i) := by fun_prop
    exact Complex.continuous_normSq.measurable.comp (continuous_vandermonde.measurable.comp hd)
  exact lintegral_prod_mul
    (ENNReal.measurable_ofReal.comp (measurable_matrixSchurAngularDensity n)).aemeasurable
    ((ENNReal.measurable_ofReal.comp hv).mul (hg.comp hU)).aemeasurable

/-- An actual product Schur chart separates its angular integral from its spectral and
strict upper integral for every measurable unitary-conjugation-invariant observable. -/
theorem matrixSchur_product_integral (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
        (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
        ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ)
            ''
            (V ×ˢ matrixSchurSortedUpperDomain n), g A =
          (∫⁻ x in V, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
            ∫⁻ y in matrixSchurSortedUpperDomain n,
              ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
                g (schurUpperCombination y) := by
  obtain ⟨V, hV, h0, hinj⟩ := matrixSchurSortedDomain_exists_injective n
  exact ⟨V, hV, h0, fun g hg hInv =>
    matrixSchur_product_integral_of_injective n V hV.measurableSet hinj g hg hInv⟩

end
end GinibrePoincare
