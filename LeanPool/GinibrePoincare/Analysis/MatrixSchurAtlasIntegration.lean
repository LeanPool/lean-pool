/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAtlasIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAtlasPartition
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurProductIntegration

/-! # Integration on one injective Schur atlas piece

Change of variables on an injective sorted Schur chart contributes its actual
Jacobian, the product of an angular density and the Vandermonde weight. For a
unitary-invariant observable, the angular conjugation drops out of its value.
Tonelli factorization separates the angular and upper-triangular integrals.
The last theorem transports this formula to a chart centered at any unitary
matrix; conjugation preserves volume because its absolute real determinant is one.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

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

theorem matrixUnitaryConjugation_injective {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Injective (matrixUnitaryConjugation U) := by
  have hh : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hinv : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      Uᴴ * (U * A * Uᴴ) * U = A := by
    intro A
    calc
      _ = (Uᴴ * U) * A * (Uᴴ * U) := by noncomm_ring
      _ = A := by rw [hh, Matrix.one_mul, Matrix.mul_one]
  intro A B he
  have he' : U * Matrix.of A * Uᴴ = U * Matrix.of B * Uᴴ :=
    (matrixUnitaryConjugation_apply U A).symm.trans (he.trans (matrixUnitaryConjugation_apply U B))
  have he'' := congrArg (fun X => Uᴴ * X * U) he'
  rw [hinv, hinv] at he''
  exact he''

theorem matrixUnitaryConjugation_set_integral {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (s : Set (Matrix (Fin n) (Fin n) ℂ)) (hs : MeasurableSet s)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞)
    (hInv : ∀ A, g (U * A * Uᴴ) = g A) :
    ∫⁻ A in matrixUnitaryConjugation U '' s, g A = ∫⁻ A in s, g A := by
  let : Measure.IsAddHaarMeasure (volume : Measure (Fin n → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  have hi := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (Fin n → Fin n → ℂ)) hs
    (fun A _ => ((matrixUnitaryConjugation U).hasFDerivAt).hasFDerivWithinAt)
    ((matrixUnitaryConjugation_injective U hU).injOn) g
  rw [hi]
  apply setLIntegral_congr_fun hs
  intro A hA
  change ENNReal.ofReal |(matrixUnitaryConjugation U).toLinearMap.det| *
    g (matrixUnitaryConjugation U A) = g A
  rw [matrixUnitaryConjugation_abs_det U hU, ENNReal.ofReal_one, one_mul,
    matrixUnitaryConjugation_apply U A]
  exact hInv _

theorem matrixSchurAtlas_product_integral {n : ℕ}
    (C : Matrix.unitaryGroup (Fin n) ℂ)
    (V : Set (SchurLowerIndex n → ℂ)) (hV : MeasurableSet V)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n)
        (0 : Matrix (Fin n) (Fin n) ℂ))
      (V ×ˢ matrixSchurSortedUpperDomain n))
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hg : Measurable g)
    (hInv : ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) :
    ∫⁻ A in matrixSchurAtlasChart C '' (V ×ˢ matrixSchurSortedUpperDomain n), g A =
      (∫⁻ x in V, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            g (schurUpperCombination y) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let S := matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ) ''
    (V ×ˢ matrixSchurSortedUpperDomain n)
  have hs : MeasurableSet S :=
    (hV.prod (measurableSet_matrixSchurSortedUpperDomain n)).image_of_continuousOn_injOn
      (matrixSchurExponentialChart_differentiable 0).continuous.continuousOn hinj
  have hset : matrixSchurAtlasChart C '' (V ×ˢ matrixSchurSortedUpperDomain n) =
      matrixUnitaryConjugation (C : Matrix (Fin n) (Fin n) ℂ) '' S := by
    erw [← Set.image_comp]
    congr 1
    funext p
    exact (matrixUnitaryConjugation_apply _ _).symm
  rw [hset]
  exact (matrixUnitaryConjugation_set_integral _ C.property S hs g (hInv _ C.property)).trans
    (matrixSchur_product_integral_of_injective n V hV hinj g hg hInv)

end
end GinibrePoincare
