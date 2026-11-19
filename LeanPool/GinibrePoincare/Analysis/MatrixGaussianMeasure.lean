/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGaussianMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity
public import LeanPool.GinibrePoincare.Analysis.MatrixOverlap
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Concrete complex Ginibre matrix Gaussian law

Rows are independent product Gaussian vectors; hence all matrix entries are
independent complex Gaussians with real-coordinate variance `(2n)⁻¹`.
The density is identified explicitly with `exp (-n Tr(GG*))`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal

namespace GinibrePoincare
noncomputable section

@[reducible] instance ginibreMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℂ))

@[reducible] instance ginibreMatrixMeasureSpace (n : ℕ) :
    MeasureSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin n → ℂ))

/-- The Ginibre matrix law as a probability measure: independent rows, each distributed as
`complexGaussianProbability n`. -/
def matrixGaussianProbability (n : ℕ) : ProbabilityMeasure (Matrix (Fin n) (Fin n) ℂ) :=
  ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n)

/-- The Ginibre matrix law `matrixGaussianProbability n` as a measure. -/
def matrixGaussianMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  matrixGaussianProbability n

instance matrixGaussianMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixGaussianMeasure n) := by
  unfold matrixGaussianMeasure
  infer_instance

/-- The Ginibre matrix density `(n / π)^(n²) exp (-n ‖G‖²_HS)`. -/
def matrixGaussianDensity (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
    Real.exp (-(n : ℝ) * matrixHSNormSq G))

theorem measurable_matrixGaussianDensity (n : ℕ) : Measurable (matrixGaussianDensity n) := by
  unfold matrixGaussianDensity
  simp only [matrixHSNormSq_eq_sum]
  fun_prop

theorem matrixGaussianDensity_eq_row_product (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) :
    matrixGaussianDensity n G = ∏ i, complexGaussianDensity n (G i) := by
  unfold matrixGaussianDensity complexGaussianDensity
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]
    unfold gaussianWeight configurationNormSq
    rw [← Real.exp_sum]
    rw [← Finset.mul_sum, matrixHSNormSq_eq_sum]
  · intro i _
    unfold gaussianWeight
    positivity

/-- The concrete matrix Gaussian is the explicitly normalized
Hilbert--Schmidt Gaussian density. -/
theorem matrixGaussianMeasure_eq_withDensity {n : ℕ} (hn : 0 < n) :
    matrixGaussianMeasure n =
      (volume : Measure (Matrix (Fin n) (Fin n) ℂ)).withDensity (matrixGaussianDensity n) := by
  change (ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n) :
    Measure (Fin n → Configuration n)) =
      (volume : Measure (Fin n → Configuration n)).withDensity (matrixGaussianDensity n)
  simp only [ProbabilityMeasure.toMeasure_pi]
  rw [show Measure.pi (fun _ : Fin n => (complexGaussianProbability n : Measure (Configuration n)))
      =
      Measure.pi (fun _ : Fin n => (volume : Measure (Configuration n)).withDensity
          (complexGaussianDensity n)) by
    congr 1
    funext i
    exact complexGaussianDensityIdentification n hn]
  have hsf : ∀ i : Fin n, SigmaFinite
      ((volume : Measure (Configuration n)).withDensity (complexGaussianDensity n)) := fun i => by
    change SigmaFinite (complexGaussianDensityMeasure n)
    rw [← complexGaussianDensityIdentification n hn]
    infer_instance
  rw [@Measure.pi_withDensity _ _ _ _ (fun _ : Fin n => (volume : Measure (Configuration n)))
    (by intro i; infer_instance) (fun _ : Fin n => complexGaussianDensity n)
    (fun _ => by unfold complexGaussianDensity gaussianWeight configurationNormSq; fun_prop) hsf,
    ← volume_pi]
  congr 1
  funext G
  exact (matrixGaussianDensity_eq_row_product n G).symm

theorem matrixGaussianMeasure_absolutelyContinuous {n : ℕ} (hn : 0 < n) :
    matrixGaussianMeasure n ≪ volume := by
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact withDensity_absolutelyContinuous _ _

theorem matrixGaussianMeasure_univ (n : ℕ) :
    matrixGaussianMeasure n Set.univ = 1 := by simp

/-- Flattening the matrix exposes its independent entry product measure. -/
theorem matrixGaussianMeasure_uncurry_map (n : ℕ) :
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℂ => fun ij : Fin n × Fin n => G ij.1 ij.2)
      (matrixGaussianMeasure n) =
        Measure.pi (fun _ : Fin n × Fin n => (complexCoordinateGaussianProbability n : Measure ℂ))
            := by
  change Measure.map (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ))
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
      (complexCoordinateGaussianProbability n : Measure ℂ)))) = _
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair,
      Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem matrixGaussianMeasure_uncurry_preserving (n : ℕ) :
    MeasurePreserving (fun G : Matrix (Fin n) (Fin n) ℂ => fun ij : Fin n × Fin n => G ij.1 ij.2)
      (matrixGaussianMeasure n)
        (Measure.pi (fun _ : Fin n × Fin n => (complexCoordinateGaussianProbability n : Measure ℂ)))
            :=
  ⟨by change Measurable (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)); fun_prop,
    matrixGaussianMeasure_uncurry_map n⟩

end
end GinibrePoincare
