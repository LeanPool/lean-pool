/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactTaylorMeasurability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTestCoefficients
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoActualPathRemainder

/-! Genuine measurability of local C² Taylor errors on compact adapted paths. -/

@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfiguration_fderiv_coordinate_sum {n : ℕ} (f : Configuration n → ℝ)
    (x h : Configuration n) :
    fderiv ℝ f x h = ∑ i : Fin n × Fin 2,
      configurationEuclideanLinearEquiv n h i * fderiv ℝ f x (ginibreCoordinateDirection i) := by
  conv_lhs => rw [itoConfigurationIncrement_expansion h]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem ginibreCompactProcess_taylor_remainder_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → Configuration n) (hX : StronglyAdapted F X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (s t : ℝ≥0) :
    Measurable (fun ω => itoTaylorRemainder f (X s ω) (X t ω-X s ω)) := by
  classical
  obtain ⟨C, hC, hG, hH⟩ := ginibreCompactProcess_test_coefficients n F X hX hCont
    f U K hU hf hK hKU hRange
  have hmX (r : ℝ≥0) : Measurable (X r) := ((hX r).mono (F.le r)).measurable
  have hmf (r : ℝ≥0) : Measurable (fun ω => f (X r ω)) :=
    ((ginibreCompactProcess_scalar_stronglyAdapted n F X hX K hRange f
      (hf.continuousOn.mono hKU) r).mono (F.le r)).measurable
  have hmcoord (i : Fin n × Fin 2) : Measurable (fun ω =>
      configurationEuclideanLinearEquiv n (X t ω-X s ω) i) :=
    ((configurationEuclideanLinearEquiv n).toContinuousLinearEquiv.continuous.measurable.comp
      ((hmX t).sub (hmX s))).eval
  have hmG (i : Fin n × Fin 2) : Measurable (fun ω =>
      fderiv ℝ f (X s ω) (ginibreCoordinateDirection i)) :=
    (((hG i).1 s).mono (F.le s)).measurable
  have hmH (i j : Fin n × Fin 2) : Measurable (fun ω =>
      itoConfigurationHessianEntry f (X s ω) i j) :=
    (((hH i j).1 s).mono (F.le s)).measurable
  have hlinear : Measurable (fun ω => fderiv ℝ f (X s ω) (X t ω-X s ω)) := by
    have he : (fun ω => fderiv ℝ f (X s ω) (X t ω-X s ω)) =
        fun ω => ∑ i : Fin n × Fin 2, configurationEuclideanLinearEquiv n (X t ω-X s ω) i *
          fderiv ℝ f (X s ω) (ginibreCoordinateDirection i) :=
      funext (fun ω => ginibreConfiguration_fderiv_coordinate_sum f (X s ω) (X t ω-X s ω))
    rw [he]
    exact Finset.measurable_sum Finset.univ (fun i hi => (hmcoord i).mul (hmG i))
  have hquadratic : Measurable (fun ω => itoDirectionalHessian f (X s ω) (X t ω-X s ω)) := by
    simp_rw [itoConfigurationHessian_coordinate_sum]
    exact Finset.measurable_sum Finset.univ (fun i hi => Finset.measurable_sum Finset.univ
      (fun j hj => ((hmcoord i).mul (hmcoord j)).mul (hmH i j)))
  have he : (fun ω => itoTaylorRemainder f (X s ω) (X t ω-X s ω)) =
      fun ω => f (X t ω)-f (X s ω)-fderiv ℝ f (X s ω) (X t ω-X s ω)-
        (1/2 : ℝ)*itoDirectionalHessian f (X s ω) (X t ω-X s ω) := by
    funext ω
    simp [itoTaylorRemainder]
  rw [he]
  exact (((hmf t).sub (hmf s)).sub hlinear).sub (measurable_const.mul hquadratic)
end
end GinibrePoincare
