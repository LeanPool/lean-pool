/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticPredictableInnovation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConditionalKernel
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.Probability.Independence.Integration

/-! Predictable centered innovations, with integrability derived from independence. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
namespace GinibrePoincare
noncomputable section

theorem ginibreIndependent_predictable_centered_conditional {Ω β ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace ζ]
    [StandardBorelSpace ζ] [Nonempty ζ]
    (P : Measure Ω) [IsProbabilityMeasure P] (Past : Ω → β) (Z : Ω → ζ)
    (hPast : Measurable Past) (ν : Measure ζ) [IsProbabilityMeasure ν]
    (hZ : HasLaw Z ν P) (hind : IndepFun Z Past P)
    (F : β → ℝ) (hF : Measurable F) (hFi : Integrable (fun ω => F (Past ω)) P)
    (φ : ζ → ℝ) (hφ : Measurable φ) (hφi : Integrable φ ν) (hφmean : (∫ z, φ z ∂ν) = 0) :
    P[(fun ω => F (Past ω)*φ (Z ω)) | MeasurableSpace.comap Past inferInstance] =ᵐ[P] (fun _ => 0)
        := by
  have hφmap : Integrable φ (P.map Z) := by rw [hZ.map_eq]; exact hφi
  have hφZ : Integrable (fun ω => φ (Z ω)) P := hφmap.comp_aemeasurable hZ.aemeasurable
  have hInd := hind.symm.comp hF hφ
  let G : β × ζ → ℝ := fun p => F p.1*φ p.2
  have hG : Measurable G := (hF.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hGi : Integrable (fun ω => G (Past ω, Z ω)) P := hInd.integrable_mul hFi hφZ
  have hCond := ginibreIndependent_condDistrib_general P Past Z hPast ν hZ hind
  have hCondω := ae_of_ae_map hPast.aemeasurable hCond
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable
      hGi
  apply hCE.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ z, F (Past ω)*φ z ∂condDistrib Z Past P (Past ω)) = 0
  rw [hκ]
  change (∫ z, F (Past ω)*φ z ∂ν) = 0
  rw [integral_const_mul, hφmean, mul_zero]

theorem ginibreIndependent_predictable_secondMoment {Ω β ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace ζ]
    (P : Measure Ω) (Past : Ω → β) (Z : Ω → ζ)
    (hPast : Measurable Past) (ν : Measure ζ)
    (hZ : HasLaw Z ν P) (hind : IndepFun Z Past P)
    (F : β → ℝ) (hF : Measurable F) (φ : ζ → ℝ) (hφ : Measurable φ) :
    (∫ ω, (F (Past ω)*φ (Z ω))^2 ∂P) =
      (∫ ω, (F (Past ω))^2 ∂P)*(∫ z, (φ z)^2 ∂ν) := by
  have hInd := hind.symm.comp (hF.pow_const 2) (hφ.pow_const 2)
  have hProd := hInd.integral_mul_eq_mul_integral
    ((hF.comp hPast).pow_const 2).aestronglyMeasurable
    ((hφ.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable.pow 2)
  simp only [Pi.mul_apply, Function.comp_apply] at hProd
  simp_rw [mul_pow]
  have hLaw := hZ.integral_comp (hφ.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at hLaw
  rw [hProd, hLaw]

theorem ginibreIndependent_predictable_memLp_two {Ω β ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace ζ]
    (P : Measure Ω) (Past : Ω → β) (Z : Ω → ζ)
    (_ : Measurable Past) (ν : Measure ζ)
    (hZ : HasLaw Z ν P) (hind : IndepFun Z Past P)
    (F : β → ℝ) (hF : Measurable F) (hFi : MemLp (fun ω => F (Past ω)) 2 P)
    (φ : ζ → ℝ) (hφ : Measurable φ) (hφi : MemLp φ 2 ν) :
    MemLp (fun ω => F (Past ω)*φ (Z ω)) 2 P := by
  have hφmap : MemLp φ 2 (P.map Z) := by rw [hZ.map_eq]; exact hφi
  have hφZ : MemLp (fun ω => φ (Z ω)) 2 P :=
    (memLp_map_measure_iff hφmap.aestronglyMeasurable hZ.aemeasurable).mp hφmap
  have hInd := hind.symm.comp (hF.pow_const 2) (hφ.pow_const 2)
  apply (memLp_two_iff_integrable_sq (hFi.aestronglyMeasurable.mul hφZ.aestronglyMeasurable)).mpr
  change Integrable (fun ω => (F (Past ω)*φ (Z ω))^2) P
  simp_rw [mul_pow]
  exact hInd.integrable_mul hFi.integrable_sq hφZ.integrable_sq

end
end GinibrePoincare
