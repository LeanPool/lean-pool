/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianCoordinateLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUCoordinateAssembly
public import LeanPool.GinibrePoincare.Concrete.GaussianProbability

/-!
# Ginibre Hamiltonian Gaussian coordinate law

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreGaussian_coordinate_assembly_law`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Finite product regrouping used to identify the actual Gaussian initial law. -/
theorem ginibreGaussian_product_curry {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι × κ => μ)).map (MeasurableEquiv.curry ι κ E) =
      Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)) := by
  let e := MeasurableEquiv.curry ι κ E
  have h : (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))).map e.symm =
      Measure.pi (fun _ : ι × κ => μ) := by
    apply (Measure.pi_eq (fun s hs => ?_)).symm
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
    have he : e.symm ⁻¹' (univ.pi s) =
        univ.pi (fun i => univ.pi (fun j => s (i, j))) := by
      ext x
      simp [e, MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
    rw [he, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_prod_type (fun p : ι × κ => μ (s p))).symm
  rw [← h, Measure.map_map e.measurable e.symm.measurable]
  simp only [MeasurableEquiv.apply_symm_apply, Function.comp_def, Measure.map_id']

theorem ginibreGaussian_scalar_rescale {n : ℕ} (hn : 0 < n) :
    (gaussianReal 0 (1/2)).map (fun x => x / Real.sqrt (n : ℝ)) =
      gaussianReal 0 (realCoordinateVariance n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : (NNReal.mk (((Real.sqrt (n : ℝ))⁻¹)^2) (sq_nonneg _))*(1/2) = realCoordinateVariance n
      := by
    apply NNReal.eq
    change ((Real.sqrt (n : ℝ))⁻¹)^2*(1/2 : ℝ) = (2*(n : ℝ))⁻¹
    rw [inv_pow, Real.sq_sqrt hnR.le]
    field_simp
  have hg := gaussianReal_map_const_mul (μ := 0) (v := (1/2)) (Real.sqrt (n : ℝ))⁻¹
  rw [mul_zero, he] at hg
  simpa only [div_eq_mul_inv, mul_comm] using hg

/-- The assembled independent variance-one-half coordinates have exactly the
existing configuration Gaussian reference law. -/
theorem ginibreGaussian_coordinate_assembly_law {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).map
      (ginibreHamiltonianOUCoordinateAssembly n) = complexGaussianMeasure n := by
  let S : ((Fin n × Fin 2) → ℝ) → ((Fin n × Fin 2) → ℝ) :=
    fun x i => x i / Real.sqrt (n : ℝ)
  let A : ((Fin n × Fin 2) → ℝ) → Configuration n :=
    fun x j => Complex.measurableEquivPi.symm (fun k => x (j, k))
  have hS : Measurable S := Measurable.of_eval (fun i => (measurable_pi_apply i).div_const _)
  have hA : Measurable A := Measurable.of_eval (fun j =>
    Complex.measurableEquivPi.symm.measurable.comp
      (Measurable.of_eval (fun k => measurable_pi_apply (j, k))))
  have he : (ginibreHamiltonianOUCoordinateAssembly n : ((Fin n × Fin 2) → ℝ) → Configuration n) = A
      ∘ S := by
    funext x j
    simp only [ginibreHamiltonianOUCoordinateAssembly, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk,
      A, S, Function.comp_def, Complex.measurableEquivPi_symm_apply, Complex.ofReal_div]
    ring
  have hSm : (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).map S =
      Measure.pi (fun _ : Fin n × Fin 2 => (gaussianReal 0 (1/2)).map (fun x => x / Real.sqrt (n :
          ℝ))) := by
    exact Measure.pi_map_pi (fun _ => (measurable_id.div_const (Real.sqrt (n : ℝ))).aemeasurable)
  rw [he,← Measure.map_map hA hS, hSm]
  simp_rw [ginibreGaussian_scalar_rescale hn]
  let e := MeasurableEquiv.curry (Fin n) (Fin 2) ℝ
  let C : (Fin n → Fin 2 → ℝ) → Configuration n := fun x j => Complex.measurableEquivPi.symm (x j)
  have hC : Measurable C := Measurable.of_eval (fun j =>
    Complex.measurableEquivPi.symm.measurable.comp (measurable_pi_apply j))
  have hAC : A = C ∘ e := rfl
  rw [hAC,← Measure.map_map hC e.measurable, ginibreGaussian_product_curry]
  rw [Measure.pi_map_pi (fun _ => Complex.measurableEquivPi.symm.measurable.aemeasurable)]
  rfl

end
end GinibrePoincare
