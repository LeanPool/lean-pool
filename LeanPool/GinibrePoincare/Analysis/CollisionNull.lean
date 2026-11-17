/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CollisionNull.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreMassPositivity

/-! # The collision locus is Gaussian-null -/


@[expose] public section


open MeasureTheory ProbabilityTheory

namespace GinibrePoincare

noncomputable section

private theorem measure_prod_diagonal_eq_zero {α : Type*}
    [MeasurableSpace α] [MeasurableEq α] (μ : Measure α)
    [SFinite μ] [NullSingletonClass μ] :
    μ.prod μ (Set.diagonal α) = 0 := by
  rw [Measure.measure_prod_null measurableSet_diagonal]
  filter_upwards with x
  simp [Set.diagonal]

private theorem complexCoordinateGaussian_nullSingleton {n : ℕ} (hn : 0 < n) :
    NullSingletonClass
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [complexCoordinateGaussianMeasure_eq_withDensity hn]
  infer_instance

private theorem coordinate_pair_map {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Measure.map (fun z : Configuration n ↦ (z i, z j))
        (complexGaussianMeasure n) =
      (complexCoordinateGaussianProbability n : Measure ℂ).prod
        (complexCoordinateGaussianProbability n : Measure ℂ) := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  have hind : iIndepFun (fun k (z : Configuration n) ↦ z k)
      (complexGaussianMeasure n) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun k ↦
      (measurable_pi_apply k).aemeasurable)]
    unfold complexGaussianMeasure complexGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_pi]
    change Measure.map id (Measure.pi fun _ : Fin n ↦ μ) =
      Measure.pi (fun k : Fin n ↦
        Measure.map (fun z : Configuration n ↦ z k)
          (Measure.pi fun _ : Fin n ↦ μ))
    rw [Measure.map_id]
    congr 1
    funext k
    exact (measurePreserving_eval (fun _ : Fin n ↦ μ) k).map_eq.symm
  have hp := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  have hi : Measure.map (fun z : Configuration n ↦ z i)
      (complexGaussianMeasure n) = μ := by
    unfold complexGaussianMeasure complexGaussianProbability
    exact (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
  have hj : Measure.map (fun z : Configuration n ↦ z j)
      (complexGaussianMeasure n) = μ := by
    unfold complexGaussianMeasure complexGaussianProbability
    exact (measurePreserving_eval (fun _ : Fin n ↦ μ) j).map_eq
  rw [hi, hj] at hp
  exact hp

private theorem coordinate_diagonal_null {n : ℕ} (hn : 0 < n)
    (i j : Fin n) (hij : i ≠ j) :
    complexGaussianMeasure n {z | z i = z j} = 0 := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  let : NullSingletonClass μ := complexCoordinateGaussian_nullSingleton hn
  have hm : Measurable (fun z : Configuration n ↦ (z i, z j)) := by fun_prop
  have hd : MeasurableSet (Set.diagonal ℂ) := measurableSet_diagonal
  change complexGaussianMeasure n
    ((fun z : Configuration n ↦ (z i, z j)) ⁻¹' Set.diagonal ℂ) = 0
  rw [← Measure.map_apply hm hd, coordinate_pair_map i j hij]
  exact measure_prod_diagonal_eq_zero μ

/-- Under the product complex Gaussian law, particle collisions form a null
set. -/
theorem complexGaussianMeasure_collisionSet (n : ℕ) :
    complexGaussianMeasure n (collisionSet n) = 0 := by
  by_cases hn : 0 < n
  · apply measure_mono_null (show collisionSet n ⊆
        ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_h : i ≠ j), {z | z i = z j} by
      intro z hz
      rcases hz with ⟨i, j, heq, hij⟩
      exact Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem j <|
        Set.mem_iUnion_of_mem hij heq)
    apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro j
    apply measure_iUnion_null
    intro hij
    exact coordinate_diagonal_null hn i j hij
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [collisionSet]

/-- The Vandermonde density is nonzero almost everywhere for the complex
Gaussian law. -/
theorem vandermondeDensity_ne_zero_ae (n : ℕ) :
    ∀ᵐ z ∂complexGaussianMeasure n, vandermondeDensity z ≠ 0 := by
  rw [ae_iff]
  apply measure_mono_null _ (complexGaussianMeasure_collisionSet n)
  intro z hz
  simp only [Set.mem_ofPred_eq, not_not] at hz
  have hvle : vandermondeWeight z ≤ 0 := by
    exact ENNReal.ofReal_eq_zero.mp hz
  have hv : vandermondeWeight z = 0 :=
    le_antisymm hvle (vandermondeWeight_nonneg z)
  exact (vandermondeWeight_eq_zero_iff z).mp hv

/-- Once the normalizing scalar is positive, the Gaussian reference measure
is absolutely continuous with respect to the normalized Ginibre measure. -/
theorem complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    {n : ℕ} (hvalid : GinibreMassIsValid n) :
    complexGaussianMeasure n ≪ ginibreMeasure n := by
  unfold ginibreMeasure rawGinibreMeasure
  exact (withDensity_absolutelyContinuous'
      measurable_vandermondeDensity.aemeasurable
      (vandermondeDensity_ne_zero_ae n)).trans
    (Measure.absolutelyContinuous_smul
      (ENNReal.inv_ne_zero.mpr hvalid.2.ne))

end

end GinibrePoincare
