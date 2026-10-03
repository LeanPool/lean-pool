/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.VectorL2Triangle

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIntegralCauchy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixIntegralSum

/-! # Iterates L2Finite Triangle

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem IteratesL2FiniteTriangle.quadratic_cross_bound {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * R + B) :
    R ≤ Real.sqrt A * Real.sqrt B := by
  exact AVenhance.Infra.VectorL2Triangle.quadratic_cross_bound hA hB hp

/-- The integral L2 triangle inequality for the actual `Vec 2` carrier. -/
theorem iterate_vector_integral_L2_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → Vec 2}
    (hf : Integrable (fun x => vecNormSq (f x)) μ)
    (hg : Integrable (fun x => vecNormSq (g x)) μ)
    (hfg : Integrable (fun x => vecDot (f x) (g x)) μ) :
    Real.sqrt (∫ x, vecNormSq (f x + g x) ∂μ) ≤
      Real.sqrt (∫ x, vecNormSq (f x) ∂μ) + Real.sqrt (∫ x, vecNormSq (g x) ∂μ) := by
  exact AVenhance.Infra.VectorL2Triangle.vector_integral_L2_add hf hg hfg

/-- Finite sums on a compact integration domain obey the L2 triangle inequality.
The integrability supplier is used on continuous scalar polynomials only. -/
theorem iterate_vector_integral_L2_sum {α ι : Type*} [MeasurableSpace α]
    [TopologicalSpace α] {μ : Measure α} {S : Set α} (s : Finset ι)
    (f : ι → α → Vec 2) (hf : ∀ i ∈ s, ContinuousOn (f i) S)
    (hI : ∀ q : α → ℝ, ContinuousOn q S → Integrable q μ) :
    Real.sqrt (∫ x, vecNormSq (∑ i ∈ s, f i x) ∂μ) ≤
      ∑ i ∈ s, Real.sqrt (∫ x, vecNormSq (f i x) ∂μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecNormSq, vecDot]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContinuousOn (f j) S := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : ContinuousOn (fun x => ∑ j ∈ s, f j x) S := continuousOn_finsetSum s hfs
    have hn (q : α → Vec 2) (hq : ContinuousOn q S) : Integrable (fun x => vecNormSq (q x)) μ := by
      apply hI
      unfold vecNormSq vecDot
      exact continuousOn_finsetSum Finset.univ (fun j _ => ((continuous_apply j).comp_continuousOn
          hq).mul
        ((continuous_apply j).comp_continuousOn hq))
    have hc : Integrable (fun x => vecDot (f i x) (∑ j ∈ s, f j x)) μ := by
      apply hI
      unfold vecDot
      exact continuousOn_finsetSum Finset.univ (fun j _ => ((continuous_apply j).comp_continuousOn
          hfi).mul
        ((continuous_apply j).comp_continuousOn hsum))
    simp only [Finset.sum_insert hi]
    exact (iterate_vector_integral_L2_add (hn _ hfi) (hn _ hsum) hc).trans
      (add_le_add le_rfl (ih hfs))

/-- Scalar finite-sum triangle inequality, without a dimension loss. -/
theorem iterate_scalar_integral_L2_sum {α ι : Type*} [MeasurableSpace α]
    [TopologicalSpace α] {μ : Measure α} {S : Set α} (s : Finset ι)
    (f : ι → α → ℝ) (hf : ∀ i ∈ s, ContinuousOn (f i) S)
    (hI : ∀ q : α → ℝ, ContinuousOn q S → Integrable q μ) :
    Real.sqrt (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤
      ∑ i ∈ s, Real.sqrt (∫ x, (f i x) ^ 2 ∂μ) := by
  classical
  let F : ι → α → Vec 2 := fun i x j => if j = 0 then f i x else 0
  have hc : ∀ i ∈ s, ContinuousOn (F i) S := by
    intro i hi
    apply continuousOn_pi.mpr
    intro j
    by_cases hj : j = 0
    · simpa only [F, hj, ite_true] using hf i hi
    · simpa only [F, hj, ite_false] using (continuousOn_const : ContinuousOn (fun _ : α => (0 :
        ℝ)) S)
  have h := iterate_vector_integral_L2_sum s F hc hI
  simpa [F, vecNormSq, vecDot, Fin.sum_univ_two, Finset.sum_apply, pow_two] using h

end AVenhance.Infra.Section4
