/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Sign
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import LeanPool.KLS.FunctionalInequalities.Probability.Variance.Product
public import LeanPool.KLS.FunctionalInequalities.Probability.Moments

/-!
# Variance of quadratic matrix forms

Generic probability statements about `x ↦ Σᵢⱼ Bᵢⱼ xᵢ xⱼ` and `x ↦ ⟪A x, x⟫`:
- continuity of the variance in the matrix for a law with finite fourth moment;
- the singular extension (Letwin, Lemma A.2): a variance bound `≤ C tr (B²)` for all symmetric
  invertible `B` extends to all symmetric `B`;
- convolution with centered noise of finite fourth moment does not decrease the variance of a
  quadratic form.

The bound itself is a hypothesis; nothing here proves a constant.
-/

@[expose] public section

namespace FunctionalInequalities.Probability

section MatrixForms

open MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace

variable {n : ℕ} (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))

include h4 in
theorem tendsto_variance_quadratic_matrix_forms
    {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : Tendsto seq atTop (𝓝 A)) :
    Tendsto (fun k => ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
      atTop (𝓝 (ProbabilityTheory.variance
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _))) := by
  classical
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hcoord (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 4 (mu : Measure _) := by
    simpa only [id_eq, EuclideanSpace.inner_basisFun_real] using
      h4.inner_const (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hprod (p : Fin n × Fin n) : MemLp
      (fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) 2 (mu : Measure _) :=
    (hcoord p.1).mul (hcoord p.2) (hpqr := ht)
  have hc (p : Fin n × Fin n) : Tendsto (fun k => seq k p.1 p.2) atTop (𝓝 (A p.1 p.2)) := by
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M p.1 p.2) := by fun_prop
    exact hcont.continuousAt.tendsto.comp hseq
  have h := FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination mu
    (fun p : Fin n × Fin n => fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) hprod
    (fun k p => seq k p.1 p.2) (fun p => A p.1 p.2) hc
  simpa only [Fintype.sum_prod_type, mul_assoc] using h

include h4 in
theorem symmetric_matrix_variance_bound_of_isUnit (C : ℝ)
    (hBound : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm → IsUnit B →
      ProbabilityTheory.variance (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, ∑ j, B i j * x i * x j) (mu : Measure _) ≤ C * (B * B).trace) :
    ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      ProbabilityTheory.variance (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, ∑ j, B i j * x i * x j) (mu : Measure _) ≤ C * (B * B).trace := by
  intro B hB
  obtain ⟨seq, hunit, hlim⟩ := Analysis.exists_symmetric_isUnit_matrix_sequence B hB
  have hvar := tendsto_variance_quadratic_matrix_forms mu h4 hlim
  have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => C * (M * M).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hright := hcont.continuousAt.tendsto.comp hlim
  exact le_of_tendsto_of_tendsto hvar hright
    (Filter.Eventually.of_forall fun k => hBound (seq k) (hunit k).1 (hunit k).2)

end MatrixForms

section Convolution

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem quadratic_variance_le_centered_noise_convolution (mu nu : ProbabilityMeasure E)
    (hmu4 : MemLp (id : E → E) 4 (mu : Measure E))
    (hnu4 : MemLp (id : E → E) 4 (nu : Measure E)) (hmean : (∫ z, z ∂(nu : Measure E)) = 0)
    (A : E →L[ℝ] E) :
    variance (fun x : E => ⟪A x, x⟫) (mu : Measure E) ≤
      variance (fun x : E => ⟪A x, x⟫) ((mu : Measure E).conv (nu : Measure E)) := by
  let q : E → ℝ := fun x => ⟪A x, x⟫
  let f : E × E → ℝ := fun p => q (p.1 + p.2)
  have hsum4 : MemLp (fun p : E × E => p.1 + p.2) 4 ((mu : Measure E).prod (nu : Measure E)) :=
    (hmu4.comp_fst (nu : Measure E)).add (hnu4.comp_snd (mu : Measure E))
  have hf : MemLp f 2 ((mu : Measure E).prod (nu : Measure E)) :=
    memLp_quadratic_of_memLp_four hsum4 A
  have hqnu : MemLp q 2 (nu : Measure E) := memLp_quadratic_of_memLp_four hnu4 A
  have hnu1 : Integrable (id : E → E) (nu : Measure E) :=
    (hnu4.mono_exponent (by norm_num : (1 : ENNReal) ≤ 4)).integrable le_rfl
  have hnoise (x : E) : (∫ z, f (x, z) ∂(nu : Measure E)) = q x + ∫ z, q z ∂(nu : Measure E) := by
    have h1 : Integrable (fun z : E => ⟪A x, z⟫) (nu : Measure E) := hnu1.const_inner (A x)
    have h2 : Integrable (fun z : E => ⟪x, A z⟫) (nu : Measure E) :=
      (A.integrable_comp hnu1).const_inner x
    have hexp (z : E) : f (x, z) = q x + ⟪A x, z⟫ + ⟪x, A z⟫ + q z := by
      simp only [f, q, map_add, inner_add_left, inner_add_right]
      rw [real_inner_comm (A z) x]
      ring
    have hi1 : (∫ z : E, ⟪A x, z⟫ ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq, hmean, inner_zero_right] using (integral_inner (𝕜 := ℝ) hnu1 (A x))
    have hAz : (∫ z : E, A z ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq, hmean, map_zero] using (A.integral_comp_comm hnu1)
    have hi2 : (∫ z : E, ⟪x, A z⟫ ∂(nu : Measure E)) = 0 := by
      simpa only [id_eq, hAz, inner_zero_right] using
        (integral_inner (𝕜 := ℝ) (A.integrable_comp hnu1) x)
    calc
      _ = ∫ z, q x + ⟪A x, z⟫ + ⟪x, A z⟫ + q z ∂(nu : Measure E) :=
        integral_congr_ae (ae_of_all _ hexp)
      _ = _ := by
        have hs0 :=
          integral_add (((integrable_const (q x)).add h1).add h2) (hqnu.integrable one_le_two)
        have hs1 := integral_add ((integrable_const (q x)).add h1) h2
        have hs2 := integral_add (integrable_const (q x)) h1
        simp only [Pi.add_apply] at hs0 hs1 hs2
        rw [hs0, hs1, hs2, integral_const, hi1, hi2]
        simp
  have hdec := FunctionalInequalities.ProductVariance.decomposition hf
  have hnonneg : 0 ≤ ∫ x, variance (fun z => f (x, z)) (nu : Measure E) ∂(mu : Measure E) :=
    integral_nonneg fun x => variance_nonneg _ _
  have havg :
    variance (fun x => ∫ z, f (x, z) ∂(nu : Measure E)) (mu : Measure E) =
      variance q (mu : Measure E) := by
    simp_rw [hnoise]
    exact variance_add_const (by fun_prop : AEStronglyMeasurable q (mu : Measure E)) _
  have hprod :
    variance q (mu : Measure E) ≤ variance f ((mu : Measure E).prod (nu : Measure E)) := by
    rw [havg] at hdec
    linarith
  have hmap :
    variance q ((mu : Measure E).conv (nu : Measure E)) =
      variance f ((mu : Measure E).prod (nu : Measure E)) := by
    unfold Measure.conv
    rw [variance_map (by fun_prop : AEMeasurable q _)
        (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)]
    rfl
  exact hmap.symm ▸ hprod

end Convolution

end FunctionalInequalities.Probability
