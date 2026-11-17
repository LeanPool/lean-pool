/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessian.Weighted

/-!
# Bounded compact weak tests for the Hessian evolution

Weak supporting identities for Letwin arXiv:2607.24164v1 Lemma 2.4 (2.6).
Given weak Hessian and inverse-derivative inputs, local integrability and
test-class qualifications are retained explicitly. No source regularity
or mathematical completion is inferred.
-/

@[expose] public section

noncomputable section

section BoundedWeightedHessianTesting
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

private theorem compact_local_memLp_two_continuous_mul {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => χ x * f x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hχ.continuousOn
  have htop : MemLp χ (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hχ.measurable.aestronglyMeasurable.restrict C
      (ae_restrict_of_forall_mem hS.measurableSet hC)
  exact htop.fun_mul (hf S hS)

/--
The weighted weak Hessian evolution identity extended to a bounded compactly supported test `η`
whose
coordinate weak derivatives are compactly supported and globally L2, with both sides integrable. -/
theorem integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (fun x => T x k i j) 2
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv :
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
            (fun x =>
              -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                    (hessianMatrix u x)⁻¹)
                  i j))
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          (∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp
                  (fun x =>
                    -(((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x k a b) *
                          (hessianMatrix u x)⁻¹)
                        i j))
                  2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst :
      ∀ i : Fin n,
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              ∑ a : Fin n,
                hessianMatrix u x i a *
                  fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ b : Fin n, HasWeakDerivAlong η (a b) (EuclideanSpace.basisFun (Fin n) ℝ b))
    (hac : ∀ b : Fin n, HasCompactSupport (a b))
    (ha2 : ∀ b : Fin n, MemLp (a b) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j =>
      -hessianMatrix u x i j +
          (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x * (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ b : Fin n,
          Integrable (fun x => Real.exp (-u x) * J x i j b * a b x)
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        Integrable (fun x => Real.exp (-u x) * E x i j * η x)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x,
              Real.exp (-u x) *
                (∑ b : Fin n,
                  J x i j b * a b x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            -(∫ x,
                Real.exp (-u x) * E x i j *
                  η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let R := fun x => (hessianMatrix u x)⁻¹
  let J := fun x i j b => ∑ c : Fin n, R x c b * T x c i j
  let E := fun x i j =>
    -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun b c => T x i b c) * R x * (Matrix.of fun b c => T x j b c)).trace
  let wgt := fun x => Real.exp (-u x)
  have hdata :=
    integral_exp_neg_hessian_flux_eq_curvature_gram hu hL hG hW hF hdet T hT hInv hFirst
  change ∀ i j : Fin n, _
  intro i j
  have hwgt : Continuous wgt := Real.continuous_exp.comp hu.continuous.neg
  have hJw (b : Fin n) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact S →
        MemLp (fun x => wgt x * J x i j b) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    compact_local_memLp_two_continuous_mul ((hdata i j).1 b) hwgt
  have hId :
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ →
        HasCompactSupport ψ →
          (∫ x,
              ∑ b : Fin n,
                (wgt x * J x i j b) *
                  fderiv ℝ ψ x
                    (EuclideanSpace.basisFun (Fin n) ℝ
                      b) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            -(∫ x, (wgt x * E x i j) * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    calc
      _ =
          ∫ x,
            wgt x *
              (∑ b : Fin n,
                J x i j b *
                  fderiv ℝ ψ x
                    (EuclideanSpace.basisFun (Fin n) ℝ
                      b)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        exact
          Filter.Eventually.of_forall
            (fun x => by simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
      _ = _ := (hdata i j).2.2.2 ψ hψ hψc
  have ht :=
    integral_flux_eq_neg_forcing_of_bounded_weak_test hJw (hdata i j).2.2.1 hId hη hbound hηc
      hweak hac ha2
  refine ⟨ht.1, ht.2.1, ?_⟩
  calc
    _ =
        ∫ x,
          ∑ b : Fin n,
            (wgt x * J x i j b) * a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall
          (fun x => by simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
    _ = _ := ht.2.2

end FunctionalInequalities.Analysis
end BoundedWeightedHessianTesting
