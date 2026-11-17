/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Standardization
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Standardization

/-!
# A-priori posterior energy bounds
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis

namespace FunctionalInequalities.KLS.BKL
open FunctionalInequalities.Analysis.BakryEmery

variable {n : ℕ}
namespace Localization

private theorem posterior_energy_transfer
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (h : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      KLS.LogConcave ν → KLS.Isotropic ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin d → Fin n,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          b * ‖u‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) d v ≤
      b * ⟪Covariance.operator
        (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by
  simpa only [cumulantEnergy] using
    compactPosterior_cumulant_bound_of_fixed_dimension μ hc hiso hLC c Q hSym hQ hd h v
variable (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- The posterior mean lies in the ball carrying the prior. -/
theorem norm_posteriorMean_le {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r)
    (p : Param n) : ‖posteriorMean μ p.1 p.2‖ ≤ r := by
  have hc' : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).of_isClosed_subset
      Measure.isClosed_support hsupp
  have hae :
    ∀ᵐ x ∂(compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))),
      ‖x‖ ≤ max r 0 := by
    rw [compactPosterior_ae μ hc' p.1 p.2]
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))] with
      x hx
    exact (mem_closedBall_zero_iff.mp (hsupp hx)).trans (le_max_left r 0)
  have hb :
    ‖∫ x, x ∂(compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))‖ ≤ r := by
    simpa [max_eq_left hr] using norm_integral_le_of_norm_le_const hae
  change
    ‖∫ x, x ∂((μ : Measure (EuclideanSpace ℝ (Fin n))).tilted (quadraticExponent p.1 p.2))‖ ≤ r
  exact hb

/-- A-priori bound on the cumulant energies along the localization. -/
theorem exists_cumulantEnergy_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ) {r : ℝ}
    (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (d : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ p : Param n,
          IsSelfAdjoint p.2 →
            (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
              ∀ u : EuclideanSpace ℝ (Fin n),
                cumulantEnergy
                    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤
                  C * ‖u‖ ^ 2 := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨r ^ 2, sq_nonneg r, ?_⟩
    intro p _ _ u
    let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := compactPosterior μ hc p.1 p.2
    have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
      change
        IsCompact (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))).support
      rw [compactPosterior_support]
      exact hc
    have hfirst (v : Fin 1 → EuclideanSpace ℝ (Fin n)) :
      cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1 v = ⟪v 0, posteriorMean μ p.1 p.2⟫ := by
      rw [cumulant, iteratedFDeriv_one_apply, ←
        tiltAverage_inner_eq_fderiv_logLaplace (π : Measure (EuclideanSpace ℝ (Fin n)))
          (fun t => compact_support_integrable_exp _ hπcompact t) (v 0) 0]
      have hzero :
        (fun x : EuclideanSpace ℝ (Fin n) => ⟪(0 : EuclideanSpace ℝ (Fin n)), x⟫) = 0 := by
        funext x
        simp
      rw [tiltAverage, expTilt, hzero, tilted_zero]
      exact integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (v 0)
    have habs : |⟪u, posteriorMean μ p.1 p.2⟫| ≤ ‖u‖ * r :=
      (abs_real_inner_le_norm u _).trans
        (mul_le_mul_of_nonneg_left (norm_posteriorMean_le μ hr hsupp p) (norm_nonneg u))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg u) hr)).2 habs
    have he :
      cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 0 u =
        ⟪u, posteriorMean μ p.1 p.2⟫ ^ 2 := by
      change
        (∑ J : Fin 0 → Fin n,
            cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1
                (Fin.cons u fun k =>
                  inverseSqrt (Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n))))
                    (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^
              2) =
          _
      simp only [hfirst, Fin.cons_zero]
      simp
    rw [he]
    simpa only [sq_abs, mul_pow, mul_comm] using hsq
  · obtain ⟨b, hb, hbound⟩ := exists_sum_sq_cumulant_le_isotropic (n := n) d
    refine ⟨b * r ^ 2, mul_nonneg hb (sq_nonneg r), ?_⟩
    intro p hSym hQ u
    have htransfer :=
      posterior_energy_transfer μ hc hiso hLC p.1 p.2 hSym hQ (by omega : 1 ≤ d) hbound u
    let A :=
      Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
    have hA : ‖A‖ ≤ r ^ 2 :=
      opNorm_covariance_compactPosterior_le_sq_radius μ hc hr hsupp p.1 p.2
    have hinner : ⟪A u, u⟫ ≤ r ^ 2 * ‖u‖ ^ 2 := by
      calc
        ⟪A u, u⟫ ≤ ‖A u‖ * ‖u‖ := real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg u)
        _ ≤ (r ^ 2 * ‖u‖) * ‖u‖ := by gcongr
        _ = r ^ 2 * ‖u‖ ^ 2 := by ring
    calc
      _ ≤ b * ⟪A u, u⟫ := htransfer
      _ ≤ b * (r ^ 2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hinner hb
      _ = (b * r ^ 2) * ‖u‖ ^ 2 := by ring

end Localization

end FunctionalInequalities.KLS.BKL
