/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Conjugation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.EnergyForm
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Regularity

/-!
# Regularity of posterior cumulant energies
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL.Localization


variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

theorem contDiff_cumulantEnergy_posterior (hiso : KLS.Isotropic μ) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun q : Param n =>
      cumulantEnergy (compactPosterior μ hc q.1 q.2 :
        Measure (EuclideanSpace ℝ (Fin n))) d u) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let A : Param n → E →L[ℝ] E :=
    fun q => Covariance.operator (compactPosterior μ hc q.1 q.2 : Measure E)
  have hAi : ContDiff ℝ ∞ (fun q => Ring.inverse (A q)) := by
    simpa only [A] using
      KLS.Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
  have hT : ∀ J : Fin d → Fin n,
      ContDiff ℝ ∞ (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
          (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
    intro J
    exact contDiff_cumulant_posterior μ hc
      (Nat.one_le_iff_ne_zero.mpr (by omega))
      (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
  have hEq :
      (fun q : Param n =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure E) d u) =
      (fun q : Param n =>
        CoordinateTensor.energyForm (A q)
          (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)))) := by
    funext q
    calc
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure E) d u =
          CoordinateTensor.energyForm
            ((1 : E →L[ℝ] E) *
              Covariance.operator (compactPosterior μ hc q.1 q.2 : Measure E) *
              (1 : E →L[ℝ] E))
            (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
              (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
        exact cumulantEnergy_eq_energyForm
          (compactPosterior μ hc q.1 q.2 : Measure E)
          (by
            simpa only [A] using
              KLS.Isotropic.compactPosterior_covariance_isPositive μ hc hiso q.1 q.2)
          (by
            simpa only [A] using
              KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2)
          (1 : E →L[ℝ] E) (by simp) (by simp) d u
      _ = CoordinateTensor.energyForm (A q)
          (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
        simp only [one_mul, mul_one, A]
  rw [hEq]
  unfold CoordinateTensor.energyForm
  apply ContDiff.sum
  intro J hJ
  apply ContDiff.sum
  intro K hK
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact hT J
    · exact hT K
  · apply contDiff_prod
    intro s hs
    exact ContDiff.inner ℝ contDiff_const
      (hAi.clm_apply contDiff_const)

end FunctionalInequalities.KLS.BKL.Localization
