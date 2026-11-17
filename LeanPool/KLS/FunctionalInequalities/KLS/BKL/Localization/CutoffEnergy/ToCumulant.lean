/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Standardization
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Envelope
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Integral

/-!
# From cutoff energy claims to compact cumulant bounds
-/

@[expose] public section

noncomputable section
section CutoffEnergyToCumulantBound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

/-! From the cutoff energy claim to the compact cumulant bound. -/

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

/-- For an isotropic law the energy at the initial parameter is the standard-basis sum
`Σ_J κ_{d+1}(u, e_J)²` (`σ = Cov^(-1/2) = Id`). -/
theorem cumulantEnergy_eq_sum_sq_of_isotropic {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hiso : KLS.Isotropic μ) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u =
      ∑ J : Fin d → Fin n,
        cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
          2 := by
  have hsqrt :
    inverseSqrt (Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hiso.covariance_identity]
    change inverseSqrt (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = 1
    apply inverseSqrt_unique _ _ isUnit_one
    · exact ContinuousLinearMap.isPositive_one
    · simp
  simp only [cumulantEnergy, hsqrt, ContinuousLinearMap.id_apply]

/--
**From the cutoff claim to the cumulant bound** (BKL p. 27, `E_m(0) = ⟨R^μ_m u, u⟩`):
`CutoffEnergyClaim K d`
gives `CumulantBoundCompact d (envelope K (d + 1))`. -/
theorem cumulantBoundCompact_of_cutoffEnergyClaim {K : ℝ} (hK : 0 ≤ K) {d : ℕ}
    (h : CutoffEnergyClaim K d) :
    LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1)) := by
  classical
  unfold LogConcave.Suspension.CumulantBoundCompact
  intro m ν hiso hLC hc u
  by_cases hu0 : u = 0
  · subst u
    have hzero (J : Fin d → Fin m) :
      cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
          (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
            (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
        0 := by
      exact
        (cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_coord_zero 0 (by simp)
    calc
      ∑ J : Fin d → Fin m,
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
              2 =
          0 := by
        apply Finset.sum_eq_zero
        intro J _
        rw [hzero J]
        norm_num
      _ ≤ envelope K (d + 1) * ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 :=
        mul_nonneg (envelope_nonneg hK (d + 1)) (sq_nonneg _)
  · let v : EuclideanSpace ℝ (Fin m) := ‖u‖⁻¹ • u
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = ‖(‖u‖ : ℝ)⁻¹‖ * ‖u‖ := norm_smul _ _
        _ = ‖u‖⁻¹ * ‖u‖ := by rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
        _ = 1 := inv_mul_cancel₀ hnorm
    have huv : ‖u‖ • v = u := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hunitApprox (ε : ℝ) (hε : 0 < ε) :
      ∑ J : Fin d → Fin m,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
            2 ≤
        envelope K (d + 1) + ε := by
      obtain ⟨Ω, _, P, _, W, _⟩ :=
        FunctionalInequalities.Probability.Diffusion.exists_brownianSetup m
      let ℱ : Filtration ℝ ‹MeasurableSpace Ω› := usualFiltration W
      have hright : ℱ.IsRightContinuous := by
        dsimp [ℱ]
        infer_instance
      have hW : ∀ k, IsBrownianFiltration (W.W k) ℱ := by
        intro k
        change IsBrownianFiltration (W.W k) (usualFiltration W)
        exact usualFiltration_brownian W k
      have hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t := by
        intro t ht
        change usualFiltration W 0 ≤ usualFiltration W t
        exact usualFiltration_le_of_nonpos W t ht
      have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s := by
        intro s hs hPs
        change MeasurableSet[usualFiltration W 0] s
        exact usualFiltration_null W s hs hPs
      obtain ⟨R₀, hR₀⟩ := h m ν hc hiso hLC v hv ε hε 0 (by norm_num)
      obtain ⟨p, hp⟩ :=
        @exists_isEldanCutoff m ν hc hiso Ω _ P _ W ℱ hright hW hℱ0 hnull (ballCutoff R₀)
          (isCutoff_ballCutoff R₀)
      have hineq := hR₀ R₀ le_rfl W ℱ hW hℱ0 hnull hp
      have hzeroIntegral : weightedEnergyIntegral ν hc P (ballCutoff R₀) p (d + 1) v 0 = 0 := by
        simp [weightedEnergyIntegral]
      rw [hzeroIntegral, mul_zero, add_zero] at hineq
      calc
        ∑ J : Fin d → Fin m,
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                  (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
                2 =
            cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin m))) d v :=
          (cumulantEnergy_eq_sum_sq_of_isotropic ν hiso d v).symm
        _ ≤ envelope K (d + 1) + ε := hineq
    have hunit :
      ∑ J : Fin d → Fin m,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
            2 ≤
        envelope K (d + 1) := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have hhalf := hunitApprox (ε / 2) (by linarith)
      linarith
    have hscale (J : Fin d → Fin m) :
      cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
          (Fin.cons u (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
        ‖u‖ *
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
      calc
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons u (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Function.update (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0
                (‖u‖ • v)) := by
          rw [Fin.update_cons_zero, huv]
        _ =
            ‖u‖ •
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Function.update (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)))
                  0 v) :=
          (cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_update_smul
            (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0 ‖u‖ v
        _ =
            ‖u‖ *
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
          rw [Fin.update_cons_zero, smul_eq_mul]
    calc
      ∑ J : Fin d → Fin m,
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons u (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
              2 =
          ∑ J : Fin d → Fin m,
            ‖u‖ ^ 2 *
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                  (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
                2 := by
        apply Finset.sum_congr rfl
        intro J _
        rw [hscale, mul_pow]
      _ =
          ‖u‖ ^ 2 *
            ∑ J : Fin d → Fin m,
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                  (Fin.cons v (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
                2 := by
        rw [Finset.mul_sum]
      _ ≤ ‖u‖ ^ 2 * envelope K (d + 1) := mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖u‖)
      _ = envelope K (d + 1) * ‖u‖ ^ 2 := mul_comm _ _

/--
The envelope at order `d + 1` is the constant of `conjecture_of_cumulantBound`: `b_{d+1} = (d!)²
K^d`. -/
theorem envelope_succ_eq (K : ℝ) (d : ℕ) : envelope K (d + 1) = (d.factorial : ℝ) ^ 2 * K ^ d := by
  unfold envelope
  rw [Nat.add_sub_cancel]
  exact mul_comm _ _

end FunctionalInequalities.KLS.BKL.Localization

end CutoffEnergyToCumulantBound
