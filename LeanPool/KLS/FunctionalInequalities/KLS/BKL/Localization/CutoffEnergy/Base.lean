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
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Integral
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance

/-!
# The second-order base case of the cutoff energy claim
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

private theorem integral_le_of_nonneg_bound
    {α : Type*} [MeasurableSpace α] {M : Measure α} {f g : α → ℝ}
    (hg : Integrable g M)
    (hf : ∀ᵐ x ∂M, 0 ≤ f x)
    (hfg : ∀ᵐ x ∂M, f x ≤ g x) :
    ∫ x, f x ∂M ≤ ∫ x, g x ∂M := by
  by_cases hi : Integrable f M
  · exact integral_mono_ae hi hg hfg
  · rw [integral_undef hi]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hfg] with x hx hxy
    exact hx.trans hxy

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

private theorem cumulantEnergy_one_is_one (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u = 1 := by
  classical
  have hexp :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((1 : ℝ) * ‖x‖))
      (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_exp_of_compact μ hc (by fun_prop)
  have hsqrt :
    inverseSqrt (Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [compactPosterior_zero] using
      KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero μ hc hiso
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let e : Fin n ≃ (Fin 1 → Fin n) :=
    { toFun := fun j _ => j
      invFun := fun J => J 0
      left_inv := fun _ => rfl
      right_inv := by
        intro J
        funext i
        fin_cases i
        rfl }
  have hcum (j : Fin n) :
    cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 (Fin.cons u (fun _ : Fin 1 => b j)) =
      ⟪u, b j⟫ := by
    have h :=
      cumulant_two_eq_covariance_of_integrable_exp (μ : Measure (EuclideanSpace ℝ (Fin n)))
        (by norm_num) hexp u (b j)
    calc
      cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 (Fin.cons u (fun _ : Fin 1 => b j)) =
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 ![u, b j] := by
        congr 1
        funext i
        fin_cases i <;> rfl
      _ = ⟪Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n))) u, b j⟫ := h
      _ = ⟪u, b j⟫ := by
        rw [hiso.covariance_identity]
        rfl
  rw [cumulantEnergy, hsqrt]
  change
    ∑ J : Fin 1 → Fin n,
        cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 (Fin.cons u (fun k => b (J k))) ^
          2 =
      1
  calc
    ∑ J : Fin 1 → Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 (Fin.cons u (fun k => b (J k))) ^
            2 =
        ∑ j : Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
              (Fin.cons u (fun k => b ((e j) k))) ^
            2 :=
      (e.sum_comp
          (fun J : Fin 1 → Fin n =>
            cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
                (Fin.cons u (fun k => b (J k))) ^
              2)).symm
    _ =
        ∑ j : Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
              (Fin.cons u (fun _ : Fin 1 => b j)) ^
            2 :=
      rfl
    _ = ∑ j : Fin n, ⟪u, b j⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcum]
    _ = ∑ j : Fin n, ⟪u, b j⟫ * ⟪b j, u⟫ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) u]
      ring
    _ = ⟪u, u⟫ := b.sum_inner_mul_inner u u
    _ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hu]
      norm_num
/--
**Base case `m = 2`** (BKL p. 25, "the case m = 2 follows from (78)"): under the compact Letwin
bound and
`K ≥ 5`, `CutoffEnergyClaim K 1`. -/
theorem cutoffEnergyClaim_one (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ}
    (hK : 5 ≤ K) : CutoffEnergyClaim K 1 := by
  classical
  intro n μ hc hiso hLC u hu ε hε T hT
  refine ⟨0, ?_⟩
  intro R _hR Ω _ P _ W ℱ hW hℱ0 hnull p hp
  let F : Param n → ℝ := fun q => ⟪cov μ hc q u, u⟫
  let G : Param n → ℝ := fun q => ballCutoff R q ^ 2 * F q
  let H : Param n → ℝ := fun q =>
    ballCutoff R q ^ 2 *
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 u
  have hγ : IsCutoff (ballCutoff (V := Param n) R) := isCutoff_ballCutoff R
  have hcov : ContDiff ℝ 2 (cov μ hc) :=
    (contDiff_posteriorCovariance_joint μ hc).of_le (WithTop.coe_le_coe.mpr le_top)
  have hF : ContDiff ℝ 2 F := by
    have hh : ContDiff ℝ 2 (fun q : Param n => ⟪u, cov μ hc q u⟫) :=
      (innerSL ℝ u).contDiff.comp (hcov.clm_apply contDiff_const)
    simpa only [F, real_inner_comm] using hh
  have hFpos (q : Param n) : 0 ≤ F q :=
    (KLS.Isotropic.compactPosterior_covariance_isPositive μ hc hiso q.1 q.2).inner_nonneg_left u
  have hGcont : Continuous G :=
    ((lipschitzWith_ballCutoff R).continuous.pow 2).mul hF.continuous
  have hGpos (q : Param n) : 0 ≤ G q := mul_nonneg (sq_nonneg _) (hFpos q)
  have hHpos (q : Param n) : 0 ≤ H q := by
    dsimp only [H, cumulantEnergy]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  obtain ⟨r, hr⟩ := hc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  let r' : ℝ := max r 0
  have hr' : 0 ≤ r' := le_max_right _ _
  have hrsupp :
    (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r' := by
    intro x hx
    have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall_zero_iff] using hr hx
    simpa only [mem_closedBall_zero_iff] using hxnorm.trans (le_max_left r 0)
  have hFbound (q : Param n) : F q ≤ r' ^ 2 := by
    have hnorm : ‖cov μ hc q u‖ ≤ ‖cov μ hc q‖ := by
      simpa only [hu, mul_one] using (cov μ hc q).le_opNorm u
    calc
      F q ≤ ‖cov μ hc q u‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖cov μ hc q u‖ := by rw [hu, mul_one]
      _ ≤ ‖cov μ hc q‖ := hnorm
      _ ≤ r' ^ 2 := KLS.opNorm_covariance_compactPosterior_le_sq_radius μ hc hr' hrsupp q.1 q.2
  have hGbound (q : Param n) : G q ≤ r' ^ 2 := by
    have hg := ballCutoff_mem_Icc R q
    have hsq : ballCutoff R q ^ 2 ≤ 1 := by nlinarith [hg.1, hg.2]
    calc
      G q ≤ 1 * (r' ^ 2) := mul_le_mul hsq (hFbound q) (hFpos q) zero_le_one
      _ = r' ^ 2 := one_mul _
  have hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |8 * G (p s ω)| ≤ 8 * r' ^ 2 := by
    filter_upwards [] with ω
    intro s _hs
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (hGpos _))]
    exact mul_le_mul_of_nonneg_left (hGbound _) (by norm_num)
  have hupperInt : Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω)) P :=
    hp.integrable_integral_of_ae_bound (continuous_const.mul hGcont) hB hT
  have h8 : LogConcave.Suspension.CumulantBoundCompact 2 8 :=
    LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact hL
  have hq := IsEldanCutoff.ae_Q_posSemidef (μ := μ) (hc := hc) hiso hγ hp
  have hbound : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → H (p s ω) ≤ 8 * G (p s ω) := by
    filter_upwards [hq] with ω hω
    intro s hs
    have hcumul :=
      KLS.compactPosterior_cumulant_bound μ hc hiso hLC (d := 2) (b := 8) (p s ω).1 (p s ω).2
        (hω s hs).1 (hω s hs).2 (by norm_num) h8 u
    calc
      H (p s ω) ≤ ballCutoff R (p s ω) ^ 2 * (8 * F (p s ω)) :=
        mul_le_mul_of_nonneg_left hcumul (sq_nonneg _)
      _ = 8 * G (p s ω) := by
        dsimp only [G]
        ring
  have hmono :
    (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω) ∂volume ∂P := by
    apply integral_le_of_nonneg_bound hupperInt
    · exact Filter.Eventually.of_forall fun ω => integral_nonneg fun s => hHpos (p s ω)
    · filter_upwards [hbound] with ω hω
      apply
        integral_le_of_nonneg_bound
          (((continuous_const.mul hGcont).comp (hp.continuous ω)).integrableOn_Ioc)
      · exact Filter.Eventually.of_forall fun s => hHpos (p s ω)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hω s hs.1.le
  have hmono' :
    weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤
      8 * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P := by
    change (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤ _
    simpa only [integral_const_mul] using hmono
  have hdyn := IsEldanCutoff.dynkin (μ := μ) (hc := hc) hiso hγ hℱ0 hnull hp hF hT
  have hgenq (q : Param n) : generator μ hc F q = -F q := generator_inner_cov μ hc hiso q u u
  have hgen :
    (∫ ω, F (p T ω) ∂P) - F 0 = -(∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P) := by
    simpa only [hgenq, mul_neg, integral_neg] using hdyn.2
  have hinit : F 0 = 1 := by
    change
      ⟪Covariance.operator (compactPosterior μ hc 0 0 : Measure (EuclideanSpace ℝ (Fin n))) u,
          u⟫ =
        1
    rw [compactPosterior_zero, hiso.covariance_identity]
    change ⟪u, u⟫ = 1
    rw [real_inner_self_eq_norm_mul_norm, hu]
    norm_num
  have hEF : 0 ≤ ∫ ω, F (p T ω) ∂P := integral_nonneg fun ω => hFpos (p T ω)
  have hupper : weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤ 8 := by
    linarith [hmono', hgen, hinit, hEF]
  have hzero := cumulantEnergy_one_is_one μ hc hiso u hu
  change
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u +
        (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤
      envelope K 2 + ε
  rw [hzero]
  have henvelope : envelope K 2 = K := by simp [envelope]
  rw [henvelope]
  linarith

end FunctionalInequalities.KLS.BKL.Localization
