/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Gronwall
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Integral
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
/-!
# Lyapunov moment bound for the cutoff Eldan process

Gronwall bound `E 𝒱(p_t) ≤ 𝒱(p_0) e^{Kt}` along a ball-cutoff Eldan process, from a generator bound
`L𝒱 ≤ K𝒱`
taken as a hypothesis, and the resulting Markov tail bound (BKL Section 5).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

theorem IsEldanCutoff.integral_lyapunov_le (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => lyapunov μ hc (p t ω)) P ∧
      ∫ ω, lyapunov μ hc (p t ω) ∂P ≤ lyapunov μ hc 0 * Real.exp (K * t) := by
  classical

  -- Define the Lyapunov observable along the actual cutoff process.
  let F : Param n → ℝ := lyapunov μ hc
  let g : Param n → ℝ := fun q => γ q ^ 2 * generator μ hc F q
  let φ : ℝ → ℝ := fun s => ∫ ω, F (p s ω) ∂P
  have hF : ContDiff ℝ 2 F :=
    (contDiff_lyapunov μ hc hiso).of_le (WithTop.coe_le_coe.mpr le_top)
  have hF3 : ContDiff ℝ 3 F :=
    (contDiff_lyapunov μ hc hiso).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγc : Continuous γ :=
    hγ.lipschitz.choose_spec.continuous
  have hgen : Continuous (generator μ hc F) :=
    continuous_generator_of_contDiff_three μ hc hiso hF3
  have hgc : Continuous g :=
    (hγc.pow 2).mul hgen
  have hgcs : HasCompactSupport g := by
    refine hγ.compactSupport.mono ?_
    intro q hq
    by_contra hqγ
    have hγq : γ q = 0 := by
      exact not_ne_iff.mp hqγ
    exact hq (by simp [g, hγq])
  obtain ⟨B₀, hB₀⟩ := hgc.bounded_above_of_compact_support hgcs
  let B : ℝ := max B₀ 0
  have hB : ∀ q : Param n, ‖g q‖ ≤ B := by
    intro q
    exact (hB₀ q).trans (le_max_left _ _)
  have hB0 : 0 ≤ B :=
    le_max_right _ _
  have hgb : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |g (p s ω)| ≤ B := by
    filter_upwards [] with ω s hs
    simpa only [Real.norm_eq_abs] using hB (p s ω)

  -- Apply the cutoff Dynkin identity.
  have hdyn (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun ω => F (p s ω)) P ∧
        φ s - F 0 =
          ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
    simpa only [F, g, φ, diffusionGenerator_cutoff] using
      h.dynkin hiso hγ hℱ0 hnull hF hs
  have hinner_bound (s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
      ‖∫ r in Set.Ioc (0 : ℝ) s, g (p r ω)‖ ≤ B * s := by
    calc
      ‖∫ r in Set.Ioc (0 : ℝ) s, g (p r ω)‖ ≤
          ∫ r in Set.Ioc (0 : ℝ) s, ‖g (p r ω)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r in Set.Ioc (0 : ℝ) s, B := by
        apply setIntegral_mono_on
        · exact (hgc.comp (h.continuous ω)).norm.integrableOn_Ioc
        · exact continuous_const.integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro r hr
          exact hB (p r ω)
      _ = B * s := by
        simp [hs]
        ring
  have hphi_bound (s : ℝ) (hs : 0 ≤ s) :
      |φ s| ≤ F 0 + B * s := by
    have hout₀ :=
      norm_integral_le_of_norm_le_const
        (μ := P)
        (f := fun ω => ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω))
        (C := B * s)
        (Filter.Eventually.of_forall (hinner_bound s hs))
    have hout :
        ‖∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P‖ ≤ B * s := by
      simpa [Measure.real_def, IsProbabilityMeasure.measure_univ] using hout₀
    have heq :
        φ s = F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
      linarith [(hdyn s hs).2]
    rw [heq]
    calc
      |F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P| ≤
          |F 0| + ‖∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P‖ :=
        abs_add_le _ _
      _ ≤ F 0 + B * s := by
        have hF0 : 0 ≤ F 0 := by
          exact le_trans (by norm_num) (one_le_lyapunov μ hc 0)
        rw [abs_of_nonneg hF0]
        linarith
  have hphib : ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) t, |φ s| ≤ C := by
    refine ⟨F 0 + B * t, ?_⟩
    intro s hs
    have hst : B * s ≤ B * t :=
      mul_le_mul_of_nonneg_left hs.2 hB0
    linarith [hphi_bound s hs.1]
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  have h' := h
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h'
  obtain ⟨_, _, _, hv⟩ := h'
  have h1 : Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun ω s => Φ (p s ω)))
    exact hv.measurable_uncurry
  have hpmeas : Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
    have h2 := Φ.symm.continuous.measurable.comp h1
    change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h2
    simpa only [Φ.symm_apply_apply] using h2
  have hmF : Measurable (fun z : Ω × ℝ => F (p z.2 z.1)) :=
    hF.continuous.measurable.comp hpmeas
  have hphim : Measurable φ := by
    have hs := hmF.stronglyMeasurable.integral_prod_left' (μ := P)
    simpa only [φ] using hs.measurable
  have hprodF (u : ℝ) (hu : 0 ≤ u) :
      Integrable
        (fun z : Ω × ℝ => F (p z.2 z.1))
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) u))) := by
    let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) u)
    change Integrable (fun z : Ω × ℝ => F (p z.2 z.1)) (P.prod ν)
    rw [integrable_prod_iff'
      (h1f := hmF.stronglyMeasurable.aestronglyMeasurable)]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hdyn s hs.1.le).1
    · have hnormm :
          Measurable (fun z : Ω × ℝ => ‖F (p z.2 z.1)‖) :=
        hmF.norm
      have hnormsm :
          AEStronglyMeasurable
            (fun s => ∫ ω, ‖F (p s ω)‖ ∂P) ν :=
        hnormm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
      apply Integrable.of_bound hnormsm (F 0 + B * u)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs0 : 0 ≤ s := hs.1.le
      have hnormeq :
          (∫ ω, ‖F (p s ω)‖ ∂P) = φ s := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg]
        change 0 ≤ lyapunov μ hc (p s ω)
        exact le_trans (by norm_num) (one_le_lyapunov μ hc _)
      have hφnonneg : 0 ≤ φ s := by
        rw [← hnormeq]
        exact integral_nonneg (fun ω => norm_nonneg _)
      rw [hnormeq, Real.norm_eq_abs, abs_of_nonneg hφnonneg]
      have hsu : B * s ≤ B * u :=
        mul_le_mul_of_nonneg_left hs.2 hB0
      linarith [hphi_bound s hs0, le_abs_self (φ s)]
  have hswapF (u : ℝ) (hu : 0 ≤ u) :
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P =
        ∫ s in Set.Ioc (0 : ℝ) u, φ s := by
    simpa only [φ] using
      integral_integral_swap (hprodF u hu)
  have hmono (u : ℝ) (hu : 0 ≤ u) :
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ∂volume ∂P ≤
        K * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P := by
    -- Use positivity and the generator bound in the scalar integral inequality.
    have hQ := h.ae_Q_posSemidef hiso hγ
    have hle :
        ∀ᵐ ω ∂P, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ≤
          K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) := by
      filter_upwards [hQ] with ω hω
      have hset :
          ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ≤
            ∫ s in Set.Ioc (0 : ℝ) u, K * F (p s ω) := by
        apply setIntegral_mono_on
        · exact (hgc.comp (h.continuous ω)).integrableOn_Ioc
        · exact
            (continuous_const.mul
              (hF.continuous.comp (h.continuous ω))).integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro s hs
          have hq := hω s hs.1.le
          have hgen' :
              generator μ hc F (p s ω) ≤ K * F (p s ω) := by
            simpa only [F] using hK (p s ω) hq.1 hq.2
          have hγ0 : 0 ≤ γ (p s ω) :=
            (hγ.mem_Icc (p s ω)).1
          have hγ1 : γ (p s ω) ≤ 1 :=
            (hγ.mem_Icc (p s ω)).2
          have hγsq : γ (p s ω) ^ 2 ≤ 1 := by
            nlinarith [mul_nonneg hγ0 (sub_nonneg.mpr hγ1)]
          by_cases hg : 0 ≤ generator μ hc F (p s ω)
          · dsimp [g]
            calc
              γ (p s ω) ^ 2 * generator μ hc F (p s ω) ≤
                  generator μ hc F (p s ω) := by
                nlinarith [mul_le_mul_of_nonneg_right hγsq hg]
              _ ≤ K * F (p s ω) := hgen'
          · have hleft :
                g (p s ω) ≤ 0 := by
              dsimp [g]
              exact
                mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
                  (le_of_not_ge hg)
            have hright : 0 ≤ K * F (p s ω) := by
              exact
                mul_nonneg hK0
                  (le_trans (by norm_num) (one_le_lyapunov μ hc _))
            exact hleft.trans hright
      rw [integral_const_mul] at hset
      exact hset
    have hgi :=
      h.integrable_integral_of_ae_bound hgc hgb hu
    have hFi :
        Integrable
          (fun ω => ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω))
          P := by
      simpa using (hprodF u hu).integral_prod_left
    have hKFi :
        Integrable
          (fun ω => K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω))
          P :=
      hFi.const_mul K
    calc
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ∂volume ∂P ≤
          ∫ ω, K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P :=
        integral_mono_ae hgi hKFi hle
      _ = K * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P := by
        rw [integral_const_mul]
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) t,
      φ s ≤ F 0 + K * ∫ r in Set.Ioc (0 : ℝ) s, φ r := by
    intro s hs
    have hd := hdyn s hs.1
    have hm := hmono s hs.1
    have hswap := hswapF s hs.1
    calc
      φ s =
          F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
        linarith [hd.2]
      _ ≤ F 0 + K * ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, F (p r ω) ∂volume ∂P := by
        linarith [hm]
      _ = F 0 + K * ∫ r in Set.Ioc (0 : ℝ) s, φ r := by
        rw [hswap]
  have hgr := le_mul_exp_of_le_add_integral hK0 hphim hphib hineq
  have hbound := hgr t ⟨ht, le_rfl⟩
  have hIt := (hdyn t ht).1
  constructor
  · simpa only [F] using hIt
  · simpa only [φ, F] using hbound

theorem IsEldanCutoff.measure_norm_gt_le (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (hR : 0 < R) :
    (P {ω | R < ‖p t ω‖}).toReal ≤ lyapunov μ hc 0 * Real.exp (K * t) / R ^ 2 := by
  classical
  obtain ⟨hInt, hmean⟩ :=
    h.integral_lyapunov_le hiso hγ hℱ0 hnull hK0 hK ht
  have hnonneg :
      0 ≤ᵐ[P] (fun ω => lyapunov μ hc (p t ω)) := by
    filter_upwards [] with ω
    exact le_trans (by norm_num) (one_le_lyapunov μ hc _)
  have hmarkov :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hInt (R ^ 2)
  have hsub :
      {ω | R < ‖p t ω‖} ⊆
        {ω | R ^ 2 ≤ lyapunov μ hc (p t ω)} := by
    intro ω hω
    have hsq : R ^ 2 < ‖p t ω‖ ^ 2 := by
      nlinarith [
        mul_pos (sub_pos.mpr hω)
          (add_pos_of_nonneg_of_pos (norm_nonneg (p t ω)) hR)]
    exact
      (le_of_lt hsq).trans
        (norm_sq_le_lyapunov μ hc (p t ω))
  have hmeasure :
      (P {ω | R < ‖p t ω‖}).toReal ≤
        (P {ω | R ^ 2 ≤ lyapunov μ hc (p t ω)}).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top P _
    · exact measure_mono hsub
  have hprob :
      (R ^ 2) *
          (P {ω | R ^ 2 ≤ lyapunov μ hc (p t ω)}).toReal ≤
        ∫ ω, lyapunov μ hc (p t ω) ∂P := by
    simpa only [Measure.real_def] using hmarkov
  have hprob' :
      (P {ω | R < ‖p t ω‖}).toReal * R ^ 2 ≤
        lyapunov μ hc 0 * Real.exp (K * t) := by
    calc
      (P {ω | R < ‖p t ω‖}).toReal * R ^ 2 =
          R ^ 2 * (P {ω | R < ‖p t ω‖}).toReal := by ring
      _ ≤ R ^ 2 *
          (P {ω | R ^ 2 ≤ lyapunov μ hc (p t ω)}).toReal :=
        mul_le_mul_of_nonneg_left hmeasure (sq_nonneg R)
      _ ≤ lyapunov μ hc 0 * Real.exp (K * t) := hprob.trans hmean
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  exact (le_div_iff₀ hR2).mpr hprob'

end FunctionalInequalities.KLS.BKL.Localization
