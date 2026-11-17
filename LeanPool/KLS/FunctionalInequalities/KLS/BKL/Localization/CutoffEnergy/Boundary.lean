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
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator

/-!
# Boundary control and horizon choice for cutoff energy
-/

@[expose] public section

noncomputable section
section BoundaryMeanValue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

/-! Boundary-term split for the ball cutoff and a mean-value choice of the horizon in `[T₀, 2T₀]`.
-/

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {p : ℝ → Ω → Param n}

private theorem measurable_path
    {γ : Param n → ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW γ p) (t : ℝ) :
    Measurable (p t) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have hm := Φ.symm.continuous.measurable.comp (hv.measurable t)
  change Measurable (fun w => Φ.symm (Φ (p t w))) at hm
  simpa only [Φ.symm_apply_apply] using hm

private theorem cumulantEnergy_nonneg
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun J _ => sq_nonneg _

private theorem exists_le_setIntegral_div
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Integrable f (volume.restrict (Set.Ioc T (2 * T)))) :
    ∃ t ∈ Set.Icc T (2 * T),
      f t ≤ (∫ s in Set.Ioc T (2 * T), f s) / T := by
  let S : Set ℝ := Set.Ioc T (2 * T)
  let ν : Measure ℝ := volume.restrict S
  let A : ℝ := (∫ s in S, f s) / T
  by_contra hn
  have hn' : ∀ t ∈ Set.Icc T (2 * T), A < f t := by
    intro t ht
    have hnot : ¬ f t ≤ A := by
      intro hle
      exact hn ⟨t, ht, hle⟩
    exact lt_of_not_ge hnot
  have hnonneg : 0 ≤ᵐ[ν] fun s => f s - A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact sub_nonneg.mpr (le_of_lt (hn' s hs'))
  have hfi : Integrable (fun s => f s - A) ν := by
    apply hf.sub
    exact integrable_const A
  have hsupport : S ⊆ Function.support (fun s => f s - A) := by
    intro s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact ne_of_gt (sub_pos.mpr (hn' s hs'))
  have hνS : 0 < ν S := by
    dsimp [ν, S]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_self, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hpos : 0 < ∫ s, f s - A ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae hnonneg hfi).2
    exact lt_of_lt_of_le hνS (measure_mono hsupport)
  have hmeasure : ν.real Set.univ = T := by
    dsimp [ν, S]
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsub :
      (∫ s in S, f s) - A * T = ∫ s, f s - A ∂ν := by
    rw [integral_sub hf (integrable_const A), integral_const]
    simp only [smul_eq_mul]
    rw [hmeasure]
    ring
  have hzero : (∫ s in S, f s) - A * T = 0 := by
    dsimp [A]
    field_simp [ne_of_gt hT]; ring
  linarith

/-- **Splitting the boundary term** of (93) for the ball cutoff: since `γ_R = 1` on `‖q‖ ≤ R`,
`E E_{d+1}(p_t) ≤ E[γ_R(p_t)² E_{d+1}(p_t)] + C · P(‖p_t‖ > R)` whenever `E_{d+1} ≤ C` on symmetric
PSD `Q`. -/
theorem IsEldanCutoff.integral_energy_le_weighted_add (hiso : KLS.Isotropic μ) {R : ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC :
      ∀ q : Param n,
        IsSelfAdjoint q.2 →
          (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
            cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                d u ≤
              C)
    (hcont :
      Continuous fun q : Param n =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ w,
        cumulantEnergy
          (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d
          u ∂P ≤
      (∫ w,
          ballCutoff R (p t w) ^ 2 *
            cumulantEnergy
              (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d
              u ∂P) +
        C * (P {w | R < ‖p t w‖}).toReal := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let A : Set Ω := {w | R < ‖p t w‖}
  have hpt : Measurable (p t) := measurable_path h t
  have hEm : Measurable (fun w => E (p t w)) := hcont.measurable.comp hpt
  have hAm : MeasurableSet A := by
    change MeasurableSet {w | R < ‖p t w‖}
    exact measurableSet_Ioi.preimage hpt.norm
  have hQ := h.ae_Q_posSemidef hiso (isCutoff_ballCutoff R)
  have hEb : ∀ᵐ w ∂P, ‖E (p t w)‖ ≤ C := by
    filter_upwards [hQ] with w hw
    have he := hC (p t w) (hw t ht).1 (hw t ht).2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(neg_nonpos.mpr hC0).trans (cumulantEnergy_nonneg _ _ _), he⟩
  have hEi : Integrable (fun w => E (p t w)) P := by
    apply Integrable.of_bound hEm.aestronglyMeasurable C
    exact hEb
  have hγm : Measurable (fun w => ballCutoff R (p t w)) :=
    (lipschitzWith_ballCutoff R).continuous.measurable.comp hpt
  have hwm : Measurable (fun w => ballCutoff R (p t w) ^ 2 * E (p t w)) :=
    (hγm.pow_const (2 : ℕ)).mul hEm
  have hwi : Integrable (fun w => ballCutoff R (p t w) ^ 2 * E (p t w)) P := by
    apply Integrable.of_bound hwm.aestronglyMeasurable C
    filter_upwards [hEb] with w hw
    have hg := ballCutoff_mem_Icc R (p t w)
    have he : 0 ≤ E (p t w) := cumulantEnergy_nonneg _ _ _
    have heC : E (p t w) ≤ C := (le_abs_self _).trans hw
    have h1 : 0 ≤ 1 - ballCutoff R (p t w) := sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + ballCutoff R (p t w) := add_nonneg zero_le_one hg.1
    have hg2 : ballCutoff R (p t w) ^ 2 ≤ 1 := by nlinarith [mul_nonneg h1 h2]
    have hle : ballCutoff R (p t w) ^ 2 * E (p t w) ≤ E (p t w) := by
      calc
        ballCutoff R (p t w) ^ 2 * E (p t w) ≤ 1 * E (p t w) :=
          mul_le_mul_of_nonneg_right hg2 he
        _ = E (p t w) := one_mul _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he)]
    exact hle.trans heC
  have hAi0 : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hAi : Integrable (fun w => C * A.indicator (fun _ : Ω => (1 : ℝ)) w) P :=
    hAi0.const_mul C
  have hpoint :
    ∀ᵐ w ∂P,
      E (p t w) ≤
        ballCutoff R (p t w) ^ 2 * E (p t w) + C * A.indicator (fun _ : Ω => (1 : ℝ)) w := by
    filter_upwards [hEb] with w hwC
    by_cases hwA : w ∈ A
    · have he : 0 ≤ E (p t w) := cumulantEnergy_nonneg _ _ _
      have heC : E (p t w) ≤ C := (le_abs_self _).trans hwC
      have hnonneg : 0 ≤ ballCutoff R (p t w) ^ 2 * E (p t w) := by
        exact mul_nonneg (sq_nonneg _) he
      have hind : A.indicator (fun _ : Ω => (1 : ℝ)) w = 1 := by simp [Set.indicator, hwA]
      rw [hind]
      linarith
    · have hwA' : ¬R < ‖p t w‖ := by
        intro hw'
        exact hwA (by simpa [A] using hw')
      have hR : ‖p t w‖ ≤ R := le_of_not_gt hwA'
      have hγ : ballCutoff R (p t w) = 1 := ballCutoff_eq_one hR
      simp [Set.indicator, hwA, hγ]
  have hind : ∫ w, A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P = (P A).toReal := by
    rw [integral_indicator hAm, setIntegral_const]
    simp [Measure.real, smul_eq_mul]
  calc
    ∫ w, E (p t w) ∂P ≤
        ∫ w,
          ballCutoff R (p t w) ^ 2 * E (p t w) + C * A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P :=
      integral_mono_ae hEi (hwi.add hAi) hpoint
    _ = (∫ w, ballCutoff R (p t w) ^ 2 * E (p t w) ∂P) + C * (P A).toReal := by
      rw [integral_add hwi hAi, integral_const_mul, hind]

/--
**Mean value in time** (the replacement for "let `T → ∞` along a subsequence", BKL p. 25): for a
cutoff
process and a continuous energy bounded on symmetric PSD `Q`, some `t ∈ [T₀, 2T₀]` has
`E[γ(p_t)² E_{d+1}(p_t)] ≤ I_{d+1}(2T₀) / T₀`, where `I_{d+1}(T) = ∫₀ᵀ E[γ² E_{d+1}(p_s)] ds`. -/
theorem IsEldanCutoff.exists_weighted_energy_le (hiso : KLS.Isotropic μ) {γ : Param n → ℝ}
    (hγ : IsCutoff γ) (h : IsEldanCutoff μ hc W ℱ hW γ p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC :
      ∀ q : Param n,
        IsSelfAdjoint q.2 →
          (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
            cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                d u ≤
              C)
    (hcont :
      Continuous fun q : Param n =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ t ∈ Set.Icc T₀ (2 * T₀),
      (∫ w,
          γ (p t w) ^ 2 *
            cumulantEnergy
              (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d
              u ∂P) ≤
        weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let F : ℝ → Ω → ℝ := fun s w => γ (p s w) ^ 2 * E (p s w)
  let f : ℝ → ℝ := fun s => ∫ w, F s w ∂P
  have hQ := h.ae_Q_posSemidef hiso hγ
  obtain ⟨Kγ, hγL⟩ := hγ.lipschitz
  have hFcont : Continuous (fun q => γ q ^ 2 * E q) := (hγL.continuous.pow 2).mul hcont
  have hFbound : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |F s w| ≤ C := by
    filter_upwards [hQ] with w hw
    intro s hs
    have he := hC (p s w) (hw s hs).1 (hw s hs).2
    have heC : E (p s w) ≤ C := by simpa [E] using he
    have he0 : 0 ≤ E (p s w) := cumulantEnergy_nonneg _ _ _
    have hg := hγ.mem_Icc (p s w)
    have h1 : 0 ≤ 1 - γ (p s w) := sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + γ (p s w) := add_nonneg zero_le_one hg.1
    have hg2 : γ (p s w) ^ 2 ≤ 1 := by nlinarith [mul_nonneg h1 h2]
    have hle : γ (p s w) ^ 2 * E (p s w) ≤ E (p s w) := by
      calc
        γ (p s w) ^ 2 * E (p s w) ≤ 1 * E (p s w) := mul_le_mul_of_nonneg_right hg2 he0
        _ = E (p s w) := one_mul _
    change |γ (p s w) ^ 2 * E (p s w)| ≤ C
    exact abs_le.mpr ⟨(neg_nonpos.mpr hC0).trans (mul_nonneg (sq_nonneg _) he0), hle.trans heC⟩
  have hjoint : Measurable (fun z : Ω × ℝ => F z.2 z.1) := by
    change Measurable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * E (p z.2 z.1))
    exact hFcont.measurable.comp h.measurable_uncurry_path
  have hprod :
    Integrable (fun z : Ω × ℝ => F z.2 z.1) (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
    constructor
    · filter_upwards [hFbound] with w hw
      apply Integrable.of_bound ((hFcont.comp (h.continuous w)).aestronglyMeasurable) C
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [F, Function.comp_apply, Real.norm_eq_abs] using hw s (hT₀.le.trans hs.1.le)
    · have hnormmeas :
        AEStronglyMeasurable (fun w => ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) P := by
        simpa only using hjoint.norm.aestronglyMeasurable.integral_prod_right'
      apply Integrable.of_bound hnormmeas (C * (2 * T₀ - T₀))
      filter_upwards [hFbound] with w hw
      have hnonneg : 0 ≤ ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀)) :=
        integral_nonneg (fun s => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        (∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) ≤ ∫ s in Set.Ioc T₀ (2 * T₀), C := by
          apply setIntegral_mono_on
          · exact (hFcont.comp (h.continuous w)).norm.integrableOn_Ioc
          · exact continuous_const.integrableOn_Ioc
          · exact measurableSet_Ioc
          · intro s hs
            simpa only [F, Function.comp_apply, Real.norm_eq_abs] using
              hw s (hT₀.le.trans hs.1.le)
        _ = C * (2 * T₀ - T₀) := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
          have hvol : (volume : Measure ℝ).real (Set.Ioc T₀ (2 * T₀)) = T₀ := by
            rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
            ring
          rw [hvol]
          ring
  have hfint : Integrable f (volume.restrict (Set.Ioc T₀ (2 * T₀))) := by
    change Integrable (fun s => ∫ w, F s w ∂P) (volume.restrict (Set.Ioc T₀ (2 * T₀)))
    exact hprod.integral_prod_right
  obtain ⟨t, ht, htf⟩ := exists_le_setIntegral_div hT₀ hfint
  have hprod' :
    Integrable (Function.uncurry (fun w s => F s w))
      (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    change
      Integrable (fun z : Ω × ℝ => F z.2 z.1) (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀))))
    exact hprod
  have hswap := integral_integral_swap hprod'
  have hfull :
    (∫ s in Set.Ioc T₀ (2 * T₀), f s) = ∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P := by
    simpa only [f, Function.uncurry] using hswap.symm
  have hlefti : Integrable (fun w => ∫ s in Set.Ioc T₀ (2 * T₀), F s w) P :=
    hprod.integral_prod_left
  have hrighti : Integrable (fun w => ∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) P := by
    simpa only [F] using
      h.integrable_integral_of_ae_bound hFcont hFbound (T := 2 * T₀) (by linarith)
  have houter :
    (∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P) ≤
      weightedEnergyIntegral μ hc P γ p d u (2 * T₀) := by
    have hmono :
      ∀ᵐ w ∂P, (∫ s in Set.Ioc T₀ (2 * T₀), F s w) ≤ (∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) := by
      filter_upwards [] with w
      apply setIntegral_mono_set
      · exact (hFcont.comp (h.continuous w)).integrableOn_Ioc
      · exact
          Filter.Eventually.of_forall
            (fun s => mul_nonneg (sq_nonneg _) (cumulantEnergy_nonneg _ _ _))
      · exact (Set.Ioc_subset_Ioc_left (by linarith)).eventuallySubset
    have hineq := integral_mono_ae hlefti hrighti hmono
    simpa only [weightedEnergyIntegral, F, E] using hineq
  refine ⟨t, ht, ?_⟩
  calc
    ∫ w,
          γ (p t w) ^ 2 *
            cumulantEnergy
              (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d
              u ∂P =
        f t := by
      rfl
    _ ≤ (∫ s in Set.Ioc T₀ (2 * T₀), f s) / T₀ := htf
    _ ≤ weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
      rw [hfull]
      exact div_le_div_of_nonneg_right houter hT₀.le

end FunctionalInequalities.KLS.BKL.Localization

end BoundaryMeanValue
