/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Integral
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Envelope
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Integral
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
/-!
# The induction step of BKL Theorem 4.1 in cutoff form

`cutoffEnergyClaim_succ`: the cutoff energy claim (95) at order `m` from the lower orders, combining
Lemma 5.2 in
cutoff form (`KLS/BKL/Localization/Energy/Integral.lean`), the Section 6 bound (104),
the Lyapunov moment and tail bounds,
the boundary
mean-value step and the envelope arithmetic (105)–(106) (BKL arXiv:2610.05474v1, pp. 24–27).
Lemma 5.1 enters as the named hypothesis `Lemma51Bound`, the exact statement of
`generator_cumulantEnergy_ge`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

/--
**BKL Lemma 5.1 as a hypothesis** (its generator form with `C = 17`, in every dimension): for every
compactly
supported isotropic log-concave prior with the third-order bound (79), every `m = r + 1 ≥ 3`,
direction `u` and
parameter with symmetric PSD `Q`,
`½ E_{m+1} − 17 m² E_m − 2 ⟨κ_m(u), L_m(u)⟩ ≤ 𝓛 E_m`. Discharged by `generator_cumulantEnergy_ge`
once that is canonical. -/
def Lemma51Bound : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    KLS.Isotropic μ →
      KLS.LogConcave μ →
        LogConcave.Suspension.CumulantBoundCompact 2 8 →
          ∀ (r : ℕ),
            2 ≤ r →
              ∀ (u : EuclideanSpace ℝ (Fin n)) (q : Param n),
                IsSelfAdjoint q.2 →
                  (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
                    (1 / 2 : ℝ) *
                            cumulantEnergy
                              (compactPosterior μ hc q.1 q.2 :
                                Measure (EuclideanSpace ℝ (Fin n)))
                              (r + 1) u -
                          17 * ((r : ℝ) + 1) ^ 2 *
                            cumulantEnergy
                              (compactPosterior μ hc q.1 q.2 :
                                Measure (EuclideanSpace ℝ (Fin n)))
                              r u -
                        2 *
                          ∑ K : Fin r → Fin n,
                            cumulant
                                (compactPosterior μ hc q.1 q.2 :
                                  Measure (EuclideanSpace ℝ (Fin n)))
                                (r + 1)
                                (Fin.cons u fun s =>
                                  inverseSqrt (cov μ hc q)
                                    (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
                              lowerDrift
                                (compactPosterior μ hc q.1 q.2 :
                                  Measure (EuclideanSpace ℝ (Fin n)))
                                (Fin.cons u fun s =>
                                  inverseSqrt (cov μ hc q)
                                    (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
                                0 ≤
                      generator μ hc
                        (fun q' : Param n =>
                          cumulantEnergy
                            (compactPosterior μ hc q'.1 q'.2 :
                              Measure (EuclideanSpace ℝ (Fin n)))
                            r u)
                        q

private theorem energy_nonneg_aux {n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private def inductionMain (K : ℝ) (m : ℕ) (δ : ℝ) : ℝ :=
  17 * (m : ℝ) ^ 2 * (2 * (envelope K (m - 1) + δ)) +
    2 * ∑ a ∈ Finset.Icc 2 (m - 2),
      ((m - 1).choose (a - 1) : ℝ) *
        Real.sqrt (envelope K (m - a + 1)) *
        (Real.sqrt (2 * (envelope K (m - 1) + δ)) *
          Real.sqrt (2 * (envelope K a + δ)))

private theorem sqrt_two_mul_aux (x y : ℝ) :
    Real.sqrt (2 * x) * Real.sqrt (2 * y) =
      2 * (Real.sqrt x * Real.sqrt y) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 * Real.sqrt x * (Real.sqrt 2 * Real.sqrt y) =
        Real.sqrt 2 ^ 2 * (Real.sqrt x * Real.sqrt y) := by ring
    _ = 2 * (Real.sqrt x * Real.sqrt y) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem inductionMain_zero_le {K : ℝ} (hK : 153 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    inductionMain K m 0 ≤ envelope K m := by
  have hK0 : 0 ≤ K := by linarith
  have hb (j : ℕ) : 0 ≤ envelope K j := envelope_nonneg hK0 j
  have hsum :
      (∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) *
          Real.sqrt (envelope K (m - a + 1)) *
          (Real.sqrt (2 * envelope K (m - 1)) *
            Real.sqrt (2 * envelope K a))) =
      (2 * Real.sqrt (envelope K (m - 1))) *
        ∑ a ∈ Finset.Icc 2 (m - 2),
          ((m - 1).choose (a - 1) : ℝ) *
            Real.sqrt (envelope K a * envelope K (m - a + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [sqrt_two_mul_aux, Real.sqrt_mul (hb a)]
    ring
  have habs := absorption_le_envelope (K := K) (C := 17)
    (by norm_num) (by linarith) (by linarith) hm
  rw [Real.sqrt_mul (hb (m - 1))] at habs
  unfold inductionMain
  simp only [add_zero]
  rw [hsum, sum_choose_mul_sqrt_envelope hK0 hm]
  nlinarith only [habs]

private theorem inductionMain_continuous (K : ℝ) (m : ℕ) :
    Continuous (inductionMain K m) := by
  unfold inductionMain
  fun_prop

private theorem exists_positive_small_aux {f : ℝ → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ f δ < f 0 + ε := by
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), f x < f 0 + ε :=
    hf.continuousAt.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η / 2, by positivity, he ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < η / 2)]
  linarith

private theorem weightedEnergyIntegral_mono_aux
    {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support}
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆
      Metric.closedBall 0 ρ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    {R : ℝ} {p : ℝ → Ω → Param n}
    (hp : IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p)
    (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    weightedEnergyIntegral μ hc P (ballCutoff R) p d u S ≤
      weightedEnergyIntegral μ hc P (ballCutoff R) p d u T := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy
      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let F : Param n → ℝ := fun q => ballCutoff R q ^ 2 * E q
  have hE : Continuous E :=
    (contDiff_cumulantEnergy_posterior μ hc hiso d u).continuous
  have hF : Continuous F :=
    ((lipschitzWith_ballCutoff R).continuous.pow 2).mul hE
  have hE0 (q : Param n) : 0 ≤ E q := energy_nonneg_aux _ _ _
  have hF0 (q : Param n) : 0 ≤ F q :=
    mul_nonneg (sq_nonneg _) (hE0 q)
  obtain ⟨C, _, hC⟩ := exists_cumulantEnergy_le μ hc hiso hLC hρ hsupp d
  have hQ := hp.ae_Q_posSemidef hiso (isCutoff_ballCutoff R)
  have hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |F (p s w)| ≤ C * ‖u‖ ^ 2 := by
    filter_upwards [hQ] with w hw
    intro s hs
    have hg := ballCutoff_mem_Icc R (p s w)
    have hg2 : ballCutoff R (p s w) ^ 2 ≤ 1 := by
      nlinarith [hg.1, hg.2]
    rw [abs_of_nonneg (hF0 _)]
    calc
      F (p s w) ≤ 1 * E (p s w) :=
        mul_le_mul_of_nonneg_right hg2 (hE0 _)
      _ ≤ C * ‖u‖ ^ 2 := by
        simpa only [one_mul] using hC (p s w) (hw s hs).1 (hw s hs).2 u
  change (∫ w, ∫ s in Set.Ioc (0 : ℝ) S, F (p s w) ∂volume ∂P) ≤
    ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, F (p s w) ∂volume ∂P
  apply integral_mono
    (hp.integrable_integral_of_ae_bound hF hB hS)
    (hp.integrable_integral_of_ae_bound hF hB (hS.trans hST))
  intro w
  apply setIntegral_mono_set ((hF.comp (hp.continuous w)).integrableOn_Ioc)
  · exact Filter.Eventually.of_forall fun s => hF0 (p s w)
  · filter_upwards [] with s hs
    exact ⟨hs.1, hs.2.trans hST⟩

/--
**The inductive step of BKL Section 6, (95)–(106), in cutoff form**: under the compact Letwin bound,
Lemma 5.1
(as the hypothesis `Lemma51Bound`) and `K ≥ max {5, 9·17, 64}`, if the cutoff claim and the
pointwise cumulant
bound hold at all orders `2 ≤ r < m` (`m ≥ 3`), then the cutoff claim holds at order `m`. -/
theorem cutoffEnergyClaim_succ (hL : LogConcave.Suspension.LetwinCompactBound)
    (h51 : Lemma51Bound) {K : ℝ} (hK : 153 ≤ K) {m : ℕ} (hm : 3 ≤ m)
    (ih : ∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1))
    (ihb :
      ∀ r : ℕ,
        2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) :
    CutoffEnergyClaim K (m - 1) := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hr : 2 ≤ r := by omega
  have hK0 : 0 ≤ K := by linarith
  have hb (j : ℕ) : 0 ≤ envelope K j := envelope_nonneg hK0 j
  have h8 : LogConcave.Suspension.CumulantBoundCompact 2 8 :=
    LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact hL
  change CutoffEnergyClaim K r
  intro n μ hc hiso hLC u hu ε hε T hT
  obtain ⟨ρ, hρpos, hsupp⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hρ : 0 ≤ ρ := hρpos.le

  -- Obtain the lower-order bounds needed by the induction step.
  obtain ⟨KL, hKL0, hKL⟩ := exists_generator_lyapunov_le μ hc hiso hLC h8 hρ hsupp
  obtain ⟨C, hC0, hCall⟩ := exists_cumulantEnergy_le μ hc hiso hLC hρ hsupp r
  have hC (q : Param n) (hS : IsSelfAdjoint q.2) (hQ : ∀ x, 0 ≤ ⟪q.2 x, x⟫) :
    cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u ≤
      C := by
    simpa only [hu, one_pow, mul_one] using hCall q hS hQ u
  have hcont :
    Continuous
      (fun q : Param n =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r
          u) :=
    (contDiff_cumulantEnergy_posterior μ hc hiso r u).continuous
  obtain ⟨δ, hδ, hδlt⟩ :=
    exists_positive_small_aux (inductionMain_continuous K (r + 1))
      (show 0 < ε / 3 by positivity)
  have hδmain : inductionMain K (r + 1) δ ≤ envelope K (r + 1) + ε / 3 := by
    have hz := inductionMain_zero_le hK hm
    linarith

  -- Choose the time and spatial cutoffs before estimating their errors.
  let T₀ : ℝ := max (max T 1) (6 * (envelope K r + δ) / ε)
  have hT₀one : 1 ≤ T₀ := (le_max_right T 1).trans (le_max_left _ _)
  have hT₀T : T ≤ T₀ := (le_max_left T 1).trans (le_max_left _ _)
  have hT₀ : 0 < T₀ := lt_of_lt_of_le zero_lt_one hT₀one
  have h2T₀ : 0 ≤ 2 * T₀ := by positivity
  have htime : 2 * (envelope K r + δ) / T₀ ≤ ε / 3 := by
    have hlarge : 6 * (envelope K r + δ) / ε ≤ T₀ := le_max_right _ _
    have hlarge' := (div_le_iff₀ hε).mp hlarge
    apply (div_le_iff₀ hT₀).mpr
    nlinarith only [hlarge']
  let Ra (a : ℕ) : ℝ :=
    if ha : 2 ≤ a ∧ a < r + 1 then
      Classical.choose (ih a ha.1 ha.2 n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀)
    else 0
  let s : Finset ℕ := Finset.Icc 2 r
  have hs : s.Nonempty := ⟨r, Finset.mem_Icc.mpr ⟨hr, le_rfl⟩⟩
  let RI : ℝ := s.sup' hs Ra
  have hV0 : 0 ≤ lyapunov μ hc 0 := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_lyapunov μ hc 0)
  let D : ℝ := C * (lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)))
  have hD : 0 ≤ D := mul_nonneg hC0 (mul_nonneg hV0 (Real.exp_pos _).le)
  let RM : ℝ := Real.sqrt (3 * D / ε) + 1
  have hRMpos : 0 < RM := by
    dsimp only [RM]
    positivity
  refine ⟨max RI RM, ?_⟩
  intro R hR Ω _ P _ W ℱ hW hℱ0 hnull p hp
  have hRI : RI ≤ R := (le_max_left _ _).trans hR
  have hRM : RM ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := hRMpos.trans_le hRM
  have hRerr : D / R ^ 2 ≤ ε / 3 := by
    have hrad : 0 ≤ 3 * D / ε := by positivity
    have hsqrtR : Real.sqrt (3 * D / ε) ≤ R := by
      have : Real.sqrt (3 * D / ε) + 1 ≤ R := hRM
      linarith
    have hsq : 3 * D / ε ≤ R ^ 2 := by
      calc
        3 * D / ε = Real.sqrt (3 * D / ε) ^ 2 := (Real.sq_sqrt hrad).symm
        _ ≤ R ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hRpos.le).mpr hsqrtR
    have hsq' := (div_le_iff₀ hε).mp hsq
    apply (div_le_iff₀ (sq_pos_of_pos hRpos)).mpr
    nlinarith only [hsq']
  have hγ : IsCutoff (ballCutoff (V := Param n) R) := isCutoff_ballCutoff R
  have hI (a : ℕ) (ha2 : 2 ≤ a) (har : a < r + 1) :
    weightedEnergyIntegral μ hc P (ballCutoff R) p a u (2 * T₀) ≤ 2 * (envelope K a + δ) := by
    have ha : 2 ≤ a ∧ a < r + 1 := ⟨ha2, har⟩
    have hamem : a ∈ s := Finset.mem_Icc.mpr ⟨ha2, by omega⟩
    have hRa : Ra a ≤ R := (Finset.le_sup' Ra hamem).trans hRI
    have hthreshold :=
      Classical.choose_spec (ih a ha2 har n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀)
    have hRa' : Classical.choose (ih a ha2 har n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀) ≤ R := by
      simpa only [Ra, dite_eq_left ha] using hRa
    have hclaim := hthreshold R hRa' W ℱ hW hℱ0 hnull hp
    have hindex : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
    rw [hindex] at hclaim

    -- Apply the energy estimate and bound the lower-order recurrence terms.
    have hnonneg := energy_nonneg_aux (μ : Measure (EuclideanSpace ℝ (Fin n))) (a - 1) u
    linarith
  obtain ⟨t, ht, hmean⟩ :=
    IsEldanCutoff.exists_weighted_energy_le hiso hγ hp r u hC0 hC hcont hT₀
  have ht0 : 0 ≤ t := hT₀.le.trans ht.1
  have hTt : T ≤ t := hT₀T.trans ht.1
  have hIat (a : ℕ) (ha2 : 2 ≤ a) (har : a < r + 1) :
    weightedEnergyIntegral μ hc P (ballCutoff R) p a u t ≤ 2 * (envelope K a + δ) :=
    (weightedEnergyIntegral_mono_aux hiso hLC hρ hsupp hp a u ht0 ht.2).trans (hI a ha2 har)
  have hmean' :
    (∫ w,
        ballCutoff R (p t w) ^ 2 *
          cumulantEnergy
            (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) r
            u ∂P) ≤
      ε / 3 :=
    hmean.trans ((div_le_div_of_nonneg_right (hI r hr (by omega)) hT₀.le).trans htime)
  have htail := hp.measure_norm_gt_le hiso hγ hℱ0 hnull hKL0 hKL ht0 hRpos
  have hexp : Real.exp (KL * t) ≤ Real.exp (KL * (2 * T₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKL0)
  have htail' :
    (P {w | R < ‖p t w‖}).toReal ≤ lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)) / R ^ 2 :=
    htail.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hV0) (sq_nonneg R))
  have htailC : C * (P {w | R < ‖p t w‖}).toReal ≤ ε / 3 := by
    calc
      C * (P {w | R < ‖p t w‖}).toReal ≤
          C * (lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)) / R ^ 2) :=
        mul_le_mul_of_nonneg_left htail' hC0
      _ = D / R ^ 2 := by
        dsimp only [D]
        ring
      _ ≤ ε / 3 := hRerr
  have hboundary := IsEldanCutoff.integral_energy_le_weighted_add hiso hp r u hC0 hC hcont ht0
  have hboundary' :
    (∫ w,
        cumulantEnergy
          (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) r
          u ∂P) ≤
      ε / 3 + ε / 3 :=
    hboundary.trans (add_le_add hmean' htailC)
  have hgen :=
    energy_integral_le_of_generator_ge hiso hLC hρ hsupp hγ hℱ0 hnull hp hr u (envelope K) hb
      (h51 n μ hc hiso hLC h8 r hr u)
      (by
        intro q hSym hQ
        have hcompact :
          IsCompact
            (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))).support := by
          rw [compactPosterior_support]
          exact hc
        have h100 :
          ∀ a,
            2 ≤ a →
              a < r + 1 →
                ∀ v : EuclideanSpace ℝ (Fin n),
                  cumulantEnergy
                      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                      (a - 1) v ≤
                    envelope K a *
                      ⟪Covariance.operator
                          (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                          v,
                        v⟫ := by
          intro a ha2 har v
          exact
            KLS.compactPosterior_cumulant_bound μ hc hiso hLC q.1 q.2 hSym hQ (by omega)
              (ihb a ha2 har) v
        have hpoint :=
          sqrt_sum_lowerDrift_sq_le_aux (compactPosterior μ hc q.1 q.2) hcompact
            (KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2)
            (fun v hv => KLS.Isotropic.compactPosterior_covariance_pos μ hc hiso q.1 q.2 hv) r
            (envelope K) h100 u
        refine hpoint.trans (le_of_eq ?_)
        have hinterval : r - 1 = r + 1 - 2 := by omega
        rw [hinterval]
        apply Finset.sum_congr rfl
        intro a ha
        have ha' := Finset.mem_Icc.mp ha
        have hindex : r + 2 - a = r + 1 - a + 1 := by omega
        rw [hindex, Nat.add_sub_cancel])
      ht0
  have hrest :
    17 * ((r : ℝ) + 1) ^ 2 * weightedEnergyIntegral μ hc P (ballCutoff R) p r u t +
        2 *
          ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
            ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K (r + 1 - a + 1)) *
              (Real.sqrt (weightedEnergyIntegral μ hc P (ballCutoff R) p r u t) *
                Real.sqrt (weightedEnergyIntegral μ hc P (ballCutoff R) p a u t)) ≤
      inductionMain K (r + 1) δ := by
    unfold inductionMain
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hIat r hr (by omega)) (by positivity)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact
        mul_le_mul (Real.sqrt_le_sqrt (hIat r hr (by omega)))
          (Real.sqrt_le_sqrt (hIat a ha'.1 (by omega))) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
  have htop := weightedEnergyIntegral_mono_aux hiso hLC hρ hsupp hp (r + 1) u hT hTt
  linarith only [hgen, hrest, hboundary', hδmain, htop]

end FunctionalInequalities.KLS.BKL.Localization
