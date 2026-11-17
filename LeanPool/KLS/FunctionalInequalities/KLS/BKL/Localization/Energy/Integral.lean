/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Integral
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Conjugation
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.EnergyForm
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic

/-!
# Integrated energy bound along the cutoff Eldan process
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
section Process

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- Separate the tensor Cauchy--Schwarz step from stochastic integration. -/
private theorem cutoff_tensor_energy_lower_bound {ι : Type*} [Fintype ι]
    (r : ℕ) (γ : ℝ) (E b : ℕ → ℝ) (Tt Lt : ι → ℝ) (g : ℝ)
    (hb : ∀ j, 0 ≤ b j) (hTsq : ∑ K, Tt K ^ 2 = E r)
    (h51 : (1 / 2 : ℝ) * E (r + 1) - 17 * ((r : ℝ) + 1) ^ 2 * E r -
      2 * ∑ K, Tt K * Lt K ≤ g)
    (hL : Real.sqrt (∑ K, Lt K ^ 2) ≤
      ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
        Real.sqrt (b (r + 1 - a + 1) * E a)) :
      (1 / 2 : ℝ) * (γ ^ 2 * E (r + 1)) - 17 * ((r : ℝ) + 1) ^ 2 * (γ ^ 2 * E r) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ((γ * Real.sqrt (E r)) * (γ * Real.sqrt (E a))) ≤
      γ ^ 2 * g := by
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg _
  have hCS : ∑ K : ι, Tt K * Lt K ≤
      Real.sqrt (∑ K : ι, Tt K ^ 2) *
        Real.sqrt (∑ K : ι, Lt K ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
  rw [hTsq] at hCS
  have hL2 := hL
  have hsq : ∀ a, Real.sqrt (b (r + 1 - a + 1) * E a) =
      Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a) :=
    fun a => Real.sqrt_mul (hb _) _
  simp only [hsq] at hL2
  have hS : ∑ K : ι, Tt K * Lt K ≤
      Real.sqrt (E r) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
        (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a)) :=
    hCS.trans (mul_le_mul_of_nonneg_left hL2 (Real.sqrt_nonneg _))
  have key := h51
  have hsum : ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
      Real.sqrt (b (r + 1 - a + 1)) *
      ((γ * Real.sqrt (E r)) * (γ * Real.sqrt (E a))) =
      γ ^ 2 * (Real.sqrt (E r) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
        ((r + 1 - 1).choose (a - 1) : ℝ) *
        (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsum]
  have hfac : (1 / 2 : ℝ) * (γ ^ 2 * E (r + 1)) -
      17 * ((r : ℝ) + 1) ^ 2 * (γ ^ 2 * E r) -
      2 * (γ ^ 2 * (Real.sqrt (E r) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
        ((r + 1 - 1).choose (a - 1) : ℝ) *
        (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a)))) =
      γ ^ 2 * ((1 / 2 : ℝ) * E (r + 1) - 17 * ((r : ℝ) + 1) ^ 2 * E r -
        2 * (Real.sqrt (E r) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a)))) := by
    ring
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ hγ2
  linarith [hS, key]

omit [IsProbabilityMeasure P] in
private theorem integrate_weighted_energy_bound {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {r : ℕ} (γ : α → ℝ) (E : ℕ → α → ℝ)
    (hγ : ∀ z, 0 ≤ γ z) (hE : ∀ j z, 0 ≤ E j z)
    (b : ℕ → ℝ) (g : α → ℝ) (hg : Integrable g ν)
    (hI : ∀ j, Integrable (fun z => γ z ^ 2 * E j z) ν)
    (hf : ∀ j, MemLp (fun z => γ z * Real.sqrt (E j z)) (ENNReal.ofReal 2) ν)
    (hterm : ∀ a ∈ Finset.Icc 2 (r + 1 - 2), Integrable
      (fun z => ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
        ((γ z * Real.sqrt (E r z)) * (γ z * Real.sqrt (E a z)))) ν)
    (hpoint : ∀ᵐ z ∂ν, (1 / 2 : ℝ) * (γ z ^ 2 * E (r + 1) z) -
      17 * ((r : ℝ) + 1) ^ 2 * (γ z ^ 2 * E r z) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
            ((γ z * Real.sqrt (E r z)) * (γ z * Real.sqrt (E a z))) ≤ g z) :
    (1 / 2 : ℝ) * (∫ z, γ z ^ 2 * E (r + 1) z ∂ν) ≤
      (∫ z, g z ∂ν) + 17 * ((r : ℝ) + 1) ^ 2 * (∫ z, γ z ^ 2 * E r z ∂ν) +
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
            (Real.sqrt (∫ z, γ z ^ 2 * E r z ∂ν) * Real.sqrt (∫ z, γ z ^ 2 * E a z ∂ν)) := by
  let weight (a : ℕ) := ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1))
  let f (a : ℕ) (z : α) := γ z * Real.sqrt (E a z)
  have hterm' : ∀ a ∈ Finset.Icc 2 (r + 1 - 2),
      Integrable (fun z => weight a * (f r z * f a z)) ν := hterm
  have hdifference : Integrable (fun z => (1 / 2 : ℝ) * (γ z ^ 2 * E (r + 1) z) -
      17 * ((r : ℝ) + 1) ^ 2 * (γ z ^ 2 * E r z)) ν :=
    ((hI (r + 1)).const_mul (1 / 2 : ℝ)).sub ((hI r).const_mul (17 * ((r : ℝ) + 1) ^ 2))
  have hsum := (integrable_finsetSum _ hterm').const_mul 2
  have hmono := integral_mono_ae (hdifference.sub hsum) hg hpoint
  change (∫ z, (1 / 2 : ℝ) * (γ z ^ 2 * E (r + 1) z) -
      17 * ((r : ℝ) + 1) ^ 2 * (γ z ^ 2 * E r z) -
      2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), weight a * (f r z * f a z) ∂ν) ≤ _ at hmono
  rw [integral_sub hdifference hsum,
    integral_sub ((hI (r + 1)).const_mul (1 / 2 : ℝ)) ((hI r).const_mul (17 * ((r : ℝ) + 1) ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ hterm'] at hmono
  simp only [integral_const_mul] at hmono
  have hsq (a : ℕ) (z : α) : f a z ^ (2 : ℝ) = γ z ^ 2 * E a z := by
    rw [Real.rpow_two]
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (hE a z)]
  have hsum_le :
      ∑ a ∈ Finset.Icc 2 (r + 1 - 2), weight a * ∫ z, f r z * f a z ∂ν ≤
        ∑ a ∈ Finset.Icc 2 (r + 1 - 2), weight a *
          (Real.sqrt (∫ z, γ z ^ 2 * E r z ∂ν) * Real.sqrt (∫ z, γ z ^ 2 * E a z ∂ν)) := by
    apply Finset.sum_le_sum
    intro a _
    have hbound := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (f := f r) (g := f a)
      (Filter.Eventually.of_forall fun z => mul_nonneg (hγ z) (Real.sqrt_nonneg _))
      (Filter.Eventually.of_forall fun z => mul_nonneg (hγ z) (Real.sqrt_nonneg _)) (hf r) (hf a)
    simp only [hsq, ← Real.sqrt_eq_rpow] at hbound
    exact mul_le_mul_of_nonneg_left hbound (by dsimp [weight]; positivity)
  dsimp only [weight] at hsum_le
  linarith [hmono, hsum_le]

omit [IsProbabilityMeasure P] in
/-- Weighted energy, square-root energy and cross terms inherit pathwise bounds. -/
private theorem cutoff_weighted_path_bounds {E : ℕ → Param n → ℝ}
    (hγ01 : ∀ q, 0 ≤ γ q ∧ γ q ≤ 1) (hEnn : ∀ d q, 0 ≤ E d q)
    (hEbd : ∀ d, ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → E d (p s w) ≤ C) :
    (∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |γ (p s w) ^ 2 * E d (p s w)| ≤ C) ∧
    (∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |γ (p s w) * Real.sqrt (E d (p s w))| ≤ C) ∧
    (∀ d d', ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |(γ (p s w) * Real.sqrt (E d (p s w))) * (γ (p s w) * Real.sqrt (E d' (p s w)))| ≤ C) := by
  have hγabs : ∀ q, |γ q| ≤ 1 := fun q =>
    abs_le.mpr ⟨by linarith [(hγ01 q).1], (hγ01 q).2⟩
  have hGbd : ∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |γ (p s w) ^ 2 * E d (p s w)| ≤ C := by
    intro d
    obtain ⟨C, _hC0, hC⟩ := hEbd d
    refine ⟨C, ?_⟩
    filter_upwards [hC] with w hw
    intro s hs
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hEnn d _))]
    have hg := hγ01 (p s w)
    calc γ (p s w) ^ 2 * E d (p s w) ≤ 1 * C :=
          mul_le_mul (pow_le_one₀ hg.1 hg.2) (hw s hs) (hEnn d _) zero_le_one
      _ = C := one_mul _
  have hfbd : ∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |γ (p s w) * Real.sqrt (E d (p s w))| ≤ C := by
    intro d
    obtain ⟨C, _hC0, hC⟩ := hEbd d
    refine ⟨Real.sqrt C, ?_⟩
    filter_upwards [hC] with w hw
    intro s hs
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |γ (p s w)| * Real.sqrt (E d (p s w)) ≤ 1 * Real.sqrt C :=
          mul_le_mul (hγabs _) (Real.sqrt_le_sqrt (hw s hs)) (Real.sqrt_nonneg _) zero_le_one
      _ = Real.sqrt C := one_mul _
  have hffbd : ∀ d d', ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |(γ (p s w) * Real.sqrt (E d (p s w))) * (γ (p s w) * Real.sqrt (E d' (p s w)))| ≤ C := by
    intro d d'
    obtain ⟨C, hC⟩ := hfbd d
    obtain ⟨C', hC'⟩ := hfbd d'
    refine ⟨C * C', ?_⟩
    filter_upwards [hC, hC'] with w hw hw'
    intro s hs
    rw [abs_mul]
    exact mul_le_mul (hw s hs) (hw' s hs) (abs_nonneg _) ((abs_nonneg _).trans (hw s hs))
  exact ⟨hGbd, hfbd, hffbd⟩

theorem energy_integral_le_of_generator_ge (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 ρ)
    (hγ : IsCutoff γ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {r : ℕ} (hr : 2 ≤ r) (u : EuclideanSpace ℝ (Fin n))
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h51 :
      ∀ q : Param n,
        IsSelfAdjoint q.2 →
          (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
            (1 / 2 : ℝ) *
                    cumulantEnergy
                      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                      (r + 1) u -
                  17 * ((r : ℝ) + 1) ^ 2 *
                    cumulantEnergy
                      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u -
                2 *
                  ∑ K : Fin r → Fin n,
                    cumulant
                        (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                        (r + 1)
                        (Fin.cons u fun s =>
                          inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
                      lowerDrift
                        (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                        (Fin.cons u fun s =>
                          inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
                        0 ≤
              generator μ hc
                (fun q' : Param n =>
                  cumulantEnergy
                    (compactPosterior μ hc q'.1 q'.2 : Measure (EuclideanSpace ℝ (Fin n))) r u)
                q)
    (hL :
      ∀ q : Param n,
        IsSelfAdjoint q.2 →
          (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
            Real.sqrt
                (∑ K : Fin r → Fin n,
                  lowerDrift
                      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                      (Fin.cons u fun s =>
                        inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
                      0 ^
                    2) ≤
              ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
                ((r + 1 - 1).choose (a - 1) : ℝ) *
                  Real.sqrt
                    (b (r + 1 - a + 1) *
                      cumulantEnergy
                        (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) a
                        u))
    {T : ℝ} (hT : 0 ≤ T) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u +
        (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P γ p (r + 1) u T ≤
      (∫ w,
            cumulantEnergy
              (compactPosterior μ hc (p T w).1 (p T w).2 : Measure (EuclideanSpace ℝ (Fin n))) r
              u ∂P) +
          17 * ((r : ℝ) + 1) ^ 2 * weightedEnergyIntegral μ hc P γ p r u T +
        2 *
          ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
            ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
              (Real.sqrt (weightedEnergyIntegral μ hc P γ p r u T) *
                Real.sqrt (weightedEnergyIntegral μ hc P γ p a u T)) := by
  classical
  have _hr :=
    hr
  -- Opaque names for the energies and the two tensor fields.


  -- Introduce the tensor energy fields and their smoothness.
  obtain ⟨E, hE⟩ :
    ∃ E : ℕ → Param n → ℝ,
      E = fun d q =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d
          u :=
    ⟨_, rfl⟩
  obtain ⟨Tt, hTt⟩ :
    ∃ Tt : Param n → (Fin r → Fin n) → ℝ,
      Tt = fun q K =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
          (Fin.cons u fun s =>
            inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) :=
    ⟨_, rfl⟩
  obtain ⟨Lt, hLt⟩ :
    ∃ Lt : Param n → (Fin r → Fin n) → ℝ,
      Lt = fun q K =>
        lowerDrift (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun s =>
            inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
          0 :=
    ⟨_, rfl⟩
  have hEapp :
    ∀ d (q : Param n),
      E d q =
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d
          u := by
    intro d q
    rw [hE]
  have hEnn : ∀ d (q : Param n), 0 ≤ E d q := by
    intro d q
    rw [hEapp]
    unfold cumulantEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEsmooth : ∀ d, ContDiff ℝ ∞ (E d) := by
    intro d
    rw [hE]
    exact contDiff_cumulantEnergy_posterior μ hc hiso d u
  have hEcont : ∀ d, Continuous (E d) := fun d => (hEsmooth d).continuous
  have hE0 : cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u = E r 0 := by
    rw [hEapp]
    simp only [Prod.fst_zero, Prod.snd_zero, compactPosterior_zero]
  have h51' :
    ∀ q : Param n,
      IsSelfAdjoint q.2 →
        (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
          (1 / 2 : ℝ) * E (r + 1) q - 17 * ((r : ℝ) + 1) ^ 2 * E r q -
              2 * ∑ K : Fin r → Fin n, Tt q K * Lt q K ≤
            generator μ hc (E r) q := by
    intro q h1 h2
    rw [hE, hTt, hLt]
    exact h51 q h1 h2
  have hL' :
    ∀ q : Param n,
      IsSelfAdjoint q.2 →
        (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
          Real.sqrt (∑ K : Fin r → Fin n, Lt q K ^ 2) ≤
            ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
              ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1) * E a q) := by
    intro q h1 h2
    rw [hE, hLt]
    exact hL q h1 h2
  have hTsq : ∀ q : Param n, ∑ K : Fin r → Fin n, Tt q K ^ 2 = E r q := by
    intro q
    rw [hEapp, hTt]
    rfl
  -- Pointwise bound on symmetric PSD parameters.


  -- Apply the pointwise generator lower bound.
  have hpt :
    ∀ q : Param n,
      IsSelfAdjoint q.2 →
        (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
          (1 / 2 : ℝ) * (γ q ^ 2 * E (r + 1) q) - 17 * ((r : ℝ) + 1) ^ 2 * (γ q ^ 2 * E r q) -
              2 *
                ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
                  ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
                    ((γ q * Real.sqrt (E r q)) * (γ q * Real.sqrt (E a q))) ≤
            γ q ^ 2 * generator μ hc (E r) q := by
    intro q h1 h2
    exact
      cutoff_tensor_energy_lower_bound r (γ q) (fun d => E d q) b (Tt q) (Lt q)
        (generator μ hc (E r) q) hb (hTsq q) (h51' q h1 h2)
        (hL' q h1 h2)
  -- Bounds along the path.
  have hQ := IsEldanCutoff.ae_Q_posSemidef hiso hγ h
  have hγc : Continuous γ := by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    exact hK.continuous
  have hγ01 : ∀ q, 0 ≤ γ q ∧ γ q ≤ 1 := fun q => hγ.mem_Icc q
  have hEbd : ∀ d, ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → E d (p s w) ≤ C := by
    intro d
    obtain ⟨C, hC0, hC⟩ := exists_cumulantEnergy_le μ hc hiso hLC hρ hsupp d
    refine ⟨C * ‖u‖ ^ 2, by positivity, ?_⟩
    filter_upwards [hQ] with w hw
    intro s hs
    rw [hEapp]
    exact hC (p s w) (hw s hs).1 (hw s hs).2 u
  have hGcont : ∀ d, Continuous (fun q => γ q ^ 2 * E d q) := fun d =>
    (hγc.pow 2).mul (hEcont d)
  obtain ⟨hGbd, hfbd, hffbd⟩ :=
    cutoff_weighted_path_bounds hγ01 hEnn
      hEbd
  -- The generator term is bounded (compact support of the cutoff).
  have hF3 : ContDiff ℝ 3 (E r) := (hEsmooth r).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgen_cont : Continuous (generator μ hc (E r)) :=
    continuous_generator_of_contDiff_three μ hc hiso hF3
  have hgc : Continuous (fun q => γ q ^ 2 * generator μ hc (E r) q) := (hγc.pow 2).mul hgen_cont
  -- Check compactly supported integrability for the stochastic estimate.
  have hgsupp : HasCompactSupport (fun q => γ q ^ 2 * generator μ hc (E r) q) := by
    have h2 : HasCompactSupport (fun q => γ q ^ 2) :=
      hγ.compactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact h2.mul_right
  obtain ⟨Bg, hBg⟩ := hgc.bounded_above_of_compact_support hgsupp
  have hgB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |γ (p s w) ^ 2 * generator μ hc (E r) (p s w)| ≤ Bg :=
    Filter.Eventually.of_forall fun w s _ => by
      simpa only [Real.norm_eq_abs] using
        hBg
          (p s w)
  -- Product measure.
  obtain ⟨Pr, hPr⟩ :
    ∃ Pr : Measure (Ω × ℝ), Pr = P.prod (volume.restrict (Set.Ioc (0 : ℝ) T)) := ⟨_, rfl⟩
  have : IsFiniteMeasure Pr := by
    rw [hPr]
    infer_instance
  have hprod :
    ∀ {φ : Param n → ℝ},
      Continuous φ →
        ∀ {B : ℝ},
          (∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) →
            Integrable (fun z : Ω × ℝ => φ (p z.2 z.1)) Pr ∧
              ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s w) ∂volume ∂P = ∫ z, φ (p z.2 z.1) ∂Pr := by
    intro φ hφ B hB
    rw [hPr]
    exact ⟨h.integrable_prod_of_ae_bound hφ hB T, h.integral_integral_eq_prod hφ hB T⟩
  have hprodae :
    ∀ {Q : Ω → ℝ → Prop}, (∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) → ∀ᵐ z ∂Pr, Q z.1 z.2 := by
    intro Q hQ'
    rw [hPr]
    exact ae_prod_restrict_Ioc_of_ae hQ' T
  have hae : ∀ᵐ z ∂Pr, IsSelfAdjoint (p z.2 z.1).2 ∧ ∀ x, 0 ≤ ⟪(p z.2 z.1).2 x, x⟫ := hprodae hQ
  have hI :
    ∀ d,
      ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s w) ^ 2 * E d (p s w) ∂volume ∂P =
        ∫ z, γ (p z.2 z.1) ^ 2 * E d (p z.2 z.1) ∂Pr := by
    intro d
    obtain ⟨C, hC⟩ := hGbd d
    exact (hprod (hGcont d) hC).2
  have hIint : ∀ d, Integrable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * E d (p z.2 z.1)) Pr := by
    intro d
    obtain ⟨C, hC⟩ := hGbd d
    exact (hprod (hGcont d) hC).1
  have hfint :
    ∀ d, Integrable (fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E d (p z.2 z.1))) Pr := by
    intro d
    obtain ⟨C, hC⟩ := hfbd d
    exact (hprod (hγc.mul (hEcont d).sqrt) hC).1
  have hfmem :
    ∀ d,
      MemLp (fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E d (p z.2 z.1))) (ENNReal.ofReal 2)
        Pr := by
    intro d
    obtain ⟨C, hC⟩ := hfbd d
    refine MemLp.of_bound (hfint d).aestronglyMeasurable C ?_
    filter_upwards [hprodae hC] with z hz
    simpa only [Real.norm_eq_abs] using hz
  have hterm :
    ∀ a ∈ Finset.Icc 2 (r + 1 - 2),
      Integrable
        (fun z : Ω × ℝ =>
          ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
            ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
              (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1)))))
        Pr := by
    intro a _
    obtain ⟨C, hC⟩ := hffbd r a
    exact ((hprod ((hγc.mul (hEcont r).sqrt).mul (hγc.mul (hEcont a).sqrt)) hC).1).const_mul _
  have hGint :
    Integrable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * generator μ hc (E r) (p z.2 z.1)) Pr :=
    (hprod hgc hgB).1
  have hGeq :
    ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s w) ^ 2 * generator μ hc (E r) (p s w) ∂volume ∂P =
      ∫ z, γ (p z.2 z.1) ^ 2 * generator μ hc (E r) (p z.2 z.1) ∂Pr :=
    (hprod hgc hgB).2
  -- Dynkin.
  have hF2 : ContDiff ℝ 2 (E r) := (hEsmooth r).of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨-, hDynkin⟩ := IsEldanCutoff.dynkin hiso hγ hℱ0 hnull h hF2 hT
  rw [hGeq] at hDynkin
  -- Integrate the pointwise bound.
  have henergy := integrate_weighted_energy_bound (r := r)
    (fun z : Ω × ℝ => γ (p z.2 z.1)) (fun j z => E j (p z.2 z.1))
    (fun z => (hγ01 (p z.2 z.1)).1) (fun j z => hEnn j (p z.2 z.1)) b
    (fun z => γ (p z.2 z.1) ^ 2 * generator μ hc (E r) (p z.2 z.1)) hGint hIint hfmem hterm
    (hae.mono fun z hz => hpt (p z.2 z.1) hz.1 hz.2)
  simp only [weightedEnergyIntegral, ← hEapp, hE0, hI]
  linarith [henergy, hDynkin]

end Process

end FunctionalInequalities.KLS.BKL.Localization
