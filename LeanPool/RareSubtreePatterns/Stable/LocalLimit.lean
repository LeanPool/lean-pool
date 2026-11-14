/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.CFBounds

/-!
# The (lattice) local limit theorem (Stage 4)

Source lines 855–883 (inventory B09, `eq:LL` and its lattice version; the paper cites
Ibragimov–Linnik, Theorem 4.2.1). Under `(H_α)` alone, with `d = latticeSpan μ` the span of
`μ` (periodic laws allowed) and `d_α = stableDensity α`:

* `PoissonDeclumping.Stable.localLimit`: uniformly over `k ∈ -n + dℤ`,
  `|a_n P(S_n = k) - d · d_α(k / a_n)| → 0`;
* `PoissonDeclumping.Stable.walkProb_eq_zero_of_not_dvd`: `P(S_n = k) = 0` off `-n + dℤ`;
* `PoissonDeclumping.Stable.localLimit_aperiodic`: the aperiodic statement `eq:LL`;
* `PoissonDeclumping.Stable.localLimit_of_support`: the paper's form with the lattice `nb + dℤ`
  for an arbitrary support point `b` of `X_1`.

Proof: Fourier inversion on `ℤ` reduced to `[-π/d, π/d]` by the twisted periodicity of `φ`,
rescaling `θ = t/a_n`, and the `L¹` convergence
`∫ |1_{|t| ≤ π a_n/d} φ(t/a_n)^n - exp((-it)^α)| dt → 0` (dominated convergence on
`|t| ≤ δ a_n` with the Stage 3 bound, and `a_n q^n → 0` on `δ a_n ≤ |t| ≤ π a_n/d`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

lemma walkProb_coe_nat (μ : PMF ℕ) (n : ℕ) (k : ℤ) :
    walkProb μ n k = (walkLaw μ n).real {k} := by
  simp [walkProb]

variable (μ a) in
/-- The rescaled truncated characteristic function `t ↦ 1_{|t| ≤ π a_n/d} φ(t/a_n)^n`. -/
noncomputable def truncCF (n : ℕ) (t : ℝ) : ℂ :=
  (Ioc (-(Real.pi * a n / latticeSpan μ)) (Real.pi * a n / latticeSpan μ)).indicator
    (fun t => stepCF μ (t / a n) ^ n) t

lemma norm_cexp_neg_mul_I' (t x : ℝ) : ‖cexp (-((t : ℂ) * x * I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma integrable_truncCF (n : ℕ) : Integrable (truncCF μ a n) := by
  unfold truncCF
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hc : Continuous fun t : ℝ => stepCF μ (t / a n) ^ n := by
    have := continuous_stepCF μ; fun_prop
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- The rescaled lattice Fourier formula: for `d ∣ k + n` and `a_n > 0`,
`a_n P(S_n = k) = (d/2π) ∫ 1_{|t| ≤ π a_n/d} φ(t/a_n)^n e^{-itk/a_n} dt`. -/
theorem mul_walkLaw_real_eq (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n : ℕ} (han : 0 < a n) {k : ℤ}
    (hk : (latticeSpan μ : ℤ) ∣ k + n) :
    ((a n * (walkLaw μ n).real {k} : ℝ) : ℂ) = (latticeSpan μ / (2 * Real.pi)) *
      ∫ t, truncCF μ a n t * cexp (-(t * (k / a n : ℝ) * I)) := by
  have hd : (0 : ℝ) < latticeSpan μ := by exact_mod_cast latticeSpan_pos hc hne
  rw [Complex.ofReal_mul, walkLaw_real_singleton_lattice hc hne n k hk]
  set L : ℝ := Real.pi * a n / latticeSpan μ with hL
  have hL0 : 0 ≤ L := by positivity
  have h1 : ∫ θ in (-(Real.pi / latticeSpan μ))..(Real.pi / latticeSpan μ),
      fourierIntegrand μ n k θ = (a n)⁻¹ • ∫ t in (-L)..L, fourierIntegrand μ n k (t / a n) := by
    rw [intervalIntegral.integral_comp_div _ han.ne', smul_smul, inv_mul_cancel₀ han.ne', one_smul]
    congr 1 <;> rw [hL] <;> field_simp
  have h2 : ∫ t in (-L)..L, fourierIntegrand μ n k (t / a n) =
      ∫ t, truncCF μ a n t * cexp (-(t * (k / a n : ℝ) * I)) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
    congr 1; funext t
    unfold truncCF
    by_cases ht : t ∈ Ioc (-L) L
    · rw [indicator_of_mem ht, indicator_of_mem ht, fourierIntegrand]
      congr 2; push_cast; ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  rw [h1, h2, Complex.real_smul]
  have : (a n : ℂ) ≠ 0 := by exact_mod_cast han.ne'
  generalize (∫ t, truncCF μ a n t * cexp (-(t * (k / a n : ℝ) * I))) = J
  push_cast
  field_simp

/-- The local limit error is controlled, uniformly in `k`, by the `L¹` distance between the
truncated rescaled characteristic function and `exp((-it)^α)`. -/
theorem abs_mul_walkLaw_real_sub_le (h : StableDomain μ α a) {n : ℕ} (han : 0 < a n) {k : ℤ}
    (hk : (latticeSpan μ : ℤ) ∣ k + n) :
    |a n * (walkLaw μ n).real {k} - latticeSpan μ * stableDensity α (k / a n)| ≤
      (latticeSpan μ / (2 * Real.pi)) * ∫ t, ‖truncCF μ a n t - stableCF α t‖ := by
  have hα := h.alpha_mem
  set x : ℝ := k / a n
  set E : ℝ → ℂ := fun t => cexp (-(t * x * I)) with hE
  have hEn : ∀ t, ‖E t‖ = 1 := fun t => norm_cexp_neg_mul_I' t x
  have hi1 : Integrable (fun t => truncCF μ a n t * E t) :=
    (integrable_truncCF n).mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun t => (hEn t).le)
  have hi2 : Integrable (fun t => stableCF α t * E t) :=
    (integrable_stableCF hα).mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun t => (hEn t).le)
  have h1 := mul_walkLaw_real_eq h.critical h.nondegenerate han hk
  have hre : a n * (walkLaw μ n).real {k} = (latticeSpan μ / (2 * Real.pi)) *
      (∫ t, truncCF μ a n t * E t).re := by
    have := congrArg Complex.re h1
    rw [Complex.ofReal_re] at this
    rw [this]
    simp only [hE, x]
    rw [show ((latticeSpan μ : ℂ) / (2 * (Real.pi : ℂ))) = (((latticeSpan μ : ℝ) /
      (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
  have hd : latticeSpan μ * stableDensity α x = (latticeSpan μ / (2 * Real.pi)) *
      (∫ t, stableCF α t * E t).re := by
    rw [stableDensity]; ring
  rw [hre, hd, ← mul_sub, ← Complex.sub_re, ← integral_sub hi1 hi2, abs_mul,
    abs_of_nonneg (by positivity)]
  gcongr
  calc |(∫ t, (truncCF μ a n t * E t - stableCF α t * E t)).re|
      ≤ ‖∫ t, (truncCF μ a n t * E t - stableCF α t * E t)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ t, ‖truncCF μ a n t * E t - stableCF α t * E t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, ‖truncCF μ a n t - stableCF α t‖ := by
        congr 1; funext t; rw [← sub_mul, norm_mul, hEn, mul_one]


/-- **The `L¹` convergence behind the local limit theorem**:
`∫ |1_{|t| ≤ π a_n/d} φ(t/a_n)^n - exp((-it)^α)| dt → 0`. -/
theorem tendsto_integral_norm_truncCF_sub (h : StableDomain μ α a) :
    Tendsto (fun n => ∫ t, ‖truncCF μ a n t - stableCF α t‖) atTop (𝓝 0) := by
  have hα := h.alpha_mem
  have hc := h.critical
  have hne := h.nondegenerate
  have hd : (0 : ℝ) < latticeSpan μ := by exact_mod_cast latticeSpan_pos hc hne
  have hat := tendsto_atTop h
  obtain ⟨γ, c, A, δ, hγ, hc0, hδ, N₃, hN₃⟩ := exists_norm_stepCF_pow_le_exp h
  set δ' : ℝ := min δ (Real.pi / latticeSpan μ) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by positivity)
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_stepCF_le_of_le_abs hc hne hδ'0
  have hcont : ∀ n : ℕ, Continuous fun t : ℝ => stepCF μ (t / a n) ^ n := fun n => by
    have := continuous_stepCF μ; fun_prop
  -- the central part
  set S : ℕ → Set ℝ := fun n => Ioc (-(δ' * a n)) (δ' * a n) with hS
  set hn : ℕ → ℝ → ℂ := fun n t =>
    (S n).indicator (fun t => stepCF μ (t / a n) ^ n) t - stableCF α t with hhn
  set rn : ℕ → ℝ → ℂ := fun n t =>
    truncCF μ a n t - (S n).indicator (fun t => stepCF μ (t / a n) ^ n) t with hrn
  set D : ℝ → ℝ := fun t => (Icc (-A) A).indicator (fun _ => (1 : ℝ)) t +
    Real.exp (-c * |t| ^ γ) + ‖stableCF α t‖ with hD
  have hDint : Integrable D := by
    refine ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const ?_ ?_)).add ?_
      |>.add (integrable_stableCF hα).norm
    · simp
    · simp
    · have := integrable_rpow_abs_mul_exp_neg (s := 0) (p := γ) (c := c) (by norm_num) hγ hc0
      simpa using this
  have hcentral : Tendsto (fun n => ∫ t, ‖hn n t‖) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ t : ℝ, (fun _ => (0 : ℝ)) t := by simp
    rw [h0]
    apply tendsto_integral_filter_of_dominated_convergence D
    · refine Eventually.of_forall fun n => ?_
      exact (((hcont n).aestronglyMeasurable (μ := volume).indicator measurableSet_Ioc).sub
        (continuous_stableCF (by linarith)).aestronglyMeasurable).norm
    · filter_upwards [eventually_ge_atTop N₃, eventually_ge_atTop 1] with n hn3 hn1
      refine Eventually.of_forall fun t => ?_
      have han := h.pos n hn1
      rw [norm_norm]
      refine (norm_sub_le _ _).trans ?_
      simp only [hD]
      gcongr
      by_cases ht : t ∈ S n
      · rw [indicator_of_mem ht, norm_pow]
        have htS : |t| ≤ δ * a n := by
          have := ht; simp only [hS, mem_Ioc] at this
          rw [abs_le]; constructor
          · nlinarith [min_le_left δ (Real.pi / latticeSpan μ)]
          · nlinarith [min_le_left δ (Real.pi / latticeSpan μ)]
        by_cases htA : |t| ≤ A
        · have : t ∈ Icc (-A) A := abs_le.1 htA
          rw [indicator_of_mem this]
          have := pow_le_one₀ (norm_nonneg _) (norm_stepCF_le μ (t / a n)) (n := n)
          linarith [Real.exp_pos (-c * |t| ^ γ)]
        · push Not at htA
          have := hN₃ n hn3 t htA.le htS
          linarith [indicator_nonneg (fun _ _ => zero_le_one) t (s := Icc (-A) A)
            (f := fun _ => (1 : ℝ))]
      · rw [indicator_of_notMem ht, norm_zero]
        exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (Real.exp_pos _).le
    · exact hDint
    · refine Eventually.of_forall fun t => ?_
      have hev : ∀ᶠ n in atTop, t ∈ S n := by
        have h1 := (hat.const_mul_atTop hδ'0).eventually_gt_atTop |t|
        filter_upwards [h1] with n hn
        simp only [hS, mem_Ioc]
        constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
      have hlim := tendsto_stepCF_pow h (ψ := id) tendsto_id (tendsto_const_nhds (x := t))
      have : Tendsto (fun n => hn n t) atTop (𝓝 0) := by
        rw [show (0 : ℂ) = stableCF α t - stableCF α t by ring]
        refine (hlim.sub_const (stableCF α t)).congr' ?_
        filter_upwards [hev] with n hn'
        simp only [hhn, id, indicator_of_mem hn']
      have := (continuous_norm.tendsto _).comp this
      simpa [Function.comp_def] using this
  -- the annulus
  have hann : ∀ n, 1 ≤ n → ∫ t, ‖rn n t‖ ≤ 2 * (Real.pi / latticeSpan μ) * (a n * q ^ n) := by
    intro n hn1
    have han := h.pos n hn1
    set L : ℝ := Real.pi * a n / latticeSpan μ with hL
    have hbd : ∀ t, ‖rn n t‖ ≤ (Ioc (-L) L).indicator (fun _ => q ^ n) t := by
      intro t
      simp only [hrn, truncCF]
      by_cases ht : t ∈ Ioc (-L) L
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        by_cases ht' : t ∈ S n
        · rw [indicator_of_mem ht', sub_self, norm_zero]; positivity
        · rw [indicator_of_notMem ht', sub_zero, norm_pow]
          apply pow_le_pow_left₀ (norm_nonneg _)
          apply hq
          · simp only [hS, mem_Ioc, not_and_or, not_lt, not_le] at ht'
            rw [abs_div, abs_of_pos han, le_div_iff₀ han]
            rcases ht' with h1 | h1
            · rw [abs_of_neg (by nlinarith)]; linarith
            · rw [abs_of_pos (by nlinarith)]; linarith
          · rw [abs_div, abs_of_pos han, div_le_iff₀ han]
            have := ht; simp only [mem_Ioc] at this
            rw [abs_le]; constructor
            · have hbound : -L ≤ t := this.1.le
              rw [hL] at hbound
              have hform : Real.pi / latticeSpan μ * a n =
                  Real.pi * a n / latticeSpan μ := by ring
              linarith only [hbound, hform]
            · have hbound : t ≤ L := this.2
              rw [hL] at hbound
              have hform : Real.pi / latticeSpan μ * a n =
                  Real.pi * a n / latticeSpan μ := by ring
              linarith only [hbound, hform]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]
        have : t ∉ S n := by
          intro ht'
          apply ht
          simp only [hS, mem_Ioc] at ht' ⊢
          have hle : δ' * a n ≤ L := by
            rw [hL]
            have := min_le_right δ (Real.pi / latticeSpan μ)
            calc δ' * a n ≤ Real.pi / latticeSpan μ * a n := by gcongr
              _ = Real.pi * a n / latticeSpan μ := by ring
          constructor <;> linarith [ht'.1, ht'.2]
        rw [indicator_of_notMem this, sub_self, norm_zero]
    calc ∫ t, ‖rn n t‖ ≤ ∫ t, (Ioc (-L) L).indicator (fun _ => q ^ n) t := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) _
            (Eventually.of_forall hbd)
          exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
      _ = 2 * (Real.pi / latticeSpan μ) * (a n * q ^ n) := by
          rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc,
            smul_eq_mul, max_eq_left (by
              have : 0 ≤ Real.pi * a n / latticeSpan μ := by positivity
              rw [hL]; linarith)]
          rw [hL]; ring
  have hann0 : Tendsto (fun n => 2 * (Real.pi / latticeSpan μ) * (a n * q ^ n)) atTop (𝓝 0) := by
    obtain ⟨C, hC, hCn⟩ := (regularlyVaryingSeq h).exists_le_mul h.monotone h.pos
      (by have := hα.1; positivity) (by rw [div_lt_one (by linarith)]; exact hα.1)
    have h1 : Tendsto (fun n : ℕ => C * ((n : ℝ) * q ^ n)) atTop (𝓝 (C * 0)) :=
      (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).const_mul C
    rw [mul_zero] at h1
    have h2 : Tendsto (fun n => a n * q ^ n) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ h1
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact mul_nonneg (h.pos n hn).le (pow_nonneg hq0 n)
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have := hCn n hn
        calc a n * q ^ n ≤ C * n * q ^ n := by gcongr
          _ = C * ((n : ℝ) * q ^ n) := by ring
    have := h2.const_mul (2 * (Real.pi / latticeSpan μ))
    rwa [mul_zero] at this
  -- combine
  have hsplit : ∀ n, 1 ≤ n → ∫ t, ‖truncCF μ a n t - stableCF α t‖ ≤
      (∫ t, ‖hn n t‖) + ∫ t, ‖rn n t‖ := by
    intro n hn1
    have hi1 : Integrable (fun t => ‖hn n t‖) :=
      ((((integrable_indicator_iff measurableSet_Ioc).2
        ((hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self))).sub
        (integrable_stableCF hα)).norm
    have hi2 : Integrable (fun t => ‖rn n t‖) :=
      ((integrable_truncCF n).sub ((integrable_indicator_iff measurableSet_Ioc).2
        ((hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self))).norm
    rw [← integral_add hi1 hi2]
    apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) (hi1.add hi2)
    refine Eventually.of_forall fun t => ?_
    simp only [hhn, hrn]
    rw [show truncCF μ a n t - stableCF α t =
      ((S n).indicator (fun t => stepCF μ (t / a n) ^ n) t - stableCF α t) +
      (truncCF μ a n t - (S n).indicator (fun t => stepCF μ (t / a n) ^ n) t) by ring]
    exact norm_add_le _ _
  have hsum := (hcentral.add hann0)
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun t => norm_nonneg _) ?_
    hsum
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact (hsplit n hn1).trans (by linarith [hann n hn1])


/-- **Lattice local limit theorem** (source lines 860–876: `eq:LL` and its lattice version).
With `d = latticeSpan μ` the span of `μ`, uniformly over the lattice `-n + dℤ`,
`a_n P(S_n = k) - d · d_α(k / a_n) → 0`. -/
theorem localLimit (h : StableDomain μ α a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ, (latticeSpan μ : ℤ) ∣ k + n →
      |a n * walkProb μ n k - latticeSpan μ * stableDensity α (k / a n)| ≤ ε := by
  have h1 := (tendsto_integral_norm_truncCF_sub h).const_mul
    ((latticeSpan μ : ℝ) / (2 * Real.pi))
  rw [mul_zero] at h1
  obtain ⟨N, hN⟩ := ((Metric.tendsto_atTop.1 h1 ε hε)).imp fun N hN => hN
  refine ⟨max N 1, fun n hn k hk => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have han := h.pos n hn1
  rw [walkProb_coe_nat]
  refine (abs_mul_walkLaw_real_sub_le h han hk).trans ?_
  have := hN n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- Off the lattice `-n + dℤ` the walk has probability zero (source lines 876–877). -/
theorem walkProb_eq_zero_of_not_dvd (h : StableDomain μ α a) {n : ℕ} {k : ℤ}
    (hk : ¬ (latticeSpan μ : ℤ) ∣ k + n) : walkProb μ n k = 0 := by
  rw [walkProb_coe_nat]
  exact walkLaw_real_singleton_eq_zero h.critical h.nondegenerate hk

/-- **Aperiodic local limit theorem** (`eq:LL`, source line 862): if `d = 1`, then
`sup_{k ∈ ℤ} |a_n P(S_n = k) - d_α(k/a_n)| → 0`. -/
theorem localLimit_aperiodic (h : StableDomain μ α a) (h1 : latticeSpan μ = 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * walkProb μ n k - stableDensity α (k / a n)| ≤ ε := by
  obtain ⟨N, hN⟩ := localLimit h hε
  refine ⟨N, fun n hn k => ?_⟩
  have := hN n hn k (by rw [h1]; exact one_dvd _)
  rwa [h1, Nat.cast_one, one_mul] at this

/-- The paper's description of the lattice: for any support point `b` of `X_1`
(i.e. `μ_{b+1} > 0`), `k ∈ nb + dℤ` iff `k ∈ -n + dℤ`. -/
theorem dvd_sub_mul_iff (h : StableDomain μ α a) {j : ℕ} (hj : μ j ≠ 0) (n : ℕ) (k : ℤ) :
    (latticeSpan μ : ℤ) ∣ k - n * ((j : ℤ) - 1) ↔ (latticeSpan μ : ℤ) ∣ k + n := by
  have hd := latticeSpan_dvd_of_ne_zero h.critical h.nondegenerate hj
  have : k + n = k - n * ((j : ℤ) - 1) + n * j := by ring
  rw [this, dvd_add_left (Dvd.dvd.mul_left hd _)]

/-- **Lattice local limit theorem in the paper's form** (source lines 868–876): for every
support point `b = j - 1` of `X_1`, uniformly over `k ∈ nb + dℤ`,
`|a_n P(S_n = k) - d · d_α(k/a_n)| → 0`, and `P(S_n = k) = 0` for `k ∉ nb + dℤ`. -/
theorem localLimit_of_support (h : StableDomain μ α a) {j : ℕ} (hj : μ j ≠ 0) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      (latticeSpan μ : ℤ) ∣ k - n * ((j : ℤ) - 1) →
      |a n * walkProb μ n k - latticeSpan μ * stableDensity α (k / a n)| ≤ ε) ∧
    (∀ (n : ℕ) (k : ℤ), ¬ (latticeSpan μ : ℤ) ∣ k - n * ((j : ℤ) - 1) → walkProb μ n k = 0) := by
  refine ⟨fun ε hε => ?_, fun n k hk => ?_⟩
  · obtain ⟨N, hN⟩ := localLimit h hε
    exact ⟨N, fun n hn k hk => hN n hn k ((dvd_sub_mul_iff h hj n k).1 hk)⟩
  · exact walkProb_eq_zero_of_not_dvd h (fun h' => hk ((dvd_sub_mul_iff h hj n k).2 h'))

end PoissonDeclumping.Stable
