/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Discrete.MartingaleDominator
public import TauCeti.MeasureTheory.Function.UniformIntegrable
public import LeanPool.MathFin.Probability.Support.DoobContinuous
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.Convergence

/-!
# Lp continuous-martingale convergence (Theorem 4.3.10, Saporito)

A continuous martingale `(M_t)` bounded in `L^p` (`p ≥ 1`) converges almost
surely to an integrable `M_∞`; for `p > 1` it also converges in `L^p`.

  Proof strategy:
    1. Sample at natural times: `N_k(ω) := M (k : ℝ) ω` is a discrete
       martingale with respect to the sub-filtration `𝓕_k := 𝓕 (k : ℝ)`.
    2. The L^p bound transfers to N (since N_k = M_k for k : ℕ).
       Also L^1 bound from finite measure + L^p bound (Hölder when p > 1,
       direct when p = 1).
    3. Apply Mathlib's `Submartingale.exists_ae_tendsto_of_bdd` to get
       almost-sure convergence of N at natural times.
    4. By path continuity, the continuous-time limit at `t → ∞` agrees
       with the natural-time limit. (This step uses Doob's L^p maximal
       inequality on the increment martingale to show
       `sup_{n ≤ t ≤ n+1} |M_t - M_n| → 0` in probability.)
    5. For `p > 1`: L^p-boundedness gives uniform integrability in L^p
       (de la Vallée-Poussin) and combined with a.s. convergence yields
       L^p convergence (Vitali).

  Steps 3, 4, and 5 are all proved below.

  Step 3 (`p ≥ 1`, natural-time a.s. convergence): proved as
  `lp_continuous_martingale_converges_at_naturals`. Uses Mathlib's
  `Submartingale.ae_tendsto_limitProcess` after transferring the `L^p` bound
  to an `L^1` bound (Hölder on a finite measure space) at the natural-time
  sub-filtration.

  Step 4 (continuous-time bridge, `p > 1`, real-time in-measure): proved as
  `lp_continuous_martingale_tendstoInMeasure`. The increment martingale
  `Y_n(s) := M(n + s) − M(n)` is built on `shiftedFiltration 𝓕 n` via
  `Martingale.sub` of a shifted process and a constant; right-continuity
  transfers from `M`. The Tau Ceti bound via `maximal_ineq_norm` controls the running max,
  the eLpNorm-triangle + Hölder gives `‖M_(n+1) − M_n‖_1 → 0`, and
  Tau Ceti's `Martingale.ae_iSup_eNorm_lt_top` gives an a.s. bound for the running max.
  A `Nat.floor` set-inclusion argument then closes the conclusion modulo a
  μ-null set. The combined natural-a.s. + real-in-measure form is
  `lp_continuous_martingale_full`.

  Step 5 (`p > 1`, natural-time `L^p` convergence): proved as
  `lp_continuous_martingale_tendsto_eLpNorm_at_naturals`. Tau Ceti's Doob
  inequality `Martingale.eLpNorm_partialSups_norm_le` bounds the running max;
  monotone convergence (`lintegral_iSup'`) lifts it to the infinite sup
  `S ω := ⨆_k ‖N_k ω‖ₑ`, yielding `MemLp ((S ω).toReal) p` — the envelope
  dominator `MeasureTheory.LpDominator.dominator`, shared with
  `L2MartingaleConvergence`. The domination lemma
  `MemLp.uniformIntegrable_of_eNorm_le` from
  `TauCeti.MeasureTheory.Function.UniformIntegrable` then gives
  `UniformIntegrable (discreteSample M) (ofReal p) μ`, and Mathlib's Vitali
  (`tendsto_Lp_finite_of_tendsto_ae`) closes it.

  The textbook claims real-time a.s. convergence (under continuous paths)
  and real-time `L^p` convergence (under uniform integrability lifted to
  real time). Both require cadlag paths, which this file does not assume —
  only right-continuity. The in-measure form is the canonical conclusion
  for right-continuous martingales.

## Main definitions

* `discreteSample`: the sample `n ↦ M n` of a continuous-time process at the natural times.
* `natTimeSubfiltration`: the filtration `k ↦ 𝓕 k` at the natural times.
* `discreteSampleLimit`: the almost-sure limit of the discrete sample, from Mathlib's
  `Filtration.limitProcess`.
* `shiftedFiltration`: the filtration `t ↦ 𝓕 (n + t)` on `ℝ≥0`.
* `incrementProc`: the increment process `Y_n t = M (n + t) − M n`.

## Main results

* `lp_continuous_martingale_converges_at_naturals`: a martingale bounded in `Lᵖ` (`p ≥ 1`) on a
  finite measure space has an integrable `M_inf` with `M n → M_inf` almost surely along the
  natural times.
* `lp_continuous_martingale_tendsto_eLpNorm_at_naturals`: for `p > 1` and an `Lᵖ` bound `R`,
  `M n → discreteSampleLimit` in `Lᵖ` along the natural times.
* `lp_continuous_martingale_tendstoInMeasure`: for `p > 1` and right-continuous paths,
  `M t → discreteSampleLimit` in measure as `t → ∞` over real times.
* `lp_continuous_martingale_full`: for `p > 1` and right-continuous paths, an integrable `M_inf`
  with a.s. convergence along the natural times and convergence in measure over real times.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 4.3.10

## Tags

martingale convergence theorem, Lp-bounded martingale, Doob maximal inequality,
continuous martingale, Vitali, almost sure convergence, MSC 60G44, MSC 60G42, MSC 60F15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Discrete-time sample of a continuous-time process at natural times. -/
noncomputable def discreteSample (M : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Sub-filtration at natural times. -/
def natTimeSubfiltration (𝓕 : Filtration ℝ mΩ) : Filtration ℕ mΩ where
  seq n := 𝓕 (n : ℝ)
  mono' n m hnm := 𝓕.mono (by exact_mod_cast hnm)
  le' n := 𝓕.le _

/-- A continuous martingale sampled at natural times is a discrete
    martingale with respect to the natural-time sub-filtration. -/
private lemma discreteSample_martingale
    {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) :
    Martingale (discreteSample M) (natTimeSubfiltration 𝓕) μ := by
  refine ⟨?_, ?_⟩
  · intro n
    exact hM.stronglyAdapted (n : ℝ)
  · intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact hM.2 (i : ℝ) (j : ℝ) hij'

/-- L^1-norm bound from L^p-norm bound on a finite measure space (Hölder). -/
lemma eLpNorm_one_le_of_eLpNorm_p
    {μ : Measure Ω} {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    {R : ℝ} (hR : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := ENNReal.ofReal p) (f := f) h1_le_p hfm).trans ?_
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hp_pos.le, one_div_one]
  gcongr

/-- The L^1 bound for the discrete sample, expressed as `ℝ≥0` for the
    Mathlib submartingale-convergence API. -/
private lemma discreteSample_l1_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ R' : ℝ≥0,
      ∀ n : ℕ, eLpNorm (discreteSample M n) 1 μ ≤ (R' : ℝ≥0∞) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_exp_nn : 0 ≤ (1 : ℝ) - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp
    linarith
  set bound : ℝ≥0∞ := ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p)
  have hbound_lt_top : bound < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg h_exp_nn (measure_ne_top _ _))
  refine ⟨bound.toNNReal, fun n ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hbound_lt_top.ne]
  exact eLpNorm_one_le_of_eLpNorm_p hp (hbound (n : ℝ))
    ((hM.stronglyMeasurable (n : ℝ)).mono (𝓕.le _)).aestronglyMeasurable

/-- The canonical limit of the discrete sample: a `(⨆ k, 𝓕 k)`-measurable
    function to which the sample converges a.s. Defined via Mathlib's
    `Filtration.limitProcess`. -/
noncomputable def discreteSampleLimit
    (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) : Ω → ℝ :=
  (natTimeSubfiltration 𝓕).limitProcess (discreteSample M) μ

/-- The discrete sample converges a.s. to its limit process. -/
private lemma discreteSample_ae_tendsto_limitProcess
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ M (n : ℝ) ω) atTop (𝓝 (discreteSampleLimit μ 𝓕 M ω)) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  exact (discreteSample_martingale hM).submartingale.ae_tendsto_limitProcess
    ((iSup_le hR').trans_lt ENNReal.coe_lt_top)

/-- The limit process is integrable (in `L^1`). -/
private lemma discreteSampleLimit_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Integrable (discreteSampleLimit μ 𝓕 M) μ := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  have hAE : ∀ n, AEStronglyMeasurable (discreteSample M n) μ := fun n ↦
    (((discreteSample_martingale hM).stronglyMeasurable n).mono
        ((natTimeSubfiltration 𝓕).le _)).aestronglyMeasurable
  have h_memLp : MemLp (discreteSampleLimit μ 𝓕 M) 1 μ :=
    MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd hAE
      ((iSup_le hR').trans_lt ENNReal.coe_lt_top)
  exact h_memLp.integrable le_rfl

/-- Theorem 4.3.10 (Saporito Ch 4.3), natural-time formulation.

    A continuous-time martingale `(M_t)` bounded in `L^p` (`p ≥ 1`)
    sampled at natural times `t = n : ℕ` converges almost surely to an
    integrable limit `M_∞ := (natTimeSubfiltration 𝓕).limitProcess`.

    This is the discrete-time skeleton of Theorem 4.3.10. The full
    continuous-time conclusion `Tendsto (fun t : ℝ ↦ M t ω) atTop ...`
    follows from this skeleton + path continuity + a maximal-oscillation
    bound (via Doob's `L^p` inequality applied to the increment martingale
    `(M_t - M_n)_{t ∈ [n, n+1]}`). For `p > 1`, the `L^p` convergence
    follows from a.s. convergence + uniform integrability in `L^p`. Both
    extensions are documented as follow-on work. -/
theorem lp_continuous_martingale_converges_at_naturals
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∃ R : ℝ,
      ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ M (n : ℝ) ω) atTop (𝓝 (M_inf ω)) := by
  obtain ⟨R, hR⟩ := hbound
  exact ⟨discreteSampleLimit μ 𝓕 M,
    discreteSampleLimit_integrable hp hM hR,
    discreteSample_ae_tendsto_limitProcess hp hM hR⟩

/-! ### Step 5: `L^p` convergence at natural times (`p > 1`). -/

open MeasureTheory.LpDominator in
/-- L^p convergence at natural times (for `p > 1`). The discrete sample of an
`L^p`-bounded continuous martingale converges to the limit process in `L^p`. -/
theorem lp_continuous_martingale_tendsto_eLpNorm_at_naturals
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M (n : ℝ) ω - discreteSampleLimit μ 𝓕 M ω) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) := by
  have hp_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  have h_sample_meas : ∀ n, AEStronglyMeasurable (discreteSample M n) μ := fun n ↦
    (((discreteSample_martingale hM).stronglyMeasurable n).mono
        ((natTimeSubfiltration 𝓕).le _)).aestronglyMeasurable
  have hdom := dominator_memLp hp (discreteSample_martingale hM) (fun n ↦ hbound n)
  have hui := hdom.uniformIntegrable_of_eNorm_le hp_one_enn ENNReal.ofReal_ne_top h_sample_meas
    (fun n ↦ (norm_le_dominator hp (discreteSample_martingale hM)
      (fun k ↦ hbound k) n).mono fun _ h ↦ by
        simpa only [← ofReal_norm, Real.norm_eq_abs] using
          ENNReal.ofReal_le_ofReal (h.trans (le_abs_self _)))
  exact tendsto_Lp_finite_of_tendsto_ae hp_one_enn ENNReal.ofReal_ne_top h_sample_meas
    (Submartingale.memLp_limitProcess (discreteSample_martingale hM).submartingale
      ((iSup_le fun (n : ℕ) ↦ hbound (n : ℝ)).trans_lt ENNReal.ofReal_lt_top))
    hui.unifIntegrable (discreteSample_ae_tendsto_limitProcess hp.le hM hbound)

/-! ### Step 4: Continuous-time bridge. -/

/-- Shifted filtration on `ℝ≥0` starting at natural index `n`:
`(shiftedFiltration 𝓕 n).seq t = 𝓕 ((n : ℝ) + t)`. -/
def shiftedFiltration (𝓕 : Filtration ℝ mΩ) (n : ℕ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 ((n : ℝ) + (t : ℝ))
  mono' s t hst := 𝓕.mono <| by
    have : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  le' _ := 𝓕.le _

/-- Shifted continuous-time process `(t : ℝ≥0) ↦ M ((n : ℝ) + t)`. -/
private noncomputable def shiftedProc (M : ℝ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M ((n : ℝ) + (t : ℝ)) ω

/-- Constant-in-time process `(_ : ℝ≥0) ↦ M (n : ℝ)`. -/
private noncomputable def constProc (M : ℝ → Ω → ℝ) (n : ℕ) (_t : ℝ≥0) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Increment process `Y_n t ω := M ((n : ℝ) + t) ω - M (n : ℝ) ω`, indexed by `t : ℝ≥0`. -/
noncomputable def incrementProc (M : ℝ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M ((n : ℝ) + (t : ℝ)) ω - M (n : ℝ) ω

private lemma shiftedProc_martingale {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 μ) (n : ℕ) :
    Martingale (shiftedProc M n) (shiftedFiltration 𝓕 n) μ := by
  refine ⟨fun t ↦ hM.stronglyMeasurable _, fun s t hst ↦ ?_⟩
  have h_le : (n : ℝ) + (s : ℝ) ≤ (n : ℝ) + (t : ℝ) := by
    have hs_le_t : (s : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hst
    linarith
  exact hM.condExp_ae_eq h_le

private lemma constProc_martingale {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 μ) (n : ℕ) :
    Martingale (constProc M n) (shiftedFiltration 𝓕 n) μ := by
  have h_le_shifted : ∀ s : ℝ≥0,
      (𝓕 (n : ℝ) : MeasurableSpace Ω) ≤ (shiftedFiltration 𝓕 n).seq s := fun s ↦
    𝓕.mono (by
      have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
      linarith)
  refine ⟨fun t ↦ (hM.stronglyMeasurable _).mono (h_le_shifted t), fun s _t _hst ↦ ?_⟩
  have hM_meas : StronglyMeasurable[(shiftedFiltration 𝓕 n).seq s] (M (n : ℝ)) :=
    (hM.stronglyMeasurable _).mono (h_le_shifted s)
  change μ[fun ω ↦ M (n : ℝ) ω | (shiftedFiltration 𝓕 n).seq s] =ᵐ[μ] fun ω ↦ M (n : ℝ) ω
  rw [condExp_of_stronglyMeasurable ((shiftedFiltration 𝓕 n).le _) hM_meas (hM.integrable _)]

private lemma incrementProc_eq_sub (M : ℝ → Ω → ℝ) (n : ℕ) :
    incrementProc M n = shiftedProc M n - constProc M n := rfl

private lemma incrementProc_martingale {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 μ) (n : ℕ) :
    Martingale (incrementProc M n) (shiftedFiltration 𝓕 n) μ := by
  rw [incrementProc_eq_sub]
  exact (shiftedProc_martingale hM n).sub (constProc_martingale hM n)

/-- Right-continuity of `M (· , ω)` transfers to the increment `incrementProc M n (· , ω)`. -/
private lemma incrementProc_isRightContinuous
    {M : ℝ → Ω → ℝ} (hM_cont : ∀ ω, _root_.IsRightContinuous (fun t : ℝ ↦ M t ω))
    (n : ℕ) (ω : Ω) :
    _root_.IsRightContinuous (fun t : ℝ≥0 ↦ incrementProc M n t ω) := by
  intro a
  refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
  set shift : ℝ≥0 → ℝ := fun t ↦ ((n : ℝ) + (t : ℝ)) with shift_def
  have h_shift_cont : Continuous shift :=
    continuous_const.add NNReal.continuous_coe
  have h_f_rc : ContinuousWithinAt (fun u : ℝ ↦ M u ω) (Set.Ioi (shift a)) (shift a) :=
    hM_cont ω _
  have h_mapsto : Set.MapsTo shift (Set.Ioi a) (Set.Ioi (shift a)) := fun t ht ↦ by
    have hlt : (a : ℝ) < (t : ℝ) := by
      exact_mod_cast ht
    change shift a < shift t
    simp only [shift_def]
    linarith
  exact h_f_rc.comp h_shift_cont.continuousWithinAt h_mapsto

/-- L^p triangle: `eLpNorm (M_(n+1) - M_n) p μ → 0` from step 5 + reindex. -/
lemma eLpNorm_increment_p_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  set L : Ω → ℝ := discreteSampleLimit μ 𝓕 M
  have h_meas_M : ∀ k : ℝ, AEStronglyMeasurable (M k) μ := fun k ↦
    ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable
  have h_meas_L : AEStronglyMeasurable L μ :=
    (Submartingale.memLp_limitProcess (discreteSample_martingale hM).submartingale
      ((iSup_le fun (n : ℕ) ↦ hbound (n : ℝ)).trans_lt ENNReal.ofReal_lt_top)).aestronglyMeasurable
  have h_one_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  -- step 5 gives ‖M n - L‖_p → 0
  have hL_step5 : Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M (n : ℝ) ω - L ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
    lp_continuous_martingale_tendsto_eLpNorm_at_naturals hp hM hbound
  -- ‖M (n+1) - L‖_p → 0 (reindex via `tendsto_add_atTop_iff_nat 1`)
  have hL_shift : Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M ((n : ℝ) + 1) ω - L ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    refine ((tendsto_add_atTop_iff_nat 1).mpr hL_step5).congr (fun n ↦ ?_)
    congr 1
    funext ω
    congr 2
    push_cast
    ring
  -- triangle: ‖M(n+1) - M n‖_p ≤ ‖M(n+1) - L‖_p + ‖M n - L‖_p
  have h_triangle : ∀ n : ℕ,
      eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) (ENNReal.ofReal p) μ
        ≤ eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - L ω) (ENNReal.ofReal p) μ
          + eLpNorm (fun ω ↦ M (n : ℝ) ω - L ω) (ENNReal.ofReal p) μ := fun n ↦ by
    have h_eq : (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω)
        = (fun ω ↦ (M ((n : ℝ) + 1) ω - L ω) - (M (n : ℝ) ω - L ω)) := by
      funext ω
      ring
    rw [h_eq]
    exact eLpNorm_sub_le h_one_le_p
  have h_rhs : Tendsto (fun n : ℕ ↦
      eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - L ω) (ENNReal.ofReal p) μ +
      eLpNorm (fun ω ↦ M (n : ℝ) ω - L ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    have h : Tendsto _ atTop (𝓝 ((0 : ℝ≥0∞) + (0 : ℝ≥0∞))) :=
      Filter.Tendsto.add hL_shift hL_step5
    rwa [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) h_rhs (fun _ ↦ zero_le) h_triangle

/-- L^1 triangle: `eLpNorm (M_(n+1) - M_n) 1 μ → 0` via Hölder from `p → 0`. -/
lemma eLpNorm_increment_one_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) 1 μ) atTop (𝓝 0) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have h_meas_diff : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) μ := fun n ↦
    ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable.sub
      ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable
  have h_one_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  set C : ℝ≥0∞ := μ Set.univ ^ (1 - 1 / p) with C_def
  have hLp : Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
    eLpNorm_increment_p_tendsto_zero hp hM hbound
  have h_holder : ∀ n : ℕ, eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) 1 μ
      ≤ eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) (ENNReal.ofReal p) μ * C := fun n ↦ by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ)
      (p := 1) (q := ENNReal.ofReal p) h_one_le_p (h_meas_diff n)).trans ?_
    rw [C_def, ENNReal.toReal_one, ENNReal.toReal_ofReal hp_pos.le, one_div_one]
  have hC_ne_top : C ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg
      (by
        have hp_inv_le_one : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp.le
        linarith)
      (measure_ne_top _ _)
  have h_bound_tendsto : Tendsto (fun n : ℕ ↦ eLpNorm
      (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) (ENNReal.ofReal p) μ * C) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hLp (Or.inr hC_ne_top)
    rwa [zero_mul] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) h_bound_tendsto (fun _ ↦ zero_le) h_holder

/-- The increment's `L^1` integral, in real-valued form. -/
lemma integral_norm_increment_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ‖M ((n : ℝ) + 1) ω - M (n : ℝ) ω‖ ∂μ) atTop (𝓝 0) := by
  have h_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) μ := fun n ↦
    ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable.sub
      ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable
  have h_eLp1 := eLpNorm_increment_one_tendsto_zero hp hM hbound
  have h_eq : (fun n : ℕ ↦ ∫ ω, ‖M ((n : ℝ) + 1) ω - M (n : ℝ) ω‖ ∂μ) =
      (fun n : ℕ ↦ (eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) 1 μ).toReal) := by
    funext n
    rw [integral_norm_eq_lintegral_eNorm (h_meas n), eLpNorm_one_eq_lintegral_eNorm (h_meas n)]
  rw [h_eq]
  have h_toReal :
      Tendsto (fun n : ℕ ↦ (eLpNorm (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) 1 μ).toReal)
        atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_eLp1
  simpa using h_toReal

/-- Sup-in-measure: for each `ε > 0`, `μ.real {ω | ε ≤ sup_{t ≤ 1} |incrementProc M n t ω|} → 0`. -/
private lemma sup_increment_measure_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hM_cont : ∀ ω, _root_.IsRightContinuous (fun t : ℝ ↦ M t ω))
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ ⨆ i : Set.Iic (1 : ℝ≥0),
      ‖incrementProc M n i ω‖}) atTop (𝓝 0) := by
  set S : ℕ → Set Ω := fun n ↦
    {ω | ε ≤ ⨆ i : Set.Iic (1 : ℝ≥0), ‖incrementProc M n i ω‖}
  have h_bound : ∀ n : ℕ,
      ε * μ.real (S n) ≤ ∫ ω, ‖M ((n : ℝ) + 1) ω - M (n : ℝ) ω‖ ∂μ := fun n ↦ by
    have h_max := ProbabilityTheory.maximal_ineq_norm (incrementProc_martingale hM n) ε 1
      (incrementProc_isRightContinuous hM_cont n)
    rw [smul_eq_mul] at h_max
    refine h_max.trans ?_
    have h_endpoint :
        (fun ω ↦ ‖incrementProc M n 1 ω‖)
          = fun ω ↦ ‖M ((n : ℝ) + 1) ω - M (n : ℝ) ω‖ := by
      funext ω
      change ‖M ((n : ℝ) + ((1 : ℝ≥0) : ℝ)) ω - _‖ = _
      rw [NNReal.coe_one]
    rw [h_endpoint]
    have hmem (t : ℝ) : MemLp (M t) (ENNReal.ofReal p) μ :=
      (hbound t).trans_lt ENNReal.ofReal_lt_top
    have hint : Integrable (fun ω ↦ M ((n : ℝ) + 1) ω - M (n : ℝ) ω) μ :=
      ((hmem _).sub (hmem _)).integrable (ENNReal.one_le_ofReal.mpr hp.le)
    exact setIntegral_le_integral hint.norm (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
  -- ε * μ.real S → 0 by sandwich with integral_norm_increment_tendsto_zero
  have h_int := integral_norm_increment_tendsto_zero hp hM hbound
  have h_eps_mul : Tendsto (fun n : ℕ ↦ ε * μ.real (S n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_int
      (fun n ↦ mul_nonneg hε.le measureReal_nonneg) h_bound
  -- divide by ε
  have h_div := h_eps_mul.const_mul ε⁻¹
  simp only [mul_zero] at h_div
  refine h_div.congr fun n ↦ ?_
  rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]

/-- The norm of the increment trajectory on `[0, 1]` is `BddAbove` a.s.,
by Tau Ceti's continuous-time bound `Martingale.ae_iSup_eNorm_lt_top`. -/
private lemma incrementProc_bddAbove_ae
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 μ)
    (hM_cont : ∀ ω, _root_.IsRightContinuous (fun t : ℝ ↦ M t ω)) (n : ℕ) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun i : Set.Iic (1 : ℝ≥0) ↦
      ‖incrementProc M n i ω‖) := by
  have hrc : ∀ᵐ ω ∂μ, ∀ t < (1 : ℝ≥0),
      ContinuousWithinAt (fun u ↦ incrementProc M n u ω) (Set.Ioi t) t :=
    ae_of_all _ fun ω t _ ↦ incrementProc_isRightContinuous hM_cont n ω t
  have h_ne_top := (incrementProc_martingale hM n).ae_iSup_eNorm_lt_top hrc
  filter_upwards [h_ne_top] with ω hω
  refine ⟨(⨆ t ≤ (1 : ℝ≥0), ‖incrementProc M n t ω‖ₑ).toReal, ?_⟩
  rintro _ ⟨i, rfl⟩
  dsimp only
  rw [← ENNReal.toReal_ofReal (norm_nonneg (incrementProc M n i ω))]
  exact ENNReal.toReal_mono hω.ne
    (by rw [ofReal_norm]; exact le_iSup₂_of_le i i.2 le_rfl)

/-- Theorem 4.3.10 (Saporito Ch 4.3), real-time convergence in measure.

An `L^p`-bounded continuous-time martingale `(M_t)` with right-continuous paths on a finite
probability space converges in measure to the natural-time limit `discreteSampleLimit μ 𝓕 M`
as `t → ∞` along all reals (not just along natural numbers). -/
theorem lp_continuous_martingale_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hM_cont : ∀ ω, _root_.IsRightContinuous (fun t : ℝ ↦ M t ω))
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    TendstoInMeasure μ M atTop (discreteSampleLimit μ 𝓕 M) := by
  set L := discreteSampleLimit μ 𝓕 M
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- Step 3 a.s. → in-measure for the discrete sample
  have h_disc_meas : TendstoInMeasure μ (discreteSample M) atTop L :=
    tendstoInMeasure_of_tendsto_ae
      (fun n : ℕ ↦ ((hM.stronglyMeasurable _).mono (𝓕.le _)).aestronglyMeasurable)
      (discreteSample_ae_tendsto_limitProcess hp.le hM hbound)
  rw [tendstoInMeasure_iff_measureReal_norm] at h_disc_meas
  have h_B := h_disc_meas (ε / 2) hε2
  have h_A := sup_increment_measure_tendsto_zero hp hM hM_cont hbound hε2
  have h_A_real := h_A.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h_B_real := h_B.comp (tendsto_nat_floor_atTop (α := ℝ))
  set A : ℕ → Set Ω := fun n ↦ {ω | ε / 2 ≤ ⨆ i : Set.Iic (1 : ℝ≥0), ‖incrementProc M n i ω‖}
  set B : ℕ → Set Ω := fun n ↦ {ω | ε / 2 ≤ ‖discreteSample M n ω - L ω‖}
  -- Set inclusion (a.s.): for t ≥ 0, {ω | ε ≤ ‖M t - L‖} ⊆ A_{⌊t⌋} ∪ B_{⌊t⌋}
  -- (modulo a μ-null set where the increment trajectory is unbounded — then the
  -- ℝ-valued iSup defaults to 0 and `‖increment s ω‖ ≤ iSup` may fail).
  have h_subset : ∀ᶠ t in (Filter.atTop : Filter ℝ),
      ∀ᵐ ω ∂μ,
        ω ∈ {ω | ε ≤ ‖M t ω - L ω‖} → ω ∈ A (Nat.floor t) ∪ B (Nat.floor t) := by
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht ↦ ?_⟩
    filter_upwards [incrementProc_bddAbove_ae hM hM_cont (Nat.floor t)] with ω h_bdd hω
    set n := Nat.floor t
    have h_n_cast : (n : ℝ) ≤ t := Nat.floor_le ht
    have h_t_lt : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
    have h_tri : ‖M t ω - L ω‖ ≤ ‖M t ω - M (n : ℝ) ω‖ + ‖M (n : ℝ) ω - L ω‖ := by
      rw [show M t ω - L ω = (M t ω - M (n : ℝ) ω) + (M (n : ℝ) ω - L ω) by ring]
      exact norm_add_le _ _
    by_cases hAB : ε / 2 ≤ ‖M t ω - M (n : ℝ) ω‖
    · left
      change ε / 2 ≤ ⨆ i : Set.Iic (1 : ℝ≥0), ‖incrementProc M n i ω‖
      refine hAB.trans ?_
      set s : ℝ≥0 := ⟨t - (n : ℝ), by linarith⟩
      have h_s_le_one : s ≤ 1 := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one]
        change t - (n : ℝ) ≤ 1
        linarith
      rw [show M t ω - M (n : ℝ) ω = incrementProc M n s ω by
        change _ = M ((n : ℝ) + (s : ℝ)) ω - M (n : ℝ) ω
        congr 2
        change t = (n : ℝ) + (t - (n : ℝ))
        ring]
      exact le_ciSup (f := fun i : Set.Iic (1 : ℝ≥0) ↦ ‖incrementProc M n i ω‖) h_bdd
        ⟨s, h_s_le_one⟩
    · right
      change ε / 2 ≤ ‖M (n : ℝ) ω - L ω‖
      have hAB' : ‖M t ω - M (n : ℝ) ω‖ < ε / 2 := not_le.mp hAB
      linarith [le_trans hω h_tri]
  have h_bound : ∀ᶠ t in (Filter.atTop : Filter ℝ),
      μ.real {ω | ε ≤ ‖M t ω - L ω‖} ≤
        μ.real (A (Nat.floor t)) + μ.real (B (Nat.floor t)) := by
    filter_upwards [h_subset] with t hsub
    have h_meas_le : μ {ω | ε ≤ ‖M t ω - L ω‖} ≤
        μ (A (Nat.floor t) ∪ B (Nat.floor t)) := measure_mono_ae hsub
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h_meas_le).trans
      (measureReal_union_le _ _)
  have h_sum : Tendsto (fun t : ℝ ↦ μ.real (A (Nat.floor t)) + μ.real (B (Nat.floor t)))
      atTop (𝓝 0) := by
    have h := h_A_real.add h_B_real
    rwa [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) h_bound

/-- Theorem 4.3.10 (Saporito Ch 4.3), combined natural-a.s. and real-time-in-measure.

For an `L^p`-bounded continuous-time martingale (`p > 1`) with right-continuous paths on a
finite probability space, there is an integrable limit `M_∞` to which the process converges
a.s. at natural times and in measure as `t → ∞` along all reals. -/
theorem lp_continuous_martingale_full
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hM_cont : ∀ ω, _root_.IsRightContinuous (fun t : ℝ ↦ M t ω))
    (hbound : ∃ R : ℝ,
      ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ M (n : ℝ) ω) atTop (𝓝 (M_inf ω))) ∧
      TendstoInMeasure μ M atTop M_inf := by
  obtain ⟨R, hR⟩ := hbound
  refine ⟨discreteSampleLimit μ 𝓕 M, ?_, ?_, ?_⟩
  · exact discreteSampleLimit_integrable hp.le hM hR
  · exact discreteSample_ae_tendsto_limitProcess hp.le hM hR
  · exact lp_continuous_martingale_tendstoInMeasure hp hM hM_cont hR

end MathFin
