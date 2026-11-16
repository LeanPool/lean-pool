/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs
-- follow the v4.35.0 `eLpNorm` triangle, zero and exponent-comparison lemmas and pass the
-- measurability witnesses its norm formulas require.
-- Modified 2026-10-31 by the KLS formalization project: `eLpNorm_two_rpow_eq_lintegral_sq` and
-- `eLpNorm_sq_eq_lintegral_nnnorm_sq` take `hg : AEStronglyMeasurable g μ`, which
-- `eLpNorm_nnreal_pow_eq_lintegral` requires in Mathlib v4.35.0 (where `eLpNorm` of a
-- non-a.e.-strongly-measurable function is `∞`); their callers pass existing witnesses.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionIncrement

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **L¹-limit of martingales is a martingale.** If each `M n` is an
`ℱ`-martingale and `M n t → F t` in `L¹(μ)` for every `t` (with `F` adapted and
integrable), then `F` is an `ℱ`-martingale. The conditional expectation is an
`L¹`-contraction (`eLpNorm_one_condExp_le_eLpNorm`), so the martingale identity
`μ[M n t | ℱ s] =ᵐ M n s` passes to the limit. Reusable for the L²-Itô integral
(#5) and its compensated analogue (#6). -/
lemma martingale_of_tendsto_eLpNorm_one
    {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {ℱ : MeasureTheory.Filtration ℝ m0}
    {M : ℕ → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ}
    (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
    (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
    (hadapt : MeasureTheory.StronglyAdapted ℱ F)
    (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
    (htend : ∀ t, Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
    MeasureTheory.Martingale F ℱ μ := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  -- The target seminorm is bounded by `‖Mₙt − Ft‖₁ + ‖Mₙs − Fs‖₁` for every `n`.
  have hbound : ∀ n, MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
      ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
        + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
    intro n
    have hdecomp : (μ[F t | ℱ s] - F s)
        = (μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s) := by ring
    calc MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
        = MeasureTheory.eLpNorm
            ((μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s)) 1 μ := by
          rw [hdecomp]
      _ ≤ MeasureTheory.eLpNorm (μ[F t | ℱ s] - μ[M n t | ℱ s]) 1 μ
          + MeasureTheory.eLpNorm (μ[M n t | ℱ s] - F s) 1 μ :=
          MeasureTheory.eLpNorm_add_le (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
          gcongr
          · have h_sub : (μ[F t | ℱ s] - μ[M n t | ℱ s]) =ᵐ[μ] μ[F t - M n t | ℱ s] :=
              (MeasureTheory.condExp_sub (hint t) (hMint n t) (ℱ s)).symm
            rw [MeasureTheory.eLpNorm_congr_ae h_sub]
            calc MeasureTheory.eLpNorm (μ[F t - M n t | ℱ s]) 1 μ
                ≤ MeasureTheory.eLpNorm (F t - M n t) 1 μ :=
                  MeasureTheory.eLpNorm_condExp_le_eLpNorm (F t - M n t) (le_refl 1)
              _ = MeasureTheory.eLpNorm (M n t - F t) 1 μ := by
                  rw [show F t - M n t = -(M n t - F t) from by ring,
                      MeasureTheory.eLpNorm_neg]
          · refine le_of_eq (MeasureTheory.eLpNorm_congr_ae ?_)
            exact ((hM n).condExp_ae_eq hst).sub (Filter.EventuallyEq.refl _ (F s))
  -- Send `n → ∞`: the bound tends to `0`, so the (constant) target seminorm is `0`.
  have hzero : MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ = 0 := by
    have htend2 : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ) Filter.atTop (nhds 0) := by
      simpa using (htend t).add (htend s)
    refine le_antisymm ?_ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend2
      (Filter.Eventually.of_forall hbound)
  rw [MeasureTheory.eLpNorm_eq_zero_iff (by norm_num)] at hzero
  filter_upwards [hzero] with ω hω
  simpa [Pi.sub_apply, sub_eq_zero] using hω

/-- **L²-convergence ⇒ L¹-convergence** (probability measure). The `L¹` seminorm
is dominated by the `L²` seminorm when `μ` is a probability measure, so an
`L²`-null sequence is `L¹`-null. Bridges the `L²`-Cauchy approximating sequence
(`cauchySeq_simpleIntegralLp_brownian`) to the `L¹` hypothesis of
`martingale_of_tendsto_eLpNorm_one`. -/
lemma tendsto_eLpNorm_one_of_eLpNorm_two
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} (hg : ∀ n, MeasureTheory.AEStronglyMeasurable (g n) μ)
    (h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 1 μ)
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
    (fun n => (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) (by norm_num)
      (hg n)).trans
      (le_of_eq (by simp [MeasureTheory.measure_univ])))

/-- **L² Hölder product.** `‖f·g‖₁ ≤ ‖f‖₂·‖g‖₂` (Cauchy–Schwarz). The
conjunct-2 (quadratic-variation) limit needs `aₙ²→a²` in `L¹` from `aₙ→a` in
`L²`, via `aₙ²−a² = (aₙ−a)(aₙ+a)` and this bound. -/
lemma eLpNorm_one_mul_le {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (f * g) 1 μ
      ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf.mul hg).aestronglyMeasurable]
  calc ∫⁻ x, ‖(f * g) x‖ₑ ∂μ
      = ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ := by
        refine lintegral_congr (fun x => ?_); rw [Pi.mul_apply, enorm_mul]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
        * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.enorm hg.enorm
    _ = MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
              hf.aestronglyMeasurable,
            MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
              hg.aestronglyMeasurable]
        norm_num

/-- **Squares converge in L¹ from L²-convergence.** If `aₙ → b` in `L²` (with
`‖b‖₂ < ⊤`) then `aₙ² → b²` in `L¹`. The conjunct-2 (quadratic-variation) engine.
Proof: `aₙ²−b² = (aₙ−b)(aₙ+b)`, bounded by `eLpNorm_one_mul_le` and the triangle
`‖aₙ+b‖₂ ≤ ‖aₙ−b‖₂ + 2‖b‖₂`, then squeezed. -/
lemma tendsto_eLpNorm_one_sq_sub
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by
  have hbound : ∀ n, MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ
      ≤ MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ) := by
    intro n
    have hfac : (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) = (a n - b) * (a n + b) := by
      funext ω; simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]; ring
    rw [hfac]
    refine le_trans (eLpNorm_one_mul_le ((ha n).sub hb) ((ha n).add hb)) ?_
    gcongr
    calc MeasureTheory.eLpNorm (a n + b) 2 μ
        = MeasureTheory.eLpNorm ((a n - b) + (2 : ℝ) • b) 2 μ := by
          congr 1; funext ω; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]; ring
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + MeasureTheory.eLpNorm ((2 : ℝ) • b) 2 μ :=
          MeasureTheory.eLpNorm_add_le (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ := by
          gcongr
          refine le_trans MeasureTheory.eLpNorm_const_smul_le (le_of_eq ?_)
          rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) from by simp [Real.enorm_eq_ofReal_abs]]
  have htend_bound : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ))
      l (nhds 0) := by
    have h1 := htend.add (tendsto_const_nhds (x := 2 * MeasureTheory.eLpNorm b 2 μ))
    have h2C : (2 : ℝ≥0∞) * MeasureTheory.eLpNorm b 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hbfin
    have := ENNReal.Tendsto.mul htend (Or.inr (by simpa using h2C)) h1
      (Or.inr (by norm_num))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend_bound
    (fun _ => bot_le) hbound

/-- **Right-continuity of the horizon integral.** For measurable `φ : Ω → ℝ → ℝ≥0∞`
integrable (iterated) over `[0, T]`, the slab integral over `(s₀, r]` tends to `0`
as `r ↓ s₀` (for `0 ≤ s₀ < T`). Tonelli (`setLIntegral_prod`) reduces this to
`tendsto_setLIntegral_zero` for `P ⊗ volume` on the sets `univ ×ˢ (s₀, r]`, of
product measure `ofReal (r − s₀) → 0`. Underlies the right-`L²`-continuity of the
L² Itô integral's slices (`‖F_r − F_{s₀}‖₂² = ∫∫_{(s₀,r]}‖H‖²`). -/
lemma tendsto_setLIntegral_Ioc_prod_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (φ : Ω → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ))
    {s₀ T : ℝ} (hs₀ : 0 ≤ s₀) (hs₀T : s₀ < T)
    (h_fin : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, φ ω u ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s₀ r, φ ω u ∂volume ∂P)
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
  have hset : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Icc
  set f : Ω × ℝ → ℝ≥0∞ :=
    ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T).indicator (Function.uncurry φ) with hf
  have h_tot : ∫⁻ z, f z ∂(P.prod volume) ≠ ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator hset,
        MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
        MeasureTheory.Measure.restrict_univ]
    simpa using h_fin
  have h_meas_to_zero : Filter.Tendsto
      (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
    have hval : (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
        = fun r => ENNReal.ofReal (r - s₀) := by
      funext r
      rw [MeasureTheory.Measure.prod_prod, measure_univ, one_mul, Real.volume_Ioc]
    rw [hval]
    have h1 : Filter.Tendsto (fun r => r - s₀)
        (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
      have h0 : Filter.Tendsto (fun r => r - s₀) (nhds s₀) (nhds (s₀ - s₀)) :=
        (continuous_sub_right s₀).tendsto s₀
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  have h_zero := MeasureTheory.tendsto_setLIntegral_zero (μ := P.prod volume) (f := f)
    (s := fun r => (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) h_tot h_meas_to_zero
  refine h_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs₀T] with r hr
  have hsub : (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r ⊆ (Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T :=
    Set.prod_mono (le_refl _) (fun u hu => ⟨le_of_lt (lt_of_le_of_lt hs₀ hu.1),
      le_of_lt (lt_of_le_of_lt hu.2 hr.2)⟩)
  have hset' : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hstep1 : ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, f z ∂(P.prod volume)
      = ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, Function.uncurry φ z ∂(P.prod volume) := by
    refine MeasureTheory.setLIntegral_congr_fun hset' (fun z hz => ?_)
    rw [hf, Set.indicator_of_mem (hsub hz)]
  rw [hstep1, MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
      MeasureTheory.Measure.restrict_univ]
  rfl

/-- **Orthogonal-increment identity for L² martingales.** For an `ℱ`-martingale
`M` on `ℝ` with square-integrable time-slices, the increment from `s` to `t ≥ s`
is `L²`-orthogonal to `M s`, giving the Pythagoras identity
`𝔼[(M t − M s)²] = 𝔼[(M t)²] − 𝔼[(M s)²]`. Cross term: `M s` is `ℱ s`-measurable,
so `𝔼[M s · M t] = 𝔼[M s · 𝔼[M t | ℱ s]] = 𝔼[(M s)²]` by the pull-out property and
the martingale identity. This underlies the increment isometry of the L² Itô
integral and the right-`L²`-continuity of its time-slices. -/
lemma integral_sq_increment_eq_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P :=
    hMs.integrable_mul hMt
  -- cross term: `∫ M s · M t = ∫ (M s)²` via pull-out + martingale identity.
  have h_cross : ∫ ω, M s ω * M t ω ∂P = ∫ ω, (M s ω) ^ 2 ∂P := by
    have h_pull : P[(fun ω => M s ω * M t ω) | ℱ s]
        =ᵐ[P] fun ω => M s ω * P[M t | ℱ s] ω := by
      have := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ s) (hmart.stronglyAdapted s) hcr (hmart.integrable t)
      exact this
    calc ∫ ω, M s ω * M t ω ∂P
        = ∫ ω, P[(fun ω => M s ω * M t ω) | ℱ s] ω ∂P :=
          (MeasureTheory.integral_condExp hm).symm
      _ = ∫ ω, M s ω * P[M t | ℱ s] ω ∂P := integral_congr_ae h_pull
      _ = ∫ ω, M s ω * M s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hmart.condExp_ae_eq hst] with ω hω using by rw [hω]
      _ = ∫ ω, (M s ω) ^ 2 ∂P := by simp_rw [pow_two]
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  calc ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_)); ring
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - 2 * (∫ ω, M s ω * M t ω ∂P) + ∫ ω, (M s ω) ^ 2 ∂P := by
        have e1 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
            = (∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω, (M s ω) ^ 2 ∂P :=
          integral_add (hMt2.sub (hcr.const_mul 2)) hMs2
        have e2 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
            = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, 2 * (M s ω * M t ω) ∂P :=
          integral_sub hMt2 (hcr.const_mul 2)
        have e3 : ∫ ω, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω, M s ω * M t ω ∂P :=
          integral_const_mul 2 _
        rw [e1, e2, e3]
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by rw [h_cross]; ring

/-- **Monotonicity of the second moment of an L² martingale.** Immediate from the
orthogonal-increment identity: `𝔼[(M t)²] − 𝔼[(M s)²] = 𝔼[(M t − M s)²] ≥ 0`. This
gives the `L²`-Cauchy property at every intermediate time `t ≤ T` from the
endpoint (`T`) `L²`-bound, since `M t − M' t` is itself a martingale. -/
lemma integral_sq_mono_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M s ω) ^ 2 ∂P ≤ ∫ ω, (M t ω) ^ 2 ∂P := by
  have h := integral_sq_increment_eq_of_martingale hmart hMs hMt hst
  have h_nn : 0 ≤ ∫ ω, (M t ω - M s ω) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith [h, h_nn]

/-- **Conditional Pythagoras for L² martingales.** `𝔼[(M t − M s)² | ℱ s] =ᵐ
𝔼[(M t)² | ℱ s] − (M s)²`. Conditional version of the orthogonal-increment identity;
the cross term `𝔼[M s · M t | ℱ s] =ᵐ (M s)²` by pull-out + the martingale identity. -/
lemma condExp_sq_increment_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P := hMs.integrable_mul hMt
  have hMsm : StronglyMeasurable[ℱ s] (M s) := hmart.stronglyAdapted s
  have hMs2m : StronglyMeasurable[ℱ s] (fun ω => (M s ω) ^ 2) := by
    have heq : (fun ω => (M s ω) ^ 2) = (fun ω => M s ω * M s ω) := by funext ω; ring
    rw [heq]; exact hMsm.mul hMsm
  have hf_int : MeasureTheory.Integrable (fun ω => (M t ω - M s ω) ^ 2) P := by
    have heq : (fun ω => (M t ω - M s ω) ^ 2)
        = (fun ω => (M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) := by funext ω; ring
    rw [heq]; exact (hMt2.sub (hcr.const_mul 2)).add hMs2
  have hcross_ae : P[(fun ω => M s ω * M t ω) | ℱ s] =ᵐ[P] fun ω => (M s ω) ^ 2 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ s) hMsm
      (show MeasureTheory.Integrable ((M s) * (M t)) P from hcr)
      (hmart.integrable t)
    filter_upwards [hpull, hmart.condExp_ae_eq hst] with ω hp hmeq
    have hp' : P[(fun ω => M s ω * M t ω) | ℱ s] ω = M s ω * (P[M t | ℱ s]) ω := by
      have : (fun ω => M s ω * M t ω) = (M s) * (M t) := rfl
      rw [this]; simpa [Pi.mul_apply] using hp
    rw [hp', hmeq, ← pow_two]
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf_int
    (fun B _ _ => (MeasureTheory.integrable_condExp.sub hMs2).integrableOn)
    (fun B hB _ => ?_)
    ((MeasureTheory.stronglyMeasurable_condExp.sub hMs2m).aestronglyMeasurable)
  have hcross : ∫ ω in B, M s ω * M t ω ∂P = ∫ ω in B, (M s ω) ^ 2 ∂P :=
    calc ∫ ω in B, M s ω * M t ω ∂P
        = ∫ ω in B, (P[(fun ω => M s ω * M t ω) | ℱ s]) ω ∂P :=
          (MeasureTheory.setIntegral_condExp hm hcr hB).symm
      _ = ∫ ω in B, (M s ω) ^ 2 ∂P :=
          MeasureTheory.setIntegral_congr_ae (hm B hB) (hcross_ae.mono (fun ω hω _ => hω))
  -- LHS `∫_B (condExp(M t²|ℱ s) − M s²)`
  have e1 : ∫ ω in B, ((P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2) ∂P
      = (∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P) - ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn hMs2.integrableOn
  have e1' : ∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P = ∫ ω in B, (M t ω) ^ 2 ∂P :=
    MeasureTheory.setIntegral_condExp hm hMt2 hB
  -- RHS `∫_B (M t − M s)²`
  have hexp : ∫ ω in B, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P :=
    MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => by ring)
  have e2a : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
      = (∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_add ((hMt2.sub (hcr.const_mul 2)).integrableOn) hMs2.integrableOn
  have e2b : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
      = (∫ ω in B, (M t ω) ^ 2 ∂P) - ∫ ω in B, 2 * (M s ω * M t ω) ∂P :=
    MeasureTheory.integral_sub hMt2.integrableOn (hcr.const_mul 2).integrableOn
  have e2c : ∫ ω in B, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω in B, M s ω * M t ω ∂P :=
    MeasureTheory.integral_const_mul 2 _
  rw [e1, e1', hexp, e2a, e2b, e2c, hcross]; ring

/-- **Cauchy-at-each-time bound for the simple integral.** For two adapted
simple integrands sharing the endpoint `T`, the `L²(P)`-distance of their integrals
at any intermediate time `t ≤ T` is bounded by the (endpoint) `L²(λ⊗P)`-distance of
their evals over `[0, T]`. The difference process `simpleIntegral W H₁ · −
simpleIntegral W H₂ ·` is a martingale (`Martingale.sub`), so its second moment is
monotone in time (`integral_sq_mono_of_martingale`), capping the `t`-value by the
`T`-value, which is the endpoint difference isometry `diff_isometry_simple`. This
upgrades the endpoint `L²`-Cauchy hypothesis to `L²`-Cauchy at *every* `t ≤ T`
without a general-`t` refinement re-derivation. -/
lemma simpleIntegral_lintegral_sq_sub_le_endpoint_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : ℝ → Ω → ℝ :=
    fun u ω => simpleIntegral W H₁ u ω - simpleIntegral W H₂ u ω with hM
  have hmart : MeasureTheory.Martingale M
      ℱ P :=
    (martingale_simpleIntegral_brownian W ℱ hℱ H₁ h_adapt₁).sub
      (martingale_simpleIntegral_brownian W ℱ hℱ H₂ h_adapt₂)
  have hMemLp : ∀ {u : ℝ}, 0 ≤ u → u ≤ T → MeasureTheory.MemLp (M u) 2 P :=
    fun {u} hu huT =>
      (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ hT H₁ h_adapt₁ hu huT).sub
        (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ hT H₂ h_adapt₂ hu huT)
  -- bridge `∫⁻‖M u‖₊² = ofReal (∫ (M u)²)` for `M u ∈ L²`.
  have h_bridge : ∀ {u : ℝ}, MeasureTheory.MemLp (M u) 2 P →
      ∫⁻ ω, (‖M u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (M u ω) ^ 2 ∂P) := by
    intro u hu
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    refine lintegral_congr (fun ω => ?_)
    rw [show (‖M u ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖M u ω‖ from (ofReal_norm _).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  calc ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (∫ ω, (M t ω) ^ 2 ∂P) := h_bridge (hMemLp ht_nn htT)
    _ ≤ ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_sq_mono_of_martingale hmart
          (hMemLp ht_nn htT) (hMemLp (le_of_lt hT) (le_refl T)) htT)
    _ = ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := (h_bridge (hMemLp (le_of_lt hT) (le_refl T))).symm
    _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp only [hM]
        exact SimplePredictable.diff_isometry_simple W ℱ hℱ hT H₁ H₂ h_eq h_adapt₁ h_adapt₂

/-- **A single adapted simple approximant within `ε` on `[0, T]`.** Extracted from
the convergent dense sequence `adaptedSimple_dense_L2_brownian`. -/
lemma exists_adaptedSimple_within
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G : SimplePredictable Ω T,
      (∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (G.partition i.castSucc)) (G.ξ i)) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε := by
  obtain ⟨Hn, h_adapt, h_tend⟩ :=
    adaptedSimple_dense_L2_brownian ℱ hT H h_meas h_progMeas h_sq_int
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε :=
    h_tend (Iio_mem_nhds hε)
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨Hn m, h_adapt m, hm⟩

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {μ : MeasureTheory.Measure Ω} (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num) hg
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`, over an arbitrary base type. -/
lemma eLpNorm_sq_eq_lintegral_nnnorm_sq {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} (g : β → ℝ) (hg : AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num) hg
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl

/-- `eval` is bounded by the sum of the coefficient bounds. -/
lemma eval_abs_le_sum_bounds {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    |H.eval s ω| ≤ ∑ i : Fin H.N, (H.ξ_bounded i).choose := by
  unfold SimplePredictable.eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hM : ∀ ω, |H.ξ i ω| ≤ (H.ξ_bounded i).choose := (H.ξ_bounded i).choose_spec
  have hM0 : 0 ≤ (H.ξ_bounded i).choose := le_trans (abs_nonneg _) (hM ω)
  split_ifs with h
  · exact hM ω
  · simpa using hM0

/-- For any `SimplePredictable` and any horizon `T`, the squared `L²(λ⊗P)` mass of
`eval` over `[0, T]` is finite (`eval` is uniformly bounded). -/
lemma eval_lintegral_sq_finite
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T' : ℝ} (H : SimplePredictable Ω T') (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set C : ℝ := ∑ i : Fin H.N, (H.ξ_bounded i).choose with hC
  have hbound : ∀ ω s, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
    intro ω s
    rw [show (‖H.eval s ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.eval s ω‖
          from (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖H.eval s ω‖ ≤ C := by
      rw [Real.norm_eq_abs]; exact eval_abs_le_sum_bounds H s ω
    nlinarith [h1, norm_nonneg (H.eval s ω)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω =>
    le_trans (MeasureTheory.lintegral_mono (fun s => hbound ω s))
      (le_of_eq (MeasureTheory.setLIntegral_const _ _)))) ?_
  rw [MeasureTheory.lintegral_const]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)

/-- `simpleIntegral W H t = 0` for `t ≤ 0` (all increments `W_t − W_t` vanish). -/
lemma simpleIntegral_eq_zero_of_nonpos
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    simpleIntegral W H t ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hp1 : 0 ≤ H.partition i.succ := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.succ)
    rwa [H.partition_zero] at this
  have hp2 : 0 ≤ H.partition i.castSucc := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [H.partition_zero] at this
  rw [min_eq_right (ht.trans hp1), min_eq_right (ht.trans hp2), sub_self, mul_zero]

/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²`. -/
lemma lintegral_nnnorm_sq_eq_ofReal_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- `∫ (W_b − W_a)² = b − a` for `0 ≤ a < b`. -/
lemma brownian_incr_sq_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P)
        = ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)).symm,
    W.increment_gaussian ha hab]
  exact LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩

/-- **Conditional diagonal.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a)² = (∫ g) · (b − a)` — the increment square is independent of the
`ℱ_a`-measurable `g`, with second moment `b − a`. -/
lemma integral_factor_increment_sq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono (ℱ.le a)).measurable
  -- IndepFun g ΔW
  have h_indep_F := hℱ.indep ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤ ℱ a :=
    hg_meas.measurable.comap_le
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  have h_indep_g_ΔWsq : ProbabilityTheory.IndepFun g (fun ω => (ΔW ω) ^ 2) P := by
    have := h_indep_g_ΔW.comp measurable_id (measurable_id.pow_const 2)
    simpa [Function.comp_def] using this
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω) ^ 2) = g * (fun ω => (ΔW ω) ^ 2) from rfl,
    h_indep_g_ΔWsq.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
    ((hΔW_meas.pow_const 2).aestronglyMeasurable), brownian_incr_sq_integral W ha hab]

end LevyStochCalc.Brownian.Ito
