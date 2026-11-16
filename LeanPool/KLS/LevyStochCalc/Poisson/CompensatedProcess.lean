/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use the v4.35.0
-- `eLpNorm`/`MemLp` API.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_sq_eq_lintegral_nnnorm_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedApprox

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

/-- The stage-`n` integral at time `t`, as an element of `L²(P)`. -/
noncomputable def stageLp (t : ℝ) (n : ℕ) : Lp ℝ 2 P :=
  (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t).toLp _

lemma stageLp_coeFn (t : ℝ) (n : ℕ) :
    (stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n : Ω → ℝ)
      =ᵐ[P] fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω :=
  MemLp.coeFn_toLp _

include hℱ in
/-- The stage integrals at a fixed time form a Cauchy sequence in `L²(P)`. -/
lemma stageLp_cauchySeq (t : ℝ) :
    CauchySeq (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · exact ⟨0, fun m _ n _ => by rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)⟩
  have hε2 : ε ^ (2 : ℝ) / 4 ≠ 0 :=
    (ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)).ne'
  obtain ⟨N₁, hN₁⟩ := ENNReal.exists_inv_nat_lt hε2
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ stageHorizon N₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  refine ⟨max N₀ N₁, fun m hm n hn => ?_⟩
  rw [stageLp, stageLp, Lp.edist_toLp_toLp]
  have hbound : ∀ {a b : ℕ}, a ≤ b → max N₀ N₁ ≤ a →
      ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global a t ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        < ε ^ (2 : ℝ) := by
    intro a b hab ha
    have hta : t ≤ stageHorizon a := hN₀.trans (stageHorizon_mono ((le_max_left _ _).trans ha))
    refine lt_of_le_of_lt (stageIntegral_sub_sq_le N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hab
      hta)
      ?_
    have hinv : ∀ {c : ℕ}, N₁ ≤ c → ((c : ℝ≥0∞) + 1)⁻¹ < ε ^ (2 : ℝ) / 4 := fun {c} hc =>
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 (le_trans (by exact_mod_cast hc) le_self_add)) hN₁
    have h1 := hinv ((le_max_right N₀ N₁).trans ha)
    have h2 := hinv ((le_max_right N₀ N₁).trans (ha.trans hab))
    calc 2 * ((a : ℝ≥0∞) + 1)⁻¹ + 2 * ((b : ℝ≥0∞) + 1)⁻¹
        = ((a : ℝ≥0∞) + 1)⁻¹ * 2 + ((b : ℝ≥0∞) + 1)⁻¹ * 2 := by ring
      _ < ε ^ (2 : ℝ) / 4 * 2 + ε ^ (2 : ℝ) / 4 * 2 :=
          ENNReal.add_lt_add (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) h1)
            (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) h2)
      _ = ε ^ (2 : ℝ) := by
          rw [show ε ^ (2 : ℝ) / 4 * 2 + ε ^ (2 : ℝ) / 4 * 2 = 4 * (ε ^ (2 : ℝ) / 4) by ring,
            ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have hsq : eLpNorm (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global m t ω
      - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) 2 P ^ (2 : ℝ)
      < ε ^ (2 : ℝ) := by
    have hmeas : AEStronglyMeasurable
        (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global m t ω
          - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) P :=
      (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global m t).aestronglyMeasurable.sub
        (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t).aestronglyMeasurable
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _ hmeas]
    rcases le_total m n with hmn | hnm
    · exact hbound hmn hm
    · have := hbound hnm hn
      refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) this
      rw [← nnnorm_neg, neg_sub]
  have h := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hsq
  refine lt_of_eq_of_lt ?_ h
  rfl

/-- The `L²` integral process at time `t`, as an element of `L²(P)`: the limit of the stage
integrals. -/
noncomputable def processLp (t : ℝ) : Lp ℝ 2 P :=
  limUnder atTop (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n)

include hℱ in
lemma stageLp_tendsto (t : ℝ) :
    Tendsto (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n) atTop
      (𝓝 (processLp N ℱ φ h_meas h_progMeas h_sq_int_global t)) :=
  (stageLp_cauchySeq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).tendsto_limUnder

include hℱ in
lemma stageLp_mem_lpMeas (t : ℝ) (n : ℕ) :
    stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n
      ∈ lpMeas ℝ ℝ (ℱ t) 2 P := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  refine (((martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).stronglyAdapted
    t).aestronglyMeasurable).congr ?_
  exact (MemLp.coeFn_toLp _).symm

include hℱ in
lemma processLp_mem_lpMeas (t : ℝ) :
    processLp N ℱ φ h_meas h_progMeas h_sq_int_global t
      ∈ lpMeas ℝ ℝ (ℱ t) 2 P := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hclosed : IsClosed {f : Lp ℝ 2 P |
      AEStronglyMeasurable[ℱ t] (↑↑f : Ω → ℝ) P} :=
    isClosed_aestronglyMeasurable (ℱ.le t)
  exact hclosed.mem_of_tendsto (stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
    (Eventually.of_forall fun n => mem_lpMeas_iff_aestronglyMeasurable.mp
      (stageLp_mem_lpMeas N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t n))

include hℱ in
lemma process_aesm (t : ℝ) :
    AEStronglyMeasurable[ℱ t]
      (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) P :=
  mem_lpMeas_iff_aestronglyMeasurable.mp
    (processLp_mem_lpMeas N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)

/-- The compensated-Poisson `L²` integral process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`, taken as
the `ℱ_t`-measurable representative of the `L²`-limit of the stage integrals. -/
noncomputable def process (t : ℝ) : Ω → ℝ :=
  (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).mk
    (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t))

include hℱ in
lemma process_ae_eq (t : ℝ) :
    process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) :=
  (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).ae_eq_mk.symm

include hℱ in
lemma process_stronglyAdapted :
    StronglyAdapted ℱ (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) :=
  fun t => (process_aesm N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).stronglyMeasurable_mk

include hℱ in
lemma process_memLp (t : ℝ) : MemLp (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) 2 P :=
  MemLp.ae_eq (process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).symm (Lp.memLp _)

include hℱ in
/-- The stage integrals converge to the process in `L²` at every time. -/
lemma stageIntegral_tendsto_process (t : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
      t ω
      - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) 2 P) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h1 := stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
  have hmem : MemLp (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) 2 P :=
    Lp.memLp _
  rw [← Lp.toLp_coeFn (processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) hmem] at h1
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n)
    (↑↑(processLp N ℱ φ h_meas h_progMeas h_sq_int_global t)) hmem).mp h1
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [stageLp_coeFn N ℱ φ h_meas h_progMeas h_sq_int_global t n,
    process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t] with ω hω hF
  simp only [Pi.sub_apply]
  rw [hω, hF]

include hℱ in
/-- At nonpositive times the process vanishes. -/
lemma process_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  have hst : ∀ n, stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n = 0 := by
    intro n
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine (stageLp_coeFn N ℱ φ h_meas h_progMeas h_sq_int_global t n).trans
      (Eventually.of_forall fun ω => ?_)
    exact stageIntegral_eq_zero_of_nonpos N ℱ φ h_meas h_progMeas h_sq_int_global n ht ω
  have hlim : processLp N ℱ φ h_meas h_progMeas h_sq_int_global t = 0 := by
    have h := stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
    simp only [hst] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  refine (process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).trans ?_
  rw [hlim]
  exact Lp.coeFn_zero ℝ 2 P

include hℱ in
/-- The process is a martingale on the natural filtration. -/
lemma martingale_process :
    Martingale (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) ℱ P := by
  refine LevyStochCalc.Brownian.Ito.martingale_of_tendsto_eLpNorm_one
    (M := fun n t => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t)
    (fun n => martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n)
    (fun n t => (martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).integrable
      t)
    (process_stronglyAdapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).integrable (by norm_num))
    (fun t => ?_)
  refine LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_of_eLpNorm_two (fun n => ?_)
    (stageIntegral_tendsto_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  exact ((memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t).sub
    (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)).aestronglyMeasurable

end Process

section Isometry

/-- The mark integral `∫⁻_E ‖φ(ω, u, e)‖² ν(de)`. -/
noncomputable def markSq (ω : Ω) (u : ℝ) : ℝ≥0∞ := ∫⁻ e, (‖φ ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν

omit [IsProbabilityMeasure P] in
include h_meas in
lemma measurable_markSq : Measurable (Function.uncurry (markSq (ν := ν) φ)) := by
  have h : Measurable (fun r : (Ω × ℝ) × E => (‖φ r.1.1 r.1.2 r.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.comp (by fun_prop :
      Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E))).nnnorm).pow_const 2
  exact h.lintegral_prod_right'

/-- The horizon integral `∫⁻_Ω ∫⁻_{[0,t]} ∫⁻_E ‖φ‖²`. -/
noncomputable def horizonInt (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, markSq (ν := ν) φ ω s ∂volume ∂P

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
lemma horizonInt_eq (t : ℝ) :
    horizonInt (P := P) (ν := ν) φ t = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := rfl

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
lemma horizonInt_mono {s r : ℝ} (h : s ≤ r) :
    horizonInt (P := P) (ν := ν) φ s ≤ horizonInt (P := P) (ν := ν) φ r :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc_right h)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include h_sq_int_global in
lemma horizonInt_lt_top (t : ℝ) : horizonInt (P := P) (ν := ν) φ t < ⊤ :=
  (horizonInt_mono φ (le_trans (le_max_left t 0) (le_add_of_nonneg_right zero_le_one))).trans_lt
    (h_sq_int_global (max t 0 + 1) (by positivity))

omit [IsProbabilityMeasure P] in
include h_meas in
lemma horizonInt_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    horizonInt (P := P) (ν := ν) φ r
      = horizonInt (P := P) (ν := ν) φ s
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, markSq (ν := ν) φ ω u ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, markSq (ν := ν) φ ω u ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, markSq (ν := ν) φ ω u ∂volume
        + ∫⁻ u in Set.Ioc s r, markSq (ν := ν) φ ω u ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr, lintegral_union measurableSet_Ioc
      (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [horizonInt, horizonInt, lintegral_congr hinner]
  exact lintegral_add_left' ((measurable_markSq φ h_meas).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) s))).aemeasurable _

include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral. -/
lemma horizonInt_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (horizonInt (P := P) (ν := ν) φ) (𝓝[>] s) (𝓝 (horizonInt (P := P) (ν := ν) φ s)) := by
  have hz := LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero (P := P)
    (markSq (ν := ν) φ) (measurable_markSq φ h_meas) hs (lt_add_one s)
    (horizonInt_lt_top φ h_sq_int_global (s + 1)).ne
  have ht := (tendsto_const_nhds (x := horizonInt (P := P) (ν := ν) φ s)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizonInt_add φ h_meas hs hr.le).symm

omit [IsProbabilityMeasure P] in
/-- The nested triple integral over `Ω × E × [0, t]` as an integral for the product measure. -/
lemma triple_eq_lintegral_prod {t : ℝ} (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) :
    ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s e ∂volume ∂ν ∂P
      = ∫⁻ q : Ω × E × ℝ, f q.1 q.2.2 q.2.1
          ∂(P.prod (ν.prod (volume.restrict (Set.Icc (0 : ℝ) t)))) := by
  have hm : Measurable (fun q : Ω × E × ℝ => f q.1 q.2.2 q.2.1) :=
    hf.comp (by fun_prop : Measurable fun q : Ω × E × ℝ => ((q.1, q.2.2, q.2.1) : Ω × ℝ × E))
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_prod (fun y : E × ℝ => f (ω, y).1 (ω, y).2.2 (ω, y).2.1)
    (hm.comp (measurable_prodMk_left (x := ω))).aemeasurable]

include hℱ in
/-- The Itô–Lévy isometry of the process at every time `t ≥ 0`. -/
theorem process_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = horizonInt (P := P) (ν := ν) φ t := by
  set μt := P.prod (ν.prod (volume.restrict (Set.Icc (0 : ℝ) t))) with hμt
  set g : Ω × E × ℝ → ℝ := fun q => φ q.1 q.2.2 q.2.1 with hg
  set gₙ : ℕ → Ω × E × ℝ → ℝ := fun n q =>
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval q.2.2 q.2.1 q.1 with hgₙ
  have hswap : Measurable fun q : Ω × E × ℝ => ((q.1, q.2.2, q.2.1) : Ω × ℝ × E) := by fun_prop
  have hgm : Measurable g := h_meas.comp hswap
  have hgₙm : ∀ n, Measurable (gₙ n) := fun n =>
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable.comp hswap
  have hφsq : Measurable (fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2
  -- the triple integrals as integrals for `μt`
  have hlift : ∀ (f : Ω → ℝ → E → ℝ≥0∞), Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) →
      ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s e ∂volume ∂ν ∂P
        = ∫⁻ q, f q.1 q.2.2 q.2.1 ∂μt := fun f hf => triple_eq_lintegral_prod f hf
  -- 1. the stage integrals
  have h1 : ∀ n, ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω‖₊
      : ℝ≥0∞) ^ 2 ∂P = ∫⁻ q, (‖gₙ n q‖₊ : ℝ≥0∞) ^ 2 ∂μt := by
    intro n
    simp only [stageIntegral]
    rw [(master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.lintegral_integral_sq_at N hℱ
      (master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n) ht]
    exact hlift (fun ω s e =>
      (‖(master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2)
      ((ENNReal.continuous_coe.measurable.comp
        (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable.nnnorm).pow_const 2)
  -- 2. `gₙ → g` in `L²(μt)`
  have h2 : Tendsto (fun n => eLpNorm (gₙ n - g) 2 μt) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => eLpNorm (gₙ n - g) 2 μt ^ (2 : ℝ)) atTop (𝓝 0) := by
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ stageHorizon N₀ := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
        exact ⟨k, hk.le⟩
      have hbound : ∀ n, N₀ ≤ n → eLpNorm (gₙ n - g) 2 μt ^ (2 : ℝ)
          ≤ stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 := by
        intro n hn
        set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
        have hdm : Measurable (fun p : Ω × ℝ × E =>
            (‖G.eval p.2.1 p.2.2 p.1 - φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
          (ENNReal.continuous_coe.measurable.comp
            (G.eval_measurable.sub h_meas).nnnorm).pow_const 2
        rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
            ((hgₙm n).sub hgm).aestronglyMeasurable,
          show (fun q => (‖(gₙ n - g) q‖₊ : ℝ≥0∞) ^ 2)
            = fun q : Ω × E × ℝ => (‖G.eval q.2.2 q.2.1 q.1 - φ q.1 q.2.2 q.2.1‖₊ : ℝ≥0∞) ^ 2
            from rfl,
          ← hlift (fun ω s e => (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2) hdm]
        calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
            = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
              refine lintegral_congr fun ω => ?_
              rw [lintegral_swap_es (fun ω s e => (‖G.eval s e ω - φ ω s e‖₊ : ℝ≥0∞) ^ 2) hdm ω]
              refine lintegral_congr fun s => lintegral_congr fun e => ?_
              rw [← nnnorm_neg, neg_sub]
          _ ≤ stageErr φ P n G := lintegral_mono fun ω =>
              lintegral_mono_set (Set.Icc_subset_Icc_right (hN₀.trans (stageHorizon_mono hn)))
      have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp [Function.comp]
      have herr : Tendsto (fun n => stageErr φ P n
          (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => bot_le)
          (fun n => (master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
        (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, hbound⟩)
    have h := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    refine h.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  -- 3. `∫⁻ ‖g‖² ∂μt` is finite (the horizon integral)
  have hgint : ∫⁻ q, (‖g q‖₊ : ℝ≥0∞) ^ 2 ∂μt = horizonInt (P := P) (ν := ν) φ t := by
    rw [← hlift (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) hφsq, horizonInt]
    exact lintegral_congr fun ω =>
      lintegral_swap_es (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) hφsq ω
  have hgfin : eLpNorm g 2 μt ≠ ⊤ := by
    refine ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_).ne
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _ hgm.aestronglyMeasurable,
      hgint]
    exact horizonInt_lt_top φ h_sq_int_global t
  have h3 := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (fun n => (hgₙm n).aestronglyMeasurable) hgm.aestronglyMeasurable hgfin h2
  -- 4. the stage integrals converge to the process
  have h4 := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (fun n => (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
      t).aestronglyMeasurable)
    (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).aestronglyMeasurable
    (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).eLpNorm_ne_top
    (stageIntegral_tendsto_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  simp_rw [h1] at h4
  rw [tendsto_nhds_unique h4 h3, hgint]

include hℱ in
/-- The Itô–Lévy isometry of the process at every time `t ≥ 0`, in the form of the nested
integral over `Ω`, time and marks. -/
theorem process_lintegral_sq' {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  process_lintegral_sq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht

include hℱ in
/-- Right-`L²`-continuity of the process. -/
theorem process_eLpNorm_two_right_tendsto (s : ℝ) :
    Tendsto (fun r => eLpNorm (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r
      - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s) 2 P) (𝓝[>] s) (𝓝 0) := by
  suffices hsq : Tendsto (fun r => ∫⁻ ω,
      (‖(process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r
        - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (𝓝[>] s) (𝓝 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
        ((process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r).sub
          (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)).aestronglyMeasurable,
      ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rcases le_or_gt 0 s with hs | hs
  · have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (horizonInt (P := P) (ν := ν) φ t).toReal := by
      intro t ht
      have hb := lintegral_sq_eq_ofReal_integral
        (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
      rw [process_lintegral_sq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg _)]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω
          - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal ((horizonInt (P := P) (ν := ν) φ r).toReal
            - (horizonInt (P := P) (ν := ν) φ s).toReal) := by
      intro r hsr
      rw [lintegral_sq_eq_ofReal_integral
        (g := fun ω => process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω
          - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
        ((process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r).sub
          (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [LevyStochCalc.Brownian.Ito.integral_sq_increment_eq_of_martingale
        (martingale_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
        (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
        (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (hs.trans hsr), hFsq hs]
    have hcont : Tendsto (fun r => (horizonInt (P := P) (ν := ν) φ r).toReal
        - (horizonInt (P := P) (ν := ν) φ s).toReal) (𝓝[>] s) (𝓝 0) := by
      have h0 := (ENNReal.tendsto_toReal (horizonInt_lt_top φ h_sq_int_global s).ne).comp
        (horizonInt_right_tendsto φ h_meas h_sq_int_global hs)
      have h1 := h0.sub_const (horizonInt (P := P) (ν := ν) φ s).toReal
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hr.2.le,
      process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hs.le] with ω hr0 hs0
    simp [hr0, hs0]

include hℱ in
/-- The process is a martingale on the right-continuous natural filtration. -/
theorem martingale_rightCont_process :
    Martingale (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) fun s => ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (process_eLpNorm_two_right_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
    (Eventually.of_forall fun r => bot_le)
    (Eventually.of_forall fun r => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

end Isometry

end LevyStochCalc.Poisson.Compensated
