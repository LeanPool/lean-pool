/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyMollifierConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth approximation in `L^{5/2} ∩ L²` with support in positive times

A space-time function in `L^{5/2} ∩ L²` vanishing at nonpositive times is the
limit, in both norms, of smooth compactly supported functions whose supports
stay in positive times: truncate to a bounded set at positive times, then
mollify at a scale below the time gap. This is the density step used to extend
the forced heat estimates of `lem:pv-stokes` to rough tensors.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The bounded positive-time truncation sets. -/
@[expose] def positiveTimeTruncation (k : ℕ) : Set (Vec3 × ℝ) :=
  {p | ‖p.1‖ < (k : ℝ) + 1 ∧ 1 / ((k : ℝ) + 1) < p.2 ∧ p.2 < (k : ℝ) + 1}

theorem positiveTimeTruncation_measurableSet (k : ℕ) :
    MeasurableSet (positiveTimeTruncation k) := by
  unfold positiveTimeTruncation
  exact ((measurableSet_lt (measurable_norm.comp measurable_fst) measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)))

/-- Truncating a function in `L^p` vanishing at nonpositive times to the bounded
positive-time sets converges in `L^p`. -/
theorem tendsto_eLpNorm_truncation {f : Vec3 × ℝ → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hptop : p ≠ ∞) (hf : MemLp f p volume) (hsupp : ∀ z, f z ≠ 0 → 0 < z.2) :
    Tendsto (fun k : ℕ => eLpNorm ((positiveTimeTruncation k).indicator f - f) p volume)
      atTop (𝓝 0) := by
  have hpt : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hmeas (k : ℕ) : AEStronglyMeasurable ((positiveTimeTruncation k).indicator f - f) volume :=
    (hf.aestronglyMeasurable.indicator (positiveTimeTruncation_measurableSet k)).sub
      hf.aestronglyMeasurable
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hmeas _)]
  have hbound := hf.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable] at hbound
  have hfin : ∫⁻ z, ‖f z‖ₑ ^ p.toReal ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by positivity)] at hbound
    exact lt_irrefl _ hbound
  have hpoint (k : ℕ) (z : Vec3 × ℝ) :
      ((positiveTimeTruncation k).indicator f - f) z = -(positiveTimeTruncation k)ᶜ.indicator f
        z := by
    by_cases hz : z ∈ positiveTimeTruncation k
    · simp [hz]
    · simp [hz]
  have hlim : Tendsto (fun k : ℕ => ∫⁻ z, ‖((positiveTimeTruncation k).indicator f - f) z‖ₑ ^
      p.toReal) atTop (𝓝 0) := by
    have hzero : (∫⁻ _z : Vec3 × ℝ, (0 : ℝ≥0∞)) = 0 := lintegral_zero
    rw [← hzero]
    refine tendsto_lintegral_of_dominated_convergence' (fun z => ‖f z‖ₑ ^ p.toReal)
      (fun k => (hmeas k).aemeasurable.enorm.pow_const p.toReal) (fun k => ?_) hfin ?_
    · refine Eventually.of_forall fun z => ?_
      dsimp only
      rw [hpoint, enorm_neg]
      apply ENNReal.rpow_le_rpow _ hpt.le
      by_cases hz : z ∈ (positiveTimeTruncation k)ᶜ
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, enorm_zero]
        exact bot_le
    · refine Eventually.of_forall fun z => ?_
      by_cases hfz : f z = 0
      · have h0 (k : ℕ) : ‖((positiveTimeTruncation k).indicator f - f) z‖ₑ ^ p.toReal = 0 := by
          rw [hpoint]
          by_cases hz : z ∈ (positiveTimeTruncation k)ᶜ
          · rw [indicator_of_mem hz, hfz, neg_zero, enorm_zero,
              ENNReal.zero_rpow_of_pos hpt]
          · rw [indicator_of_notMem hz, neg_zero, enorm_zero, ENNReal.zero_rpow_of_pos hpt]
        simp only [h0]
        exact tendsto_const_nhds
      · have hz2 : 0 < z.2 := hsupp z hfz
        have hev : ∀ᶠ k : ℕ in atTop, z ∈ positiveTimeTruncation k := by
          have h1 : ∀ᶠ k : ℕ in atTop, ‖z.1‖ < (k : ℝ) + 1 :=
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_gt_atTop _
          have h2 : ∀ᶠ k : ℕ in atTop, z.2 < (k : ℝ) + 1 :=
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_gt_atTop _
          have h3 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < z.2 :=
            (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hz2)
          filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
          exact ⟨hk1, hk3, hk2⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with k hk
        rw [hpoint, indicator_of_notMem (Set.notMem_compl_iff.mpr hk), neg_zero, enorm_zero,
          ENNReal.zero_rpow_of_pos hpt]
  have hcont := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hcont
  exact hcont.comp hlim

/-- A function in `L^{5/2} ∩ L²` vanishing at nonpositive times is a limit in both
norms of smooth compactly supported functions supported in positive times. -/
theorem exists_smooth_approx_two_norms {f : Vec3 × ℝ → ℝ}
    (h52 : MemLp f (ENNReal.ofReal (5 / 2)) volume) (h2 : MemLp f 2 volume)
    (hsupp : ∀ z, f z ≠ 0 → 0 < z.2) :
    ∃ h : ℕ → Vec3 × ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (h n)) ∧
      (∀ n, HasCompactSupport (h n)) ∧ (∀ n, tsupport (h n) ⊆ {p | 0 < p.2}) ∧
      Tendsto (fun n => eLpNorm (h n - f) (ENNReal.ofReal (5 / 2)) volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (h n - f) 2 volume) atTop (𝓝 0) := by
  have hp52 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  let S : ℕ → Set (Vec3 × ℝ) := positiveTimeTruncation
  let fk : ℕ → Vec3 × ℝ → ℝ := fun k => (S k).indicator f
  have hfk52 (k : ℕ) : MemLp (fk k) (ENNReal.ofReal (5 / 2)) volume :=
    h52.indicator (positiveTimeTruncation_measurableSet k)
  have hfk2 (k : ℕ) : MemLp (fk k) 2 volume := h2.indicator (positiveTimeTruncation_measurableSet k)
  have hfkloc (k : ℕ) : LocallyIntegrable (fk k) volume := (hfk2 k).locallyIntegrable hp2
  have hSball (k : ℕ) : S k ⊆ Metric.closedBall (0 : Vec3 × ℝ) ((k : ℝ) + 1) := by
    intro z hz
    obtain ⟨h1, h3, h4⟩ := hz
    have hk1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    refine max_le h1.le ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [h3, h4, hk1]
  have hfkc (k : ℕ) : HasCompactSupport (fk k) :=
    HasCompactSupport.intro (isCompact_closedBall _ _) fun z hz =>
      indicator_of_notMem (fun h => hz (hSball k h)) f
  -- mollification scales
  let ε : ℕ → ℕ → ℝ := fun k n => 1 / (((k : ℝ) + 1) * ((n : ℝ) + 2))
  have hεpos (k n : ℕ) : 0 < ε k n := by positivity
  have hεlim (k : ℕ) : Tendsto (ε k) atTop (𝓝 0) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := (2 : ℝ)))
    have h' := (h.const_mul_atTop (by positivity : (0 : ℝ) < (k : ℝ) + 1)).inv_tendsto_atTop
    refine h'.congr fun n => ?_
    simp only [Pi.inv_apply, ε, one_div]
  have hεsmall (k n : ℕ) : ε k n ≤ 1 / (2 * ((k : ℝ) + 1)) := by
    simp only [ε]
    apply one_div_le_one_div_of_le (by positivity)
    have : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith only [this]
    nlinarith only [this, (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  have hconv (k : ℕ) : ∀ᶠ n in atTop,
      eLpNorm (fun x => spaceTimeMollify (fk k) (ε k n) (hεpos k n) x - fk k x)
          (ENNReal.ofReal (5 / 2)) volume ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
      eLpNorm (fun x => spaceTimeMollify (fk k) (ε k n) (hεpos k n) x - fk k x) 2 volume ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
      ENNReal.ofReal_pos.2 (by positivity)
    exact ((tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp hp52 ENNReal.ofReal_ne_top (hfk52 k)
      (hεlim k) (hεpos k)).eventually (ge_mem_nhds hpos)).and
      ((tendsto_eLpNorm_sub_zero_spaceTimeMollify_lp hp2 (by norm_num) (hfk2 k)
      (hεlim k) (hεpos k)).eventually (ge_mem_nhds hpos))
  choose nk hnk using fun k => (hconv k).exists
  have hkey (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hqtop : q ≠ ∞) (hfq : MemLp f q volume)
      (hbound : ∀ k, eLpNorm (fun x => spaceTimeMollify (fk k) (ε k (nk k))
        (hεpos k (nk k)) x - fk k x) q volume ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1))) :
      Tendsto (fun k => eLpNorm (spaceTimeMollify (fk k) (ε k (nk k)) (hεpos k (nk k)) - f)
        q volume) atTop (𝓝 0) := by
    have htrunc := tendsto_eLpNorm_truncation (by positivity) hqtop hfq hsupp
    have hsmall : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [ENNReal.ofReal_zero] at h
    have hupper := hsmall.add htrunc
    rw [add_zero] at hupper
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun k => bot_le) fun k => ?_
    have hsplit : spaceTimeMollify (fk k) (ε k (nk k)) (hεpos k (nk k)) - f =
        (fun x => spaceTimeMollify (fk k) (ε k (nk k)) (hεpos k (nk k)) x - fk k x) +
          ((positiveTimeTruncation k).indicator f - f) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, fk, S]
      ring
    rw [hsplit]
    exact (eLpNorm_add_le hq1).trans (add_le_add (hbound k) le_rfl)
  refine ⟨fun k => spaceTimeMollify (fk k) (ε k (nk k)) (hεpos k (nk k)), fun k =>
    spaceTimeMollify_contDiff _ (hfkloc k), fun k => spaceTimeMollify_hasCompactSupport _ (hfkc k),
    fun k => ?_, ?_, ?_⟩
  · -- the support stays in positive times
    have hsub : Function.support (spaceTimeMollify (fk k) (ε k (nk k)) (hεpos k (nk k))) ⊆
        {p : Vec3 × ℝ | 1 / (2 * ((k : ℝ) + 1)) ≤ p.2} := by
      refine (spaceTimeMollify_support_subset _).trans ?_
      rintro z ⟨b, hb, s', hs', rfl⟩
      have hs'S : s' ∈ S k := by
        by_contra hns
        exact hs' (indicator_of_notMem hns f)
      have hb2 : |b.2| < ε k (nk k) := by
        rw [Metric.mem_ball, dist_zero_right] at hb
        exact lt_of_le_of_lt (norm_snd_le b) hb
      have hs2 : 1 / ((k : ℝ) + 1) < s'.2 := hs'S.2.1
      have hsmall := hεsmall k (nk k)
      have hhalf : 1 / ((k : ℝ) + 1) = 2 * (1 / (2 * ((k : ℝ) + 1))) := by
        field_simp
      change 1 / (2 * ((k : ℝ) + 1)) ≤ b.2 + s'.2
      rw [abs_lt] at hb2
      linarith only [hb2.1, hs2, hsmall, hhalf]
    have hclosed : IsClosed {p : Vec3 × ℝ | 1 / (2 * ((k : ℝ) + 1)) ≤ p.2} :=
      isClosed_le continuous_const continuous_snd
    intro z hz
    have hz' := closure_minimal hsub hclosed hz
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1))) hz'
  · exact hkey _ hp52 ENNReal.ofReal_ne_top h52 fun k => (hnk k).1
  · exact hkey _ hp2 (by norm_num) h2 fun k => (hnk k).2

end ESS

end
