/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.QuadraticVariationL2
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralL2

/-! # Weighted quadratic variation — `∑ wₜₖ(ΔBₖ)² → ∫₀ᵀ w_s ds` in `L²`

The second-order term of Itô's lemma. For a **bounded adapted weight process** `w` with
continuous paths, the `w`-weighted sum of squared Brownian increments along the uniform
partition of `[0,T]` converges in `L²(μ)` to the pathwise integral `∫₀ᵀ w_s ds`
(`tendsto_weighted_qv_process`). The classical instantiation is `w s ω = h (s, B s ω)` for
jointly continuous bounded `h` (the time-dependent Itô formula's `h = f_xx`; the
time-independent weight `g (B s ω)` is the case of `h` constant in time) — the fluctuation
engine never cared where the weight came from, only that it is adapted and bounded.

This generalizes `QuadraticVariationL2.tendsto_qv` (the `w ≡ 1` case, limit `T`). The
proof splits the difference into

* **Term I** (fluctuation) `∑ w_{tₖ}·((ΔBₖ)² − Δtₖ)`, which → 0 in `L²` by the same
  weak-Markov orthogonality + Gaussian-kurtosis engine as `tendsto_qv`, now carrying the
  `𝓕_{tₖ}`-measurable bounded weight `w_{tₖ}`; and
* **Term II** (Riemann sum of a continuous path)
  `∑ w_{tₖ}·Δtₖ − ∫₀ᵀ w_s ds → 0`, pathwise by continuity of `s ↦ w_s ω`, then in `L²`
  by dominated convergence (`|·| ≤ C·T`). Exported standalone as
  `tendsto_riemann_L2_process` — the time-dependent Itô formula also consumes it for the
  `∑ f_t·Δtₖ → ∫₀ᵀ f_t(s,B_s) ds` drift term.

## Main results

* `tendsto_riemann_continuous`: left-endpoint Riemann sums of a continuous bounded `h : ℝ≥0 → ℝ`
  along `unifPart T n` converge to its integral.
* `tendsto_riemann_L2_process`: left-endpoint Riemann sums of a bounded continuous-path process
  converge in `L²` to its pathwise integral over `(0, T]`.
* `tendsto_weighted_qv_process`: for a bounded adapted weight process `w` with continuous paths,
  `∑ₖ w_{tₖ}(ΔBₖ)²` along the uniform partition converges in `L²(μ)` to `∫₀ᵀ w_s ds`.
* `tendsto_weighted_qv_process_of_ae_continuous`: the same when the paths of `w` are continuous
  on `[0, T]` only almost surely.
* `measurable_pathIntegral`, `memLp_pathIntegral_process`: the pathwise integral of a bounded
  measurable process with continuous paths is measurable and in `L²(μ)`.
* `exists_continuous_version_of_ae_continuousOn`: a bounded measurable weight with a.s.
  continuous paths on `[0, T]` has a version continuous on every path.

## Tags

weighted quadratic variation, Itô formula, second-order term, Riemann sum convergence,
squared Brownian increments, mean-square limit, MSC 60H05, MSC 60J65
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIsometryAdapted QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsPreBrownianReal B μ)

include hB

/-- For `χ` adapted to `𝓕_{t₀}` and in `L²`, the centered squared increment integrates
against `χ` to zero: `E[χ·((ΔB)² − (t₁−t₀))] = 0`. The `χ ≡ 1` case is
`integral_increment_centered_mean`; the general adapted `L²` weight is what makes the
weighted-QV fluctuation's cross terms vanish. Immediate from the isometry kernel
`integral_adapted_mul_increment_sq` (`E[χ·(ΔB)²] = E[χ]·(t₁−t₀)`) minus `(t₁−t₀)·E[χ]`. -/
private theorem integral_adapted_mul_centered_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : Measurable[ItoIntegralL2.natFiltration hBmeas t₀] χ) :
    ∫ ω, χ ω * ((B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hχm : Measurable χ := hχ.mono ((ItoIntegralL2.natFiltration hBmeas).le t₀) le_rfl
  have hΔm : Measurable (fun ω ↦ B t₁ ω - B t₀ ω) := by fun_prop
  rw [(adapted_indepFun_increment (hB.isFilteredPreBrownian hBmeas) ht hχ).integral_mul_comp
      (g := fun x ↦ x ^ 2 - ((t₁ : ℝ) - t₀)) (by fun_prop) hχm.aestronglyMeasurable
      hΔm.aemeasurable,
    integral_increment_centered_mean hB ht, mul_zero]

/-- **Term I, per-`n` bound.** The `L²` norm² of the weighted fluctuation
`∑ₖ w_{tₖ}·((ΔBₖ)² − Δtₖ)` is at most `∑ₖ C²·2(Δtₖ)²` for any adapted weight process `w`
bounded by `C`: the cross terms vanish (`integral_adapted_mul_centered_sq`), and each
diagonal term is `≤ C²·2(Δtₖ)²` (pointwise `w² ≤ C²` plus
`integral_increment_sq_centered`). The weighted analogue of
`sum_increment_sq_sub_sq_integral`. -/
private theorem weighted_fluctuation_integral_le
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, Measurable[ItoIntegralL2.natFiltration hBmeas s] (w s))
    {C : ℝ} (hC : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n,
        w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
             - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range n,
          C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  set t : ℕ → ℝ≥0 := unifPart T n
  set Y : ℕ → Ω → ℝ := fun k ω ↦ (B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)
    with hY_def
  set a : ℕ → Ω → ℝ := fun k ω ↦ w (t k) ω * Y k ω with ha_def
  have hw_meas : ∀ s, Measurable (w s) := fun s ↦
    (hw_adapt s).mono ((ItoIntegralL2.natFiltration hBmeas).le s) le_rfl
  have hYL2 : ∀ k, MemLp (Y k) 2 μ := fun k ↦ memLp_increment_sq_centered_two hB (t k) (t (k + 1)) _
  have ha_aesm : ∀ k, AEStronglyMeasurable (a k) μ := fun k ↦
    (hw_meas (t k)).aestronglyMeasurable.mul (hYL2 k).aestronglyMeasurable
  have haL2 : ∀ k, MemLp (a k) 2 μ := fun k ↦
    MemLp.mono ((hYL2 k).const_mul C) (ha_aesm k) (ae_of_all _ fun ω ↦ by
      simp only [ha_def, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw_bdd _ _) (abs_nonneg _))
  have hint : ∀ k l, Integrable (fun ω ↦ a k ω * a l ω) μ :=
    fun k l ↦ (haL2 k).integrable_mul (haL2 l)
  set 𝓕 := ItoIntegralL2.natFiltration hBmeas
  have hY_adapt : ∀ k, Measurable[𝓕 (t (k + 1))] (Y k) := fun k ↦
    measurable_increment_sq_sub (hB.isFilteredPreBrownian hBmeas)
      (hmono (Nat.le_succ k)) le_rfl _
  have ha_adapt : ∀ k, Measurable[𝓕 (t (k + 1))] (a k) := fun k ↦
    ((hw_adapt (t k)).mono (𝓕.mono (hmono (Nat.le_succ k))) le_rfl).mul (hY_adapt k)
  have hcross : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, l ≠ k →
      ∫ ω, a k ω * a l ω ∂μ = 0 := by
    intro k _ l _ hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · have hχ : Measurable[𝓕 (t k)] (fun ω ↦ a l ω * w (t k) ω) :=
        ((ha_adapt l).mono (𝓕.mono (hmono (Nat.succ_le_of_lt hlt))) le_rfl).mul (hw_adapt (t k))
      have h := integral_adapted_mul_centered_sq hB hBmeas (hmono (Nat.le_succ k)) hχ
      rw [show (fun ω ↦ a k ω * a l ω)
            = (fun ω ↦ (a l ω * w (t k) ω)
                * ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)))
          from funext fun ω ↦ by simp only [ha_def, hY_def]; ring]
      exact h
    · have hχ : Measurable[𝓕 (t l)] (fun ω ↦ a k ω * w (t l) ω) :=
        ((ha_adapt k).mono (𝓕.mono (hmono (Nat.succ_le_of_lt hgt))) le_rfl).mul (hw_adapt (t l))
      have h := integral_adapted_mul_centered_sq hB hBmeas (hmono (Nat.le_succ l)) hχ
      rw [show (fun ω ↦ a k ω * a l ω)
            = (fun ω ↦ (a k ω * w (t l) ω)
                * ((B (t (l + 1)) ω - B (t l) ω) ^ 2 - ((t (l + 1) : ℝ) - t l)))
          from funext fun ω ↦ by simp only [ha_def, hY_def]; ring]
      exact h
  have hdiag : ∀ k ∈ Finset.range n,
      ∫ ω, a k ω * a k ω ∂μ ≤ C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
    intro k _
    have hgsq : ∀ ω, (w (t k) ω) ^ 2 ≤ C ^ 2 := fun ω ↦ by
      nlinarith [hw_bdd (t k) ω, abs_nonneg (w (t k) ω), sq_abs (w (t k) ω)]
    have hle : ∀ ω, a k ω * a k ω ≤ C ^ 2 * (Y k ω * Y k ω) := fun ω ↦ by
      simp only [ha_def]
      nlinarith [hgsq ω, mul_self_nonneg (Y k ω)]
    calc ∫ ω, a k ω * a k ω ∂μ
        ≤ ∫ ω, C ^ 2 * (Y k ω * Y k ω) ∂μ :=
          integral_mono (hint k k) (((hYL2 k).integrable_mul (hYL2 k)).const_mul _) hle
      _ = C ^ 2 * ∫ ω, Y k ω * Y k ω ∂μ := integral_const_mul _ _
      _ = C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
          rw [show (fun ω ↦ Y k ω * Y k ω)
                = (fun ω ↦ ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)) ^ 2)
              from funext fun ω ↦ by simp only [hY_def]; ring,
              integral_increment_sq_centered hB (hmono (Nat.le_succ k))]
  calc ∫ ω, (∑ k ∈ Finset.range n, a k ω) ^ 2 ∂μ
      = ∫ ω, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        change (∑ k ∈ Finset.range n, a k ω) ^ 2
          = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∫ ω, a k ω * a l ω ∂μ := by
        rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint k l]
        exact Finset.sum_congr rfl fun k _ ↦ integral_finsetSum _ fun l _ ↦ hint k l
    _ ≤ ∑ k ∈ Finset.range n, C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [Finset.sum_eq_single k (fun l hl hlk ↦ hcross k hk l hl hlk) fun h ↦ absurd hk h]
        exact hdiag k hk

/-- **Term I → 0 in `L²`.** The weighted fluctuation `∑ₖ w_{tₖ}·((ΔBₖ)² − Δtₖ)` of a
bounded adapted weight process vanishes in `L²(μ)` as the mesh shrinks, with explicit
rate `2C²T²/n`. Squeeze of the per-`n` bound `weighted_fluctuation_integral_le` (the
weighted analogue of the `tendsto_qv` rate `2T²/n`). -/
private theorem tendsto_weighted_fluctuation
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, Measurable[ItoIntegralL2.natFiltration hBmeas s] (w s))
    {C : ℝ} (hC : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
            w (unifPart T n k) ω
              * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
                 - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C ^ 2 * (T : ℝ) ^ 2 / n)
    (Eventually.of_forall fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * C ^ 2 * (T : ℝ) ^ 2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (weighted_fluctuation_integral_le hB hBmeas hw_adapt hC hw_bdd T n).trans (le_of_eq ?_)
  have hΔ : ∀ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n :=
    fun k _ ↦ unifPart_succ_sub T n k
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [show (∑ k ∈ Finset.range n, C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2))
        = ∑ _k ∈ Finset.range n, C ^ 2 * (2 * ((T : ℝ) / n) ^ 2)
      from Finset.sum_congr rfl fun k hk ↦ by rw [hΔ k hk],
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

omit hB in
/-- **Riemann sums of a continuous path, bounded on `[0,T]`, converge to its integral.** For
`h : ℝ≥0 → ℝ` continuous with `|h s| ≤ C` for `s ≤ T` (a *local* bound — only the values on
`[0,T]` matter), the left-endpoint Riemann sums along the uniform partition of `[0,T]`
converge to `∫₀ᵀ h ∂timeMeasure`. Mathlib has no Riemann-sum lemma, so this is built from
scratch: the left-endpoint step function integrates (over `timeMeasure`, via
`timeMeasure_Ioc`) to the Riemann sum, converges pointwise to `h` on `(0,T]` by continuity
(each `s` lies in a unique partition cell whose left endpoint is within `T/n`), and dominated
convergence (bound `C`, finite measure `timeMeasure (0,T]=T`) upgrades this to convergence of
the integrals. The pathwise core: consumed in-file by the `L²` wrappers
(`tendsto_riemann_L2_process`, `memLp_pathIntegral_process`) and Term II of
`tendsto_weighted_qv_process`, and — through the local bound, applied per path of a process
with no *uniform* bound — by the exponential-growth path integral
(`ItoFormulaLocalized.pathIntegral_expGrowth_memLp`). -/
theorem tendsto_riemann_continuous {h : ℝ≥0 → ℝ} (hcont : Continuous h)
    (T : ℝ≥0) {C : ℝ} (hbdd : ∀ s ≤ T, |h s| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        h (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, h s ∂ItoIntegralL2.timeMeasure)) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hbdd 0 (by positivity))
  set ν := ItoIntegralL2.timeMeasure with hν
  have hfin : IsFiniteMeasure (ν.restrict (Set.Ioc 0 T)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hν,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- partition facts
  have hmono := unifPart_mono T
  have hlast : ∀ n, 0 < n → unifPart T n n = T := fun n hn ↦ unifPart_self T hn.ne'
  have hgap : ∀ n, 0 < n → ∀ k, (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n :=
    fun n _ k ↦ unifPart_succ_sub T n k
  -- the left-endpoint step function
  set F : ℕ → ℝ≥0 → ℝ := fun n s ↦ ∑ k ∈ Finset.range n,
    (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator (fun _ ↦ h (unifPart T n k)) s
    with hF
  -- on `(0,T]`, the step function equals the unique cell's left value, within `T/n` of `s`
  have hkey : ∀ n, 0 < n → ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, ∃ k, k < n ∧
      F n s = h (unifPart T n k) ∧ |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := by
    intro n hn s hs
    have hex : ∃ k, s ≤ unifPart T n (k + 1) :=
      ⟨n - 1, by rw [Nat.sub_add_cancel hn, hlast n hn]; exact hs.2⟩
    set K := Nat.find hex
    have hKspec : s ≤ unifPart T n (K + 1) := Nat.find_spec hex
    have hKle : K ≤ n - 1 := Nat.find_le (by rw [Nat.sub_add_cancel hn, hlast n hn]; exact hs.2)
    have hKlt : K < n := lt_of_le_of_lt hKle (Nat.sub_lt hn one_pos)
    have hlow : unifPart T n K < s := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · rw [hK0, unifPart_zero]; exact hs.1
      · have hmin := Nat.find_min hex (m := K - 1) (Nat.sub_lt hKpos one_pos)
        have hK1 : K - 1 + 1 = K := by omega
        rw [hK1] at hmin
        exact not_le.mp hmin
    refine ⟨K, hKlt, ?_, ?_⟩
    · simp only [hF]
      rw [Finset.sum_eq_single K]
      · rw [Set.indicator_of_mem]; exact ⟨hlow, hKspec⟩
      · intro l _ hlK
        apply Set.indicator_of_notMem
        rintro ⟨hl1, hl2⟩
        rcases lt_or_gt_of_ne hlK with hlt | hgt
        · exact (Nat.find_min hex hlt) hl2
        · exact absurd hl1 (not_lt.mpr (le_trans hKspec (hmono n (Nat.succ_le_of_lt hgt))))
      · intro hKnot; exact absurd (Finset.mem_range.mpr hKlt) hKnot
    · rw [abs_le]
      have hcoe_low : (unifPart T n K : ℝ) < s := by exact_mod_cast hlow
      have hcoe_hi : (s : ℝ) ≤ unifPart T n (K + 1) := by exact_mod_cast hKspec
      have hg := hgap n hn K
      have hTn : (0 : ℝ) ≤ (T : ℝ) / n := div_nonneg (NNReal.coe_nonneg T) (Nat.cast_nonneg n)
      constructor
      · nlinarith [hcoe_low, hcoe_hi, hg]
      · nlinarith [hcoe_low, hTn]
  -- pointwise bound on `(0,T]`
  have hbound : ∀ n, ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, ‖F n s‖ ≤ C := by
    intro n s hs
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp only [hF, hn0, Finset.range_zero, Finset.sum_empty, norm_zero]; exact hC0
    · obtain ⟨k, hklt, hval, _⟩ := hkey n hn s hs
      rw [hval, Real.norm_eq_abs]; exact hbdd _ (unifPart_le_T hklt.le)
  -- pointwise convergence `F n s → h s` on `(0,T]`
  have hptwise : ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, Tendsto (fun n ↦ F n s) atTop (𝓝 (h s)) := by
    intro s hs
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ := hkey n hn1 s hs
    rw [hval]
    refine hδc ?_
    rw [NNReal.dist_eq]
    have hn_gt : (T : ℝ) / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    calc |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := hclose
      _ < δ := by
          rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
          exact (div_lt_iff₀ hδ).mp hn_gt
  -- the step function integrates to the Riemann sum
  have hstep_integ : ∀ n, ∫ s in Set.Ioc 0 T, F n s ∂ν
      = ∑ k ∈ Finset.range n,
          h (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    have hInt : ∀ k ∈ Finset.range n,
        Integrable ((Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ ↦ h (unifPart T n k))) (ν.restrict (Set.Ioc 0 T)) :=
      fun k _ ↦ (integrable_const _).indicator measurableSet_Ioc
    simp only [hF]
    rw [integral_finsetSum _ hInt]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
      show Set.Ioc (0 : ℝ≥0) T ∩ Set.Ioc (unifPart T n k) (unifPart T n (k + 1))
          = Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) by
        rw [Set.Ioc_inter_Ioc, max_eq_right zero_le, min_eq_right (unifPart_le_T hkn)],
      measureReal_def, hν, ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal
        (sub_nonneg.mpr (by exact_mod_cast hmono n (Nat.le_succ k)))]
    ring
  -- dominated convergence assembles the result
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (ν.restrict (Set.Ioc 0 T)) := fun n ↦ by
    simp only [hF]
    exact (Finset.measurable_sum _
      (fun k _ ↦ measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
  have hconv := tendsto_integral_of_dominated_convergence (F := F) (f := h)
    (fun _ ↦ C) hmeas (integrable_const C)
    (fun n ↦ ae_restrict_of_forall_mem measurableSet_Ioc (hbound n))
    (ae_restrict_of_forall_mem measurableSet_Ioc hptwise)
  exact (tendsto_congr hstep_integ).mp hconv

omit hB in
/-- A left-endpoint Riemann weight-sum of a bounded process is bounded by `C·T`:
`|∑_{k<n} w_{t_k}(ω)·(t_{k+1} − t_k)| ≤ C·T`. Shared left-endpoint bound for the
weighted-QV Riemann term, `memLp_pathIntegral_process`, and the time-dependent Itô
formula's drift sum. -/
lemma abs_riemann_weight_sum_le {w : ℝ≥0 → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    |∑ k ∈ Finset.range n,
        w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| ≤ C * T := by
  have hΔnn : ∀ k, (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k := fun k ↦
    sub_nonneg.mpr (by
      exact_mod_cast unifPart_mono T n (Nat.le_succ k))
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg hC0 (NNReal.coe_nonneg T)
  · calc |∑ k ∈ Finset.range n,
            w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ ∑ k ∈ Finset.range n,
            |w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, C * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
          Finset.sum_le_sum fun k _ ↦ by
            rw [abs_mul, abs_of_nonneg (hΔnn k)]
            exact mul_le_mul_of_nonneg_right (hw_bdd _ _) (hΔnn k)
      _ = C * ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
          rw [Finset.mul_sum]
      _ = C * T := by rw [unifPart_mesh_sum T hn.ne']

omit hB in
/-- **The pathwise integral `ω ↦ ∫₀ᵀ w_s(ω) ds` of a measurable process with continuous paths
is measurable.** It is the pointwise limit of the (measurable) left-endpoint Riemann sums —
each path is bounded on the compact `[0,T]` (no *uniform* bound needed), so
`tendsto_riemann_continuous` applies per path. The shared measurability core of the `L²`
Riemann lemmas and `memLp_pathIntegral_process`, exported for the exponential-growth path
integral (`ItoFormulaLocalized`), whose integrand has no uniform bound. -/
theorem measurable_pathIntegral
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω) (T : ℝ≥0) :
    Measurable fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure :=
  measurable_of_tendsto_metrizable
    (fun n ↦ Finset.measurable_sum _ fun k _ ↦ (hw_meas (unifPart T n k)).mul_const _)
    (tendsto_pi_nhds.mpr fun ω ↦ by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
        (hw_cont ω).continuousOn
      exact tendsto_riemann_continuous (h := fun s ↦ w s ω) (hw_cont ω) T
        (fun s hs ↦ by rw [← Real.norm_eq_abs]; exact hC s ⟨zero_le, hs⟩))

omit hB in
/-- The pathwise integral inherits the Riemann sums' uniform bound `C·T`
(`abs_riemann_weight_sum_le` carried to the limit). The shared bound core of the `L²`
Riemann lemmas below and of `memLp_pathIntegral_process`. -/
theorem abs_pathIntegral_le
    {w : ℝ≥0 → Ω → ℝ} (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) (ω : Ω) :
    |∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure| ≤ C * T :=
  le_of_tendsto
    (Filter.Tendsto.abs
      (tendsto_riemann_continuous (h := fun s ↦ w s ω) (hw_cont ω) T (fun s _ ↦ hw_bdd s ω)))
    (Eventually.of_forall fun n ↦ abs_riemann_weight_sum_le hC0 hw_bdd T n ω)

omit hB in
/-- **Left-endpoint Riemann sums of a bounded continuous-path process converge in `L²` to
its path integral**: `∑ₖ w_{tₖ}·Δtₖ → ∫₀ᵀ w_s ds` in `L²(μ)`. Pathwise this is
`tendsto_riemann_continuous`; dominated convergence (uniform bound `C·T` on both sides)
upgrades it to `L²`. Consumed by `tendsto_weighted_qv_process` (Term II) and by the
time-dependent Itô formula's drift term `∑ f_t(tₖ, B_{tₖ})·Δtₖ → ∫₀ᵀ f_t(s, B_s) ds`. -/
theorem tendsto_riemann_L2_process [IsFiniteMeasure μ]
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
            w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  set Rsum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hRsum
  set Ipath : Ω → ℝ := fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure with hIpath
  have hpath : ∀ ω, Tendsto (fun n ↦ Rsum n ω) atTop (𝓝 (Ipath ω)) := fun ω ↦
    tendsto_riemann_continuous (h := fun s ↦ w s ω) (hw_cont ω) T (fun s _ ↦ hw_bdd _ _)
  have hR_meas : ∀ n, Measurable (Rsum n) := fun n ↦
    Finset.measurable_sum _ (fun k _ ↦ (hw_meas _).mul_const _)
  have hI_meas : Measurable Ipath := measurable_pathIntegral hw_meas hw_cont T
  have hR_bdd : ∀ n ω, |Rsum n ω| ≤ C * T := fun n ω ↦ by
    simp only [hRsum]; exact abs_riemann_weight_sum_le hC0 hw_bdd T n ω
  have hI_bdd : ∀ ω, |Ipath ω| ≤ C * T := fun ω ↦ abs_pathIntegral_le hw_cont hC0 hw_bdd T ω
  have hRI_nbd : ∀ n, ∀ᵐ ω ∂μ, ‖(Rsum n ω - Ipath ω) ^ 2‖ ≤ (2 * C * (T : ℝ)) ^ 2 := by
    intro n
    refine Eventually.of_forall fun ω ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_le.mp (hR_bdd n ω)
    have h2 := abs_le.mp (hI_bdd ω)
    exact sq_le_sq' (by nlinarith [h1.1, h2.2]) (by nlinarith [h1.2, h2.1])
  have hRI_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ (Rsum n ω - Ipath ω) ^ 2) μ := fun n ↦
    (((hR_meas n).sub hI_meas).pow_const 2).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ (Rsum n ω - Ipath ω) ^ 2) atTop (𝓝 ((fun _ ↦ (0 : ℝ)) ω)) :=
    Eventually.of_forall fun ω ↦ by simpa using ((hpath ω).sub_const (Ipath ω)).pow 2
  simpa using tendsto_integral_of_dominated_convergence
    (fun _ ↦ (2 * C * (T : ℝ)) ^ 2) hRI_meas (integrable_const _) hRI_nbd hlim

omit hB in
/-- **Per-`n` integrability of the squared Riemann defect**: both the weight-sum and the
path integral are uniformly bounded by `C·T`, so the squared defect is dominated by
`(2CT)²`. The integrability companion of `tendsto_riemann_L2_process`, supplying the
squeeze's side condition in `tendsto_weighted_qv_process`. -/
theorem integrable_riemann_defect_sq [IsFiniteMeasure μ]
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ (∑ k ∈ Finset.range n,
        w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2) μ := by
  have hmeas : Measurable (fun ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
    - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) :=
    (Finset.measurable_sum _ fun k _ ↦ (hw_meas _).mul_const _).sub
      (measurable_pathIntegral hw_meas hw_cont T)
  refine Integrable.mono' (integrable_const ((2 * C * (T : ℝ)) ^ 2))
    (hmeas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := abs_le.mp (abs_riemann_weight_sum_le hC0 hw_bdd T n ω)
  have h2 := abs_le.mp (abs_pathIntegral_le hw_cont hC0 hw_bdd T ω)
  exact sq_le_sq' (by nlinarith [h1.1, h2.2]) (by nlinarith [h1.2, h2.1])

omit hB in
/-- **A weight whose paths are almost surely continuous on `[0, T]` has a version continuous on
every path**, agreeing with it on `[0, T]` almost surely. Stop the weight at `T`, and set it to `0`
off a measurable set of full measure on which the paths are continuous on `[0, T]`. Measurability
and the bound survive; adaptedness need not, so this serves the pathwise integral and not the
fluctuation term. -/
theorem exists_continuous_version_of_ae_continuousOn
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s)) (T : ℝ≥0)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T))
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) :
    ∃ v : ℝ≥0 → Ω → ℝ, (∀ s, Measurable (v s)) ∧ (∀ ω, Continuous fun s ↦ v s ω)
      ∧ (∀ s ω, |v s ω| ≤ C) ∧ ∀ᵐ ω ∂μ, ∀ s ≤ T, v s ω = w s ω := by
  obtain ⟨S, hS, hSc, hμS⟩ : ∃ S, MeasurableSet S
      ∧ (∀ ω ∈ S, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)) ∧ μ Sᶜ = 0 :=
    ⟨(toMeasurable μ {ω | ¬ ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)})ᶜ,
      (measurableSet_toMeasurable _ _).compl,
      fun ω hω ↦ not_not.1 fun h ↦ hω (subset_toMeasurable _ _ h),
      by rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hw_cont⟩
  refine ⟨fun s ↦ S.indicator (w (min s T)), fun s ↦ (hw_meas _).indicator hS, fun ω ↦ ?_,
    fun s ω ↦ ?_, (measure_eq_zero_iff_ae_notMem.1 hμS).mono fun ω hω s hs ↦ by
      simp only [Set.indicator_of_mem (not_not.1 hω), min_eq_left hs]⟩
  · by_cases hω : ω ∈ S
    · simpa only [Set.indicator_of_mem hω, Function.comp_def, id] using
        (hSc ω hω).comp_continuous (continuous_id.min continuous_const)
          fun s ↦ ⟨zero_le, min_le_right s T⟩
    · simpa only [Set.indicator_of_notMem hω] using continuous_const
  · by_cases hω : ω ∈ S
    · simpa only [Set.indicator_of_mem hω] using hw_bdd _ ω
    · simpa only [Set.indicator_of_notMem hω, abs_zero] using hC0

/-- **Weighted quadratic variation, process-weight form, for almost surely continuous paths.**
For a bounded adapted weight process `w` whose paths are almost surely continuous on `[0,T]`, the
`w`-weighted sum of squared increments along the uniform partition of `[0,T]` converges in `L²(μ)`
to `∫₀ᵀ w_s ds`. The fluctuation engine (Term I) needs only adaptedness and boundedness of the
weight. The Riemann term (Term II) needs only measurability, boundedness and path continuity, so
there the weight is replaced by a version continuous on every path
(`exists_continuous_version_of_ae_continuousOn`): that keeps every hypothesis of
`tendsto_riemann_L2_process` and changes nothing on `[0,T]` almost surely. Adaptedness would not
survive that replacement, which is why it is done for Term II only. -/
theorem tendsto_weighted_qv_process_of_ae_continuous
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, Measurable[ItoIntegralL2.natFiltration hBmeas s] (w s))
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
                w (unifPart T n k) ω
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
              - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hw_meas : ∀ s, Measurable (w s) := fun s ↦
    (hw_adapt s).mono ((ItoIntegralL2.natFiltration hBmeas).le s) le_rfl
  set Ssum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 with hSsum
  set Rsum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hRsum
  set Ipath : Ω → ℝ := fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure with hIpath
  change Tendsto (fun n ↦ ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0)
  -- **Term I**: the fluctuation `Ssum − Rsum → 0` in `L²` (= `tendsto_weighted_fluctuation`)
  have hTermI : Tendsto (fun n ↦ ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    refine (tendsto_congr fun n ↦ ?_).mp
      (tendsto_weighted_fluctuation hB hBmeas hw_adapt hC0 hw_bdd T)
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
    change (∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 = (Ssum n ω - Rsum n ω) ^ 2
    have hbase : (∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) = Ssum n ω - Rsum n ω := by
      simp only [hSsum, hRsum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hbase]
  -- **Term II**: the Riemann remainder `Rsum − Ipath → 0` in `L²` (the standalone lemma)
  -- for the Riemann term, pass to a version `v` of the weight that is continuous on every path
  obtain ⟨v, hv_meas, hv_cont, hv_bdd, hv⟩ :=
    exists_continuous_version_of_ae_continuousOn hw_meas T hw_cont hC0 hw_bdd
  have hvw : ∀ᵐ ω ∂μ, ∀ n, (∑ k ∈ Finset.range n,
        v (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      - ∫ s in Set.Ioc 0 T, v s ω ∂ItoIntegralL2.timeMeasure) ^ 2 = (Rsum n ω - Ipath ω) ^ 2 := by
    filter_upwards [hv] with ω hω n
    rw [Finset.sum_congr rfl fun k hk ↦ by
        rw [hω _ (unifPart_le_T (Finset.mem_range.mp hk).le)],
      setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ hω s hs.2]
  have hTermII : Tendsto (fun n ↦ ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) :=
    (tendsto_riemann_L2_process hv_meas hv_cont hC0 hv_bdd T).congr fun n ↦
      integral_congr_ae (hvw.mono fun ω h ↦ h n)
  -- integrability of the two squared pieces (upper bounds for the squeeze)
  have hInt_I : ∀ n, Integrable (fun ω ↦ (Ssum n ω - Rsum n ω) ^ 2) μ := by
    intro n
    have heq : (fun ω ↦ Ssum n ω - Rsum n ω) = fun ω ↦ ∑ k ∈ Finset.range n,
        w (unifPart T n k) ω * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
      funext ω
      rw [hSsum, hRsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hmemS : MemLp (fun ω ↦ Ssum n ω - Rsum n ω) 2 μ := by
      rw [heq]
      refine memLp_finsetSum _ fun k _ ↦ ?_
      have hZ : MemLp (fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 2 μ :=
        memLp_increment_sq_centered_two hB (unifPart T n k) (unifPart T n (k + 1)) _
      have haesm : AEStronglyMeasurable (fun ω ↦ w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) μ :=
        (hw_meas _).aestronglyMeasurable.mul hZ.aestronglyMeasurable
      refine MemLp.mono (hZ.const_mul C) haesm (Eventually.of_forall fun ω ↦ ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hw_bdd _ _) (abs_nonneg _)
    have hsq : (fun ω ↦ (Ssum n ω - Rsum n ω) ^ 2)
        = fun ω ↦ (Ssum n ω - Rsum n ω) * (Ssum n ω - Rsum n ω) := by funext ω; ring
    rw [hsq]; exact hmemS.integrable_mul hmemS
  have hInt_II : ∀ n, Integrable (fun ω ↦ (Rsum n ω - Ipath ω) ^ 2) μ := fun n ↦
    (integrable_riemann_defect_sq hv_meas hv_cont hC0 hv_bdd T n).congr (hvw.mono fun ω h ↦ h n)
  -- **Assembly**: `(Ssum−Ipath)² ≤ 2(Ssum−Rsum)² + 2(Rsum−Ipath)²`, squeeze both terms to `0`
  have hupper : Tendsto (fun n ↦ 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ
      + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa using (hTermI.const_mul 2).add (hTermII.const_mul 2)
  refine squeeze_zero (fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) (fun n ↦ ?_) hupper
  have hptwise : ∀ ω, (Ssum n ω - Ipath ω) ^ 2
      ≤ 2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2 := fun ω ↦ by
    nlinarith [sq_nonneg (Ssum n ω - 2 * Rsum n ω + Ipath ω)]
  calc ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          (((hInt_I n).const_mul 2).add ((hInt_II n).const_mul 2))
          (Eventually.of_forall hptwise)
    _ = 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ := by
        rw [integral_add ((hInt_I n).const_mul 2) ((hInt_II n).const_mul 2),
          integral_const_mul, integral_const_mul]

/-- **Weighted quadratic variation, process-weight form.** For a bounded adapted weight
process `w` with continuous paths, the `w`-weighted sum of squared increments along the
uniform partition of `[0,T]` converges in `L²(μ)` to `∫₀ᵀ w_s ds`. Both Itô-formula layers
(`g = f′′∘B` and the time-dependent `f_xx(·, B)`) are instantiations. The case of
`tendsto_weighted_qv_process_of_ae_continuous` in which every path is continuous. -/
theorem tendsto_weighted_qv_process
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, Measurable[ItoIntegralL2.natFiltration hBmeas s] (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
                w (unifPart T n k) ω
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
              - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) :=
  tendsto_weighted_qv_process_of_ae_continuous hB hBmeas hw_adapt hC0 hw_bdd T
    (Eventually.of_forall fun ω ↦ (hw_cont ω).continuousOn)

omit hB in
/-- The pathwise integral `ω ↦ ∫₀ᵀ w_s(ω) ds` of a bounded measurable process with
continuous paths lies in `L²(μ)`: it is measurable (a pointwise limit of the measurable
Riemann sums via `tendsto_riemann_continuous`) and bounded by `C·T`. Exported for the
Itô-formula assemblies, where the `ds`-terms must be `L²` functions. -/
theorem memLp_pathIntegral_process [IsFiniteMeasure μ]
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    MemLp (fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) 2 μ :=
  MemLp.of_bound (measurable_pathIntegral hw_meas hw_cont T).aestronglyMeasurable
    (C * T) (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_pathIntegral_le hw_cont hC0 hw_bdd T ω)

omit hB in
/-- `memLp_pathIntegral_process` for a weight whose paths are continuous on `[0, T]` only almost
surely: the pathwise integral agrees almost surely with that of a version continuous on every
path. -/
theorem memLp_pathIntegral_process_of_ae_continuous [IsFiniteMeasure μ]
    {w : ℝ≥0 → Ω → ℝ} (hw_meas : ∀ s, Measurable (w s))
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)) :
    MemLp (fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) 2 μ := by
  obtain ⟨v, hv_meas, hv_cont, hv_bdd, hv⟩ :=
    exists_continuous_version_of_ae_continuousOn hw_meas T hw_cont hC0 hw_bdd
  exact (memLp_pathIntegral_process hv_meas hv_cont hC0 hv_bdd T).ae_eq
    (hv.mono fun ω hω ↦ setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ hω s hs.2)

end MathFin
