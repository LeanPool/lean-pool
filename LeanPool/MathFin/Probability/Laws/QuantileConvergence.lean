/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Quantile
public import Mathlib.Probability.StrongLaw

/-!
# Convergence of quantiles and of empirical distribution functions

Two limit theorems for the quantile layer of `Probability/Laws/Quantile.lean`.

* **Quantiles are continuous along almost-sure convergence.** If `X n → Y` almost surely and the
  `α`-quantile `q` of `Y` is *strict*, meaning `α < P(Y ≤ x)` for every `x > q`, then the
  `α`-quantiles of the `X n` converge to `q` (`tendsto_quantile_of_tendsto_ae`). The half below `q`
  needs nothing: there `P(Y ≤ x) < α` by the Galois connection, and continuity of `P` along the
  decreasing events `⋃_{n ≥ N} {X n ≤ x}` pushes the strict inequality onto the `X n`. The half
  above `q` runs the same argument with the increasing events `⋂_{n ≥ N} {X n ≤ x}`, and it is
  where strictness enters: across a flat stretch of the limit CDF at level `α` the quantiles of the
  `X n` are free to oscillate.
* **The strong law for the empirical CDF.** For pairwise independent, identically distributed
  `εᵢ` whose law has a continuous CDF `G`, almost surely the empirical CDF
  `x ↦ (1/m) #{i < m | εᵢ ≤ x}` converges to `G` at every point at once
  (`tendsto_empiricalCDF_ae`). Etemadi's strong law (`ProbabilityTheory.strong_law_ae`) gives the
  convergence at each rational `x`; the empirical CDF is monotone in `x` and `G` is continuous, so
  every real point is squeezed between rational ones. Because the almost-sure event does not
  depend on `x`, the empirical CDF may be evaluated at a *random* point. This is the conditional
  law of large numbers behind the large-portfolio limit of `Risk/Credit/VasicekIRB.lean`.

## Main definitions

* `empiricalCDF`: the empirical CDF `x ↦ (1/m) #{i < m | ε i ω ≤ x}` of the first `m`
  observations.

## Main results

* `cdf_map_eq_measureReal`: the CDF of a pushforward law.
* `tendsto_quantile_of_tendsto_ae`: quantiles converge along almost-sure convergence to a limit
  with a strict quantile.
* `empiricalCDF_mono`: the empirical distribution function is monotone.
* `tendsto_empiricalCDF_ae`: for pairwise independent observations with a common law whose CDF `G`
  is continuous, almost surely the empirical CDF converges to `G` at every `x`.

## References

* [van der Vaart (1998)][VanDerVaart1998], Lemma 21.2

## Tags

convergence of quantiles, empirical distribution function, Glivenko–Cantelli,
strong law of large numbers, large portfolio limit, empirical CDF, MSC 60F15, MSC 62G30
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The CDF of the law of `X` at `x` is the probability of `{X ≤ x}`. -/
lemma cdf_map_eq_measureReal [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P)
    (x : ℝ) : cdf (P.map X) x = P.real (X ⁻¹' Iic x) := by
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hX measurableSet_Iic]

/-! ### Quantiles along almost-sure convergence -/

/-- **Quantiles converge along almost-sure convergence.** If `X n → Y` almost surely and the
`α`-quantile of `Y` is strict (`α < P(Y ≤ x)` for every `x` above it), then the `α`-quantiles of the
laws of the `X n` converge to the `α`-quantile of the law of `Y`. -/
theorem tendsto_quantile_of_tendsto_ae [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω))) {α : ℝ} (hα : α ∈ Ioo 0 1)
    (hstrict : ∀ x, quantile (P.map Y) α < x → α < cdf (P.map Y) x) :
    Tendsto (fun n ↦ quantile (P.map (X n)) α) atTop (𝓝 (quantile (P.map Y) α)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- below the quantile: `P(Y ≤ a) < α`, and the events `⋃_{n ≥ N} {X n ≤ a}` decrease into
    -- `{Y ≤ a}` up to a null set
    rw [lt_quantile_iff hα, cdf_map_eq_measureReal hY, measureReal_def] at ha
    have hYa := (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 ha
    let B : ℕ → Set Ω := fun N ↦ ⋃ n ≥ N, X n ⁻¹' Iic a
    have hB : Antitone B := fun N M hNM ω hω ↦ by
      obtain ⟨n, hn, h⟩ := mem_iUnion₂.1 hω
      exact mem_iUnion₂.2 ⟨n, hNM.trans hn, h⟩
    have hBlim := tendsto_measure_iInter_atTop (fun N ↦ .iUnion fun n ↦ .iUnion fun _ ↦
      (hX n).nullMeasurableSet_preimage measurableSet_Iic) hB ⟨0, measure_ne_top _ _⟩
    have hinter : P (⋂ N, B N) ≤ P (Y ⁻¹' Iic a) := by
      refine measure_mono_ae <| hlim.mono fun ω hω hmem ↦ ?_
      change Y ω ≤ a
      by_contra! h
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hω.eventually (lt_mem_nhds h))
      obtain ⟨n, hn, hle⟩ := mem_iUnion₂.1 (mem_iInter.1 hmem N)
      exact (hN n hn).not_ge hle
    obtain ⟨N, hN⟩ := (hBlim.eventually (gt_mem_nhds (hinter.trans_lt hYa))).exists
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [lt_quantile_iff hα, cdf_map_eq_measureReal (hX n), measureReal_def,
      ← ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)]
    exact (measure_mono fun ω h ↦ mem_iUnion₂.2 ⟨n, hn, h⟩).trans_lt hN
  · -- above the quantile: take `q < c < b' < b`; strictness gives `α < P(Y ≤ c)`, and the events
    -- `⋂_{n ≥ N} {X n ≤ b'}` increase to a set containing `{Y ≤ c}` up to a null set
    obtain ⟨b', hqb', hb'b⟩ := exists_between hb
    obtain ⟨c, hqc, hcb'⟩ := exists_between hqb'
    have hYc := hstrict c hqc
    rw [cdf_map_eq_measureReal hY, measureReal_def] at hYc
    have hYc' := (ENNReal.ofReal_lt_iff_lt_toReal hα.1.le (measure_ne_top _ _)).2 hYc
    let A : ℕ → Set Ω := fun N ↦ ⋂ n ≥ N, X n ⁻¹' Iic b'
    have hA : Monotone A := fun N M hNM ω hω ↦
      mem_iInter₂.2 fun n hn ↦ mem_iInter₂.1 hω n (hNM.trans hn)
    have hunion : P (Y ⁻¹' Iic c) ≤ P (⋃ N, A N) := by
      refine measure_mono_ae <| hlim.mono fun ω hω (hYω : Y ω ≤ c) ↦ ?_
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hω.eventually (gt_mem_nhds (hYω.trans_lt hcb')))
      exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn ↦ (hN n hn).le⟩
    obtain ⟨N, hN⟩ :=
      ((tendsto_measure_iUnion_atTop hA).eventually (lt_mem_nhds (hYc'.trans_le hunion))).exists
    filter_upwards [eventually_ge_atTop N] with n hn
    refine lt_of_le_of_lt ((quantile_le_iff hα).2 ?_) hb'b
    rw [cdf_map_eq_measureReal (hX n), measureReal_def]
    exact ((ENNReal.ofReal_lt_iff_lt_toReal hα.1.le (measure_ne_top _ _)).1
      (hN.trans_le (measure_mono fun ω hω ↦ mem_iInter₂.1 hω n hn))).le

/-! ### The strong law for the empirical CDF -/

/-- The **empirical CDF** of the first `m` observations `ε 0 ω, …, ε (m - 1) ω`, at `x`: the
fraction of them that are at most `x`. -/
noncomputable def empiricalCDF (ε : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i ∈ Finset.range m, (Iic x).indicator 1 (ε i ω)

/-- The empirical CDF is monotone in the evaluation point. -/
lemma empiricalCDF_mono (ε : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : Monotone (empiricalCDF ε m ω) :=
  fun _ _ hxy ↦ mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ ↦
    indicator_le_indicator_of_subset (Iic_subset_Iic.2 hxy) (fun _ ↦ zero_le_one) _)
    (inv_nonneg.2 m.cast_nonneg)

/-- **The strong law for the empirical CDF.** If the `ε i` are pairwise independent with a common
law `μ` whose CDF is continuous, then almost surely the empirical CDF converges to `cdf μ` at every
point simultaneously. -/
theorem tendsto_empiricalCDF_ae [IsProbabilityMeasure P] {ε : ℕ → Ω → ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hε : ∀ i, HasLaw (ε i) μ P)
    (hind : Pairwise fun i j ↦ ε i ⟂ᵢ[P] ε j) (hG : Continuous (cdf μ)) :
    ∀ᵐ ω ∂P, ∀ x, Tendsto (fun m ↦ empiricalCDF ε m ω x) atTop (𝓝 (cdf μ x)) := by
  -- Etemadi's strong law at each rational threshold
  have hrat : ∀ᵐ ω ∂P, ∀ t : ℚ,
      Tendsto (fun m ↦ empiricalCDF ε m ω t) atTop (𝓝 (cdf μ t)) := by
    refine ae_all_iff.2 fun t ↦ ?_
    have hf : Measurable ((Iic (t : ℝ)).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Iic
    have hbound (y : ℝ) : ‖(Iic (t : ℝ)).indicator (1 : ℝ → ℝ) y‖ ≤ 1 := by
      by_cases hy : y ∈ Iic (t : ℝ) <;> simp [hy]
    have hslln := strong_law_ae (fun i ω ↦ (Iic (t : ℝ)).indicator 1 (ε i ω))
      (.of_bound (hf.comp_aemeasurable (hε 0).aemeasurable).aestronglyMeasurable 1
        (ae_of_all _ fun ω ↦ hbound (ε 0 ω)))
      (fun i j hij ↦ (hind hij).comp hf hf)
      (fun i ↦ (IdentDistrib.mk (hε i).aemeasurable (hε 0).aemeasurable
        ((hε i).map_eq.trans (hε 0).map_eq.symm)).comp hf)
    have hmean : P[fun ω ↦ (Iic (t : ℝ)).indicator 1 (ε 0 ω)] = cdf μ t := by
      rw [← Function.comp_def, (hε 0).integral_comp hf.aestronglyMeasurable,
        integral_indicator_one measurableSet_Iic, cdf_eq_real]
    filter_upwards [hslln] with ω hω
    simpa only [empiricalCDF, hmean, smul_eq_mul] using hω
  filter_upwards [hrat] with ω hω x
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- a rational `t < x` with `a < G t`, by continuity of `G` at `x`
    obtain ⟨l, u, ⟨hlx, hxu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      ((isOpen_lt continuous_const hG).mem_nhds ha)
    obtain ⟨t, hlt, htx⟩ := exists_rat_btwn hlx
    filter_upwards [(hω t).eventually (lt_mem_nhds (hsub ⟨hlt, htx.trans hxu⟩))] with m hm
    exact hm.trans_le (empiricalCDF_mono ε m ω htx.le)
  · -- a rational `t > x` with `G t < b`, by continuity of `G` at `x`
    obtain ⟨l, u, ⟨hlx, hxu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      ((isOpen_lt hG continuous_const).mem_nhds hb)
    obtain ⟨t, hxt, htu⟩ := exists_rat_btwn hxu
    filter_upwards [(hω t).eventually (gt_mem_nhds (hsub ⟨hlx.trans hxt, htu⟩))] with m hm
    exact (empiricalCDF_mono ε m ω hxt.le).trans_lt hm

end MathFin
