/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public import LeanPool.MultiplicativeErgodic.Birkhoff.Average

/-!
# Birkhoff's pointwise ergodic theorem

The ergodic case: the limit is a.e. the constant `∫ f`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Finset

open scoped ENNReal

open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

variable {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}
/-- `∫ Sₙf = n ∫ f`, by measure preservation. -/
theorem integral_birkhoffSum (hmp : MeasurePreserving σ μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffSum σ f n ω ∂μ = n * ∫ ω, f ω ∂μ := by
  simp only [birkhoffSum]
  rw [integral_finsetSum (f := fun i ω => f (σ^[i] ω)) _
    (fun i _ => (hmp.iterate i).integrable_comp_of_integrable hf)]
  have hcomp : ∀ i ∈ Finset.range n, ∫ ω, f (σ^[i] ω) ∂μ = ∫ ω, f ω ∂μ := by
    intro i _
    have hmap : Measure.map (σ^[i]) μ = μ := (hmp.iterate i).map_eq
    calc ∫ ω, f (σ^[i] ω) ∂μ = ∫ ω, f ω ∂(Measure.map (σ^[i]) μ) :=
          (integral_map (hmp.iterate i).measurable.aemeasurable
            (by rw [hmap]; exact hf.aestronglyMeasurable)).symm
      _ = ∫ ω, f ω ∂μ := by rw [hmap]
  rw [Finset.sum_congr rfl hcomp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- If the Birkhoff averages of `g` converge a.e. to a *constant* `c`, then `|c| ≤ ‖g‖₁`.

Proved from `maximal_inequality_global` rather than Fatou: for `t < |c|`, a.e. `ω` has some
`Aⱼ|g|(ω) ≥ |Aⱼg(ω)| > t`, so the maximal set has full measure and the global maximal
inequality reads `t ≤ ‖g‖₁`. -/
theorem abs_le_integral_abs_of_ae_tendsto_const [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving σ μ μ) (g : Ω → ℝ) (hgm : Measurable g) (hg : Integrable g μ)
    {c : ℝ} (hc : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ g n ω) Filter.atTop (nhds c)) :
    |c| ≤ ∫ x, |g x| ∂μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases le_or_gt |c| ε with hsmall | hbig
  · have : (0 : ℝ) ≤ ∫ x, |g x| ∂μ := integral_nonneg fun x => abs_nonneg _
    linarith
  -- `t := |c| - ε > 0`; a.e. `ω` lies in the maximal set at level `t`.
  set t : ℝ := |c| - ε with htdef
  have ht : 0 < t := by rw [htdef]; linarith
  have hfull : ∀ᵐ ω ∂μ, ∃ j, 1 ≤ j ∧ t * j < birkhoffSum σ (fun y => |g y|) j ω := by
    filter_upwards [hc] with ω hω
    -- `|Aⱼg(ω)| → |c| > t`, so some `j ≥ 1` has `|Aⱼg(ω)| > t`.
    have habs : Filter.Tendsto (fun n : ℕ => |birkhoffAverage ℝ σ g n ω|)
        Filter.atTop (nhds |c|) := hω.abs
    have hev := (habs.eventually (eventually_gt_nhds (by rw [htdef]; linarith : t < |c|)))
    obtain ⟨j, hjt, hj1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    refine ⟨j, hj1, ?_⟩
    rw [birkhoffAverage_real, abs_div, abs_of_pos hj0, lt_div_iff₀ hj0] at hjt
    refine lt_of_lt_of_le (by linarith [hjt] : t * (j : ℝ) < |birkhoffSum σ g j ω|) ?_
    simpa [birkhoffSum] using
      Finset.abs_sum_le_sum_abs (fun i => g (σ^[i] ω)) (Finset.range j)
  have hmeas : μ.real {ω | ∃ j, 1 ≤ j ∧ t * j < birkhoffSum σ (fun y => |g y|) j ω} = 1 := by
    have h1 : μ {ω | ∃ j, 1 ≤ j ∧ t * j < birkhoffSum σ (fun y => |g y|) j ω} = μ Set.univ := by
      refine measure_congr ?_
      filter_upwards [hfull] with ω hω
      simp only [ Set.mem_univ, iff_true, eq_iff_iff]
      exact hω
    rw [measureReal_def, h1, measure_univ]; simp
  have hglob := maximal_inequality_global (f := fun y => |g y|) (ε := t) hmp hg.abs hgm.abs
  rw [hmeas, mul_one] at hglob
  have : ∫ x, ‖|g x|‖ ∂μ = ∫ x, |g x| ∂μ := by
    simp [Real.norm_eq_abs, abs_abs]
  rw [show (fun x => |(|g x|)|) = fun x => |g x| by funext x; rw [abs_abs]] at hglob
  linarith [hglob]

/-- **Birkhoff's pointwise ergodic theorem, ergodic form.** For an ergodic measure-preserving
map the Birkhoff averages converge a.e. to `∫ f ∂μ`.

Two steps. For *bounded* `f` the averages are uniformly bounded, so dominated convergence gives
`∫ Aₙf → c`, and `∫ Aₙf = ∫ f` for every `n` (`integral_birkhoffSum`) forces `c = ∫ f`. For
general `L¹` `f`, truncate: `c(f) - c(f_N) = c(f - f_N)` by linearity of limits, and
`|c(f - f_N)| ≤ ‖f - f_N‖₁` by `abs_le_integral_abs_of_ae_tendsto_const`, which tends to `0`. -/
theorem ae_tendsto_birkhoffAverage_of_ergodic [IsProbabilityMeasure μ] (hσ : Ergodic σ μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ f n ω) Filter.atTop (nhds (∫ x, f x ∂μ)) := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  obtain ⟨c, hc⟩ := exists_ae_tendsto_birkhoffAverage_const hσ f hfm hf
  suffices hval : c = ∫ x, f x ∂μ by rwa [← hval]
  -- Truncations, as in `ae_tendsto_birkhoffAverage`.
  set T : ℕ → Ω → ℝ := fun N x => if (N : ℝ) < |f x| then 0 else f x with hT
  have hTm : ∀ N, Measurable (T N) := fun N =>
    Measurable.ite (measurableSet_lt measurable_const hfm.abs) measurable_const hfm
  have hTle : ∀ N x, |T N x| ≤ (N : ℝ) := by
    intro N x
    simp only [hT]
    split
    · simp
    · exact not_lt.mp (by assumption)
  have hTint : ∀ N, Integrable (T N) μ := fun N =>
    Integrable.mono' (integrable_const ((N : ℝ))) (hTm N).aestronglyMeasurable
      (by filter_upwards with x using by rw [Real.norm_eq_abs]; exact hTle N x)
  -- Bounded case: the constant for `T N` is `∫ T N`.
  have hbounded : ∀ N : ℕ, ∀ d : ℝ,
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => birkhoffAverage ℝ σ (T N) n ω)
        Filter.atTop (nhds d)) → d = ∫ x, T N x ∂μ := by
    intro N d hd
    have hAbound : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖birkhoffAverage ℝ σ (T N) n ω‖ ≤ (N : ℝ) := by
      intro n
      filter_upwards with ω
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [birkhoffAverage_real]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, birkhoffAverage_real, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
      calc |birkhoffSum σ (T N) n ω| ≤ ∑ i ∈ Finset.range n, |T N (σ^[i] ω)| := by
            simpa [birkhoffSum] using
              Finset.abs_sum_le_sum_abs (fun i => T N (σ^[i] ω)) (Finset.range n)
        _ ≤ ∑ _i ∈ Finset.range n, (N : ℝ) :=
            Finset.sum_le_sum (fun i _ => hTle N _)
        _ = (N : ℝ) * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hlim := tendsto_integral_of_dominated_convergence
      (F := fun n : ℕ => fun ω => birkhoffAverage ℝ σ (T N) n ω) (f := fun _ => d)
      (bound := fun _ => (N : ℝ))
      (fun n => by
        simp only [birkhoffAverage_real]
        exact (((Finset.measurable_sum _
          (fun i _ => (hTm N).comp (hmp.measurable.iterate i))).div_const _)).aestronglyMeasurable)
      (integrable_const _) hAbound hd
    -- `∫ Aₙ(T N) = ∫ T N` for `n ≥ 1` (at `n = 0` the average is `0/0 = 0`, hence the
    -- eventual, not pointwise, congruence).
    have hconst : ∀ᶠ n : ℕ in Filter.atTop,
        ∫ ω, birkhoffAverage ℝ σ (T N) n ω ∂μ = ∫ x, T N x ∂μ := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [birkhoffAverage_real]
      rw [integral_div, integral_birkhoffSum hmp _ (hTint N)]
      field_simp
    have hlim' : Filter.Tendsto (fun n : ℕ => ∫ ω, birkhoffAverage ℝ σ (T N) n ω ∂μ)
        Filter.atTop (nhds d) := by simpa using hlim
    exact tendsto_nhds_unique (hlim'.congr' hconst) tendsto_const_nhds
  -- Each truncation has its own constant, equal to its integral.
  have hTconv : ∀ N : ℕ, ∃ d : ℝ, (∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (T N) n ω) Filter.atTop (nhds d)) ∧
      d = ∫ x, T N x ∂μ := by
    intro N
    obtain ⟨d, hd⟩ := exists_ae_tendsto_birkhoffAverage_const hσ (T N) (hTm N) (hTint N)
    exact ⟨d, hd, hbounded N d hd⟩
  -- `|c - ∫ T N| ≤ ‖f - T N‖₁`, by linearity of limits and the maximal-inequality bound.
  have hclose : ∀ N : ℕ, |c - ∫ x, T N x ∂μ| ≤ ∫ x, |f x - T N x| ∂μ := by
    intro N
    obtain ⟨d, hd, hdval⟩ := hTconv N
    have hdiff : ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => birkhoffAverage ℝ σ (fun y => f y - T N y) n ω)
        Filter.atTop (nhds (c - d)) := by
      filter_upwards [hc, hd] with ω h1 h2
      refine (h1.sub h2).congr (fun n => ?_)
      simp only [birkhoffAverage_real, ← sub_div]
      congr 1
      simp [birkhoffSum, Finset.sum_sub_distrib]
    have hb := abs_le_integral_abs_of_ae_tendsto_const hmp (fun y => f y - T N y)
      (hfm.sub (hTm N)) (hf.sub (hTint N)) hdiff
    rwa [hdval] at hb
  -- `‖f - T N‖₁ → 0` by dominated convergence.
  have hL1 : Filter.Tendsto (fun N : ℕ => ∫ x, |f x - T N x| ∂μ) Filter.atTop (nhds 0) := by
    have hbound : ∀ N : ℕ, ∀ᵐ x ∂μ, ‖|f x - T N x|‖ ≤ |f x| := by
      intro N
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_abs]
      simp only [hT]
      split
      · simp
      · simp
    have hptw : ∀ᵐ x ∂μ, Filter.Tendsto (fun N : ℕ => |f x - T N x|) Filter.atTop (nhds 0) := by
      filter_upwards with x
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt |f x|
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hlt : ¬ ((N : ℝ) < |f x|) := by
        have hx : (|f x|) < (N : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
        linarith
      simp [hT, hlt]
    have hdc := tendsto_integral_of_dominated_convergence
      (F := fun N : ℕ => fun x => |f x - T N x|) (f := fun _ => (0 : ℝ)) (bound := fun x => |f x|)
      (fun N => ((hfm.sub (hTm N)).abs).aestronglyMeasurable) hf.abs hbound hptw
    simpa using hdc
  -- Hence `∫ T N → ∫ f` and `∫ T N → c`, so `c = ∫ f`.
  have hto_f : Filter.Tendsto (fun N : ℕ => ∫ x, T N x ∂μ) Filter.atTop
      (nhds (∫ x, f x ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hL1.eventually (gt_mem_nhds hδ))
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq, ← integral_sub (hTint N) hf]
    refine lt_of_le_of_lt (le_trans abs_integral_le_integral_abs (le_of_eq ?_)) (hN₀ N hN)
    congr 1
    funext x
    rw [abs_sub_comm]
  have hto_c : Filter.Tendsto (fun N : ℕ => ∫ x, T N x ∂μ) Filter.atTop (nhds c) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hL1.eventually (gt_mem_nhds hδ))
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hclose N) (hN₀ N hN)
  exact tendsto_nhds_unique hto_c hto_f

/-!
## Note: powers of an ergodic map need not be ergodic

Downstream (`kingman`'s `limsup ≤ C` half) the block decomposition
`f_n ≤ Σ_{i<q} f_N ∘ σ^{iN} + boundary` produces a Birkhoff average *for `σ^N`*. It is tempting
to apply `ae_tendsto_birkhoffAverage_of_ergodic` to `σ^N` directly, but **`σ` ergodic does not
imply `σ^N` ergodic**, and this is not an artefact of small or atomic spaces.

Counterexample on an infinite, atomless, standard Borel space: `X = {0,1} × [0,1]` with
`½·(counting × Lebesgue)`, `σ (0, y) = (1, y)` and `σ (1, y) = (0, S y)` for `S` ergodic on
`[0,1]`. Then `σ` is ergodic but `σ² (i, y) = (i, S y)` preserves `{0} × [0,1]`, of measure `½`.
This is an exercise of Rudolph [rudolph1990fundamentals] with `n = k = 2`; Rudolph
poses that exercise precisely because ergodic maps with non-ergodic powers exist on Lebesgue
spaces. `σ^N` is ergodic for every `N` exactly when `σ` is *totally ergodic*, i.e. has no
non-trivial root of unity in its point spectrum — which infiniteness does not give.

**This costs nothing**, because the standard proof does not use `σ^N`-ergodicity: averaging the
decomposition over the offset `j ∈ [0, N)` turns the `σ^N`-average of `f_N` into a `σ`-average,
so only ergodicity of `σ` itself is needed.
See `easyking_of_integrable`'s docstring in `ProofMet.Kingman`,
which already records the offset average.
-/

end MultiplicativeErgodic
