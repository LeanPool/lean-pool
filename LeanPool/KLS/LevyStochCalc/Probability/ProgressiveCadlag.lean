/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Probability.Progressive
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Right-continuous adapted processes are progressively measurable

An adapted process with right-continuous paths is progressively measurable: on `(-∞, i] × Ω` it
is the pointwise limit of the dyadic right-staircases `t ↦ X_{⌈2ⁿt⌉/2ⁿ ∧ i}`, each of which
takes countably many values, all at times bounded by `i`.

## Main statements

* `Probability.dyadicCeil` — the dyadic right-staircase, capped at a horizon.
* `LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous` — a right-continuous
  adapted process is progressively measurable.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_uncurry` — a progressively
  measurable process is jointly measurable.
* `LevyStochCalc.Probability.exists_everywhere_cadlag_modification` — under the usual
  conditions, an almost-surely càdlàg adapted process has an everywhere-càdlàg modification.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc` — the integral
  of a progressively measurable process over `[0, t]` is measurable for `ℱ t`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Right-continuity along `𝓝[>] t` upgrades to `𝓝[≥] t`. -/
theorem tendsto_nhdsGE_of_nhdsGT {f : ℝ → ℝ} {t : ℝ}
    (h : Tendsto f (𝓝[>] t) (𝓝 (f t))) : Tendsto f (𝓝[≥] t) (𝓝 (f t)) := by
  have hset : Set.Ici t = Set.Ioi t ∪ {t} := by
    ext x
    simp [le_iff_lt_or_eq]
  rw [hset, nhdsWithin_union, nhdsWithin_singleton]
  exact h.sup (tendsto_pure_nhds f t)

/-- The dyadic right-staircase at scale `2⁻ⁿ`, capped at the horizon `i`. -/
noncomputable def dyadicCeil (n : ℕ) (i t : ℝ) : ℝ :=
  min ((⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n) i

theorem dyadicCeil_le (n : ℕ) (i t : ℝ) : dyadicCeil n i t ≤ i := min_le_right _ _

theorem le_dyadicCeil (n : ℕ) {i t : ℝ} (ht : t ≤ i) : t ≤ dyadicCeil n i t := by
  refine le_min ?_ ht
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc t * 2 ^ n = (2 : ℝ) ^ n * t := by ring
    _ ≤ (⌈(2 : ℝ) ^ n * t⌉ : ℝ) := Int.le_ceil _

theorem measurable_dyadicCeil (n : ℕ) (i : ℝ) : Measurable (dyadicCeil n i) := by
  have hcast : Measurable ((↑) : ℤ → ℝ) := measurable_of_countable _
  exact (((hcast.comp
    (Int.measurable_ceil.comp (measurable_const.mul measurable_id))).div
    measurable_const).min measurable_const)

theorem tendsto_dyadicCeil {i t : ℝ} (ht : t ≤ i) :
    Tendsto (fun n => dyadicCeil n i t) atTop (𝓝 t) := by
  have hupper : ∀ n : ℕ, (⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n ≤ t + (1 / 2 : ℝ) ^ n := by
    intro n
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : (⌈(2 : ℝ) ^ n * t⌉ : ℝ) ≤ (2 : ℝ) ^ n * t + 1 := (Int.ceil_lt_add_one _).le
    have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
      rw [div_pow, one_pow, div_mul_cancel₀ _ (by positivity : ((2 : ℝ) ^ n) ≠ 0)]
    nlinarith [h1, h2]
  have hzero : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htop : Tendsto (fun n : ℕ => t + ((1 : ℝ) / 2) ^ n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add hzero
  have hmid : Tendsto (fun n : ℕ => (⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
      (Filter.Eventually.of_forall fun n => ?_)
      (Filter.Eventually.of_forall fun n => hupper n)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    calc t * 2 ^ n = (2 : ℝ) ^ n * t := by ring
      _ ≤ (⌈(2 : ℝ) ^ n * t⌉ : ℝ) := Int.le_ceil _
  have := hmid.min (tendsto_const_nhds (x := i))
  rwa [min_eq_left ht] at this

/-- **A right-continuous adapted process is progressively measurable.** -/
theorem progressivelyMeasurable_of_rightContinuous
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    ProgressivelyMeasurable ℱ (fun ω s => X s ω) := by
  refine ProgressivelyMeasurable.of_isStronglyProgressive ?_
  intro i
  let : MeasurableSpace Ω := ℱ i
  -- the staircase, as a function of a dyadic index and the sample point
  have hslice : ∀ (n : ℕ) (k : ℤ),
      Measurable fun ω : Ω => X (min ((k : ℝ) / 2 ^ n) i) ω := by
    intro n k
    exact (hadapt _).mono (ℱ.mono (min_le_right _ _)) le_rfl
  have hF : ∀ n : ℕ, Measurable fun p : ℤ × Ω => X (min ((p.1 : ℝ) / 2 ^ n) i) p.2 := fun n =>
    measurable_from_prod_countable_right (fun k => hslice n k)
  have hg : ∀ n : ℕ, Measurable fun q : Set.Iic i × Ω => X (dyadicCeil n i (q.1 : ℝ)) q.2 := by
    intro n
    have he : Measurable fun q : Set.Iic i × Ω =>
        ((⌈(2 : ℝ) ^ n * (q.1 : ℝ)⌉ : ℤ), q.2) :=
      (Int.measurable_ceil.comp (measurable_const.mul
        (measurable_subtype_coe.comp measurable_fst))).prodMk measurable_snd
    exact (hF n).comp he
  have hconv : ∀ q : Set.Iic i × Ω,
      Tendsto (fun n => X (dyadicCeil n i (q.1 : ℝ)) q.2) atTop (𝓝 (X (q.1 : ℝ) q.2)) := by
    rintro ⟨⟨t, ht⟩, ω⟩
    have hge : Tendsto (fun n => dyadicCeil n i t) atTop (𝓝[≥] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_dyadicCeil (Set.mem_Iic.mp ht))
        (Filter.Eventually.of_forall fun n => le_dyadicCeil n (Set.mem_Iic.mp ht))
    exact (tendsto_nhdsGE_of_nhdsGT (hright ω t)).comp hge
  exact (measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.mpr hconv)).stronglyMeasurable

/-- A progressively measurable real process is jointly measurable. -/
theorem ProgressivelyMeasurable.measurable_uncurry
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) : Measurable (Function.uncurry H) := by
  have hmono : ∀ t : ℝ, @Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance
      ≤ @Prod.instMeasurableSpace Ω ℝ ‹MeasurableSpace Ω› inferInstance :=
    fun t => sup_le_sup (MeasurableSpace.comap_mono (ℱ.le t)) le_rfl
  have hf : ∀ n : ℕ, Measurable fun p : Ω × ℝ =>
      (Set.Iic ((n : ℕ) : ℝ)).indicator (H p.1) p.2 :=
    fun n => ((h ((n : ℕ) : ℝ)).mono (hmono _)).measurable
  have hconv : ∀ p : Ω × ℝ,
      Tendsto (fun n : ℕ => (Set.Iic ((n : ℕ) : ℝ)).indicator (H p.1) p.2) atTop
        (𝓝 (Function.uncurry H p)) := by
    intro p
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈p.2⌉₊] with n hn
    have hle : p.2 ≤ ((n : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil p.2) (by exact_mod_cast hn)
    exact (Set.indicator_of_mem (Set.mem_Iic.mpr hle) _).symm
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hconv)

/-- **A right-continuous adapted process is jointly measurable.** -/
theorem measurable_uncurry_of_rightContinuous
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    Measurable (Function.uncurry X) :=
  ((progressivelyMeasurable_of_rightContinuous hadapt hright).measurable_uncurry).comp
    measurable_swap

/-- **An almost-surely càdlàg adapted process has an everywhere-càdlàg adapted modification**,
when `ℱ 0` contains the `P`-null sets and lies below `ℱ t` for `t ≤ 0`. -/
theorem exists_everywhere_cadlag_modification
    {P : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ → Ω → ℝ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L)) :
    ∃ Y : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Y t)) ∧ (∀ t : ℝ, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by
  classical
  obtain ⟨N, hsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hcad)
  have hNout : ∀ ω : Ω, ω ∉ N → ∀ t : ℝ,
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L) :=
    fun ω hω => not_not.mp fun h => hω (hsub h)
  have hNF : ∀ t : ℝ, MeasurableSet[ℱ t] N := by
    intro t
    rcases le_or_gt 0 t with h | h
    · exact ℱ.mono h _ (hnull N hNmeas hNzero)
    · exact hℱ0 t h.le _ (hnull N hNmeas hNzero)
  refine ⟨fun t ω => if ω ∈ N then 0 else X t ω, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · exact Measurable.piecewise (hNF t) measurable_const (hadapt t)
  · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω
    simp [Set.notMem_of_mem_compl hω]
  · intro ω t
    by_cases hω : ω ∈ N
    · simp only [hω, ite_eq_left]
      exact tendsto_const_nhds
    · simpa [hω] using (hNout ω hω t).1
  · intro ω t
    by_cases hω : ω ∈ N
    · refine ⟨0, ?_⟩
      simp only [hω, ite_eq_left]
      exact tendsto_const_nhds
    · obtain ⟨L, hL⟩ := (hNout ω hω t).2
      exact ⟨L, by simpa [hω] using hL⟩

/-- The integral of a progressively measurable process over `[0, t]` is `ℱ t`-measurable. -/
theorem ProgressivelyMeasurable.measurable_setIntegral_Icc
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume := by
  let : MeasurableSpace Ω := ℱ t
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hind : Measurable fun ω : Ω =>
      ∫ s in Set.Icc (0 : ℝ) t, (Set.Iic t).indicator (H ω) s ∂volume :=
    ((h t).integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable
  have heq : (fun ω : Ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume)
      = fun ω : Ω => ∫ s in Set.Icc (0 : ℝ) t, (Set.Iic t).indicator (H ω) s ∂volume := by
    funext ω
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    exact (Set.indicator_of_mem (Set.mem_Iic.mpr hs.2) (H ω)).symm
  rw [heq]
  exact hind

end LevyStochCalc.Probability
