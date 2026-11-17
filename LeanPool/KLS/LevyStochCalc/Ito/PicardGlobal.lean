/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardWindow

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- Two right-continuous processes that agree a.s. at each time of `[0, T]` agree, almost surely,
at every time of `[0, T]` simultaneously. -/
theorem ae_all_eq_of_rightCont {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T → A (q : ℝ) ω = B (q : ℝ) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [h (q : ℝ) hq] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hq' => absurd hq' hq
  have hend : ∀ᵐ ω ∂P, (0 : ℝ) ≤ T → A T ω = B T ω := by
    by_cases hT : (0 : ℝ) ≤ T
    · filter_upwards [h T ⟨hT, le_rfl⟩] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hT' => absurd hT' hT
  filter_upwards [hA, hB, hrat, hend] with ω hAω hBω hqω hTω
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq]
    exact hTω (ht.1.trans ht.2)
  · have hex : ∀ k : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((k : ℝ) + 1)) T := by
      intro k
      refine exists_rat_btwn (lt_min ?_ hlt)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    choose q hq1 hq2 using hex
    have hqIcc : ∀ k, ((q k : ℝ)) ∈ Set.Icc (0 : ℝ) T := fun k =>
      ⟨(ht.1.trans_lt (hq1 k)).le, ((hq2 k).trans_le (min_le_right _ _)).le⟩
    have htend : Filter.Tendsto (fun k : ℕ => (q k : ℝ)) Filter.atTop
        (nhdsWithin t (Set.Ioi t)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.Eventually.of_forall fun k => hq1 k⟩
      have hub : ∀ k : ℕ, (q k : ℝ) ≤ t + 1 / ((k : ℝ) + 1) := fun k =>
        ((hq2 k).trans_le (min_le_left _ _)).le
      have hlb : ∀ k : ℕ, t ≤ (q k : ℝ) := fun k => (hq1 k).le
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := tendsto_const_nhds (x := t) (f := Filter.atTop (α := ℕ)) |>.add
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hlb hub
    have h1 := (hAω t).comp htend
    have h2 := (hBω t).comp htend
    have heqq : ((fun s => A s ω) ∘ fun k : ℕ => (q k : ℝ))
        = ((fun s => B s ω) ∘ fun k : ℕ => (q k : ℝ)) :=
      funext fun k => hqω (q k) (hqIcc k)
    rw [heqq] at h1
    exact tendsto_nhds_unique h1 h2

/-! ### The glued path map -/

/-- Glue a family of window solutions, using on `[0, t]` the member whose horizon covers `t`. -/
noncomputable def globalPatch (Y : ℕ → ℝ → Ω → (Fin n → ℝ)) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => Y ⌈t⌉₊ t ω

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is jointly measurable. -/
theorem measurable_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, Measurable (Function.uncurry (Y k))) :
    Measurable (Function.uncurry (globalPatch Y)) := by
  have h : Measurable fun p : ℕ × (ℝ × Ω) => Function.uncurry (Y p.1) p.2 :=
    measurable_from_prod_countable_right fun k => hY k
  exact h.comp ((measurable_fst.nat_ceil).prodMk measurable_id)

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is progressively measurable: below any time only finitely many members
of the family are read, on measurable pieces of the time axis. -/
theorem progressivelyMeasurable_globalPatch
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hsum : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => globalPatch Y s p.1 i) p.2)
      = ∑ k ∈ Finset.range (⌈t⌉₊ + 1),
          (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
            (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := by
    funext p
    rw [Finset.sum_apply]
    by_cases hp : p.2 ≤ t
    · have hmem : ⌈p.2⌉₊ ∈ Finset.range (⌈t⌉₊ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono hp))
      rw [Finset.sum_eq_single_of_mem ⌈p.2⌉₊ hmem]
      · rw [Set.indicator_of_mem (by simp : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = ⌈p.2⌉₊})]
        simp [Set.indicator_of_mem (Set.mem_Iic.mpr hp), globalPatch]
      · intro b _ hb
        exact Set.indicator_of_notMem (by simpa [eq_comm] using hb) _
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hq : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = k}
      · rw [Set.indicator_of_mem hq, Set.indicator_of_notMem (by simpa using hp)]
      · exact Set.indicator_of_notMem hq _
  have hterm : ∀ k : ℕ, StronglyMeasurable
      (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
        (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := fun k =>
    (hY k i t).indicator
      ((measurable_snd (α := Ω) (β := ℝ)).nat_ceil (measurableSet_singleton k))
  rw [hsum]
  exact Finset.stronglyMeasurable_sum _ fun k _ => hterm k

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

/-- Window solutions on nested windows agree, almost surely, along whole paths. -/
theorem ae_all_windows_agree
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)))
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)),
      Y p.1 t ω = Y p.2 t ω := by
  rw [MeasureTheory.ae_all_iff]
  rintro ⟨j, k⟩
  have hTpos : (0 : ℝ) < min ((j : ℝ) + 1) ((k : ℝ) + 1) :=
    lt_min (by positivity) (by positivity)
  have hpt := ae_eq_of_solvesOn W N ℱ hℱW hℱN coeffs x₀ hReg hLip (hYm j) (hYm k)
    (hYS j) (hYS k) hTpos
    (SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_left _ _) (hYsol j))
    (SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_right _ _) (hYsol k))
  refine ae_all_eq_of_rightCont (hYcad j) (hYcad k) fun t ht => ?_
  filter_upwards [hpt t ht] with ω hω
  exact funext hω

omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map coincides, almost surely, with each member of a consistent family on that
member's window. -/
theorem ae_globalPatch_eq {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hcons : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ,
      ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)), Y p.1 t ω = Y p.2 t ω) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1), globalPatch Y t ω = Y k t ω := by
  filter_upwards [hcons] with ω hω
  intro k t ht
  refine hω (⌈t⌉₊, k) t ⟨ht.1, le_min ?_ ht.2⟩
  exact (Nat.le_ceil t).trans (by linarith)

omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map has a finite `S²` norm on every window. -/
theorem lintegral_sq_iSup_globalPatch_lt_top {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
      (‖globalPatch Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hYS ⌈T'⌉₊ T' hT')
  filter_upwards [hagree] with ω hω
  refine le_of_eq (iSup_congr fun t => ?_)
  rw [hω ⌈T'⌉₊ (t : ℝ) ⟨t.2.1, t.2.2.trans ((Nat.le_ceil T').trans (by linarith))⟩]

omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map is almost surely càdlàg on the SDE time domain. -/
theorem cadlag_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => Y k s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => globalPatch Y s ω) (nhdsWithin t (Set.Ioi t))
          (nhds (globalPatch Y t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => globalPatch Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ) := by
  filter_upwards [hagree, MeasureTheory.ae_all_iff.mpr hYcad] with ω hω hcad
  intro t ht
  set k := ⌈t⌉₊ + 1 with hk
  have htk : t < (k : ℝ) := by
    have := Nat.le_ceil t
    push_cast [hk]
    linarith
  have hpatch : ∀ s : ℝ, 0 ≤ s → s ≤ (k : ℝ) + 1 → globalPatch Y s ω = Y k s ω :=
    fun s hs0 hs1 => hω k s ⟨hs0, hs1⟩
  constructor
  · have hev : ∀ᶠ s in nhdsWithin t (Set.Ioi t), globalPatch Y s ω = Y k s ω := by
      have hmem : Set.Iio ((k : ℝ) + 1) ∈ nhdsWithin t (Set.Ioi t) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [hmem, self_mem_nhdsWithin] with s hs hs'
      exact hpatch s (ht.trans (le_of_lt hs')) (le_of_lt hs)
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
    rw [hpatch t ht (by linarith)]
    exact (hcad k t).1
  · intro i
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · obtain ⟨ℓ, hℓ⟩ := (hcad 0 t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Iio t ∈ nhdsWithin t (Set.Iio t) := self_mem_nhdsWithin
      filter_upwards [hmem] with s hs
      have : ⌈s⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by simp only [Set.mem_Iio] at hs; linarith [ht0])
      simp [globalPatch, this]
    · obtain ⟨ℓ, hℓ⟩ := (hcad k t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Ioo (0 : ℝ) t ∈ nhdsWithin t (Set.Iio t) := by
        refine Filter.inter_mem ?_ self_mem_nhdsWithin
        exact nhdsWithin_le_nhds (Ioi_mem_nhds ht0)
      filter_upwards [hmem] with s hs
      rw [hpatch s hs.1.le (by linarith [hs.2])]

/-- **The glued path map solves the equation on every window.** -/
theorem solvesOn_globalPatch
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYa : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (globalPatch Y) T := by
  have hpm := measurable_globalPatch hYm
  have hpa := fun i => progressivelyMeasurable_globalPatch hYa i
  have hpS := lintegral_sq_iSup_globalPatch_lt_top hagree hYS
  refine ⟨measurable_sigma_comp_state coeffs hReg hpm,
    progressivelyMeasurable_sigma_comp_state coeffs hReg hpa,
    lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS,
    measurable_gamma_comp_state coeffs hReg hpm,
    markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa,
    lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS, ?_⟩
  intro t ht
  have htk : t ≤ (⌈t⌉₊ : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have heqn := (hYsol ⌈t⌉₊).eqn t ⟨ht.1, htk⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Y ⌈t⌉₊ s ω = globalPatch Y s ω := by
      filter_upwards [hagree] with ω hω
      refine (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun s hs => ?_)
      exact (hω ⌈t⌉₊ s ⟨hs.1, hs.2.trans htk⟩).symm
    have hcongr := picardStep_congr_ae W N ℱ hℱW hℱN coeffs (Y ⌈t⌉₊) (globalPatch Y) x₀
      (hYsol ⌈t⌉₊).h_σ_meas (hYsol ⌈t⌉₊).h_σ_progMeas (hYsol ⌈t⌉₊).h_σ_sq
      (hYsol ⌈t⌉₊).h_γ_meas (hYsol ⌈t⌉₊).h_γ_progMeas (hYsol ⌈t⌉₊).h_γ_sq
      (measurable_sigma_comp_state coeffs hReg hpm)
      (progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
      (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
      (measurable_gamma_comp_state coeffs hReg hpm)
      (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
      (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS) ht0 hae
    filter_upwards [heqn, hagree, hcongr] with ω h1 h2 h3
    intro i
    rw [h2 ⌈t⌉₊ t ⟨ht.1, htk⟩, h1 i, h3]
  · subst ht0
    filter_upwards [heqn, hagree,
      ae_picardStep_zero W N ℱ hℱW hℱN coeffs (Y ⌈(0 : ℝ)⌉₊) x₀
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_meas (hYsol ⌈(0 : ℝ)⌉₊).h_σ_progMeas
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_sq (hYsol ⌈(0 : ℝ)⌉₊).h_γ_meas
        (hYsol ⌈(0 : ℝ)⌉₊).h_γ_progMeas (hYsol ⌈(0 : ℝ)⌉₊).h_γ_sq,
      ae_picardStep_zero W N ℱ hℱW hℱN coeffs (globalPatch Y) x₀
        (measurable_sigma_comp_state coeffs hReg hpm)
        (progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
        (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
        (measurable_gamma_comp_state coeffs hReg hpm)
        (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
        (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)] with ω h1 h2 h3 h4
    intro i
    rw [h2 ⌈(0 : ℝ)⌉₊ 0 ⟨le_rfl, htk⟩, h1 i, h3 i, h4 i]

/-- A solution on a window starts at the initial datum. -/
theorem ae_eq_initial_of_solvesOn (x₀ : Fin n → ℝ) {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hT : 0 ≤ T) (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
      h.h_γ_meas h.h_γ_progMeas h.h_γ_sq] with ω h1 h2
  funext i
  rw [h1 i, h2 i]

/-- **Existence of a solution on `[0, ∞)`.** The window solutions of `exists_solvesOn` are
consistent, so gluing them along `⌈t⌉₊` gives a càdlàg, progressively measurable path map with
a finite `S²` norm on every window that solves the equation on every window. -/
theorem exists_globalSolution [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry X)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
        ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
            Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) := by
  have hex : ∀ k : ℕ, ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y ((k : ℝ) + 1) := fun k =>
    exists_solvesOn W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀ (by positivity)
  choose Y hYm hYa hYcad hYS hYsol using hex
  have hright : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)) := by
    intro k
    filter_upwards [hYcad k] with ω hω
    exact fun t => (hω t).1
  have hagree := ae_globalPatch_eq (Y := Y)
    (ae_all_windows_agree W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hright hYS hYsol)
  have hsol := solvesOn_globalPatch W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hagree hYS hYsol
  exact ⟨globalPatch Y, measurable_globalPatch hYm,
    fun i => progressivelyMeasurable_globalPatch hYa i,
    ae_eq_initial_of_solvesOn W N ℱ hℱW hℱN coeffs x₀ zero_le_one (hsol 1),
    cadlag_globalPatch hagree hYcad,
    lintegral_sq_iSup_globalPatch_lt_top hagree hYS, hsol⟩

end Glue

end LevyStochCalc.Ito.Picard
