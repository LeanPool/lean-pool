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

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoOptionalStopping
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrement

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

/-- The two-valued stopping time that stops at `c`, unless `τ` has already reached `c`. -/
noncomputable def stepStop (c : ℝ) : Ω → WithTop ℝ :=
  fun ω => if (c : WithTop ℝ) ≤ τ ω then ⊤ else (c : WithTop ℝ)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_stepStop (c : ℝ) (ω : Ω) : τ ω ≤ stepStop τ c ω := by
  rw [stepStop]
  split_ifs with h
  · exact le_top
  · exact (not_le.mp h).le

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem stepStop_eq_or (c : ℝ) (ω : Ω) :
    stepStop τ c ω = ((c : ℝ) : WithTop ℝ) ∨ stepStop τ c ω = ⊤ := by
  rw [stepStop]
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem isStoppingTime_stepStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    MeasureTheory.IsStoppingTime ℱ (stepStop τ c) := by
  intro i
  by_cases hci : c ≤ i
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | τ ω < ((c : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [stepStop, Set.mem_ofPred_eq]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [ite_eq_left h, top_le_iff]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hcon
          exact absurd h (not_le.mpr hcon)
      · simp only [ite_eq_right h]
        exact ⟨fun _ => not_le.mp h, fun _ => by exact_mod_cast hci⟩
    rw [hset]
    exact ℱ.mono hci _ (hτ.measurableSet_lt c)
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [stepStop, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [ite_eq_left h, top_le_iff]
        simp
      · simp only [ite_eq_right h]
        exact fun hcon => hci (by exact_mod_cast hcon)
    rw [hset]
    exact @MeasurableSet.empty Ω (ℱ i)

/-- A point of the uniform grid on `[0, t]` with `n` steps. -/
noncomputable def gridPt (t : ℝ) (n k : ℕ) : ℝ := (k : ℝ) * t / (n : ℝ)

/-- The stopping time that stops at the first grid point strictly beyond `τ`, among the first
`k + 1` points. -/
noncomputable def gridStopAux (t : ℝ) (n : ℕ) : ℕ → Ω → WithTop ℝ
  | 0 => stepStop τ (gridPt t n 0)
  | (k + 1) => fun ω => min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux t n k ω)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridStopAux_le_iff (t : ℝ) (n k : ℕ) (ω : Ω) (a : WithTop ℝ) :
    gridStopAux τ t n k ω ≤ a ↔ ∃ j ≤ k, stepStop τ (gridPt t n j) ω ≤ a := by
  induction k with
  | zero =>
    constructor
    · intro h
      exact ⟨0, le_rfl, h⟩
    · rintro ⟨j, hj, hjle⟩
      rw [Nat.le_zero] at hj
      subst hj
      exact hjle
  | succ k ih =>
    rw [gridStopAux, min_le_iff, ih]
    constructor
    · rintro (h | ⟨j, hj, hjle⟩)
      · exact ⟨k + 1, le_rfl, h⟩
      · exact ⟨j, hj.trans (Nat.le_succ k), hjle⟩
    · rintro ⟨j, hj, hjle⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hlt, hjle⟩
      · have : j = k + 1 := le_antisymm hj hge
        subst this
        exact Or.inl hjle

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_gridStopAux (t : ℝ) (n k : ℕ) (ω : Ω) : τ ω ≤ gridStopAux τ t n k ω := by
  induction k with
  | zero => exact le_stepStop τ _ ω
  | succ k ih => exact le_min (le_stepStop τ _ ω) ih

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridStopAux_eq (t : ℝ) (n k : ℕ) (ω : Ω) :
    (∃ j ≤ k, gridStopAux τ t n k ω = ((gridPt t n j : ℝ) : WithTop ℝ))
      ∨ gridStopAux τ t n k ω = ⊤ := by
  induction k with
  | zero =>
    rcases stepStop_eq_or τ (gridPt t n 0) ω with h | h
    · exact Or.inl ⟨0, le_rfl, h⟩
    · exact Or.inr h
  | succ k ih =>
    have hval : gridStopAux τ t n (k + 1) ω
        = min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) := rfl
    rw [hval]
    rcases le_total (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) with h | h
    · rw [min_eq_left h]
      rcases stepStop_eq_or τ (gridPt t n (k + 1)) ω with h1 | h1
      · exact Or.inl ⟨k + 1, le_rfl, h1⟩
      · exact Or.inr h1
    · rw [min_eq_right h]
      rcases ih with ⟨j, hj, hje⟩ | hje
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ k), hje⟩
      · exact Or.inr hje

theorem isStoppingTime_gridStopAux {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopAux τ t n k) := by
  intro i
  have hset : {ω | gridStopAux τ t n k ω ≤ ((i : ℝ) : WithTop ℝ)}
      = ⋃ j : Fin (k + 1), {ω | stepStop τ (gridPt t n j) ω ≤ ((i : ℝ) : WithTop ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, gridStopAux_le_iff]
    constructor
    · rintro ⟨j, hj, hjle⟩
      exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, hjle⟩
    · rintro ⟨j, hjle⟩
      exact ⟨j.1, Nat.lt_succ_iff.mp j.2, hjle⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j => isStoppingTime_stepStop τ hτ (gridPt t n j) i

/-- The stopping time that stops at the first point of the uniform grid on `[0, t]` with `n`
steps that lies strictly beyond `τ`. -/
noncomputable def gridStop (t : ℝ) (n : ℕ) : Ω → WithTop ℝ := gridStopAux τ t n n

theorem isStoppingTime_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStop τ t n) :=
  isStoppingTime_gridStopAux τ hτ t n n

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_gridStop (t : ℝ) (n : ℕ) (ω : Ω) : τ ω ≤ gridStop τ t n ω :=
  le_gridStopAux τ t n n ω

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) : 0 ≤ gridPt t n k := by
  unfold gridPt
  positivity

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_lt_of_lt {t : ℝ} (ht : 0 < t) {n k : ℕ} (hk : k < n) : gridPt t n k < t := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le k) hk
  rw [gridPt, div_lt_iff₀ hn]
  have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
  nlinarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_self {t : ℝ} {n : ℕ} (hn : n ≠ 0) : gridPt t n n = t := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [gridPt]
  field_simp

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The grid stopping time takes one of the grid values strictly below `t`, or a value at
least `t`. -/
theorem gridStop_finiteRange {t : ℝ} {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    (∃ c ∈ (Finset.range n).image (gridPt t n),
        gridStop τ t n ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω := by
  rcases gridStopAux_eq τ t n n ω with ⟨j, hj, hje⟩ | hje
  · rcases lt_or_eq_of_le hj with hlt | rfl
    · exact Or.inl ⟨gridPt t n j, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, rfl⟩, hje⟩
    · refine Or.inr ?_
      rw [gridStop, hje, gridPt_self hn]
  · exact Or.inr (by rw [gridStop, hje]; exact le_top)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Eventually in the mesh, the grid stopping time falls strictly below any time the stopping
time has already passed. -/
theorem eventually_gridStop_lt {t : ℝ} (ht : 0 < t) (ω : Ω) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hτs : τ ω < ((s : ℝ) : WithTop ℝ)) :
    ∀ᶠ n in Filter.atTop, gridStop τ t n ω < ((s : ℝ) : WithTop ℝ) := by
  have hne : τ ω ≠ ⊤ := by
    intro h
    rw [h] at hτs
    exact absurd hτs (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrs : r < s := by
    rw [← hr] at hτs
    exact_mod_cast hτs
  set u : ℝ := max r 0 with hu
  have hu0 : 0 ≤ u := le_max_right r 0
  have hus : u < s := max_lt hrs hs
  have hpos : 0 < s - u := sub_pos.mpr hus
  obtain ⟨N, hN⟩ := exists_nat_gt (t / (s - u))
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hstep : t / (n : ℝ) < s - u := by
    have h1 : t / (s - u) < (n : ℝ) := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hpos] at h1
    linarith
  set j : ℕ := ⌊u * (n : ℝ) / t⌋₊ + 1 with hj
  have hfl : (⌊u * (n : ℝ) / t⌋₊ : ℝ) ≤ u * (n : ℝ) / t :=
    Nat.floor_le (by positivity)
  have hfl' : u * (n : ℝ) / t < (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hjc : (j : ℝ) = (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 := by
    rw [hj]
    push_cast
    ring
  have hgu : u < gridPt t n j := by
    rw [gridPt, lt_div_iff₀ hnpos, hjc]
    have := hfl'
    rw [div_lt_iff₀ ht] at this
    nlinarith
  have hgs : gridPt t n j < s := by
    have hle : gridPt t n j ≤ u + t / (n : ℝ) := by
      rw [gridPt, hjc, div_le_iff₀ hnpos]
      have := hfl
      rw [le_div_iff₀ ht] at this
      field_simp
      nlinarith
    linarith
  have hjn : j ≤ n := by
    by_contra hcon
    push Not at hcon
    have : t ≤ gridPt t n j := by
      rw [gridPt, le_div_iff₀ hnpos]
      have : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hcon.le
      nlinarith
    linarith
  have hstep' : stepStop τ (gridPt t n j) ω = ((gridPt t n j : ℝ) : WithTop ℝ) := by
    rw [stepStop, ite_eq_right]
    rw [← hr]
    intro hcon
    have : gridPt t n j ≤ r := by exact_mod_cast hcon
    have : gridPt t n j ≤ u := le_trans this (le_max_left r 0)
    linarith
  calc gridStop τ t n ω ≤ stepStop τ (gridPt t n j) ω :=
        (gridStopAux_le_iff τ t n n ω _).mpr ⟨j, hjn, le_rfl⟩
    _ = ((gridPt t n j : ℝ) : WithTop ℝ) := hstep'
    _ < ((s : ℝ) : WithTop ℝ) := by exact_mod_cast hgs

end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The local property of the Itô integral.** At a time the stopping time has not reached,
cutting the integrand off at it changes nothing. -/
theorem stochasticIntegralBrownian_stopped_eq_of_le
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
          (Probability.measurable_uncurry_stopped hτ hm)
          (Probability.ProgressivelyMeasurable.stopped hτ hp)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
  classical
  -- the cut integrand and its approximations
  have hmS := Probability.measurable_uncurry_stopped hτ hm
  have hpS := Probability.ProgressivelyMeasurable.stopped hτ hp
  have hqS := energy_lt_top_of_abs_le (P := P) (fun ω s => Probability.abs_stopped_le τ H ω s) hq
  have hmG : ∀ n : ℕ, Measurable (Function.uncurry
      (Probability.stopped (gridStop τ t n) H)) :=
    fun n => Probability.measurable_uncurry_stopped (isStoppingTime_gridStop τ hτ t n) hm
  have hpG : ∀ n : ℕ, Probability.ProgressivelyMeasurable ℱ
      (Probability.stopped (gridStop τ t n) H) :=
    fun n => Probability.ProgressivelyMeasurable.stopped (isStoppingTime_gridStop τ hτ t n) hp
  have hqG : ∀ (n : ℕ) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Probability.stopped (gridStop τ t n) H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun n => energy_lt_top_of_abs_le (P := P)
      (fun ω s => Probability.abs_stopped_le (gridStop τ t n) H ω s) hq
  -- the event on which the stopping time has not been reached
  set A : Set Ω := {ω | ((t : ℝ) : WithTop ℝ) ≤ τ ω} with hAdef
  have hAmeas : MeasurableSet A := by
    have hcompl : A = {ω | τ ω < ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp only [hAdef, Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    rw [hcompl]
    exact (ℱ.le t _ (hτ.measurableSet_lt t)).compl
  -- on that event the approximations already agree with the uncut integral
  have hagree : ∀ n : ℕ, n ≠ 0 → ∀ᵐ ω ∂P, ω ∈ A →
      stochasticIntegralBrownian W ℱ hℱ (Probability.stopped (gridStop τ t n) H)
          (hmG n) (hpG n) (hqG n) t ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
    intro n hn
    have hid := stochasticIntegralBrownian_stopped (gridStop τ t n) W ℱ hℱ
      (isStoppingTime_gridStop τ hτ t n) hm hp hq ht
      ((Finset.range n).image (gridPt t n))
      (by
        intro c hc
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact gridPt_nonneg ht.le n k)
      (by
        intro c hc
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
        exact gridPt_lt_of_lt ht (Finset.mem_range.mp hk))
      (gridStop_finiteRange τ hn)
    filter_upwards [hid] with ω hω hωA
    rw [hω]
    have hzero : ∀ c ∈ (Finset.range n).image (gridPt t n),
        hitInd (gridStop τ t n) c ω = 0 := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
      have hlt : gridPt t n k < t := gridPt_lt_of_lt ht (Finset.mem_range.mp hk)
      have hne : gridStop τ t n ω ≠ ((gridPt t n k : ℝ) : WithTop ℝ) := by
        intro hcon
        have h1 : ((t : ℝ) : WithTop ℝ) ≤ ((gridPt t n k : ℝ) : WithTop ℝ) :=
          le_trans hωA (le_trans (le_gridStop τ t n ω) (le_of_eq hcon))
        exact absurd (by exact_mod_cast h1 : t ≤ gridPt t n k) (not_le.mpr hlt)
      simp [hitInd, Set.indicator_of_notMem (show ω ∉ {ω | gridStop τ t n ω
        = ((gridPt t n k : ℝ) : WithTop ℝ)} from hne)]
    have hsum : ∑ c ∈ (Finset.range n).image (gridPt t n),
        hitInd (gridStop τ t n) c ω
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [hzero c hc, zero_mul]
    rw [hsum, sub_zero]
  -- the approximations converge to the cut integrand in energy
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ t n) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity hm t
    have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun n => measurable_energyDensity ((hmG n).sub hmS) t
    have hptw : ∀ (n : ℕ) (ω : Ω) (s : ℝ),
        (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro n ω s
      have habs : |Probability.stopped (gridStop τ t n) H ω s - Probability.stopped τ H ω s|
          ≤ |H ω s| := by
        rw [Probability.stopped, Probability.stopped]
        by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω
        · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
            h1 (le_trans hcon (le_gridStop τ t n ω))
          simp [h1, h2]
      have hle : (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using habs
      gcongr
    have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
      filter_upwards [MeasureTheory.ae_lt_top hbmeas (hq t ht).ne] with ω hfin
      have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
          Filter.Tendsto (fun n : ℕ =>
            (‖Probability.stopped (gridStop τ t n) H ω s
              - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0) := by
        have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by
          simp
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
          MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
        have hsne : s ≠ 0 := by simpa using hs0
        have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
        by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
          have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω :=
            le_trans hτs (le_gridStop τ t n ω)
          simp [Probability.stopped, h1, hτs]
        · rw [not_le] at hτs
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
            (eventually_gridStop_lt τ ht ω hs hsmem.2 hτs)
          refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
          have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω := not_le.mpr (hN n hn)
          have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
          simp [Probability.stopped, h1, h2]
      have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (F := fun n s => (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2)
        (f := fun _ : ℝ => (0 : ℝ≥0∞))
        (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
        (fun n => ((((hmG n).sub hmS).comp measurable_prodMk_left).nnNorm.coe_nnreal_ennreal
          ).pow_const 2)
        (fun n => Filter.Eventually.of_forall fun s => hptw n ω s) hfin.ne hlims
      simpa using hconv
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      (f := fun _ : Ω => (0 : ℝ≥0∞))
      (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      hFmeas
      (fun n => Filter.Eventually.of_forall fun ω =>
        lintegral_mono fun s => hptw n ω s)
      (hq t ht).ne hinner
    simpa using hconv
  -- the squeeze
  set D : Ω → ℝ≥0∞ := fun ω => A.indicator (fun ω =>
    (‖stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H) hmS hpS hqS t ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) ω with hDdef
  have hSImeas : ∀ {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
      (hpK : Probability.ProgressivelyMeasurable ℱ K)
      (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Measurable (stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t) := by
    intro K hmK hpK hqK
    exact ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ K hmK hpK hqK t).mono
      (ℱ.le t)).measurable
  have hDmeas : Measurable D := by
    refine Measurable.indicator ?_ hAmeas
    exact ((((hSImeas hmS hpS hqS).sub (hSImeas hm hp hq)).nnNorm).coe_nnreal_ennreal).pow_const 2
  have hDle : ∀ n : ℕ, n ≠ 0 → ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t n) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro n hn
    rw [← isometry_diff_stochasticIntegralBrownian W ℱ hℱ
      (Probability.stopped (gridStop τ t n) H) (Probability.stopped τ H)
      (hmG n) hmS (hpG n) hpS (hqG n) hqS ht]
    refine lintegral_mono_ae ?_
    filter_upwards [hagree n hn] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [hDdef]
      have hrev : ∀ x y : ℝ, ‖x - y‖₊ = ‖y - x‖₊ := by
        intro x y
        rw [← NNReal.coe_inj]
        simpa using norm_sub_rev x y
      rw [Set.indicator_of_mem hωA, hω hωA, hrev]
    · simp only [hDdef]
      rw [Set.indicator_of_notMem hωA]
      exact zero_le
  have hDzero : ∫⁻ ω, D ω ∂P = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hEtend ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hDle n hn.ne'
  have hDae := (MeasureTheory.lintegral_eq_zero_iff hDmeas).mp hDzero
  filter_upwards [hDae] with ω hω hωA
  have h0 : D ω = 0 := hω
  simp only [hDdef] at h0
  rw [Set.indicator_of_mem (show ω ∈ A from hωA)] at h0
  have hnn : (‖stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H) hmS hpS hqS t ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using h0
  have : ‖stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H) hmS hpS hqS t ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ = 0 := by
    exact_mod_cast hnn
  have hsub : stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H) hmS hpS hqS t ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω = 0 := by
    simpa using this
  linarith [hsub]

/-- **The Itô integral to a positive time sees the integrand only at positive times.** -/
theorem stochasticIntegralBrownian_congr_of_pos
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  classical
  have hle1 : ∀ (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ),
      |(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
    intro H ω s
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    simpa [indIoc] using indIoc_le_one (Ω := Ω) 0 t ω s
  have hmI : ∀ {H : Ω → ℝ → ℝ}, Measurable (Function.uncurry H) →
      Measurable (Function.uncurry fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hm => (measurable_uncurry_indIoc (Ω := Ω) 0 t).mul hm
  have hpI : ∀ {H : Ω → ℝ → ℝ}, Probability.ProgressivelyMeasurable ℱ H →
      Probability.ProgressivelyMeasurable ℱ (fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hp => (progressivelyMeasurable_indIoc₀ ℱ ht).mul hp
  have hqI : ∀ {H : Ω → ℝ → ℝ}, (∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) →
      ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun {H} hq => energy_lt_top_of_abs_le (hle1 H) hq
  have key : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : Probability.ProgressivelyMeasurable ℱ H)
      (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s)
          (hmI hm) (hpI hp) (hqI hq) t
        =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
    intro H hm hp hq
    have hsplit := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H hm hp hq
      (le_refl (0 : ℝ)) ht (hmI hm) (hpI hp) (hqI hq) ht
    have hz := stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H hm hp hq (le_refl (0 : ℝ))
    filter_upwards [hsplit, hz] with ω hω hω0
    rw [hω, min_self, min_eq_left ht.le]
    simpa using hω0
  have hfun : (fun (ω : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₁ ω s)
      = fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₂ ω s := by
    funext ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
    · rw [hagree ω s hs.1]
    · rw [Set.indicator_of_notMem hs, zero_mul, zero_mul]
  have hcongr := stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun
    (hmI hm₁) (hpI hp₁) (hqI hq₁) (hmI hm₂) (hpI hp₂) (hqI hq₂) t
  refine ((key H₁ hm₁ hp₁ hq₁).symm.trans ?_).trans (key H₂ hm₂ hp₂ hq₂)
  rw [hcongr]

/-- **Two integrands agreeing up to a stopping time have the same integral at a time that
stopping time has not reached.** -/
theorem stochasticIntegralBrownian_congr_of_le
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  classical
  have e1 := stochasticIntegralBrownian_stopped_eq_of_le τ W ℱ hℱ hτ hm₁ hp₁ hq₁ ht
  have e2 := stochasticIntegralBrownian_stopped_eq_of_le τ W ℱ hℱ hτ hm₂ hp₂ hq₂ ht
  have hstop : ∀ (ω : Ω) (s : ℝ), 0 < s →
      Probability.stopped τ H₁ ω s = Probability.stopped τ H₂ ω s := by
    intro ω s hs
    unfold LevyStochCalc.Probability.stopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [ite_eq_left hle, ite_eq_left hle, hagree ω s hs hle]
    · rw [ite_eq_right hle, ite_eq_right hle]
  have e3 := stochasticIntegralBrownian_congr_of_pos W ℱ hℱ
    (Probability.measurable_uncurry_stopped hτ hm₁)
    (Probability.ProgressivelyMeasurable.stopped hτ hp₁)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H₁ ω s) hq₁)
    (Probability.measurable_uncurry_stopped hτ hm₂)
    (Probability.ProgressivelyMeasurable.stopped hτ hp₂)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H₂ ω s) hq₂)
    hstop ht
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]

end Local

end LevyStochCalc.Brownian.Ito
