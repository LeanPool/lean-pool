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
public import Mathlib.Probability.Process.Stopping

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

@[expose] public section

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A process cut off at a stopping time. -/
noncomputable def stopped (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  if (s : WithTop ℝ) ≤ τ ω then H ω s else 0

theorem abs_stopped_le (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    |stopped τ H ω s| ≤ |H ω s| := by
  rw [stopped]
  split_ifs
  · exact le_rfl
  · simp

/-- The region cut out by a stopping time before a time `t`. -/
def stoppedRegion (τ : Ω → WithTop ℝ) (t : ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | p.2 ≤ t ∧ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}

theorem mem_stoppedRegion {τ : Ω → WithTop ℝ} {t : ℝ} {p : Ω × ℝ} :
    p ∈ stoppedRegion τ t ↔ p.2 ≤ t ∧ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := Iff.rfl

/-- The cut region before `t` is measurable for the σ-algebra at `t`. -/
theorem measurableSet_stoppedRegion {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) :
    MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] (stoppedRegion τ t) := by
  let : MeasurableSpace Ω := ℱ t
  set U : Set (Ω × ℝ) := ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)}
    ×ˢ (Set.Ioi (q : ℝ) ∩ Set.Iic t) with hUdef
  have hU : MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
    · exact (ℱ.mono (min_le_right (q : ℝ) t)) _ (hτ (min (q : ℝ) t))
    · exact measurableSet_Ioi.inter measurableSet_Iic
  have heq : stoppedRegion τ t = (Set.univ ×ˢ Set.Iic t) \ U := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Set.mem_univ _, h1⟩, ?_⟩
      rw [hUdef]
      rintro hmem
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hq1, hq2⟩ := hq
      have hle : ((p.2 : ℝ) : WithTop ℝ) ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ) := h2.trans hq1
      have hle' : p.2 ≤ min (q : ℝ) t := by exact_mod_cast hle
      exact absurd (hle'.trans (min_le_left _ _)) (not_le.mpr hq2.1)
    · rintro ⟨⟨-, h1⟩, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hcon
        exact absurd hcon (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hcon
      have hrlt : r < p.2 := by exact_mod_cast hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine h2 ?_
      rw [hUdef]
      refine Set.mem_iUnion.mpr ⟨q, ?_, ⟨hq2, h1⟩⟩
      change τ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)
      rw [← hr]
      have : r ≤ min (q : ℝ) t := le_min hq1.le (hq1.le.trans (hq2.le.trans h1))
      exact_mod_cast this
  rw [heq]
  exact (MeasurableSet.univ.prod measurableSet_Iic).diff hU

/-- **Cutting off at a stopping time preserves progressive measurability.** -/
theorem ProgressivelyMeasurable.stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ (LevyStochCalc.Probability.stopped τ H) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (LevyStochCalc.Probability.stopped τ H p.1) p.2)
      = Set.indicator (stoppedRegion τ t)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h1 : p ∈ stoppedRegion τ t
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ stoppedRegion τ t from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        LevyStochCalc.Probability.stopped, ite_eq_left h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2 ∈ Set.Iic t
      · have h3 : ¬ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, LevyStochCalc.Probability.stopped, ite_eq_right h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hH t).indicator (measurableSet_stoppedRegion hτ t)

/-- The whole region cut out by a stopping time. -/
def stoppedSet (τ : Ω → WithTop ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}

theorem measurableSet_stoppedSet {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) : MeasurableSet (stoppedSet τ) := by
  have hcompl : (stoppedSet τ)ᶜ
      = ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((q : ℝ) : WithTop ℝ)} ×ˢ Set.Ioi (q : ℝ) := by
    ext p
    simp only [stoppedSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_iUnion,
      Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro hlt
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hlt
        exact absurd hlt (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hlt
      have hrlt : r < p.2 := by exact_mod_cast hlt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine ⟨q, ?_, hq2⟩
      rw [← hr]
      exact_mod_cast hq1.le
    · rintro ⟨q, hq1, hq2⟩
      calc τ p.1 ≤ ((q : ℝ) : WithTop ℝ) := hq1
        _ < ((p.2 : ℝ) : WithTop ℝ) := by exact_mod_cast hq2
  have hmc : MeasurableSet (stoppedSet τ)ᶜ := by
    rw [hcompl]
    exact MeasurableSet.iUnion fun q =>
      ((ℱ.le (q : ℝ)) _ (hτ (q : ℝ))).prod measurableSet_Ioi
  simpa using hmc.compl

/-- **Cutting off at a stopping time preserves joint measurability.** -/
theorem measurable_uncurry_stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (LevyStochCalc.Probability.stopped τ H)) := by
  have hfun : Function.uncurry (LevyStochCalc.Probability.stopped τ H)
      = Set.indicator (stoppedSet τ) (Function.uncurry H) := by
    funext p
    by_cases hp : p ∈ stoppedSet τ
    · rw [Set.indicator_of_mem hp]
      exact ite_eq_left hp
    · rw [Set.indicator_of_notMem hp]
      exact ite_eq_right hp
  rw [hfun]
  exact hH.indicator (measurableSet_stoppedSet hτ)

end LevyStochCalc.Probability
