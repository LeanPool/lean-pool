/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.HittingTime
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.Positivity.Finset

/-!
# Fitness Level

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- The real-valued harmonic number, convenient for runtime certificates. -/
noncomputable def harmonicReal (n : ℕ) : ℝ :=
  (harmonic n : ℝ)

@[simp] theorem harmonicReal_zero : harmonicReal 0 = 0 := by
  simp [harmonicReal]

/-- Harmonic numbers are nonnegative. -/
theorem harmonicReal_nonneg (n : ℕ) : 0 ≤ harmonicReal n := by
  have hq : (0 : ℚ) ≤ harmonic n := by
    rw [harmonic_eq_sum_Icc]
    exact Finset.sum_nonneg (fun i hi => by positivity)
  change (0 : ℝ) ≤ (harmonic n : ℝ)
  exact_mod_cast hq

/-- Harmonic numbers are monotone in their natural-number index. -/
theorem harmonicReal_mono {a b : ℕ} (hab : a ≤ b) :
    harmonicReal a ≤ harmonicReal b := by
  have hq : harmonic a ≤ harmonic b := by
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      exact ⟨hi.1, hi.2.trans hab⟩
    · intro i hi hia
      positivity
  change (harmonic a : ℝ) ≤ (harmonic b : ℝ)
  exact_mod_cast hq

/-- Dropping from level `k` to any lower level saves at least `1/k` harmonic units. -/
theorem harmonicReal_add_inv_le_of_lt {j k : ℕ} (hjk : j < k) :
    harmonicReal j + ((k : ℝ)⁻¹) ≤ harmonicReal k := by
  cases k with
  | zero => omega
  | succ m =>
      have hjm : j ≤ m := by omega
      calc
        harmonicReal j + (((m + 1 : ℕ) : ℝ)⁻¹) ≤
            harmonicReal m + (((m + 1 : ℕ) : ℝ)⁻¹) := by
          linarith [harmonicReal_mono hjm]
        _ = harmonicReal (m + 1) := by
          simp [harmonicReal, harmonic_succ]

/-- The classical harmonic expression appearing in the OneMax fitness-level bound. -/
def harmonicRuntimeBound (c : ℝ) (n : ℕ) : ℝ :=
  c * (n : ℝ) * (harmonic n : ℝ)

/-- Convert a harmonic runtime estimate into the usual logarithmic estimate. -/
theorem harmonicRuntimeBound_le_log (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    harmonicRuntimeBound c n ≤ c * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  unfold harmonicRuntimeBound
  have hcn : 0 ≤ c * (n : ℝ) :=
    mul_nonneg hc (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hcn

/-- A wrapper useful for deterministic post-processing of a harmonic runtime estimate. -/
theorem runtime_le_log_of_le_harmonic
    (runtime c : ℝ) (hc : 0 ≤ c) (n : ℕ)
    (hRuntime : runtime ≤ harmonicRuntimeBound c n) :
    runtime ≤ c * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  exact hRuntime.trans (harmonicRuntimeBound_le_log c hc n)

/-- Target set encoded by the zero level of a natural-valued potential. -/
def potentialTarget {α : Type*} (V : α → ℕ) : Set α :=
  {x | V x = 0}

/-- Membership in a natural-valued zero-potential target is decidable. -/
instance instDecidablePredPotentialTarget {α : Type*} (V : α → ℕ) :
    DecidablePred (fun x => x ∈ potentialTarget V) := by
  intro x
  change Decidable (V x = 0)
  infer_instance

/-- Harmonic runtime certificate associated with a per-bad-bit progress rate `rate`. -/
noncomputable def harmonicLevelRuntime {α : Type*}
    (rate : ℝ) (V : α → ℕ) (x : α) : ℝ :=
  rate⁻¹ * harmonicReal (V x)

/-- The harmonic runtime certificate is nonnegative for a positive rate. -/
theorem harmonicLevelRuntime_nonneg {α : Type*}
    (rate : ℝ) (V : α → ℕ) (hrate : 0 < rate) (x : α) :
    0 ≤ harmonicLevelRuntime rate V x := by
  unfold harmonicLevelRuntime
  exact mul_nonneg (inv_nonneg.mpr hrate.le) (harmonicReal_nonneg (V x))

/--
A finite weighted expectation bound used in fitness-level arguments.
If every outcome has value at most `A`, and event outcomes save an additional `d`,
then the expectation plus `d` times the event mass is at most `A`.
-/
theorem weightedExpectation_add_eventMass_mul_le
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (event : Ω → Prop)
    (F : Ω → ℝ) (A d : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (hAll : ∀ ω, F ω ≤ A)
    (hEvent : ∀ ω, event ω → F ω + d ≤ A) :
    (∑ ω, w ω * F ω) + d * finiteEventMass w event ≤ A := by
  classical
  unfold finiteEventMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ ω, (w ω * F ω +
        d * (({x | event x} : Set Ω).indicator w ω))) ≤
        ∑ ω, w ω * A := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : event ω
      · have hmem : ω ∈ ({x | event x} : Set Ω) := he
        rw [Set.indicator_of_mem hmem w]
        calc
          w ω * F ω + d * w ω = w ω * (F ω + d) := by ring
          _ ≤ w ω * A := mul_le_mul_of_nonneg_left (hEvent ω he) (hw ω)
      · have hnotmem : ω ∉ ({x | event x} : Set Ω) := he
        rw [Set.indicator_of_notMem hnotmem w]
        simp only [mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left (hAll ω) (hw ω)
    _ = A := by
      calc
        (∑ ω, w ω * A) = (∑ ω, w ω) * A := by
          simpa using (Finset.sum_mul Finset.univ w A).symm
        _ = A := by rw [hsum, one_mul]

/--
Finite fitness-level theorem for the common situation where a level-`k` state has
progress probability at least `k * rate`, and the potential never increases.
The harmonic certificate `H_k / rate` is then a Bellman supersolution.
-/
theorem harmonicFitnessLevel_superSolution
    {α Ω : Type*} [Fintype α] [Fintype Ω] [DecidableEq α]
    (w : α → Ω → ℝ) (step : α → Ω → α)
    (V : α → ℕ) (rate : ℝ)
    (hrate : 0 < rate)
    (hw : ∀ x ω, 0 ≤ w x ω)
    (hsum : ∀ x, ∑ ω, w x ω = 1)
    (hmono : ∀ x ω, V (step x ω) ≤ V x)
    (hprogress : ∀ x, 0 < V x →
      (V x : ℝ) * rate ≤
        finiteEventMass (w x) (fun ω => V (step x ω) < V x)) :
    IsRuntimeSuperSolution
      (finiteRandomTransition w step)
      (potentialTarget V)
      (harmonicLevelRuntime rate V) := by
  constructor
  · intro x hx
    have hx0 : V x = 0 := by simpa [potentialTarget] using hx
    simp [harmonicLevelRuntime, hx0]
  · intro x hx
    have hx0 : V x ≠ 0 := by
      simpa [potentialTarget] using hx
    have hkpos : 0 < V x := Nat.pos_of_ne_zero hx0
    have hkrealpos : 0 < (V x : ℝ) := by exact_mod_cast hkpos
    let d : ℝ := rate⁻¹ * ((V x : ℝ)⁻¹)
    have hdnonneg : 0 ≤ d := by
      dsimp [d]
      exact mul_nonneg (inv_nonneg.mpr hrate.le) (inv_nonneg.mpr hkrealpos.le)
    have hAll : ∀ ω,
        harmonicLevelRuntime rate V (step x ω) ≤
          harmonicLevelRuntime rate V x := by
      intro ω
      unfold harmonicLevelRuntime
      exact mul_le_mul_of_nonneg_left
        (harmonicReal_mono (hmono x ω)) (inv_nonneg.mpr hrate.le)
    have hEvent : ∀ ω,
        V (step x ω) < V x →
          harmonicLevelRuntime rate V (step x ω) + d ≤
            harmonicLevelRuntime rate V x := by
      intro ω hω
      have hh := harmonicReal_add_inv_le_of_lt hω
      have hscaled := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hrate.le)
      dsimp [d]
      unfold harmonicLevelRuntime
      calc
        rate⁻¹ * harmonicReal (V (step x ω)) + rate⁻¹ * (V x : ℝ)⁻¹ =
            rate⁻¹ * (harmonicReal (V (step x ω)) + (V x : ℝ)⁻¹) := by ring
        _ ≤ rate⁻¹ * harmonicReal (V x) := hscaled
    have hweighted := weightedExpectation_add_eventMass_mul_le
      (w x) (fun ω => V (step x ω) < V x)
      (fun ω => harmonicLevelRuntime rate V (step x ω))
      (harmonicLevelRuntime rate V x) d
      (hw x) (hsum x) hAll hEvent
    have hdq : d * ((V x : ℝ) * rate) = 1 := by
      dsimp [d]
      calc
        rate⁻¹ * (V x : ℝ)⁻¹ * ((V x : ℝ) * rate) =
            (rate⁻¹ * rate) * ((V x : ℝ)⁻¹ * (V x : ℝ)) := by ring
        _ = 1 := by
          simp [ne_of_gt hrate, ne_of_gt hkrealpos]
    have hmass : 1 ≤ d *
        finiteEventMass (w x) (fun ω => V (step x ω) < V x) := by
      calc
        1 = d * ((V x : ℝ) * rate) := hdq.symm
        _ ≤ d * finiteEventMass (w x) (fun ω => V (step x ω) < V x) :=
          mul_le_mul_of_nonneg_left (hprogress x hkpos) hdnonneg
    have hEV :
        expectedValueAfter (finiteRandomTransition w step)
          (harmonicLevelRuntime rate V) x =
        ∑ ω, w x ω * harmonicLevelRuntime rate V (step x ω) := by
      unfold expectedValueAfter finiteRandomTransition
      exact pushforwardWeight_expectation (w x) (step x) (harmonicLevelRuntime rate V)
    rw [hEV]
    calc
      1 + ∑ ω, w x ω * harmonicLevelRuntime rate V (step x ω) ≤
          d * finiteEventMass (w x) (fun ω => V (step x ω) < V x) +
            ∑ ω, w x ω * harmonicLevelRuntime rate V (step x ω) := by
        linarith [hmass]
      _ = (∑ ω, w x ω * harmonicLevelRuntime rate V (step x ω)) +
            d * finiteEventMass (w x) (fun ω => V (step x ω) < V x) := by ring
      _ ≤ harmonicLevelRuntime rate V x := hweighted

/-- The fitness-level certificate bounds every truncated expected hitting time. -/
theorem harmonicFitnessLevel_finiteHorizonBound
    {α Ω : Type*} [Fintype α] [Fintype Ω] [DecidableEq α]
    (w : α → Ω → ℝ) (step : α → Ω → α)
    (V : α → ℕ) (rate : ℝ)
    (hrate : 0 < rate)
    (hw : ∀ x ω, 0 ≤ w x ω)
    (hsum : ∀ x, ∑ ω, w x ω = 1)
    (hmono : ∀ x ω, V (step x ω) ≤ V x)
    (hprogress : ∀ x, 0 < V x →
      (V x : ℝ) * rate ≤
        finiteEventMass (w x) (fun ω => V (step x ω) < V x)) :
    HasUniformFiniteHorizonRuntimeBound
      (finiteRandomTransition w step)
      (potentialTarget V)
      (harmonicLevelRuntime rate V) := by
  apply hasUniformFiniteHorizonRuntimeBound_of_superSolution
  · exact finiteRandomTransition_stochastic w step hw hsum
  · exact harmonicLevelRuntime_nonneg rate V hrate
  · exact harmonicFitnessLevel_superSolution
      w step V rate hrate hw hsum hmono hprogress

end ECRuntime
