/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.TrajectoryHittingTime

/-!
# Stage 25: conventional first-hitting-time semantics

Stage 24 proves the main expectation bridge by defining the extended pathwise hitting
observable as the supremum of the finite truncated hitting costs.  That definition is
ideal for monotone convergence, but the conventional probabilistic statement uses the
least time at which the trajectory enters the target.

This file proves that the two representations coincide pointwise.  The supplied initial
state is treated as time zero, while coordinate `k+1` of the infinite trajectory is the
state at time `k+1`.  If a target state is ever reached, `Nat.find` selects the least
hitting index.  If no target state is ever reached, the conventional hitting time is
`⊤ : ENNReal`.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- Shift an infinite trajectory by one time step. -/
def transitionTrajectoryShift {α : Type*} (path : ℕ → α) : ℕ → α :=
  fun t => path (t + 1)

@[simp] theorem transitionTrajectoryShift_apply {α : Type*}
    (path : ℕ → α) (t : ℕ) :
    transitionTrajectoryShift path t = path (t + 1) := by
  rfl

/-- State of a trajectory at an absolute time, using the supplied deterministic initial
state at time zero.  Positive times are read from the Ionescu--Tulcea path coordinates. -/
def transitionTrajectoryState {α : Type*} (x : α) (path : ℕ → α) : ℕ → α
  | 0 => x
  | t + 1 => path (t + 1)

@[simp] theorem transitionTrajectoryState_zero {α : Type*}
    (x : α) (path : ℕ → α) :
    transitionTrajectoryState x path 0 = x := by
  rfl

@[simp] theorem transitionTrajectoryState_succ {α : Type*}
    (x : α) (path : ℕ → α) (t : ℕ) :
    transitionTrajectoryState x path (t + 1) = path (t + 1) := by
  rfl

/-- After removing the time-zero state, absolute time `t+1` becomes time `t` of the
shifted trajectory started from the first post-initial state. -/
theorem transitionTrajectoryState_shift {α : Type*}
    (x : α) (path : ℕ → α) (t : ℕ) :
    transitionTrajectoryState (path 1) (transitionTrajectoryShift path) t =
      transitionTrajectoryState x path (t + 1) := by
  cases t <;> simp [transitionTrajectoryState, transitionTrajectoryShift, Nat.add_assoc]

/-- The first `t` post-initial states of the shifted path are the tail of the first
`t+1` post-initial states of the original path. -/
@[simp] theorem Fin_tail_transitionTrajectoryTail {α : Type*}
    (t : ℕ) (path : ℕ → α) :
    Fin.tail (transitionTrajectoryTail (t + 1) path) =
      transitionTrajectoryTail t (transitionTrajectoryShift path) := by
  ext j
  rfl

/-- Real-valued version of the infinite-path truncated observable.  This is only a
proof helper; the public measure-theoretic observable remains `ENNReal`-valued. -/
def transitionTrajectoryTruncatedHittingCostReal {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (t : ℕ) (path : ℕ → α) : ℝ :=
  finiteTrajectoryTruncatedHittingCost target t x
    (transitionTrajectoryTail t path)

@[simp] theorem transitionTrajectoryTruncatedHittingCostReal_zero {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) :
    transitionTrajectoryTruncatedHittingCostReal target x 0 path = 0 := by
  rfl

/-- One-step recursion for the real-valued pathwise truncated cost. -/
theorem transitionTrajectoryTruncatedHittingCostReal_succ {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (t : ℕ) (path : ℕ → α) :
    transitionTrajectoryTruncatedHittingCostReal target x (t + 1) path =
      if x ∈ target then 0
      else 1 + transitionTrajectoryTruncatedHittingCostReal
        target (path 1) t (transitionTrajectoryShift path) := by
  unfold transitionTrajectoryTruncatedHittingCostReal
  rw [finiteTrajectoryTruncatedHittingCost]
  rw [Fin_tail_transitionTrajectoryTail]
  rfl

/-- If `k` is the first target-hitting index, the real horizon-`t` truncated cost is
exactly `min k t`. -/
theorem transitionTrajectoryTruncatedHittingCostReal_eq_min_of_first_hit
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)] :
    ∀ k (x : α) (path : ℕ → α),
      transitionTrajectoryState x path k ∈ target →
      (∀ j, j < k → transitionTrajectoryState x path j ∉ target) →
      ∀ t,
        transitionTrajectoryTruncatedHittingCostReal target x t path =
          (Nat.min k t : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro x path hhit _hbefore t
      have hx : x ∈ target := by
        simpa using hhit
      cases t with
      | zero =>
          simp
      | succ t =>
          rw [transitionTrajectoryTruncatedHittingCostReal_succ]
          simp [hx]
  | succ k ih =>
      intro x path hhit hbefore t
      have hx : x ∉ target := by
        have h0 := hbefore 0 (Nat.zero_lt_succ k)
        simpa using h0
      have hhitShift :
          transitionTrajectoryState (path 1) (transitionTrajectoryShift path) k ∈ target := by
        rw [transitionTrajectoryState_shift]
        exact hhit
      have hbeforeShift :
          ∀ j, j < k →
            transitionTrajectoryState (path 1) (transitionTrajectoryShift path) j ∉ target := by
        intro j hj
        rw [transitionTrajectoryState_shift]
        exact hbefore (j + 1) (by omega)
      cases t with
      | zero =>
          simp
      | succ t =>
          rw [transitionTrajectoryTruncatedHittingCostReal_succ]
          rw [ite_eq_right hx]
          rw [ih (path 1) (transitionTrajectoryShift path) hhitShift hbeforeShift t]
          have hmin : Nat.min (k + 1) (t + 1) = Nat.min k t + 1 := by
            simpa only [Nat.min_eq_min] using
              (Nat.add_min_add_right k t 1)
          rw [hmin]
          simp only [Nat.cast_add, Nat.cast_one]
          ac_rfl

/-- If the trajectory never reaches the target, every real truncated cost equals the
truncation horizon itself. -/
theorem transitionTrajectoryTruncatedHittingCostReal_eq_horizon_of_never_hits
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)] :
    ∀ t (x : α) (path : ℕ → α),
      (∀ k, transitionTrajectoryState x path k ∉ target) →
      transitionTrajectoryTruncatedHittingCostReal target x t path = (t : ℝ) := by
  intro t
  induction t with
  | zero =>
      intro x path _hnever
      simp
  | succ t ih =>
      intro x path hnever
      have hx : x ∉ target := by
        simpa using hnever 0
      have hneverShift :
          ∀ k,
            transitionTrajectoryState (path 1) (transitionTrajectoryShift path) k ∉ target := by
        intro k
        rw [transitionTrajectoryState_shift]
        exact hnever (k + 1)
      rw [transitionTrajectoryTruncatedHittingCostReal_succ]
      rw [ite_eq_right hx]
      rw [ih (path 1) (transitionTrajectoryShift path) hneverShift]
      simp only [Nat.cast_add, Nat.cast_one]
      ac_rfl

/-- `ENNReal` form of the finite-horizon `min(k,t)` characterization. -/
theorem transitionTrajectoryTruncatedHittingCost_eq_min_of_first_hit
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) (k t : ℕ)
    (hhit : transitionTrajectoryState x path k ∈ target)
    (hbefore : ∀ j, j < k → transitionTrajectoryState x path j ∉ target) :
    transitionTrajectoryTruncatedHittingCost target x t path =
      ENNReal.ofReal (Nat.min k t : ℝ) := by
  unfold transitionTrajectoryTruncatedHittingCost
  unfold finiteTrajectoryTruncatedHittingCostENNReal
  change ENNReal.ofReal
      (transitionTrajectoryTruncatedHittingCostReal target x t path) = _
  rw [transitionTrajectoryTruncatedHittingCostReal_eq_min_of_first_hit
    target k x path hhit hbefore t]

/-- `ENNReal` form of the fact that a never-hitting trajectory accumulates one unit at
every finite horizon. -/
theorem transitionTrajectoryTruncatedHittingCost_eq_horizon_of_never_hits
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α)
    (hnever : ∀ k, transitionTrajectoryState x path k ∉ target)
    (t : ℕ) :
    transitionTrajectoryTruncatedHittingCost target x t path =
      ENNReal.ofReal (t : ℝ) := by
  unfold transitionTrajectoryTruncatedHittingCost
  unfold finiteTrajectoryTruncatedHittingCostENNReal
  change ENNReal.ofReal
      (transitionTrajectoryTruncatedHittingCostReal target x t path) = _
  rw [transitionTrajectoryTruncatedHittingCostReal_eq_horizon_of_never_hits
    target t x path hnever]

/-- If `k` is the first target-hitting index, the Stage-24 supremum hitting time is
exactly the embedded natural number `k`. -/
theorem transitionTrajectoryHittingTime_eq_ofReal_natCast_of_first_hit
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) (k : ℕ)
    (hhit : transitionTrajectoryState x path k ∈ target)
    (hbefore : ∀ j, j < k → transitionTrajectoryState x path j ∉ target) :
    transitionTrajectoryHittingTime target x path = ENNReal.ofReal (k : ℝ) := by
  unfold transitionTrajectoryHittingTime
  apply le_antisymm
  · refine iSup_le ?_
    intro t
    rw [transitionTrajectoryTruncatedHittingCost_eq_min_of_first_hit
      target x path k t hhit hbefore]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast Nat.min_le_left k t
  · calc
      ENNReal.ofReal (k : ℝ) =
          transitionTrajectoryTruncatedHittingCost target x k path := by
            symm
            rw [transitionTrajectoryTruncatedHittingCost_eq_min_of_first_hit
              target x path k k hhit hbefore]
            simp
      _ ≤ ⨆ t : ℕ, transitionTrajectoryTruncatedHittingCost target x t path :=
        le_iSup (fun t : ℕ => transitionTrajectoryTruncatedHittingCost target x t path) k

/-- A trajectory that never reaches the target has infinite Stage-24 hitting time. -/
theorem transitionTrajectoryHittingTime_eq_top_of_never_hits
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α)
    (hnever : ∀ k, transitionTrajectoryState x path k ∉ target) :
    transitionTrajectoryHittingTime target x path = ⊤ := by
  unfold transitionTrajectoryHittingTime
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (lt_top_iff_ne_top.mp hb)
  refine ⟨n, ?_⟩
  rw [transitionTrajectoryTruncatedHittingCost_eq_horizon_of_never_hits
    target x path hnever n]
  simpa using hn

/-- Conventional extended first-hitting time: the least natural index at which the
trajectory enters the target, or `⊤` when no such index exists. -/
noncomputable def transitionTrajectoryFirstHittingTime {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) : ENNReal := by
  classical
  exact if h : ∃ k, transitionTrajectoryState x path k ∈ target then
    ENNReal.ofReal (Nat.find h : ℝ)
  else
    ⊤

/-- The conventional least-index first-hitting time is pointwise equal to the Stage-24
supremum of finite truncations. -/
theorem transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime
    {α : Type*} (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) :
    transitionTrajectoryFirstHittingTime target x path =
      transitionTrajectoryHittingTime target x path := by
  classical
  unfold transitionTrajectoryFirstHittingTime
  by_cases h : ∃ k, transitionTrajectoryState x path k ∈ target
  · rw [dite_eq_left h]
    have hhit : transitionTrajectoryState x path (Nat.find h) ∈ target :=
      Nat.find_spec h
    have hbefore :
        ∀ j, j < Nat.find h → transitionTrajectoryState x path j ∉ target := by
      intro j hj
      exact Nat.find_min h hj
    exact (transitionTrajectoryHittingTime_eq_ofReal_natCast_of_first_hit
      target x path (Nat.find h) hhit hbefore).symm
  · rw [dite_eq_right h]
    have hnever : ∀ k, transitionTrajectoryState x path k ∉ target := by
      intro k hk
      exact h ⟨k, hk⟩
    exact (transitionTrajectoryHittingTime_eq_top_of_never_hits
      target x path hnever).symm

/-- The conventional first-hitting-time observable is measurable because it is
pointwise equal to the measurable Stage-24 supremum observable. -/
@[fun_prop] theorem measurable_transitionTrajectoryFirstHittingTime
    {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) :
    Measurable (transitionTrajectoryFirstHittingTime target x) := by
  have hfun :
      transitionTrajectoryFirstHittingTime target x =
        transitionTrajectoryHittingTime target x := by
    funext path
    exact transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime
      target x path
  rw [hfun]
  exact measurable_transitionTrajectoryHittingTime target x

/-- Conventional formulation of the main semantic theorem: `runtimeSup` is the
expectation of the least target-hitting index, with value `⊤` on never-hitting paths. -/
theorem runtimeSup_eq_lintegral_transitionTrajectoryFirstHittingTime
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (x : α) :
    runtimeSup P target x =
      ∫⁻ path : ℕ → α,
        transitionTrajectoryFirstHittingTime target x path
      ∂transitionTrajectoryMeasure P hP x := by
  have hfun :
      transitionTrajectoryFirstHittingTime target x =
        transitionTrajectoryHittingTime target x := by
    funext path
    exact transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime
      target x path
  rw [hfun]
  exact runtimeSup_eq_lintegral_transitionTrajectoryHittingTime P target hP x

/-- Reverse orientation of the conventional first-hitting-time expectation identity. -/
theorem transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (x : α) :
    (∫⁻ path : ℕ → α,
        transitionTrajectoryFirstHittingTime target x path
      ∂transitionTrajectoryMeasure P hP x) =
      runtimeSup P target x := by
  exact (runtimeSup_eq_lintegral_transitionTrajectoryFirstHittingTime
    P target hP x).symm

end ECRuntime
