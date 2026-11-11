/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.Drift

/-!
# Hitting Time

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/--
`finiteHorizonRuntime P target t x` is the expected number of non-target steps
accumulated during the next `t` transitions, starting from `x`.

For a genuine Markov chain this is `E[min(T_target,t)]`.  Defining the finite
horizon quantity recursively keeps the first runtime layer entirely finite-state.
-/
def finiteHorizonRuntime {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] : ℕ → α → ℝ
  | 0, _ => 0
  | t + 1, x =>
      if x ∈ target then 0
      else 1 + expectedValueAfter P (finiteHorizonRuntime P target t) x

@[simp] theorem finiteHorizonRuntime_zero {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (x : α) :
    finiteHorizonRuntime P target 0 x = 0 := by
  rfl

@[simp] theorem finiteHorizonRuntime_succ_of_mem {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (t : ℕ) (x : α)
    (hx : x ∈ target) :
    finiteHorizonRuntime P target (t + 1) x = 0 := by
  simp [finiteHorizonRuntime, hx]

@[simp] theorem finiteHorizonRuntime_succ_of_not_mem {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (t : ℕ) (x : α)
    (hx : x ∉ target) :
    finiteHorizonRuntime P target (t + 1) x =
      1 + expectedValueAfter P (finiteHorizonRuntime P target t) x := by
  simp [finiteHorizonRuntime, hx]

/--
`finiteHorizonRuntime` is extensional in the target set, even when the two equal target
expressions carry different `DecidablePred` instances.  This is the finite-horizon
counterpart of `runtimeSup_congr_target`.
-/
theorem finiteHorizonRuntime_congr_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α)
    (s t : Set α)
    [ds : DecidablePred (fun x => x ∈ s)]
    [dt : DecidablePred (fun x => x ∈ t)]
    (hst : s = t) (horizon : ℕ) (x : α) :
    @finiteHorizonRuntime α _ P s ds horizon x =
      @finiteHorizonRuntime α _ P t dt horizon x := by
  subst t
  have hdec : ds = dt := Subsingleton.elim _ _
  cases hdec
  rfl

/-- Every finite-horizon runtime is nonnegative for a stochastic matrix. -/
theorem finiteHorizonRuntime_nonneg {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) :
    ∀ t x, 0 ≤ finiteHorizonRuntime P target t x := by
  intro t
  induction t with
  | zero =>
      intro x
      simp
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · simp [finiteHorizonRuntime, hx]
      · rw [finiteHorizonRuntime_succ_of_not_mem P target t x hx]
        exact add_nonneg zero_le_one
          (expectedValueAfter_nonneg P hP (finiteHorizonRuntime P target t) (ih) x)

/--
A Bellman supersolution dominates every finite-horizon expected runtime.
This is the finite-state certificate theorem used by the later fitness-level proof.
-/
theorem finiteHorizonRuntime_le_of_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : α → ℝ)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hR : IsRuntimeSuperSolution P target R) :
    ∀ t x, finiteHorizonRuntime P target t x ≤ R x := by
  intro t
  induction t with
  | zero =>
      intro x
      simpa using hRnonneg x
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · rw [finiteHorizonRuntime_succ_of_mem P target t x hx]
        rw [hR.1 x hx]
      · rw [finiteHorizonRuntime_succ_of_not_mem P target t x hx]
        have hEV :
            expectedValueAfter P (finiteHorizonRuntime P target t) x ≤
              expectedValueAfter P R x :=
          expectedValueAfter_mono P hP (finiteHorizonRuntime P target t) R (ih) x
        have hEV' :
            1 + expectedValueAfter P (finiteHorizonRuntime P target t) x ≤
              1 + expectedValueAfter P R x := by
          simpa [add_comm] using (add_le_add_left hEV 1)
        exact hEV'.trans (hR.2 x hx)

/-- Increasing the truncation horizon cannot decrease the expected truncated runtime. -/
theorem finiteHorizonRuntime_mono_succ {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) :
    ∀ t x, finiteHorizonRuntime P target t x ≤
      finiteHorizonRuntime P target (t + 1) x := by
  intro t
  induction t with
  | zero =>
      intro x
      simpa using (finiteHorizonRuntime_nonneg P target hP 1 x)
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · simp [finiteHorizonRuntime, hx]
      · rw [finiteHorizonRuntime_succ_of_not_mem P target t x hx]
        rw [finiteHorizonRuntime_succ_of_not_mem P target (t + 1) x hx]
        have hEV := expectedValueAfter_mono P hP
          (finiteHorizonRuntime P target t)
          (finiteHorizonRuntime P target (t + 1))
          (ih) x
        simpa [add_comm] using (add_le_add_left hEV 1)

/-- A pointwise bound that holds uniformly for every truncation horizon. -/
def HasUniformFiniteHorizonRuntimeBound {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (B : α → ℝ) : Prop :=
  ∀ t x, finiteHorizonRuntime P target t x ≤ B x

/-- Bellman certificates immediately yield uniform finite-horizon runtime bounds. -/
theorem hasUniformFiniteHorizonRuntimeBound_of_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : α → ℝ)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hR : IsRuntimeSuperSolution P target R) :
    HasUniformFiniteHorizonRuntimeBound P target R := by
  exact finiteHorizonRuntime_le_of_superSolution P target hP R hRnonneg hR

end ECRuntime
