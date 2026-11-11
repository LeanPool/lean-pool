/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.GeometricRuntime
public import LeanPool.ECRuntime.Transition

/-!
# Stage 26 fix 15: one-level survival bounds

The remaining stochastic fitness-level theorem is adaptive: after the process enters a
level, the state from which that level is entered depends on the complete earlier
trajectory.  Before constructing a multi-level coupling, isolate the local statement
that is uniform over all possible entry states.

`finiteLevelSurvival P level k x` is the finite-state recursion for the probability
mass of remaining in `level` through the next `k` transitions when the current state is
`x`.  It is zero when `x` is already outside the level.  The main theorem proves the
standard geometric estimate

  `finiteLevelSurvival P level k x <= (1 - p)^k`

from a uniform lower bound `p` on the one-step exit mass of every state in the level.
The following stage can identify this recursion with the corresponding strict tail of
the actual level-exit hitting time under `transitionTrajectoryMeasure`.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/--
Finite-horizon survival mass for a single level.  At horizon zero it is one exactly
when the current state is in the level.  At a positive horizon it propagates one step
through `P`, but only while the current state remains in the level.
-/
def finiteLevelSurvival {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)] : ℕ → α → ℝ
  | 0, x => if x ∈ level then 1 else 0
  | k + 1, x =>
      if x ∈ level then
        ∑ y, P x y * finiteLevelSurvival P level k y
      else
        0

@[simp] theorem finiteLevelSurvival_zero_of_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (x : α) (hx : x ∈ level) :
    finiteLevelSurvival P level 0 x = 1 := by
  simp [finiteLevelSurvival, hx]

theorem finiteLevelSurvival_zero_of_not_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (x : α) (hx : x ∉ level) :
    finiteLevelSurvival P level 0 x = 0 := by
  simp [finiteLevelSurvival, hx]

@[simp] theorem finiteLevelSurvival_succ_of_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (k : ℕ) (x : α) (hx : x ∈ level) :
    finiteLevelSurvival P level (k + 1) x =
      ∑ y, P x y * finiteLevelSurvival P level k y := by
  simp [finiteLevelSurvival, hx]

@[simp] theorem finiteLevelSurvival_succ_of_not_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (k : ℕ) (x : α) (hx : x ∉ level) :
    finiteLevelSurvival P level (k + 1) x = 0 := by
  simp [finiteLevelSurvival, hx]

/-- Survival is identically zero at every horizon when the current state is outside. -/
@[simp] theorem finiteLevelSurvival_eq_zero_of_not_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (k : ℕ) (x : α) (hx : x ∉ level) :
    finiteLevelSurvival P level k x = 0 := by
  cases k with
  | zero => exact finiteLevelSurvival_zero_of_not_mem P level x hx
  | succ k => exact finiteLevelSurvival_succ_of_not_mem P level k x hx

/-- A stochastic transition matrix gives nonnegative finite-level survival masses. -/
theorem finiteLevelSurvival_nonneg
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) :
    ∀ k x, 0 ≤ finiteLevelSurvival P level k x := by
  intro k
  induction k with
  | zero =>
      intro x
      by_cases hx : x ∈ level
      · simp [finiteLevelSurvival, hx]
      · simp [finiteLevelSurvival, hx]
  | succ k ih =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_succ_of_mem P level k x hx]
        exact Finset.sum_nonneg (fun y _ =>
          mul_nonneg (hP.1 x y) (ih y))
      · rw [finiteLevelSurvival_succ_of_not_mem P level k x hx]

/--
An event and its complement partition the total mass of any finite real-valued weight
function.  No nonnegativity assumption is needed for this algebraic identity.
-/
theorem finiteEventMass_add_compl
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) :
    finiteEventMass w event + finiteEventMass w (fun x => ¬ event x) =
      ∑ x, w x := by
  classical
  unfold finiteEventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases he : event x
  · have hmem : x ∈ ({y | event y} : Set α) := he
    have hnotmem : x ∉ ({y | ¬ event y} : Set α) := by
      intro hneg
      exact hneg he
    rw [Set.indicator_of_mem hmem w, Set.indicator_of_notMem hnotmem w]
    simp
  · have hnotmem : x ∉ ({y | event y} : Set α) := he
    have hmem : x ∈ ({y | ¬ event y} : Set α) := he
    rw [Set.indicator_of_notMem hnotmem w, Set.indicator_of_mem hmem w]
    simp

/--
If the one-step mass that remains in the level is at most `1-p` from every level
state, then survival for `k` transitions is at most `(1-p)^k`.
-/
theorem finiteLevelSurvival_le_geometric_of_stay_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) (p : unitInterval)
    (hstay : ∀ x, x ∈ level →
      finiteEventMass (P x) (fun y => y ∈ level) ≤ 1 - (p : ℝ)) :
    ∀ k x, x ∈ level →
      finiteLevelSurvival P level k x ≤ (1 - (p : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [finiteLevelSurvival, hx]
  | succ k ih =>
      intro x hx
      rw [finiteLevelSurvival_succ_of_mem P level k x hx]
      have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
      calc
        (∑ y, P x y * finiteLevelSurvival P level k y) ≤
            finiteEventMass (P x) (fun y => y ∈ level) *
              (1 - (p : ℝ)) ^ k := by
          unfold finiteEventMass
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro y _hy
          by_cases hylevel : y ∈ level
          · have hmem : y ∈ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_mem hmem (P x)]
            exact mul_le_mul_of_nonneg_left
              (ih y hylevel) (hP.1 x y)
          · have hnotmem : y ∉ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_notMem hnotmem (P x)]
            rw [finiteLevelSurvival_eq_zero_of_not_mem P level k y hylevel]
            simp
        _ ≤ (1 - (p : ℝ)) * (1 - (p : ℝ)) ^ k := by
          exact mul_le_mul_of_nonneg_right (hstay x hx) (pow_nonneg hq k)
        _ = (1 - (p : ℝ)) ^ (k + 1) := by
          rw [pow_succ]
          ring

/--
Uniform one-step exit probability is the natural EC hypothesis.  For a stochastic row,
exit mass at least `p` is equivalent to stay mass at most `1-p`; hence the same
geometric survival estimate follows.
-/
theorem finiteLevelSurvival_le_geometric_of_exit_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) (p : unitInterval)
    (hexit : ∀ x, x ∈ level →
      (p : ℝ) ≤ finiteEventMass (P x) (fun y => y ∉ level)) :
    ∀ k x, x ∈ level →
      finiteLevelSurvival P level k x ≤ (1 - (p : ℝ)) ^ k := by
  apply finiteLevelSurvival_le_geometric_of_stay_mass P level hP p
  intro x hx
  have hpartition :=
    finiteEventMass_add_compl (P x) (fun y => y ∈ level)
  have hrow : (∑ y, P x y) = 1 := hP.2 x
  rw [hrow] at hpartition
  have hprogress := hexit x hx
  linarith

/--
`ENNReal` packaging of the one-level estimate, in exactly the survival profile used by
the canonical geometric waiting-time law from `GeometricRuntime.lean`.
-/
theorem finiteLevelSurvival_ofReal_le_geometricSurvival_of_exit_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) (p : unitInterval)
    (hexit : ∀ x, x ∈ level →
      (p : ℝ) ≤ finiteEventMass (P x) (fun y => y ∉ level))
    (k : ℕ) (x : α) (hx : x ∈ level) :
    ENNReal.ofReal (finiteLevelSurvival P level k x) ≤
      geometricSurvival p k := by
  unfold geometricSurvival
  exact ENNReal.ofReal_le_ofReal
    (finiteLevelSurvival_le_geometric_of_exit_mass
      P level hP p hexit k x hx)

/-- Exact-survival version of the generic one-level recursion: if every state in a
level has the same one-step exit mass `q`, then survival for `k` transitions is exactly
`(1-q)^k`. -/
theorem finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) (q : ℝ)
    (hexit : ∀ x, x ∈ level →
      finiteEventMass (P x) (fun y => y ∉ level) = q) :
    ∀ k x, x ∈ level →
      finiteLevelSurvival P level k x = (1 - q) ^ k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [finiteLevelSurvival, hx]
  | succ k ih =>
      intro x hx
      rw [finiteLevelSurvival_succ_of_mem P level k x hx]
      have hpartition := finiteEventMass_add_compl (P x) (fun y => y ∈ level)
      have hrow : (∑ y, P x y) = 1 := hP.2 x
      have hstay :
          finiteEventMass (P x) (fun y => y ∈ level) = 1 - q := by
        rw [hrow, hexit x hx] at hpartition
        linarith
      calc
        (∑ y, P x y * finiteLevelSurvival P level k y) =
            ∑ y,
              ({z | z ∈ level} : Set α).indicator (P x) y * (1 - q) ^ k := by
          apply Finset.sum_congr rfl
          intro y _hy
          by_cases hylevel : y ∈ level
          · have hmem : y ∈ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_mem hmem, ih y hylevel]
          · have hnotmem : y ∉ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_notMem hnotmem]
            rw [finiteLevelSurvival_eq_zero_of_not_mem P level k y hylevel]
            simp
        _ = finiteEventMass (P x) (fun y => y ∈ level) * (1 - q) ^ k := by
          unfold finiteEventMass
          rw [Finset.sum_mul]
        _ = (1 - q) ^ (k + 1) := by
          rw [hstay, pow_succ]
          ring

end ECRuntime
