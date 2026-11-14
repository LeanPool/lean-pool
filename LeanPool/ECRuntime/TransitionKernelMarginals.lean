/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteTrajectory
public import LeanPool.ECRuntime.TransitionKernel

/-!
# Stage 18: finite marginals of the infinite trajectory law

Stage 17 constructs Mathlib's Ionescu--Tulcea trajectory measure from a finite stochastic
transition matrix.  Stages 15--16 independently construct explicit finite trajectory weights.
This file puts both finite-horizon objects into measure-theoretic form without yet proving that
they coincide.

There are two main ingredients.

* `transitionPrefixMeasure` is the `partialTraj` marginal on histories through time `t`.
  Mathlib's `traj_map_frestrictLe_apply` identifies it exactly with the restriction of the
  infinite trajectory measure.
* `finiteTrajectoryPMF` packages the explicit Stage-15 real path weights as an honest PMF on
  `FiniteTrajectory α t`; its singleton probabilities are exactly `ENNReal.ofReal` of the
  recursive path weights.

The next bridge can therefore be stated as an equality of two finite probability measures after
removing the deterministic time-zero coordinate from `transitionPrefixMeasure`.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- The explicit Stage-15 path weights packaged as a finite probability mass function. -/
noncomputable def finiteTrajectoryPMF {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) (x : α) :
    PMF (FiniteTrajectory α t) :=
  PMF.ofFintype
    (fun path => ENNReal.ofReal (finiteTrajectoryWeight P t x path))
    (by
      have hnonneg :
          ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory α t)),
            0 ≤ finiteTrajectoryWeight P t x path := by
        intro path _hpath
        exact finiteTrajectoryWeight_nonneg P hP t x path
      calc
        (∑ path : FiniteTrajectory α t,
            ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
            ENNReal.ofReal
              (∑ path : FiniteTrajectory α t,
                finiteTrajectoryWeight P t x path) := by
          symm
          exact ENNReal.ofReal_sum_of_nonneg hnonneg
        _ = 1 := by
          rw [finiteTrajectoryWeight_sum P hP t x]
          simp)

@[simp] theorem finiteTrajectoryPMF_apply {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (path : FiniteTrajectory α t) :
    finiteTrajectoryPMF P hP t x path =
      ENNReal.ofReal (finiteTrajectoryWeight P t x path) := by
  rfl

/-- Measure associated with the explicit finite trajectory PMF. -/
noncomputable def finiteTrajectoryMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) (x : α) :
    Measure (FiniteTrajectory α t) :=
  (finiteTrajectoryPMF P hP t x).toMeasure

instance instIsProbabilityMeasureFiniteTrajectoryMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) (x : α) :
    IsProbabilityMeasure (finiteTrajectoryMeasure P hP t x) := by
  unfold finiteTrajectoryMeasure
  infer_instance

/-- Point masses of the explicit finite trajectory measure recover the Stage-15 path weights. -/
@[simp] theorem finiteTrajectoryMeasure_singleton {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (path : FiniteTrajectory α t) :
    finiteTrajectoryMeasure P hP t x {path} =
      ENNReal.ofReal (finiteTrajectoryWeight P t x path) := by
  rw [finiteTrajectoryMeasure]
  rw [PMF.toMeasure_apply_singleton _ path (measurableSet_singleton path)]
  exact finiteTrajectoryPMF_apply P hP t x path

/-- Mathlib's finite history marginal through time `t`, started from the deterministic state `x`.
The history includes time zero, so its state space is `Finset.Iic t -> α`. -/
noncomputable def transitionPrefixMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    Measure ((i : Finset.Iic t) → α) :=
  Kernel.partialTraj
      (X := fun _ : ℕ => α)
      (fun n => transitionHistoryKernel P hP n) 0 t
      (Function.const (Finset.Iic (0 : ℕ)) x)

instance instIsProbabilityMeasureTransitionPrefixMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    IsProbabilityMeasure (transitionPrefixMeasure P hP x t) := by
  unfold transitionPrefixMeasure
  infer_instance

/-- Arbitrary finite restrictions of the Stage-17 infinite trajectory measure are exactly
Mathlib's corresponding `partialTraj` marginals. -/
theorem transitionTrajectoryMeasure_map_frestrictLe {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    (transitionTrajectoryMeasure P hP x).map (Preorder.frestrictLe t) =
      transitionPrefixMeasure P hP x t := by
  unfold transitionTrajectoryMeasure transitionTrajectoryKernel transitionPrefixMeasure
  simpa using
    (Kernel.traj_map_frestrictLe_apply
      (X := fun _ : ℕ => α)
      (κ := fun n => transitionHistoryKernel P hP n)
      0 t (Function.const (Finset.Iic (0 : ℕ)) x))

/-- The finite prefix measures themselves form a projective family under restriction. -/
theorem transitionPrefixMeasure_map_frestrictLe₂ {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α)
    {s t : ℕ} (hst : s ≤ t) :
    (transitionPrefixMeasure P hP x t).map
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) hst) =
      transitionPrefixMeasure P hP x s := by
  unfold transitionPrefixMeasure
  simpa using
    (Kernel.partialTraj_map_frestrictLe₂_apply
      (X := fun _ : ℕ => α)
      (κ := fun n => transitionHistoryKernel P hP n)
      (a := 0) (b := s) (c := t)
      (Function.const (Finset.Iic (0 : ℕ)) x) hst)

/-- Drop the deterministic time-zero coordinate from a finite Mathlib history. -/
def transitionPrefixTail {α : Type*} (t : ℕ)
    (hist : (i : Finset.Iic t) → α) : FiniteTrajectory α t :=
  fun j => hist ⟨j.val + 1, Finset.mem_Iic.mpr (by
    have hj := j.isLt
    omega)⟩

@[fun_prop] theorem measurable_transitionPrefixTail {α : Type*}
    [MeasurableSpace α] (t : ℕ) : Measurable (transitionPrefixTail (α := α) t) := by
  unfold transitionPrefixTail
  fun_prop

/-- The `partialTraj` prefix marginal, pushed forward to the Stage-15 convention that stores only
states after the externally supplied initial state.  Stage 19's central target is to prove this
measure equal to `finiteTrajectoryMeasure`. -/
noncomputable def transitionFiniteTrajectoryMarginal {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    Measure (FiniteTrajectory α t) :=
  (transitionPrefixMeasure P hP x t).map (transitionPrefixTail t)

instance instIsProbabilityMeasureTransitionFiniteTrajectoryMarginal
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    IsProbabilityMeasure (transitionFiniteTrajectoryMarginal P hP x t) := by
  unfold transitionFiniteTrajectoryMarginal
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_transitionPrefixTail (α := α) t).aemeasurable).mpr inferInstance

end ECRuntime
