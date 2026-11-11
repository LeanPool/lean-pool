/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.TransitionKernelMarginals
public import Mathlib.Probability.Kernel.Deterministic

/-!
# Stage 20: one-step dynamics of finite Ionescu--Tulcea marginals

Stage 19 puts the explicit Stage-15 finite path law and the tail projection of
Mathlib's Ionescu--Tulcea law into the same projective system.  Projective
consistency alone is not enough to identify the two laws: we also need the
one-step transition rule.

This file isolates that dynamic ingredient at the level where Mathlib's
`partialTraj` API is strongest.  A history through time `t + 1` is split into
its prefix through time `t` and its final state.  Under this split, the
one-step `partialTraj` kernel is exactly the product of the identity kernel on
the prefix and the repository's history-dependent transition kernel.  The
corresponding prefix/next-state measure therefore has the expected singleton
mass formula.

The next stage can transport this verified joint formula through the
`transitionPrefixTail` convention and compare it to the explicit `Fin.snoc`
recursion of the Stage-15 trajectory weights.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- Final coordinate of a complete history through time `t + 1`. -/
def transitionHistoryNext {α : Type*} (t : ℕ)
    (hist : (i : Finset.Iic (t + 1)) → α) : α :=
  hist ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩

/-- The unique state stored by a function on `Ioc t (t + 1)`. -/
def transitionIocNext {α : Type*} (t : ℕ)
    (tail : (i : Finset.Ioc t (t + 1)) → α) : α :=
  tail ⟨t + 1, Finset.right_mem_Ioc.mpr t.lt_succ_self⟩

/-- Split a history through time `t + 1` into its history through time `t`
and its final state. -/
def transitionHistorySplit {α : Type*} (t : ℕ)
    (hist : (i : Finset.Iic (t + 1)) → α) :
    ((i : Finset.Iic t) → α) × α :=
  (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist,
    transitionHistoryNext t hist)

@[fun_prop] theorem measurable_transitionHistorySplit {α : Type*}
    [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α] (t : ℕ) :
    Measurable (transitionHistorySplit (α := α) t) := by
  exact measurable_of_finite _

/-- Splitting after Mathlib's one-step history gluing recovers the original
prefix and the unique state of the `Ioc` component. -/
theorem transitionHistorySplit_IicProdIoc {α : Type*} (t : ℕ)
    (z : ((i : Finset.Iic t) → α) ×
      ((i : Finset.Ioc t (t + 1)) → α)) :
    transitionHistorySplit t
        (_root_.IicProdIoc (X := fun _ : ℕ => α) t (t + 1) z) =
      (z.1, transitionIocNext t z.2) := by
  apply Prod.ext
  · funext i
    simp [transitionHistorySplit, Preorder.frestrictLe₂_apply,
      _root_.IicProdIoc, Finset.mem_Iic.mp i.2]
  · simp [transitionHistorySplit, transitionHistoryNext, transitionIocNext,
      _root_.IicProdIoc]

/-- Under the prefix/final-state split, Mathlib's one-step `partialTraj`
kernel is exactly the identity kernel on the old history paired with the
history-dependent transition kernel. -/
theorem transitionPartialTraj_succ_map_split {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) :
    (Kernel.partialTraj
        (X := fun _ : ℕ => α)
        (fun n => transitionHistoryKernel P hP n) t (t + 1)).map
        (transitionHistorySplit t) =
      Kernel.prod Kernel.id (transitionHistoryKernel P hP t) := by
  let : ∀ _ : ℕ, MeasurableSpace α := fun _ => inferInstance
  have htailMeas :
      Measurable (transitionIocNext (α := α) t) :=
    measurable_of_finite _
  have htail :
      transitionIocNext (α := α) t ∘
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) t) =
        id := by
    funext y
    simp [transitionIocNext, MeasurableEquiv.piSingleton]
  rw [Kernel.partialTraj_succ_self]
  rw [← Kernel.map_comp_right _
    (measurable_IicProdIoc (X := fun _ : ℕ => α))
    (measurable_transitionHistorySplit (α := α) t)]
  have hcomp :
      transitionHistorySplit (α := α) t ∘
          _root_.IicProdIoc (X := fun _ : ℕ => α) t (t + 1) =
        Prod.map id (transitionIocNext t) := by
    funext z
    exact transitionHistorySplit_IicProdIoc t z
  rw [hcomp]
  rw [← Kernel.map_prod_map Kernel.id
    ((transitionHistoryKernel P hP t).map
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) t))
    measurable_id htailMeas]
  rw [Kernel.map_id]
  rw [← Kernel.map_comp_right
    (transitionHistoryKernel P hP t)
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => α) t).measurable
    htailMeas]
  rw [htail, Kernel.map_id]

/-- The history-dependent next-state kernel has exactly the original
transition-matrix singleton probabilities. -/
@[simp] theorem transitionHistoryKernel_singleton {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ)
    (hist : (i : Finset.Iic t) → α) (y : α) :
    transitionHistoryKernel P hP t hist {y} =
      ENNReal.ofReal (P (transitionHistoryLast t hist) y) := by
  rw [transitionHistoryKernel_apply]
  rw [PMF.toMeasure_apply_singleton _ y (measurableSet_singleton y)]
  exact transitionPMF_apply P hP (transitionHistoryLast t hist) y

/-- Joint law of the history through time `t` and the next state, started
from a deterministic initial state. -/
noncomputable def transitionPrefixPairMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    Measure (((i : Finset.Iic t) → α) × α) :=
  (transitionPrefixMeasure P hP x (t + 1)).map
    (transitionHistorySplit t)

instance instIsProbabilityMeasureTransitionPrefixPairMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    IsProbabilityMeasure (transitionPrefixPairMeasure P hP x t) := by
  unfold transitionPrefixPairMeasure
  refine (Measure.isProbabilityMeasure_map_iff ?_).mpr inferInstance
  exact
    (measurable_transitionHistorySplit (α := α) t).aemeasurable

/-- The joint prefix/next-state law is also the push-forward of the complete
prefix measure through `transitionHistorySplit`. -/
theorem transitionPrefixPairMeasure_eq_map {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    transitionPrefixPairMeasure P hP x t =
      (transitionPrefixMeasure P hP x (t + 1)).map
        (transitionHistorySplit t) := by
  rfl

/-- Dynamic recursion for the joint prefix/next-state law. -/
theorem transitionPrefixPairMeasure_eq_comp {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    transitionPrefixPairMeasure P hP x t =
      (Kernel.comp
        (Kernel.prod Kernel.id (transitionHistoryKernel P hP t))
        (Kernel.partialTraj
          (X := fun _ : ℕ => α)
          (fun n => transitionHistoryKernel P hP n) 0 t))
        (Function.const (Finset.Iic (0 : ℕ)) x) := by
  rw [transitionPrefixPairMeasure_eq_map]
  unfold transitionPrefixMeasure
  rw [← Kernel.map_apply _
    (measurable_transitionHistorySplit (α := α) t)]
  rw [Kernel.partialTraj_succ_eq_comp
    (X := fun _ : ℕ => α)
    (κ := fun n => transitionHistoryKernel P hP n)
    (a := 0) (b := t) (Nat.zero_le t)]
  rw [Kernel.map_comp]
  rw [transitionPartialTraj_succ_map_split P hP t]

/-- Singleton form of the one-step Markov recursion.  The mass of seeing a
particular history `pref` through time `t` and then state `y` is the prefix
mass times the original transition probability from the last state of that
history. -/
theorem transitionPrefixPairMeasure_singleton {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ)
    (pref : (i : Finset.Iic t) → α) (y : α) :
    transitionPrefixPairMeasure P hP x t {(pref, y)} =
      transitionPrefixMeasure P hP x t {pref} *
        ENNReal.ofReal (P (transitionHistoryLast t pref) y) := by
  rw [transitionPrefixPairMeasure_eq_comp P hP x t]
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton (pref, y))]
  rw [MeasureTheory.lintegral_fintype]
  unfold transitionPrefixMeasure
  have hpair :
      ({(pref, y)} : Set (((i : Finset.Iic t) → α) × α)) =
        ({pref} : Set ((i : Finset.Iic t) → α)) ×ˢ ({y} : Set α) := by
    simp
  calc
    (∑ hist : ((i : Finset.Iic t) → α),
        Kernel.prod Kernel.id (transitionHistoryKernel P hP t) hist {(pref, y)} *
          Kernel.partialTraj
            (X := fun _ : ℕ => α)
            (fun n => transitionHistoryKernel P hP n) 0 t
            (Function.const (Finset.Iic (0 : ℕ)) x) {hist}) =
        Kernel.prod Kernel.id (transitionHistoryKernel P hP t) pref {(pref, y)} *
          Kernel.partialTraj
            (X := fun _ : ℕ => α)
            (fun n => transitionHistoryKernel P hP n) 0 t
            (Function.const (Finset.Iic (0 : ℕ)) x) {pref} := by
      apply Fintype.sum_eq_single pref
      intro hist hne
      rw [hpair, Kernel.prod_apply_prod]
      simp [Kernel.id_apply, hne]
    _ =
        (transitionHistoryKernel P hP t pref {y}) *
          Kernel.partialTraj
            (X := fun _ : ℕ => α)
            (fun n => transitionHistoryKernel P hP n) 0 t
            (Function.const (Finset.Iic (0 : ℕ)) x) {pref} := by
      rw [hpair, Kernel.prod_apply_prod]
      simp [Kernel.id_apply]
    _ =
        Kernel.partialTraj
            (X := fun _ : ℕ => α)
            (fun n => transitionHistoryKernel P hP n) 0 t
            (Function.const (Finset.Iic (0 : ℕ)) x) {pref} *
          ENNReal.ofReal (P (transitionHistoryLast t pref) y) := by
      rw [transitionHistoryKernel_singleton]
      ac_rfl

end ECRuntime
