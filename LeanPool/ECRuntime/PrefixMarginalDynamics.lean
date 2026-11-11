/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteMarginalDynamics

/-!
# Stage 21: singleton recursion for complete finite prefixes

Stage 20 identifies the one-step `partialTraj` dynamics after splitting a history
through time `t + 1` into its prefix through time `t` and its final state.  Before
passing to the repository's post-initial `FiniteTrajectory` convention, this file
extracts the clean singleton recursion at the complete-history level.

The key theorem is

`transitionPrefixMeasure_singleton_succ`:

    μ_{t+1} {hist}
      = μ_t {hist|_{≤t}} * ofReal (P hist_t hist_{t+1}).

This is the dynamic induction principle needed to identify the Ionescu--Tulcea
finite marginals with the explicit Stage-15 path weights.  The file also records
that the horizon-zero prefix law is exactly the Dirac mass at the supplied initial
history.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- Splitting a complete history through time `t + 1` into its prefix and final
state loses no information. -/
theorem transitionHistorySplit_injective {α : Type*} (t : ℕ) :
    Function.Injective (transitionHistorySplit (α := α) t) := by
  intro hist₁ hist₂ hsplit
  funext i
  rcases i with ⟨i, hiLe⟩
  have hiLe' : i ≤ t + 1 := Finset.mem_Iic.mp hiLe
  by_cases hit : i ≤ t
  · have hfst :
        (transitionHistorySplit t hist₁).1 =
          (transitionHistorySplit t hist₂).1 :=
      congrArg Prod.fst hsplit
    have hvalue := congrFun hfst
      (⟨i, Finset.mem_Iic.mpr hit⟩ : ↥(Finset.Iic t))
    simpa only [transitionHistorySplit, Preorder.frestrictLe₂_apply] using hvalue
  · have hiEq : i = t + 1 := by omega
    subst i
    have hsnd :
        (transitionHistorySplit t hist₁).2 =
          (transitionHistorySplit t hist₂).2 :=
      congrArg Prod.snd hsplit
    simpa only [transitionHistorySplit, transitionHistoryNext] using hsnd

/-- Evaluating the Stage-20 pair law at the split of a concrete history recovers
exactly the singleton mass of that history under the `(t+1)`-prefix law. -/
theorem transitionPrefixPairMeasure_singleton_split
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ)
    (hist : (i : Finset.Iic (t + 1)) → α) :
    transitionPrefixPairMeasure P hP x t {transitionHistorySplit t hist} =
      transitionPrefixMeasure P hP x (t + 1) {hist} := by
  rw [transitionPrefixPairMeasure_eq_map]
  rw [Measure.map_apply
    (measurable_transitionHistorySplit (α := α) t)
    (measurableSet_singleton (transitionHistorySplit t hist))]
  have hpre :
      transitionHistorySplit (α := α) t ⁻¹'
          ({transitionHistorySplit t hist} :
            Set (((i : Finset.Iic t) → α) × α)) =
        ({hist} : Set ((i : Finset.Iic (t + 1)) → α)) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      exact (transitionHistorySplit_injective (α := α) t) hq
    · intro hq
      subst q
      rfl
  rw [hpre]

/-- Exact one-step singleton recursion for the complete finite Ionescu--Tulcea
prefix law. -/
theorem transitionPrefixMeasure_singleton_succ
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ)
    (hist : (i : Finset.Iic (t + 1)) → α) :
    transitionPrefixMeasure P hP x (t + 1) {hist} =
      transitionPrefixMeasure P hP x t
          {Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist} *
        ENNReal.ofReal
          (P
            (transitionHistoryLast t
              (Preorder.frestrictLe₂
                (π := fun _ : ℕ => α) t.le_succ hist))
            (transitionHistoryNext t hist)) := by
  rw [← transitionPrefixPairMeasure_singleton_split P hP x t hist]
  simpa [transitionHistorySplit] using
    (transitionPrefixPairMeasure_singleton P hP x t
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist)
      (transitionHistoryNext t hist))

/-- At horizon zero the complete-prefix law is the Dirac measure at the supplied
initial history. -/
theorem transitionPrefixMeasure_zero_eq_dirac
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) :
    transitionPrefixMeasure P hP x 0 =
      Measure.dirac (Function.const (Finset.Iic (0 : ℕ)) x) := by
  unfold transitionPrefixMeasure
  rw [Kernel.partialTraj_self]
  exact Kernel.id_apply (Function.const (Finset.Iic (0 : ℕ)) x)

/-- Singleton form of the horizon-zero base law, written without introducing a
`DecidableEq` assumption on the state space. -/
theorem transitionPrefixMeasure_zero_singleton
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α)
    (hist : (i : Finset.Iic 0) → α) :
    transitionPrefixMeasure P hP x 0 {hist} =
      ({hist} : Set ((i : Finset.Iic 0) → α)).indicator 1
        (Function.const (Finset.Iic (0 : ℕ)) x) := by
  rw [transitionPrefixMeasure_zero_eq_dirac]
  exact Measure.dirac_apply (Function.const (Finset.Iic (0 : ℕ)) x) {hist}

end ECRuntime
