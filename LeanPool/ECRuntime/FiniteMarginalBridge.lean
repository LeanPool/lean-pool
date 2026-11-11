/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteTrajectoryConsistency
public import LeanPool.ECRuntime.TransitionKernelMarginals

/-!
# Stage 19: common finite-marginal structure

Stage 18 supplies two probability measures on `FiniteTrajectory α t`: the explicit
Stage-15 path-weight measure and the tail projection of Mathlib's `partialTraj` law.
Before proving their full equality, this file factors out the common projective structure.

The explicit PMFs are compatible under `Fin.init`; the Ionescu--Tulcea tail marginals
are compatible under the same map; and projecting the infinite trajectory law directly
to the first `t` post-initial coordinates gives exactly the latter finite marginal.
The two constructions also agree at horizon zero.

The remaining finite-marginal bridge is therefore reduced to a one-step extension
identity, after which equality at every horizon follows by induction.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- The explicit Stage-15 PMFs form a projective family under deletion of the final state. -/
theorem finiteTrajectoryPMF_map_init {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) (x : α) :
    PMF.map Fin.init (finiteTrajectoryPMF P hP (t + 1) x) =
      finiteTrajectoryPMF P hP t x := by
  classical
  ext pref
  rw [PMF.map_apply, tsum_fintype]
  have hnonneg :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory α (t + 1))),
        0 ≤ (if Fin.init path = pref
          then finiteTrajectoryWeight P (t + 1) x path else 0) := by
    intro path _hpath
    split_ifs
    · exact finiteTrajectoryWeight_nonneg P hP (t + 1) x path
    · exact le_rfl
  calc
    _ =
        ∑ path : FiniteTrajectory α (t + 1),
          ENNReal.ofReal
            (if Fin.init path = pref
              then finiteTrajectoryWeight P (t + 1) x path else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases h : Fin.init path = pref
      · have h' : pref = Fin.init path := h.symm
        rw [ite_eq_left h', ite_eq_left h]
        exact finiteTrajectoryPMF_apply P hP (t + 1) x path
      · have h' : pref ≠ Fin.init path := by
          intro hp
          exact h hp.symm
        rw [ite_eq_right h', ite_eq_right h]
        simp
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory α (t + 1),
          if Fin.init path = pref
            then finiteTrajectoryWeight P (t + 1) x path else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal (finiteTrajectoryWeight P t x pref) := by
      rw [finiteTrajectoryWeight_init_fiber_sum P hP t x pref]
    _ = finiteTrajectoryPMF P hP t x pref := by
      rfl

/-- Measure-level projective consistency of the explicit finite trajectory laws. -/
theorem finiteTrajectoryMeasure_map_init {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (t : ℕ) (x : α) :
    (finiteTrajectoryMeasure P hP (t + 1) x).map Fin.init =
      finiteTrajectoryMeasure P hP t x := by
  have hinit :
      Measurable (Fin.init : FiniteTrajectory α (t + 1) → FiniteTrajectory α t) := by
    fun_prop
  unfold finiteTrajectoryMeasure
  calc
    Measure.map Fin.init (finiteTrajectoryPMF P hP (t + 1) x).toMeasure =
        (PMF.map Fin.init (finiteTrajectoryPMF P hP (t + 1) x)).toMeasure := by
      exact PMF.toMeasure_map Fin.init _ hinit
    _ = (finiteTrajectoryPMF P hP t x).toMeasure := by
      rw [finiteTrajectoryPMF_map_init P hP t x]

/-- Dropping the last post-initial coordinate commutes with first restricting a full
Mathlib prefix by one time step. -/
theorem transitionPrefixTail_frestrict_succ {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic (t + 1)) → α) :
    Fin.init (transitionPrefixTail (t + 1) hist) =
      transitionPrefixTail t
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist) := by
  ext j
  simp [transitionPrefixTail, Fin.init, Preorder.frestrictLe₂_apply]

/-- The tail-projected Mathlib prefix laws are projectively consistent in the same
`Fin.init` convention as the explicit Stage-15 laws. -/
theorem transitionFiniteTrajectoryMarginal_map_init {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    (transitionFiniteTrajectoryMarginal P hP x (t + 1)).map Fin.init =
      transitionFiniteTrajectoryMarginal P hP x t := by
  have hinit :
      Measurable (Fin.init : FiniteTrajectory α (t + 1) → FiniteTrajectory α t) := by
    fun_prop
  have htailSucc : Measurable (transitionPrefixTail (α := α) (t + 1)) :=
    measurable_transitionPrefixTail (α := α) (t + 1)
  have htail : Measurable (transitionPrefixTail (α := α) t) :=
    measurable_transitionPrefixTail (α := α) t
  have hrestrict :
      Measurable
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ :
          ((i : Finset.Iic (t + 1)) → α) → ((i : Finset.Iic t) → α)) := by
    fun_prop
  have hfun :
      (Fin.init : FiniteTrajectory α (t + 1) → FiniteTrajectory α t) ∘
          transitionPrefixTail (α := α) (t + 1) =
        transitionPrefixTail (α := α) t ∘
          Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ := by
    funext hist
    exact transitionPrefixTail_frestrict_succ t hist
  unfold transitionFiniteTrajectoryMarginal
  calc
    Measure.map Fin.init
        (Measure.map (transitionPrefixTail (α := α) (t + 1))
          (transitionPrefixMeasure P hP x (t + 1))) =
        Measure.map
          ((Fin.init : FiniteTrajectory α (t + 1) → FiniteTrajectory α t) ∘
            transitionPrefixTail (α := α) (t + 1))
          (transitionPrefixMeasure P hP x (t + 1)) := by
      rw [Measure.map_map hinit htailSucc]
    _ = Measure.map
          (transitionPrefixTail (α := α) t ∘
            Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ)
          (transitionPrefixMeasure P hP x (t + 1)) := by
      rw [hfun]
    _ = Measure.map (transitionPrefixTail (α := α) t)
          (Measure.map
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ)
            (transitionPrefixMeasure P hP x (t + 1))) := by
      symm
      rw [Measure.map_map htail hrestrict]
    _ = Measure.map (transitionPrefixTail (α := α) t)
          (transitionPrefixMeasure P hP x t) := by
      rw [transitionPrefixMeasure_map_frestrictLe₂ P hP x t.le_succ]

/-- Direct projection from an infinite trajectory to its first `t` states after time zero. -/
def transitionTrajectoryTail {α : Type*} (t : ℕ) (path : ℕ → α) :
    FiniteTrajectory α t :=
  fun j => path (j.val + 1)

@[fun_prop] theorem measurable_transitionTrajectoryTail {α : Type*}
    [MeasurableSpace α] (t : ℕ) :
    Measurable (transitionTrajectoryTail (α := α) t) := by
  unfold transitionTrajectoryTail
  fun_prop

/-- Restricting a full trajectory through time `t` and then dropping time zero is the
same function as directly taking the first `t` post-initial states. -/
theorem transitionPrefixTail_frestrictLe {α : Type*}
    (t : ℕ) (path : ℕ → α) :
    transitionPrefixTail t (Preorder.frestrictLe t path) =
      transitionTrajectoryTail t path := by
  ext j
  simp [transitionPrefixTail, transitionTrajectoryTail, Preorder.frestrictLe_apply]

/-- The infinite Stage-17 law pushed directly to its first `t` post-initial coordinates
is exactly the tail-projected finite marginal from Stage 18. -/
theorem transitionTrajectoryMeasure_map_tail {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    (transitionTrajectoryMeasure P hP x).map (transitionTrajectoryTail t) =
      transitionFiniteTrajectoryMarginal P hP x t := by
  have hrestrict :
      Measurable (Preorder.frestrictLe t :
        (ℕ → α) → ((i : Finset.Iic t) → α)) := by
    fun_prop
  have htail : Measurable (transitionPrefixTail (α := α) t) :=
    measurable_transitionPrefixTail (α := α) t
  have hfun :
      transitionTrajectoryTail (α := α) t =
        transitionPrefixTail (α := α) t ∘ Preorder.frestrictLe t := by
    funext path
    symm
    exact transitionPrefixTail_frestrictLe t path
  unfold transitionFiniteTrajectoryMarginal
  rw [hfun]
  rw [← Measure.map_map htail hrestrict]
  rw [transitionTrajectoryMeasure_map_frestrictLe P hP x t]

/-- At horizon zero both finite constructions are the unique probability law on the
empty trajectory type.  This is the base case for the future one-step induction. -/
theorem transitionFiniteTrajectoryMarginal_zero_eq_finiteTrajectoryMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) :
    transitionFiniteTrajectoryMarginal P hP x 0 =
      finiteTrajectoryMeasure P hP 0 x := by
  apply Measure.ext_iff_singleton.mpr
  intro path
  have hsingleton : ({path} : Set (FiniteTrajectory α 0)) = Set.univ := by
    ext q
    simp [Subsingleton.elim q path]
  rw [hsingleton]
  simp

end ECRuntime
