/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteMarginalBridge
public import LeanPool.ECRuntime.PrefixMarginalDynamics

/-!
# Stage 22: exact identification of finite trajectory marginals

Stage 21 gives the exact singleton recursion for complete `partialTraj` prefixes.  This
file closes the finite-marginal bridge to the explicit Stage-15 path law.

The proof uses the elementary equivalence

    history through time t  <->  (state at time 0, post-initial trajectory of length t).

Under this equivalence the complete prefix law is exactly the product of the Dirac mass
at the supplied initial state and `finiteTrajectoryMeasure`.  Projecting the second
coordinate then proves that the Ionescu--Tulcea finite marginal and the explicit finite
trajectory measure agree at every horizon.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- State reached after a finite post-initial trajectory.  At horizon zero this is the
supplied initial state. -/
def finiteTrajectoryEndpoint {α : Type*} (x : α) :
    (t : ℕ) → FiniteTrajectory α t → α
  | 0, _path => x
  | t + 1, path => path (Fin.last t)

/-- Peeling the first state from a nonempty trajectory does not change its endpoint,
provided the peeled state is used as the new initial state. -/
@[simp] theorem finiteTrajectoryEndpoint_succ {α : Type*}
    (x : α) (t : ℕ) (path : FiniteTrajectory α (t + 1)) :
    finiteTrajectoryEndpoint x (t + 1) path =
      finiteTrajectoryEndpoint (path 0) t (Fin.tail path) := by
  cases t with
  | zero =>
      simp [finiteTrajectoryEndpoint]
  | succ t =>
      simp [finiteTrajectoryEndpoint, Fin.tail]

/-- Appending a final state factors the explicit finite path weight into the old path
weight and one final transition probability. -/
theorem finiteTrajectoryWeight_snoc {α : Type*}
    (P : TransitionMatrix α) :
    ∀ t x (path : FiniteTrajectory α t) y,
      finiteTrajectoryWeight P (t + 1) x (Fin.snoc path y) =
        finiteTrajectoryWeight P t x path *
          P (finiteTrajectoryEndpoint x t path) y := by
  intro t
  induction t with
  | zero =>
      intro x path y
      simp [finiteTrajectoryWeight, finiteTrajectoryEndpoint, Fin.snoc_zero]
  | succ t ih =>
      intro x path y
      rw [finiteTrajectoryWeight_snoc_succ P t x path y]
      rw [ih (path 0) (Fin.tail path) y]
      change
        P x (path 0) *
            (finiteTrajectoryWeight P t (path 0) (Fin.tail path) *
              P (finiteTrajectoryEndpoint (path 0) t (Fin.tail path)) y) =
          (P x (path 0) *
            finiteTrajectoryWeight P t (path 0) (Fin.tail path)) *
              P (finiteTrajectoryEndpoint x (t + 1) path) y
      rw [finiteTrajectoryEndpoint_succ]
      ac_rfl

/-- The time-zero coordinate of a complete prefix. -/
def transitionHistoryHead {α : Type*} (t : ℕ)
    (hist : (i : Finset.Iic t) → α) : α :=
  hist ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩

/-- Reconstruct a complete history from its time-zero state and its post-initial tail. -/
def transitionHistoryOfHeadTail {α : Type*} (t : ℕ)
    (z : α × FiniteTrajectory α t) : (i : Finset.Iic t) → α :=
  fun i =>
    if hi : i.1 = 0 then z.1
    else z.2 ⟨i.1 - 1, by
      have hit : i.1 ≤ t := Finset.mem_Iic.mp i.2
      omega⟩

@[simp] theorem transitionHistoryHead_ofHeadTail {α : Type*}
    (t : ℕ) (z : α × FiniteTrajectory α t) :
    transitionHistoryHead t (transitionHistoryOfHeadTail t z) = z.1 := by
  simp [transitionHistoryHead, transitionHistoryOfHeadTail]

@[simp] theorem transitionPrefixTail_ofHeadTail {α : Type*}
    (t : ℕ) (z : α × FiniteTrajectory α t) :
    transitionPrefixTail t (transitionHistoryOfHeadTail t z) = z.2 := by
  ext j
  simp [transitionPrefixTail, transitionHistoryOfHeadTail]

/-- A complete history is recovered from its head and post-initial tail. -/
theorem transitionHistoryOfHeadTail_headTail {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic t) → α) :
    transitionHistoryOfHeadTail t
        (transitionHistoryHead t hist, transitionPrefixTail t hist) = hist := by
  funext i
  by_cases hi : i.1 = 0
  · have hi' : i = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ := by
      apply Subtype.ext
      exact hi
    rw [hi']
    simp [transitionHistoryOfHeadTail, transitionHistoryHead]
  · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
    have hpredlt : i.1 - 1 < t := by
      have hit : i.1 ≤ t := Finset.mem_Iic.mp i.2
      omega
    change
      (if h : i.1 = 0 then transitionHistoryHead t hist
       else transitionPrefixTail t hist ⟨i.1 - 1, hpredlt⟩) = hist i
    rw [dite_eq_right hi]
    unfold transitionPrefixTail
    apply congrArg hist
    apply Subtype.ext
    change i.1 - 1 + 1 = i.1
    omega

/-- Complete histories split canonically into their initial state and post-initial
finite trajectory. -/
def transitionHistoryHeadTailEquiv {α : Type*} (t : ℕ) :
    ((i : Finset.Iic t) → α) ≃ α × FiniteTrajectory α t where
  toFun hist := (transitionHistoryHead t hist, transitionPrefixTail t hist)
  invFun := transitionHistoryOfHeadTail t
  left_inv := transitionHistoryOfHeadTail_headTail t
  right_inv z := by
    apply Prod.ext
    · exact transitionHistoryHead_ofHeadTail t z
    · exact transitionPrefixTail_ofHeadTail t z

@[simp] theorem transitionHistoryHeadTailEquiv_apply {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic t) → α) :
    transitionHistoryHeadTailEquiv t hist =
      (transitionHistoryHead t hist, transitionPrefixTail t hist) := by
  rfl

@[simp] theorem transitionHistoryHeadTailEquiv_symm_apply {α : Type*}
    (t : ℕ) (z : α × FiniteTrajectory α t) :
    (transitionHistoryHeadTailEquiv t).symm z =
      transitionHistoryOfHeadTail t z := by
  rfl

/-- The final state of a complete prefix agrees with the endpoint of its post-initial
trajectory once its time-zero state is supplied as the initial state. -/
theorem finiteTrajectoryEndpoint_transitionPrefixTail {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic t) → α) :
    finiteTrajectoryEndpoint (transitionHistoryHead t hist) t
        (transitionPrefixTail t hist) =
      transitionHistoryLast t hist := by
  cases t with
  | zero =>
      simp [finiteTrajectoryEndpoint, transitionHistoryHead,
        transitionHistoryLast]
  | succ t =>
      simp [finiteTrajectoryEndpoint, transitionPrefixTail,
        transitionHistoryLast]

/-- Removing the final coordinate of a complete prefix commutes with its post-initial
tail projection. -/
theorem transitionPrefixTail_restrict_succ {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic (t + 1)) → α) :
    transitionPrefixTail t
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist) =
      Fin.init (transitionPrefixTail (t + 1) hist) := by
  symm
  exact transitionPrefixTail_frestrict_succ t hist

/-- The post-initial tail of a complete `(t+1)`-prefix is obtained by appending its
final state to the tail of the restricted `t`-prefix. -/
theorem transitionPrefixTail_eq_snoc {α : Type*}
    (t : ℕ) (hist : (i : Finset.Iic (t + 1)) → α) :
    transitionPrefixTail (t + 1) hist =
      Fin.snoc
        (transitionPrefixTail t
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist))
        (transitionHistoryNext t hist) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [transitionPrefixTail, transitionHistoryNext]
  · simp [transitionPrefixTail, Preorder.frestrictLe₂_apply]

/-- Exact singleton formula for the complete Ionescu--Tulcea prefix law.  A history
has nonzero mass only when its time-zero coordinate is the supplied initial state;
then its mass is exactly the explicit Stage-15 path weight of its post-initial tail. -/
theorem transitionPrefixMeasure_singleton_eq_finiteTrajectoryWeight
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) :
    ∀ t (hist : (i : Finset.Iic t) → α),
      transitionPrefixMeasure P hP x t {hist} =
        ({x} : Set α).indicator
          (fun _ =>
            ENNReal.ofReal
              (finiteTrajectoryWeight P t x (transitionPrefixTail t hist)))
          (transitionHistoryHead t hist) := by
  classical
  intro t
  induction t with
  | zero =>
      intro hist
      rw [transitionPrefixMeasure_zero_eq_dirac P hP x]
      rw [Measure.dirac_apply (Function.const (Finset.Iic (0 : ℕ)) x) {hist}]
      by_cases hx : transitionHistoryHead 0 hist = x
      · have hhist : hist = Function.const (Finset.Iic (0 : ℕ)) x := by
          funext i
          have hi : i.1 = 0 := by
            have hit : i.1 ≤ 0 := Finset.mem_Iic.mp i.2
            omega
          have hi' : i =
              ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := by
            apply Subtype.ext
            exact hi
          rw [hi']
          simpa [transitionHistoryHead, Function.const] using hx
        subst hist
        simp [finiteTrajectoryWeight, transitionHistoryHead,
          Function.const]
      · have hne : Function.const (Finset.Iic (0 : ℕ)) x ≠ hist := by
          intro hEq
          apply hx
          rw [← hEq]
          simp [transitionHistoryHead, Function.const]
        simp [Set.indicator, hne, hx]
  | succ t ih =>
      intro hist
      let pref :=
        Preorder.frestrictLe₂ (π := fun _ : ℕ => α) t.le_succ hist
      have hhead : transitionHistoryHead t pref =
          transitionHistoryHead (t + 1) hist := by
        rfl
      rw [transitionPrefixMeasure_singleton_succ P hP x t hist]
      rw [ih pref]
      rw [hhead]
      by_cases hx : transitionHistoryHead (t + 1) hist = x
      · have hmem :
            transitionHistoryHead (t + 1) hist ∈ ({x} : Set α) := by
          simpa using hx
        simp only [Set.indicator_of_mem hmem
          (fun _ =>
            ENNReal.ofReal
              (finiteTrajectoryWeight P t x (transitionPrefixTail t pref)))]
        rw [Set.indicator_of_mem hmem
          (fun _ =>
            ENNReal.ofReal
              (finiteTrajectoryWeight P (t + 1) x
                (transitionPrefixTail (t + 1) hist)))]
        rw [transitionPrefixTail_eq_snoc t hist]
        rw [finiteTrajectoryWeight_snoc P]
        have hend :
            finiteTrajectoryEndpoint x t (transitionPrefixTail t pref) =
              transitionHistoryLast t pref := by
          rw [← hx, ← hhead]
          exact finiteTrajectoryEndpoint_transitionPrefixTail t pref
        rw [hend]
        rw [ENNReal.ofReal_mul
          (finiteTrajectoryWeight_nonneg P hP t x
            (transitionPrefixTail t pref))]
      · have hnotmem :
            transitionHistoryHead (t + 1) hist ∉ ({x} : Set α) := by
          simpa using hx
        rw [Set.indicator_of_notMem hnotmem
          (fun _ =>
            ENNReal.ofReal
              (finiteTrajectoryWeight P t x (transitionPrefixTail t pref)))]
        rw [Set.indicator_of_notMem hnotmem
          (fun _ =>
            ENNReal.ofReal
              (finiteTrajectoryWeight P (t + 1) x
                (transitionPrefixTail (t + 1) hist)))]
        simp only [zero_mul]

/-- Under the head/tail equivalence, the complete finite prefix law is the product of
the fixed initial-state Dirac mass and the explicit finite trajectory measure. -/
theorem transitionPrefixMeasure_map_headTailEquiv
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    (transitionPrefixMeasure P hP x t).map
        (transitionHistoryHeadTailEquiv t) =
      (Measure.dirac x).prod (finiteTrajectoryMeasure P hP t x) := by
  classical
  apply Measure.ext_iff_singleton.mpr
  intro z
  have hmeas : Measurable (transitionHistoryHeadTailEquiv t :
      ((i : Finset.Iic t) → α) → α × FiniteTrajectory α t) :=
    measurable_of_finite _
  rw [Measure.map_apply hmeas (measurableSet_singleton z)]
  have hpre :
      (transitionHistoryHeadTailEquiv t :
          ((i : Finset.Iic t) → α) → α × FiniteTrajectory α t) ⁻¹' {z} =
        {(transitionHistoryHeadTailEquiv t).symm z} := by
    ext hist
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply (transitionHistoryHeadTailEquiv t).injective
      simpa using h
    · intro h
      rw [h]
      simp
  rw [hpre]
  rw [transitionPrefixMeasure_singleton_eq_finiteTrajectoryWeight P hP x t]
  have hpair :
      ({z} : Set (α × FiniteTrajectory α t)) =
        ({z.1} : Set α) ×ˢ ({z.2} : Set (FiniteTrajectory α t)) := by
    rcases z with ⟨a, path⟩
    simp
  rw [hpair, Measure.prod_prod]
  rw [Measure.dirac_apply x {z.1}]
  rw [finiteTrajectoryMeasure_singleton P hP t x z.2]
  by_cases hz : z.1 = x
  · simp [hz]
  · have hzx : x ≠ z.1 := by
      intro h
      exact hz h.symm
    simp [hz, hzx]

/-- The full finite-marginal bridge: at every horizon, the tail projection of the
Ionescu--Tulcea prefix law is exactly the explicit Stage-15 finite trajectory measure. -/
theorem transitionFiniteTrajectoryMarginal_eq_finiteTrajectoryMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    transitionFiniteTrajectoryMarginal P hP x t =
      finiteTrajectoryMeasure P hP t x := by
  have hheadTail : Measurable (transitionHistoryHeadTailEquiv t :
      ((i : Finset.Iic t) → α) → α × FiniteTrajectory α t) :=
    measurable_of_finite _
  have hsnd : Measurable (Prod.snd :
      α × FiniteTrajectory α t → FiniteTrajectory α t) := measurable_snd
  have hfun :
      transitionPrefixTail (α := α) t =
        (Prod.snd : α × FiniteTrajectory α t → FiniteTrajectory α t) ∘
          (transitionHistoryHeadTailEquiv t :
            ((i : Finset.Iic t) → α) → α × FiniteTrajectory α t) := by
    funext hist
    rfl
  unfold transitionFiniteTrajectoryMarginal
  rw [hfun]
  rw [← Measure.map_map hsnd hheadTail]
  rw [transitionPrefixMeasure_map_headTailEquiv P hP x t]
  rw [Measure.map_snd_prod]
  simp

/-- Direct corollary for the Stage-17 infinite trajectory law: projecting to the first
`t` post-initial states produces the explicit finite trajectory measure. -/
theorem transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (x : α) (t : ℕ) :
    (transitionTrajectoryMeasure P hP x).map (transitionTrajectoryTail t) =
      finiteTrajectoryMeasure P hP t x := by
  rw [transitionTrajectoryMeasure_map_tail P hP x t]
  exact transitionFiniteTrajectoryMarginal_eq_finiteTrajectoryMeasure P hP x t

end ECRuntime
