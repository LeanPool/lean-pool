/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.HittingTime
public import Mathlib.Basic.ENNReal.Real

/-!
# Unrestricted Runtime

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/--
The supremum of all finite-horizon expected runtimes, represented in `ENNReal`.

This is the natural infinite-horizon quantity determined by our finite-state Bellman
semantics. A later measure-theoretic bridge can identify it with the expectation of
the sample-path hitting time by monotone convergence.
-/
noncomputable def runtimeSup {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (x : α) : ENNReal :=
  ⨆ t : ℕ, ENNReal.ofReal (finiteHorizonRuntime P target t x)

/--
`runtimeSup` is invariant under replacing the target by an equal set, even when
Lean has selected different `DecidablePred` instances for the two target expressions.
-/
theorem runtimeSup_congr_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α)
    (s t : Set α)
    [ds : DecidablePred (fun x => x ∈ s)]
    [dt : DecidablePred (fun x => x ∈ t)]
    (hst : s = t) (x : α) :
    @runtimeSup α _ P s ds x = @runtimeSup α _ P t dt x := by
  subst t
  have hdec : ds = dt := Subsingleton.elim _ _
  cases hdec
  rfl

/-- Each finite truncation is below the unrestricted runtime supremum. -/
theorem finiteHorizonRuntime_ofReal_le_runtimeSup
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (t : ℕ) (x : α) :
    ENNReal.ofReal (finiteHorizonRuntime P target t x) ≤
      runtimeSup P target x := by
  unfold runtimeSup
  exact le_iSup (fun s : ℕ => ENNReal.ofReal (finiteHorizonRuntime P target s x)) t

/-- A uniform real bound on all truncations bounds the unrestricted runtime supremum. -/
theorem runtimeSup_le_of_uniform_bound
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (B : α → ℝ)
    (hB : HasUniformFiniteHorizonRuntimeBound P target B) (x : α) :
    runtimeSup P target x ≤ ENNReal.ofReal (B x) := by
  unfold runtimeSup
  refine iSup_le ?_
  intro t
  exact ENNReal.ofReal_le_ofReal (hB t x)

/-- A finite Bellman certificate gives a finite unrestricted runtime supremum. -/
theorem runtimeSup_le_of_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : α → ℝ)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hR : IsRuntimeSuperSolution P target R) (x : α) :
    runtimeSup P target x ≤ ENNReal.ofReal (R x) := by
  exact runtimeSup_le_of_uniform_bound P target R
    (hasUniformFiniteHorizonRuntimeBound_of_superSolution
      P target hP R hRnonneg hR) x

/-- Any real-valued certificate bound rules out infinite unrestricted runtime. -/
theorem runtimeSup_ne_top_of_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : α → ℝ)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hR : IsRuntimeSuperSolution P target R) (x : α) :
    runtimeSup P target x ≠ ⊤ := by
  have hle : runtimeSup P target x ≤ ENNReal.ofReal (R x) :=
    runtimeSup_le_of_superSolution P target hP R hRnonneg hR x
  exact ne_top_of_le_ne_top (by simp) hle

end ECRuntime
