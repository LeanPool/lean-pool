/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceComposition

/-!
# Assembling a trace over its ordered vertex parameters

The trace in XII, page 243, concatenates one two-edge walk for each
region interval between consecutive vertex parameters. This file proves
that finite assembly, including the length count. It separates the
ordering of the parameters from the geometric construction of each
individual step.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Assemble trace steps over consecutive entries of a finite parameter
list. Each interval contributes exactly two edges, so the full walk
has twice the number of intervals as its length. -/
theorem exists_traceSteps_of_partition {S : Type*} [TopologicalSpace S]
    {Γ K : Drawing S} {f : ℝ → S} {n : ℕ} (t : Fin (n + 1) → ℝ)
    (hΓ : ∀ i, f (t i) ∈ Γ.V) (hK : ∀ i, f (t i) ∈ K.V)
    (hsteps : ∀ i : Fin n,
      ∃ W : GraphWalk K.toGraph (f (t i.castSucc)) (f (t i.succ)),
        TraceSteps Γ K f (t i.castSucc) (t i.succ) W ∧ W.length = 2) :
    ∃ W : GraphWalk K.toGraph (f (t 0)) (f (t (Fin.last n))),
      TraceSteps Γ K f (t 0) (t (Fin.last n)) W ∧ W.length = 2 * n := by
  induction n with
  | zero =>
    refine ⟨.nil (hK 0), ?_, rfl⟩
    exact ⟨rfl, rfl, hΓ 0⟩
  | succ n ih =>
    let t' : Fin (n + 1) → ℝ := fun i => t i.succ
    have hsteps' : ∀ i : Fin n,
        ∃ W : GraphWalk K.toGraph (f (t' i.castSucc)) (f (t' i.succ)),
          TraceSteps Γ K f (t' i.castSucc) (t' i.succ) W ∧ W.length = 2 := by
      intro i
      exact hsteps i.succ
    obtain ⟨Wtail, htail, htailLength⟩ := ih t' (fun i => hΓ i.succ) (fun i => hK i.succ) hsteps'
    obtain ⟨Wfirst, hfirst, hfirstLength⟩ := hsteps 0
    refine ⟨Wfirst.append Wtail, traceSteps_append Wfirst Wtail hfirst htail, ?_⟩
    have hl := GraphWalk.length_append Wfirst Wtail
    rw [hfirstLength, htailLength] at hl
    exact hl.trans (by omega)

end GraphMinor.GM12
