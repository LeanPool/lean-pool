/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: P4849T1SetDiagonalSubsequence]

/-!
# P4849T1SetDiagonalSubsequence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1SetDiagonalSubsequence (C : ℕ → Set GaussianInt) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ L : Set GaussianInt,
      ∀ F : Finset GaussianInt, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F,
        (x ∈ C (σ n) ↔ x ∈ L) := by
-- BODY
  classical
  have : Countable GaussianInt :=
    Function.Injective.countable (f := fun z : GaussianInt => (z.re, z.im)) (by
      intro a b h
      exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let : TopologicalSpace Bool := ⊥
  have : DiscreteTopology Bool := ⟨rfl⟩
  let b : ℕ → GaussianInt → Bool := fun n x => decide (x ∈ C n)
  obtain ⟨l, σ, hσ, hl⟩ := CompactSpace.tendsto_subseq b
  refine ⟨σ, hσ, {x | l x = true}, ?_⟩
  intro F
  have hpoint (x : GaussianInt) : ∀ᶠ n in Filter.atTop, b (σ n) x = l x := by
    have hx := (tendsto_pi_nhds.mp hl) x
    simpa only [nhds_discrete, Filter.tendsto_pure, Function.comp_apply] using hx
  have hfinite : ∀ᶠ n in Filter.atTop, ∀ x ∈ F, b (σ n) x = l x :=
    F.eventually_all.mpr (fun x _ => hpoint x)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfinite
  refine ⟨N, ?_⟩
  intro n hn x hx
  have heq := hN n hn x hx
  change (x ∈ C (σ n) ↔ l x = true)
  rw [← heq]
  simp [b]

end ApollonianSuperharmonic

end
