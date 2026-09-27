/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — uniformity passes to vertex sub-blocks

The per-triple counting of `Nibble.AX1.uniform_triple_codegree` needs the three triangle-degree
scales of a cluster triple to agree.  One way to equalise them without any probability is to replace
the three clusters `U, W, X` by *sub-blocks* `U' ⊆ U`, `W' ⊆ W`, `X' ⊆ X` of prescribed relative
sizes (see `RESIDUAL.md`, §3(b)).  For that one needs uniformity to be inherited by large subsets,
which Mathlib does not record.  This file supplies it.

* `Nibble.AX1.edgeDensity_sub_lt_of_isUniform` — the density of a pair of subsets of relative size
  at least `α ≥ ε` differs from the density of the pair by less than `ε`.
* `Nibble.AX1.isUniform_subblock` — such a pair of subsets is `(ε/α)`-uniform.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # CoreGapSubblock -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type}

/-- A pair of subsets of relative size at least `α ≥ ε` of an `ε`-uniform pair has density within
`ε` of the density of the pair. -/
theorem edgeDensity_sub_lt_of_isUniform (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A' B' : Finset V} {ε α : ℝ} (hU : G.IsUniform ε A B) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hεα : ε ≤ α) (hcardA : α * (#A : ℝ) ≤ (#A' : ℝ)) (hcardB : α * (#B : ℝ) ≤ (#B' : ℝ)) :
    |(G.edgeDensity A' B' : ℝ) - (G.edgeDensity A B : ℝ)| < ε := by
  refine hU hA' hB' ?_ ?_
  · calc (#A : ℝ) * ε ≤ (#A : ℝ) * α := by
          have : (0 : ℝ) ≤ (#A : ℝ) := Nat.cast_nonneg _
          nlinarith only [hεα]
      _ = α * (#A : ℝ) := by ring
      _ ≤ (#A' : ℝ) := hcardA
  · calc (#B : ℝ) * ε ≤ (#B : ℝ) * α := by
          have : (0 : ℝ) ≤ (#B : ℝ) := Nat.cast_nonneg _
          nlinarith only [hεα]
      _ = α * (#B : ℝ) := by ring
      _ ≤ (#B' : ℝ) := hcardB

/-- **Uniformity passes to large sub-blocks.**  If `(A, B)` is `ε`-uniform and `A' ⊆ A`, `B' ⊆ B`
have relative size at least `α`, with `ε ≤ α ≤ 1/2`, then `(A', B')` is `(ε/α)`-uniform.

The proof is the obvious one: a subset of `A'` of relative size `ε/α` has absolute size at least
`ε|A|`, so uniformity of `(A, B)` applies to it and to `(A', B')` itself, and the two densities are
each within `ε` of `d(A, B)`, hence within `2ε ≤ ε/α` of each other. -/
theorem isUniform_subblock (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A' B' : Finset V} {ε α : ℝ} (hU : G.IsUniform ε A B) (hε : 0 < ε) (hA' : A' ⊆ A)
    (hB' : B' ⊆ B) (hεα : ε ≤ α) (hα : 2 * α ≤ 1)
    (hcardA : α * (#A : ℝ) ≤ (#A' : ℝ)) (hcardB : α * (#B : ℝ) ≤ (#B' : ℝ)) :
    G.IsUniform (ε / α) A' B' := by
  have hα0 : 0 < α := lt_of_lt_of_le hε hεα
  have hbase : |(G.edgeDensity A' B' : ℝ) - (G.edgeDensity A B : ℝ)| < ε :=
    edgeDensity_sub_lt_of_isUniform G hU hA' hB' hεα hcardA hcardB
  intro A'' hA'' B'' hB'' hcA hcB
  -- the sub-sub-blocks are large in `A` and `B`
  have hcA' : (#A : ℝ) * ε ≤ (#A'' : ℝ) := by
    have h1 : (#A : ℝ) * ε = α * (#A : ℝ) * (ε / α) := by field_simp
    have h2 : α * (#A : ℝ) * (ε / α) ≤ (#A' : ℝ) * (ε / α) := by
      have : (0 : ℝ) ≤ ε / α := le_of_lt (div_pos hε hα0)
      nlinarith only [hcardA, this]
    linarith only [hcA, h1.le, h2]
  have hcB' : (#B : ℝ) * ε ≤ (#B'' : ℝ) := by
    have h1 : (#B : ℝ) * ε = α * (#B : ℝ) * (ε / α) := by field_simp
    have h2 : α * (#B : ℝ) * (ε / α) ≤ (#B' : ℝ) * (ε / α) := by
      have : (0 : ℝ) ≤ ε / α := le_of_lt (div_pos hε hα0)
      nlinarith only [hcardB, this]
    linarith only [hcB, h1.le, h2]
  have hsub : |(G.edgeDensity A'' B'' : ℝ) - (G.edgeDensity A B : ℝ)| < ε :=
    hU (hA''.trans hA') (hB''.trans hB') hcA' hcB'
  have hεα' : 2 * ε ≤ ε / α := by
    rw [le_div_iff₀ hα0]
    nlinarith only [hε, hα]
  rw [abs_lt] at hbase hsub ⊢
  constructor <;> linarith only [hbase, hsub, hεα']

end Nibble.AX1
