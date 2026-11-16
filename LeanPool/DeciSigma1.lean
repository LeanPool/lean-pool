/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Arithmetic.DifferenceConstraints
public import LeanPool.DeciSigma1.Arithmetic.ElementaryBounds
public import LeanPool.DeciSigma1.Arithmetic.FinitePaths
public import LeanPool.DeciSigma1.Automata.Basic
public import LeanPool.DeciSigma1.Automata.Constraints
public import LeanPool.DeciSigma1.Constraints.Basic
public import LeanPool.DeciSigma1.Constraints.Closure
public import LeanPool.DeciSigma1.Constraints.Signed
public import LeanPool.DeciSigma1.Constraints.GroundBounds
public import LeanPool.DeciSigma1.Constraints.RankedExtensions
public import LeanPool.DeciSigma1.Constraints.TopFree.Basic
public import LeanPool.DeciSigma1.Encodings
public import LeanPool.DeciSigma1.Entailment.Basic
public import LeanPool.DeciSigma1.Entailment.Decide
public import LeanPool.DeciSigma1.Entailment.Embedding
public import LeanPool.DeciSigma1.Entailment.Guard
public import LeanPool.DeciSigma1.Entailment.Logic
public import LeanPool.DeciSigma1.Examples.Entailment
public import LeanPool.DeciSigma1.Examples.Readers
public import LeanPool.DeciSigma1.Examples.Satisfiability
public import LeanPool.DeciSigma1.Examples.Sentences
public import LeanPool.DeciSigma1.Full.Basic
public import LeanPool.DeciSigma1.Full.Closure.Automata
public import LeanPool.DeciSigma1.Full.Closure.Basic
public import LeanPool.DeciSigma1.Full.Decide
public import LeanPool.DeciSigma1.Full.Logic
public import LeanPool.DeciSigma1.Full.Models.Observations
public import LeanPool.DeciSigma1.Full.Models.RegularCones
public import LeanPool.DeciSigma1.Full.Models.Pinning
public import LeanPool.DeciSigma1.Full.Models.Signed.Transfer
public import LeanPool.DeciSigma1.Full.Reduction.Compile
public import LeanPool.DeciSigma1.Full.Reduction.Realization
public import LeanPool.DeciSigma1.Full.Reduction.Transfer
public import LeanPool.DeciSigma1.Holes.Bound
public import LeanPool.DeciSigma1.Holes.Fresh.Bound
public import LeanPool.DeciSigma1.Holes.Fresh.ElementaryBound
public import LeanPool.DeciSigma1.Holes.Fresh.ChannelPreservation
public import LeanPool.DeciSigma1.Holes.Fresh.ChannelTransport
public import LeanPool.DeciSigma1.Holes.Fresh.Deletion
public import LeanPool.DeciSigma1.Holes.Fresh.DeletionCoordinates
public import LeanPool.DeciSigma1.Holes.Fresh.Hierarchy
public import LeanPool.DeciSigma1.Holes.Fresh.Parsing
public import LeanPool.DeciSigma1.Holes.Periodic.Bound
public import LeanPool.DeciSigma1.Holes.Periodic.Deletion
public import LeanPool.DeciSigma1.Holes.Periodic.Pieces
public import LeanPool.DeciSigma1.Holes.Periodic.Basic
public import LeanPool.DeciSigma1.Holes.Periodic.Transport
public import LeanPool.DeciSigma1.Holes.Tail.Candidates
public import LeanPool.DeciSigma1.Holes.Tail.ClosedFactors
public import LeanPool.DeciSigma1.Holes.Tail.Compression
public import LeanPool.DeciSigma1.Holes.Tail.ElementaryBound
public import LeanPool.DeciSigma1.Holes.Tail.Levels
public import LeanPool.DeciSigma1.Holes.Tail.RayCompatibility
public import LeanPool.DeciSigma1.Holes.Tail.RayFamilies
public import LeanPool.DeciSigma1.Holes.Tail.Rays
public import LeanPool.DeciSigma1.Holes.Tail.RunCovers
public import LeanPool.DeciSigma1.Holes.Tail.TerminalRays
public import LeanPool.DeciSigma1.Holes.Tail.WindowChains
public import LeanPool.DeciSigma1.Logic.Decide
public import LeanPool.DeciSigma1.Logic.Flatten
public import LeanPool.DeciSigma1.Logic.Syntax
public import LeanPool.DeciSigma1.Main
public import LeanPool.DeciSigma1.Readers.Basic
public import LeanPool.DeciSigma1.Satisfiability.Decide
public import LeanPool.DeciSigma1.Satisfiability.Shape
public import LeanPool.DeciSigma1.Semantics.Classes
public import LeanPool.DeciSigma1.Semantics.FiniteMedian
public import LeanPool.DeciSigma1.Semantics.Median
public import LeanPool.DeciSigma1.Semantics.Order
public import LeanPool.DeciSigma1.Semantics.PrefixSet
public import LeanPool.DeciSigma1.Semantics.Selector
public import LeanPool.DeciSigma1.Semantics.Tree
public import LeanPool.DeciSigma1.Words.Basic
public import LeanPool.DeciSigma1.Words.Deletion
public import LeanPool.DeciSigma1.Words.Periods
public import LeanPool.DeciSigma1.Words.SuffixChains

/-!
# Decidability of the Sigma-one theory of non-structural subtyping

Source: url:https://github.com/noti0na1/deci-sigma1/tree/4d1702fd657be4d7bb3203e2e7302856353124c7
Authors: Yaoyu Zhao
Status: verified
Main declarations: `DeciSigma1.decideBooleanSentence`, `DeciSigma1.booleanSentence_regular_iff`,
  `DeciSigma1.decideBooleanSentenceTopFree`, `DeciSigma1.exists_small_hole`,
  `DeciSigma1.smallHoleBound_le`
Tags: subtyping, decidability, automata, infinite-trees
MSC: 03B25, 68N18, 68Q45
-/

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The Σ₁ theory of non-structural subtype constraints

Decision procedures for the Boolean combinations of existential and universal sentences over
non-structural subtype constraints, and for the core problem of the proof, disjunctive
entailment `Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` between a finite conjunction of subtype constraints
and a disjunction of variable inequalities. They cover one constructor of any finite arity: for
bottom, the constructor and top with any variance, and for bottom and a covariant constructor,
over arbitrary, regular and finite trees. Satisfiability and entailment are special sentences
(`DeciSigma1.Encodings`). The public statements are in `DeciSigma1.Main`.
-/

@[expose] public section
