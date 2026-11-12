/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies, Joël Riou
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Card

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Finite standard simplices

The geometric constructions use the standard simplex as a subset of a finite-dimensional
function space, preserving the set-based domain of the upstream formalization.
This specializes the set definition in `Mathlib.Analysis.Convex.StdSimplex`.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped BigOperators

/-- The nonnegative real weights of total mass one on a finite index type. -/
def StandardSimplex (ι : Type*) [Fintype ι] : Set (ι → Real) :=
  {weights | (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1}

end ApollonianSuperharmonic

end
