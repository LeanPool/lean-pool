/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: IntegerLatticeFunction]

/-!
# IntegerLatticeFunction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An integer lattice function is a function $f:\mathbb Z[i]\to\mathbb Z$.
We identify $\mathbb Z[i]$ with the square lattice $\mathbb Z^2$ by real and
imaginary coordinates.
-/
abbrev IntegerLatticeFunction :=
-- BODY
  GaussianInt → ℤ

end ApollonianSuperharmonic

end
