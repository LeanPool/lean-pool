/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: LatticeCell]

/-!
# LatticeCell

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A lattice cell is indexed by its lower-left corner $x\in\mathbb Z[i]$ and
is denoted $s_x$.  Thus the collection of lattice cells is identified with
$\mathbb Z[i]$; the four vertices of $s_x$ are $x,x+1,x+i,x+1+i$.
-/
abbrev LatticeCell : Type :=
-- BODY
  GaussianInt

end ApollonianSuperharmonic

end
