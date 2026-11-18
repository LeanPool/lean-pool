/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: BandPackingShiftPotential]

/-!
# BandPackingShiftPotential

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $w=A+Bi\in\mathbb Z[i]$, the integral quadratic correction attached
to a packing shift is
$$
 \Psi_w(x_1,x_2)=
 A\frac{x_1(x_1-1)}2-A\frac{x_2(x_2-1)}2+Bx_1x_2.
$$
The two products in the numerators are even, so this is integer-valued
on the Gaussian lattice.
-/
def BandPackingShiftPotential (w x : GaussianInt) : ℤ :=
-- BODY
  w.re * (x.re * (x.re - 1) / 2) -
    w.re * (x.im * (x.im - 1) / 2) + w.im * x.re * x.im

end ApollonianSuperharmonic

end
