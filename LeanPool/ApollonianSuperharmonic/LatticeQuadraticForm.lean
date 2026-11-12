/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import Mathlib.Data.Matrix.Mul
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: LatticeQuadraticForm]

/-!
# LatticeQuadraticForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a real $2\times2$ matrix $A$ and a lattice point
$x=(x_1,x_2)\in\mathbb Z^2$, define the lattice quadratic function
$$
 q_A(x)=\frac12 x^{\mathsf T}Ax.
$$
This function is denoted by $\operatorname{LatticeQuadraticForm}(A,x)$ in
the formalization.
-/
noncomputable def LatticeQuadraticForm
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : GaussianInt) : ℝ :=
-- BODY
  let v : Fin 2 → ℝ := ![(x.re : ℝ), (x.im : ℝ)]
  (1 / 2 : ℝ) * dotProduct v (Matrix.mulVec A v)

end ApollonianSuperharmonic

end
