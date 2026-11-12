/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction
public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm

-- [TABLET NODE: QuadraticGrowthAtInfinity]

/-!
# QuadraticGrowthAtInfinity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An integer lattice function $g$ has quadratic growth $A$ at infinity if
$$
 g(x)=q_A(x)+o(|x|^2).
$$
Explicitly, for every $\varepsilon>0$ there is $R\in\mathbb R$ such that
whenever $|x|^2=x_1^2+x_2^2\geq R$,
$$
 |g(x)-q_A(x)|\leq\varepsilon |x|^2.
$$
-/
def QuadraticGrowthAtInfinity
    (A : Matrix (Fin 2) (Fin 2) ℝ) (g : IntegerLatticeFunction) : Prop :=
-- BODY
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : GaussianInt,
    R ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 →
      |(g x : ℝ) - LatticeQuadraticForm A x| ≤
        ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2)

end ApollonianSuperharmonic

end
