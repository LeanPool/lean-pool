/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleMatrix

-- [TABLET NODE: IntegralityLattice]

/-!
# IntegralityLattice

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a band circle $C$, identify $u=u_1+iu_2\in\mathbb Z[i]$ with
$(u_1,u_2)\in\mathbb Z^2$ and define
$$
 L_C=\{u\in\mathbb Z[i]:A_C(u_1,u_2)^t\in\mathbb Z^2\}.
$$
Matrix linearity shows directly that this set contains zero and is closed
under addition and negation, so $L_C$ is regarded as an additive subgroup of
$\mathbb Z[i]$.  This is the matrix-integrality lattice from equation (1.5)
of the paper.
-/
def IntegralityLattice (C : BandCircle) : AddSubgroup GaussianInt where
-- BODY
  carrier := {u | ∀ i : Fin 2, ∃ n : ℤ,
    Matrix.mulVec (CircleMatrix C)
      ![((u.re : ℤ) : ℝ), ((u.im : ℤ) : ℝ)] i = (n : ℝ)}
  zero_mem' := by
    intro i
    refine ⟨0, ?_⟩
    simp [Matrix.mulVec]
  add_mem' := by
    intro x y hx hy i
    obtain ⟨mx, hmx⟩ := hx i
    obtain ⟨my, hmy⟩ := hy i
    refine ⟨mx + my, ?_⟩
    rw [show ![(((x + y).re : ℤ) : ℝ), (((x + y).im : ℤ) : ℝ)] =
        ![((x.re : ℤ) : ℝ), ((x.im : ℤ) : ℝ)] +
          ![((y.re : ℤ) : ℝ), ((y.im : ℤ) : ℝ)] by
      ext j
      fin_cases j <;> simp]
    rw [Matrix.mulVec_add, Pi.add_apply, hmx, hmy]
    norm_num
  neg_mem' := by
    intro x hx i
    obtain ⟨m, hm⟩ := hx i
    refine ⟨-m, ?_⟩
    rw [show ![(((-x).re : ℤ) : ℝ), (((-x).im : ℤ) : ℝ)] =
        -![((x.re : ℤ) : ℝ), ((x.im : ℤ) : ℝ)] by
      ext j
      fin_cases j <;> simp]
    rw [Matrix.mulVec_neg, Pi.neg_apply, hm]
    norm_num

end ApollonianSuperharmonic

end
