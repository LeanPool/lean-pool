/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: P4994T6Rotation]

/-!
# P4994T6Rotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $n\geq0$, let $R_n$ be the additive automorphism of $\mathbb Z^2$
defined by $R_0=\operatorname{id}$ and
$R_{n+1}(x)=((R_nx)_1-(R_nx)_2,(R_nx)_1)$.
Thus $R_n$ is the $n$th power of $R(x,y)=(x-y,x)$; the inverse of $R$
is $(x,y)\mapsto(y,y-x)$.
-/
def P4994T6Rotation : Nat → ((Int × Int) ≃+ (Int × Int)) :=
-- BODY
  fun
  | 0 => AddEquiv.refl _
  | n + 1 => (P4994T6Rotation n).trans
      { toFun := fun p => (p.1 - p.2, p.1)
        invFun := fun p => (p.2, p.2 - p.1)
        left_inv := by intro p; ext <;> simp
        right_inv := by intro p; ext <;> simp
        map_add' := by intro p q; ext <;> simp; omega }

end ApollonianSuperharmonic

end
