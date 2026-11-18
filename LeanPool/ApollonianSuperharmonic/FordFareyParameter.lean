/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Order.Ring.Int


-- [TABLET NODE: FordFareyParameter]

/-!
# FordFareyParameter

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A reduced Ford--Farey parameter consists of integers $p,p_1,p_2$ and
natural numbers $q,q_1,q_2$ such that $q>0$, $\gcd(q,|p|)=1$,
$$
 (p,q)=(p_1,q_1)+(p_2,q_2),\qquad
 p_1q-q_1p=1,\qquad p_2q-q_2p=-1,
$$
with $0\leq q_1<q$ and $0<q_2$.  When $q=1$ the data are required to be
$(p_1,q_1)=(1,0)$ and $(p_2,q_2)=(p-1,1)$; the first of these denotes the
oriented line parent, not a curvature-zero Ford circle.
-/
structure FordFareyParameter where
-- BODY
  /-- The numerator of the reduced Ford fraction. -/
  p : Int
  /-- The positive denominator of the reduced Ford fraction. -/
  q : Nat
  q_pos : 0 < q
  reduced : Nat.Coprime q p.natAbs
  /-- The numerator of the first Farey parent, with the line-parent convention at q = 1. -/
  p₁ : Int
  /-- The first parent denominator, strictly smaller than q. -/
  q₁ : Nat
  /-- The numerator of the second Farey parent. -/
  p₂ : Int
  /-- The positive second parent denominator. -/
  q₂ : Nat
  sum_p : p = p₁ + p₂
  sum_q : q = q₁ + q₂
  det₁ : p₁ * (q : Int) - (q₁ : Int) * p = 1
  det₂ : p₂ * (q : Int) - (q₂ : Int) * p = -1
  q₁_lt : q₁ < q
  q₂_pos : 0 < q₂
  unit_case : q = 1 → p₁ = 1 ∧ q₁ = 0 ∧ p₂ = p - 1 ∧ q₂ = 1

end ApollonianSuperharmonic

end
