/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order

-- [TABLET NODE: P3889T1TwoRaySectorDecomposition]

/-!
# P3889T1TwoRaySectorDecomposition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $x,u,v\in\mathbb R^2$ and $r\in\mathbb R$, put
$B=B(x,r)$, $R_w=\{x+tw:t\geq0\}$ and
$[w,h]=w_1h_2-w_2h_1$. A two-ray sector decomposition consists of
two nonempty connected open plane sets $L,R$, disjoint from one
another, with
$$
 L\cup R=B\setminus(R_u\cup R_v).
$$
For each $w\in\{u,v\}$ and $0<t<r$, writing $z=x+tw$, the data
also require a $\delta>0$ with $B(z,\delta)\subseteq B$ such that
$L\cap B(z,\delta)$ and $R\cap B(z,\delta)$ are, in either order,
the two sets
$$
 \{q\in B(z,\delta):[w,q-z]>0\},\qquad
 \{q\in B(z,\delta):[w,q-z]<0\}.
$$
Balls use the product norm $\|(s,t)\|=\max(|s|,|t|)$, as does
the Lean plane $\mathbb R\times\mathbb R$.
-/
structure P3889T1TwoRaySectorDecomposition
    (x : Real × Real) (r : Real) (u v : Real × Real) where
-- BODY
  /-- One connected open component of the ball with the two rays removed. -/
  left : Set (Real × Real)
  /-- The other connected open component, disjoint from the first. -/
  right : Set (Real × Real)
  left_open : IsOpen left
  right_open : IsOpen right
  left_connected : IsConnected left
  right_connected : IsConnected right
  disjoint : Disjoint left right
  cover : left ∪ right = Metric.ball x r \
    ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
      {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v})
  sides : ∀ w : Real × Real, (w = u ∨ w = v) →
    ∀ t : Real, 0 < t → t < r →
    let z := x + t • w
    ∃ δ : Real, 0 < δ ∧ Metric.ball z δ ⊆ Metric.ball x r ∧
      ((left ∩ Metric.ball z δ =
          {q | q ∈ Metric.ball z δ ∧
            0 < w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1)} ∧
        right ∩ Metric.ball z δ =
          {q | q ∈ Metric.ball z δ ∧
            w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) < 0}) ∨
       (right ∩ Metric.ball z δ =
          {q | q ∈ Metric.ball z δ ∧
            0 < w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1)} ∧
        left ∩ Metric.ball z δ =
          {q | q ∈ Metric.ball z δ ∧
            w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) < 0}))

end ApollonianSuperharmonic

end
