/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P4733T1ContainedWalk]

/-!
# P4733T1ContainedWalk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A list $p$ is a contained walk in $T,U$ from $x$ to $y$ if its optional
head is $x$, its optional last element is $y$, every entry belongs to
$\operatorname{FootprintVertices}(T)\cap\operatorname{FootprintVertices}(U)$,
and every consecutive unordered pair belongs to
$\operatorname{FootprintEdges}(T)\cap\operatorname{FootprintEdges}(U)$.
The last condition means that for every decomposition
$p=l_1\mathbin{+\!+}[a,b]\mathbin{+\!+}l_2$, the edge $\{a,b\}$
belongs to both graphs. Constant and repeating lists are permitted.
-/
def P4733T1ContainedWalk (T U : ProtoTile) (x y : GaussianInt)
    (p : List GaussianInt) : Prop :=
-- BODY
  p.head? = some x ∧ p.getLast? = some y ∧
    (∀ z ∈ p, z ∈ FootprintVertices T ∩ FootprintVertices U) ∧
    ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ → {a, b} ∈ FootprintEdges T ∩ FootprintEdges U

end ApollonianSuperharmonic

end
