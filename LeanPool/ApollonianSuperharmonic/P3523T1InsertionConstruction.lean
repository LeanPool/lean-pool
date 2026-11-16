/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3523T1BoundaryFaceSplit
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import LeanPool.ApollonianSuperharmonic.P3475T1TriangleTree
public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionData

-- [TABLET NODE: P3523T1InsertionConstruction]

/-!
# P3523T1InsertionConstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $s$ be an ordered subdivision and $t$ a triangle tree, as in
`P3475T1BoundarySubdivision` and
`P3475T1TriangleTree`. Put $I=\operatorname{Fin}(n+3)$.
List the indices $s.\mathrm{start}(0)+k$ for $0\le k<n+3$ in that
order, delete exactly those whose parameter is zero, and replace each
remaining $j$ by the triple
$$
 (j-1,\ j,\ s.\mathrm{start}(s.\mathrm{edge}(j)+1)).
$$
Call the resulting list $L$. Initially take the finite face family
$\mathcal F_0=\{s.\mathrm{start}(t.\mathrm{face}(k)(\operatorname{Fin}3)):
k\in\operatorname{Fin}(t.\mathrm{count})\}$, the label set
$V_0=s.\mathrm{start}(\operatorname{Fin}(r+3))$, and the boundary
pair set $B_0=\{\{s.\mathrm{start}(i),s.\mathrm{start}(i+1)\}:i\}$.
For a triple $(a,d,b)$ update the faces by
`P3523T1BoundaryFaceSplit`, update $V$ by adjoining $d$,
and update $B$ by deleting $\{a,b\}$ and adjoining $\{a,d\}$ and
$\{d,b\}$. For every natural $h$, the three states are the folds of
these updates along the first $h$ entries of $L$ (and so are constant
once $h\ge |L|$). These four data form
`P3523T1InsertionData`. There is just one face family,
not a separately chosen source and target family.
-/
noncomputable def P3523T1InsertionConstruction {r n : Nat}
    {q : P3381T1PolygonBoundary r} {p : P3381T1PolygonBoundary n}
    (s : P3475T1BoundarySubdivision q p)
    {X K : Set (Real × Real)} (t : P3475T1TriangleTree q X K) :
    P3523T1InsertionData (Fin (n + 3)) := by
-- BODY
  classical
  let steps := ((List.ofFn fun k : Fin (n + 3) => s.start 0 + k).filter
    fun j => s.parameter j ≠ 0).map
      fun j => (j - 1, j, s.start (s.edge j + 1))
  let initialFaces : Finset (Finset (Fin (n + 3))) :=
    Finset.univ.image fun k : Fin t.count =>
      Finset.univ.image (s.start ∘ t.face k)
  let initialVertices := Finset.univ.image s.start
  let initialBoundary := Finset.univ.image fun i : Fin (r + 3) =>
    ({s.start i, s.start (i + 1)} : Finset (Fin (n + 3)))
  exact {
    steps := steps
    faces := fun k => (steps.take k).foldl
      (fun fs e => P3523T1BoundaryFaceSplit fs e.1 e.2.1 e.2.2) initialFaces
    vertices := fun k => (steps.take k).foldl
      (fun vs e => insert e.2.1 vs) initialVertices
    boundary := fun k => (steps.take k).foldl
      (fun es e => insert {e.1, e.2.1}
        (insert {e.2.1, e.2.2} (es.erase {e.1, e.2.2}))) initialBoundary }

end ApollonianSuperharmonic

end
