/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import LeanPool.ApollonianSuperharmonic.P3544T1RayParity
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order

-- [TABLET NODE: P3650T1ExposedCorner]

/-!
# P3650T1ExposedCorner

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a boundary $p$ of `P3381T1PolygonBoundary`, an exposed
corner consists of an index $b$ and a real linear functional $\ell$
whose values at all indexed vertices are distinct, with its unique
maximum at $p_b$. Put $a=p_{b-1}$, $B=p_b$, $c=p_{b+1}$, with indices
read cyclically. The determinant of $(a,B,c)$ in
`P3381T1TriangleDeterminant` is nonzero. The data include an
affine height function $h$ with $h(a)=h(c)=0$, $h(B)=1$, together with
the existence of a positive product-metric radius $r$ such that,
for every $x\in B(B,r)$,
$$
 x\in O_p\quad\Longleftrightarrow\quad
 x=B+s(a-B)+t(c-B)\text{ for some }s,t>0,
$$
where $O_p$ is `P3544T1RayParity`. Thus the local odd set
is precisely the open convex cone between the two lower incident rays.
-/
structure P3650T1ExposedCorner {n : Nat} (p : P3381T1PolygonBoundary n) where
-- BODY
  /-- The unique boundary vertex maximizing the chosen linear functional. -/
  b : Fin (n + 3)
  /-- A linear functional with distinct values on all boundary vertices. -/
  ell : (Real × Real) →ₗ[Real] Real
  distinct_heights : Function.Injective (ell ∘ p.vertex)
  maximum : ∀ i, i ≠ b → ell (p.vertex i) < ell (p.vertex b)
  nondegenerate : P3381T1TriangleDeterminant
    ![p.vertex (b - 1), p.vertex b, p.vertex (b + 1)] ≠ 0
  /-- The affine height normalized to zero at the two neighbors and one at the exposed vertex. -/
  height : (Real × Real) →ᵃ[Real] Real
  height_prev : height (p.vertex (b - 1)) = 0
  height_top : height (p.vertex b) = 1
  height_next : height (p.vertex (b + 1)) = 0
  cone_odd : ∃ r : Real, 0 < r ∧ ∀ x ∈ Metric.ball (p.vertex b) r,
    (x ∈ P3544T1RayParity p ↔ ∃ s t : Real, 0 < s ∧ 0 < t ∧
      x = p.vertex b + s • (p.vertex (b - 1) - p.vertex b) +
        t • (p.vertex (b + 1) - p.vertex b))

end ApollonianSuperharmonic

end
