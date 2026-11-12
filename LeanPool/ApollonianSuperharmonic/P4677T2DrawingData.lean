/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation

-- [TABLET NODE: P4677T2DrawingData]

/-!
# P4677T2DrawingData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For Gaussian integers $u,v$ and an additive subgroup $L$, periodic drawing
data consist of positions on `PeriodicSubtileIndex`, edge arcs,
and regions indexed by `PeriodicSubtileFaceIndex`, with the
geometric laws of `PlaneTriangulation`: injective positions,
symmetric arcs, interval homeomorphisms with the specified endpoint
positions on allowed edges, intersections of distinct allowed edges
exactly at common endpoint positions, open connected pairwise disjoint
face regions, face frontier exactly the three side arcs, and coverage
by positions, allowed arcs, and face regions. Here adjacency is
`AllowedSubtileIncidence` and face vertices are
`SixSubtileFaceVertices`. The abstract graph laws, including
three-connectivity and the two-face incidence law, are not part of these
data. A coordinate function $c:L\to\mathbb Z^2$ satisfies
$c_1(w)u+c_2(w)v=w$. Vertex shift adds $c(w)$ to the two integer
coordinates, preserving the label; face shift does the same. Both shifts
have the zero and addition action laws.
Adjacency is invariant, and the face-vertex map is equivariant. Positions,
edge arcs, and open face regions translate by the real vector of $w$.
There are finite vertex, ordered-edge, and face representative sets.
Every ordered-edge representative $(a,b)$ satisfies allowed incidence
between $a$ and $b$.
The vertex representatives are exactly the six zero-coordinate indices;
the face representatives are exactly the twelve zero-coordinate faces.
Every vertex has a unique representative in its shift orbit, and every
ordered adjacent pair and every face is a shift of a representative.
These data contain no tile, selected lattice point, footprint walk, or
fundamental set of lattice cells.
-/
structure P4677T2DrawingData (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) where
-- BODY
  /-- The embedded position of each periodic occurrence index. -/
  position : PeriodicSubtileIndex → Real × Real
  /-- The stored plane arc for each ordered pair of occurrence indices. -/
  edgeArc : PeriodicSubtileIndex → PeriodicSubtileIndex → Set (Real × Real)
  /-- The open region of each translated face label. -/
  faceRegion : PeriodicSubtileFaceIndex → Set (Real × Real)
  position_injective : Function.Injective position
  arc_symmetric : ∀ a b, edgeArc a b = edgeArc b a
  arc_homeomorph : ∀ a b, AllowedSubtileIncidence a b →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ edgeArc a b,
      ((h ⟨0, by norm_num⟩ : edgeArc a b) : Real × Real) = position a ∧
      ((h ⟨1, by norm_num⟩ : edgeArc a b) : Real × Real) = position b
  arc_intersections : ∀ a b c d,
    AllowedSubtileIncidence a b → AllowedSubtileIncidence c d →
    ({a, b} : Set PeriodicSubtileIndex) ≠ {c, d} →
      edgeArc a b ∩ edgeArc c d =
        position '' (({a, b} : Set PeriodicSubtileIndex) ∩ {c, d})
  region_open : ∀ f, IsOpen (faceRegion f)
  region_connected : ∀ f, IsConnected (faceRegion f)
  region_disjoint : Pairwise fun f g => Disjoint (faceRegion f) (faceRegion g)
  face_boundary : ∀ f,
    frontier (faceRegion f) =
      edgeArc (SixSubtileFaceVertices f 0) (SixSubtileFaceVertices f 1) ∪
      edgeArc (SixSubtileFaceVertices f 1) (SixSubtileFaceVertices f 2) ∪
      edgeArc (SixSubtileFaceVertices f 2) (SixSubtileFaceVertices f 0)
  plane_cover : Set.range position ∪
    {p | ∃ a b, AllowedSubtileIncidence a b ∧ p ∈ edgeArc a b} ∪
    {p | ∃ f, p ∈ faceRegion f} = Set.univ
  /-- The integral coefficients of a period in the chosen two-vector basis. -/
  coordinates : L → Int × Int
  coordinates_spec : ∀ w,
    (coordinates w).1 * u + (coordinates w).2 * v = (w : GaussianInt)
  /-- Translate an occurrence index by a period lattice element. -/
  shift : L → PeriodicSubtileIndex → PeriodicSubtileIndex
  /-- Translate the entire face index by a period lattice element. -/
  faceShift : L → PeriodicSubtileFaceIndex → PeriodicSubtileFaceIndex
  shift_eq : ∀ w a, shift w a =
    ⟨a.label, a.first + (coordinates w).1, a.second + (coordinates w).2⟩
  faceShift_eq : ∀ w f, faceShift w f =
    ⟨f.label, f.first + (coordinates w).1, f.second + (coordinates w).2⟩
  shift_zero : ∀ a, shift 0 a = a
  shift_add : ∀ w z a, shift (w + z) a = shift w (shift z a)
  faceShift_zero : ∀ f, faceShift 0 f = f
  faceShift_add : ∀ w z f, faceShift (w + z) f = faceShift w (faceShift z f)
  edge_periodic : ∀ w a b,
    AllowedSubtileIncidence (shift w a) (shift w b) ↔ AllowedSubtileIncidence a b
  face_vertices_periodic : ∀ w f i,
    SixSubtileFaceVertices (faceShift w f) i = shift w (SixSubtileFaceVertices f i)
  position_periodic : ∀ w a,
    position (shift w a) = position a + GaussianRealPoint w
  edgeArc_periodic : ∀ w a b,
    edgeArc (shift w a) (shift w b) =
      (fun p => p + GaussianRealPoint w) '' edgeArc a b
  faceRegion_periodic : ∀ w f,
    faceRegion (faceShift w f) =
      (fun p => p + GaussianRealPoint w) '' faceRegion f
  /-- The six zero-coordinate occurrence representatives. -/
  vertexReps : Finset PeriodicSubtileIndex
  /-- The selected finite family of ordered allowed-edge representatives. -/
  edgeReps : Finset (PeriodicSubtileIndex × PeriodicSubtileIndex)
  /-- The twelve zero-coordinate face representatives. -/
  faceReps : Finset PeriodicSubtileFaceIndex
  vertex_reps : ∀ a, a ∈ vertexReps ↔ a.first = 0 ∧ a.second = 0
  edge_reps_allowed : ∀ r ∈ edgeReps, AllowedSubtileIncidence r.1 r.2
  face_reps : ∀ f, f ∈ faceReps ↔
    f.first = 0 ∧ f.second = 0
  vertex_orbits : ∀ a, ∃! r,
    r ∈ vertexReps ∧ ∃ w, a = shift w r
  edge_orbits : ∀ a b, AllowedSubtileIncidence a b →
    ∃ r ∈ edgeReps, ∃ w, a = shift w r.1 ∧ b = shift w r.2
  face_orbits : ∀ f, ∃ r ∈ faceReps, ∃ w, f = faceShift w r

end ApollonianSuperharmonic

end
