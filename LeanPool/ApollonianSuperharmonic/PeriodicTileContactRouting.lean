/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex

-- [TABLET NODE: PeriodicTileContactRouting]

/-!
# PeriodicTileContactRouting

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a periodic tile complex $P$, a periodic contact routing is a proper,
compactly locally finite, periodic plane drawing of the prescribed graph,
made from genuine common-edge ports and tile-interior half-stars.  It chooses
a point $v_a$ in the interior of each closed-square tile realization.  For
each prescribed edge $ab$ it chooses, symmetrically, an actual two-element
lattice edge
$$
 e_{ab}\in E(T_a)\cap E(T_b)
$$
and an optional port whose value is the Euclidean midpoint $p_{ab}$ of that
edge.  The optional port is *none* exactly for nonedges; a nonedge also
has empty chosen-edge, half-arc, and full-arc data.

For a prescribed edge $ab$, the half-arc $H_{ab}$ is an arc from $v_a$ to
$p_{ab}$ contained in the interior of $T_a$ except at the port.  Distinct
ports at $a$ are distinct, and distinct incident half-arcs meet exactly at
$v_a$.  The full arc $A_{ab}=H_{ab}\cup H_{ba}$ is an arc from $v_a$ to
$v_b$, is symmetric in $a,b$, and two distinct full arcs meet exactly in
the positions of their common graph endpoints.  The vertex positions are
injective.  Compact local finiteness means that every compact subset of the
plane meets only finitely many full arcs.

Translation by the period lattice translates vertex positions, selected
lattice edges, optional ports, half-arcs, and full arcs.  Thus this object
contains precisely a periodic proper drawing of the prescribed adjacency
relation.  It has no second face type, no routed face regions, and no
plane-cover datum.  In particular, an isolated raw corner contact with no
common footprint edge produces neither a port nor a drawn edge.
-/
structure PeriodicTileContactRouting {ι : Type}
    (P : PeriodicTileComplex ι) where
-- BODY
  /-- The tile-interior point representing each graph vertex. -/
  position : ι → Real × Real
  /-- The selected common unit footprint edge of each prescribed adjacency. -/
  portEdge : ι → ι → Finset GaussianInt
  /-- The midpoint port of a prescribed edge, absent on nonedges. -/
  port : ι → ι → Option (Real × Real)
  /-- The half arc inside the first tile, ending at the selected edge port. -/
  halfArc : ι → ι → Set (Real × Real)
  /-- The symmetric full arc joining the two incident tile positions. -/
  edgeArc : ι → ι → Set (Real × Real)
  portEdge_symmetric : ∀ a b, portEdge a b = portEdge b a
  port_symmetric : ∀ a b, port a b = port b a
  portEdge_common : ∀ a b, P.plane.adjacent a b →
    portEdge a b ∈ FootprintEdges (P.tile a) ∩
      FootprintEdges (P.tile b)
  portEdge_two : ∀ a b, P.plane.adjacent a b →
    (portEdge a b).card = 2
  port_midpoint : ∀ a b, P.plane.adjacent a b →
    port a b = some
      (((∑ z ∈ portEdge a b, (((z.re : Int) : Real))) / 2),
        ((∑ z ∈ portEdge a b, (((z.im : Int) : Real))) / 2))
  port_eq_none_iff : ∀ a b,
    port a b = none ↔ ¬ P.plane.adjacent a b
  nonedge_has_no_portEdge : ∀ a b, ¬ P.plane.adjacent a b →
    portEdge a b = ∅
  nonedge_has_no_halfArc : ∀ a b, ¬ P.plane.adjacent a b →
    halfArc a b = ∅
  nonedge_has_no_edgeArc : ∀ a b, ¬ P.plane.adjacent a b →
    edgeArc a b = ∅
  position_in_tile_interior : ∀ a,
    position a ∈ interior (TileRealization (P.tile a))
  position_injective : Function.Injective position
  incident_ports_distinct : ∀ a b c p q,
    port a b = some p → port a c = some q → b ≠ c → p ≠ q
  halfArc_homeomorph : ∀ a b p, port a b = some p →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ halfArc a b,
      ((h ⟨0, by norm_num⟩ : halfArc a b) : Real × Real) =
          position a ∧
      ((h ⟨1, by norm_num⟩ : halfArc a b) : Real × Real) = p
  halfArc_supported : ∀ a b p, port a b = some p →
    halfArc a b ⊆ interior (TileRealization (P.tile a)) ∪ {p}
  incident_halfArc_intersections : ∀ a b c,
    P.plane.adjacent a b → P.plane.adjacent a c → b ≠ c →
      halfArc a b ∩ halfArc a c = {position a}
  edgeArc_symmetric : ∀ a b, edgeArc a b = edgeArc b a
  edgeArc_from_halfArcs : ∀ a b p, port a b = some p →
    edgeArc a b = halfArc a b ∪ halfArc b a
  edgeArc_homeomorph : ∀ a b, P.plane.adjacent a b →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ edgeArc a b,
      ((h ⟨0, by norm_num⟩ : edgeArc a b) : Real × Real) =
          position a ∧
      ((h ⟨1, by norm_num⟩ : edgeArc a b) : Real × Real) =
          position b
  edgeArc_intersections : ∀ a b c d,
    P.plane.adjacent a b → P.plane.adjacent c d →
    ({a, b} : Set ι) ≠ ({c, d} : Set ι) →
      edgeArc a b ∩ edgeArc c d =
        position '' (({a, b} : Set ι) ∩ ({c, d} : Set ι))
  compact_local_finiteness : ∀ K : Set (Real × Real), IsCompact K →
    Set.Finite {e : ι × ι |
      P.plane.adjacent e.1 e.2 ∧ (edgeArc e.1 e.2 ∩ K).Nonempty}
  position_periodic : ∀ u : P.lattice, ∀ a,
    position (P.shift u a) = position a + GaussianRealPoint u
  portEdge_periodic : ∀ u : P.lattice, ∀ a b,
    portEdge (P.shift u a) (P.shift u b) =
      (portEdge a b).image (fun z => z + (u : GaussianInt))
  port_periodic : ∀ u : P.lattice, ∀ a b,
    port (P.shift u a) (P.shift u b) =
      (port a b).map (fun p => p + GaussianRealPoint u)
  halfArc_periodic : ∀ u : P.lattice, ∀ a b,
    halfArc (P.shift u a) (P.shift u b) =
      (fun p => p + GaussianRealPoint u) '' halfArc a b
  edgeArc_periodic : ∀ u : P.lattice, ∀ a b,
    edgeArc (P.shift u a) (P.shift u b) =
      (fun p => p + GaussianRealPoint u) '' edgeArc a b

end ApollonianSuperharmonic

end
