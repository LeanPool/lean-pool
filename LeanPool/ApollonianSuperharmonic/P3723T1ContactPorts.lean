/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1EdgeContact
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: P3723T1ContactPorts]

/-!
# P3723T1ContactPorts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a `PeriodicTileComplex` $P$, this record has a position
$x_a$ for each index, a selected lattice edge $e_{ab}$ and optional
plane point $q_{ab}$ for each ordered pair, with the following laws.
The edge and port are symmetric. On every genuine
`P3723T1EdgeContact`, the edge belongs to both footprint
edge sets, has two endpoints, and the port is present and equals the
coordinatewise sum of these endpoints divided by two. Off contacts
the port is absent and the edge empty, and port absence is equivalent
to noncontact.

Each position is the center
$\operatorname{GaussianRealPoint}(z)+(1/2,1/2)$ of some cell
$z\in T_a.\mathrm{cells}$, is in the tile's ambient interior, and
the position map is injective. For $a\ne b$, the interior of $T_a$'s
realization is disjoint from all of $T_b$'s realization. Every present
port is in both ambient frontiers and in no third tile realization.
Two present ports at the same point have the same unordered owner
pair, and distinct contacts incident to one index have distinct ports.

Every index has finitely many contact neighbors. The record retains a
finite set of ordered genuine contact representatives such that every
ordered contact is a simultaneous lattice shift of one of them.
A shift stabilizing any unordered pair of indices is zero, and genuine
contact is invariant under simultaneous shifts. Positions translate
by the real period, selected edges by endpointwise lattice translation,
and ports by optional real translation, for every pair including
noncontacts. No reverse implication from contact to prescribed
adjacency is included.
-/
structure P3723T1ContactPorts {ι : Type} (P : PeriodicTileComplex ι) where
-- BODY
  /-- The selected constituent-cell center used as the tile position. -/
  position : ι → Real × Real
  /-- The selected common unit footprint edge at each genuine contact. -/
  portEdge : ι → ι → Finset GaussianInt
  /-- The midpoint of the selected edge, absent exactly on noncontacts. -/
  port : ι → ι → Option (Real × Real)
  portEdge_symmetric : ∀ a b, portEdge a b = portEdge b a
  port_symmetric : ∀ a b, port a b = port b a
  portEdge_common : ∀ a b, P3723T1EdgeContact P a b →
    portEdge a b ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)
  portEdge_two : ∀ a b, P3723T1EdgeContact P a b → (portEdge a b).card = 2
  port_midpoint : ∀ a b, P3723T1EdgeContact P a b →
    port a b = some
      (((∑ z ∈ portEdge a b, (((z.re : Int) : Real))) / 2),
        ((∑ z ∈ portEdge a b, (((z.im : Int) : Real))) / 2))
  port_eq_none_iff : ∀ a b, port a b = none ↔ ¬ P3723T1EdgeContact P a b
  noncontact_has_no_portEdge : ∀ a b, ¬ P3723T1EdgeContact P a b →
    portEdge a b = ∅
  position_cell : ∀ a, ∃ z ∈ (P.tile a).cells,
    position a = GaussianRealPoint z + ((1 / 2 : Real), (1 / 2 : Real))
  position_in_tile_interior : ∀ a, position a ∈ interior (TileRealization (P.tile a))
  position_injective : Function.Injective position
  interior_disjoint_tiles : ∀ a b, a ≠ b →
    Disjoint (interior (TileRealization (P.tile a))) (TileRealization (P.tile b))
  port_frontier : ∀ a b p, port a b = some p →
    p ∈ frontier (TileRealization (P.tile a)) ∩ frontier (TileRealization (P.tile b))
  port_no_third : ∀ a b p, port a b = some p →
    ∀ c, c ≠ a → c ≠ b → p ∉ TileRealization (P.tile c)
  port_owner_pair : ∀ a b c d p, port a b = some p → port c d = some p →
    ({a, b} : Set ι) = {c, d}
  incident_ports_distinct : ∀ a b c p q,
    port a b = some p → port a c = some q → b ≠ c → p ≠ q
  finite_degree : ∀ a, Set.Finite {b | P3723T1EdgeContact P a b}
  /-- A finite set representing all ordered genuine contacts under period translation. -/
  contactOrbitReps : Finset (ι × ι)
  contactOrbitReps_genuine : ∀ e ∈ contactOrbitReps, P3723T1EdgeContact P e.1 e.2
  contact_orbit_representatives : ∀ a b, P3723T1EdgeContact P a b →
    ∃ e ∈ contactOrbitReps, ∃ u : P.lattice,
      a = P.shift u e.1 ∧ b = P.shift u e.2
  unordered_stabilizer : ∀ u : P.lattice, ∀ a b,
    ({P.shift u a, P.shift u b} : Set ι) = {a, b} → u = 0
  contact_periodic : ∀ u : P.lattice, ∀ a b,
    P3723T1EdgeContact P (P.shift u a) (P.shift u b) ↔ P3723T1EdgeContact P a b
  position_periodic : ∀ u : P.lattice, ∀ a,
    position (P.shift u a) = position a + GaussianRealPoint u
  portEdge_periodic : ∀ u : P.lattice, ∀ a b,
    portEdge (P.shift u a) (P.shift u b) =
      (portEdge a b).image (fun z => z + (u : GaussianInt))
  port_periodic : ∀ u : P.lattice, ∀ a b,
    port (P.shift u a) (P.shift u b) =
      (port a b).map (fun p => p + GaussianRealPoint u)

end ApollonianSuperharmonic

end
