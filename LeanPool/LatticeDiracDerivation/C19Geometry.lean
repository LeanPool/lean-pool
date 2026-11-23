/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/C19Geometry.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Foundation

/-!
DIRAC-001 substrate geometry. C19 consists of the owning center site plus
eighteen neighbors: six face neighbors and twelve edge neighbors. This module
indexes those eighteen neighbors; the center is represented by `Site` itself.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

/-- The index type of the eighteen neighbors of a C19 stencil: indices `0`–`5` are the six face
neighbors and `6`–`17` are the twelve edge neighbors. -/
abbrev C19Neighbor := Fin 18

/-- The integer coordinate along `axis` of the offset vector of `neighbor`: each face neighbor
has one entry `±1`, each edge neighbor has two entries `±1`, and all other entries are `0`. -/
def c19Coord (axis : Fin 3) (neighbor : C19Neighbor) : ℤ :=
  match neighbor.val, axis.val with
  | 0, 0 => 1 | 1, 0 => -1 | 2, 1 => 1 | 3, 1 => -1
  | 4, 2 => 1 | 5, 2 => -1
  | 6, 0 => -1 | 6, 1 => -1
  | 7, 0 => -1 | 7, 1 => 1
  | 8, 0 => 1 | 8, 1 => -1
  | 9, 0 => 1 | 9, 1 => 1
  | 10, 0 => -1 | 10, 2 => -1
  | 11, 0 => -1 | 11, 2 => 1
  | 12, 0 => 1 | 12, 2 => -1
  | 13, 0 => 1 | 13, 2 => 1
  | 14, 1 => -1 | 14, 2 => -1
  | 15, 1 => -1 | 15, 2 => 1
  | 16, 1 => 1 | 16, 2 => -1
  | 17, 1 => 1 | 17, 2 => 1
  | _, _ => 0

/-- The bond weight of a C19 neighbor: `2` for the six face neighbors (indices below `6`) and
`1` for the twelve edge neighbors. -/
def c19Weight (neighbor : C19Neighbor) : ℝ :=
  if neighbor.val < 6 then 2 else 1

/-- The opposite C19 neighbor, whose offset vector is the negative of the offset of
`neighbor`. -/
def c19Reverse (neighbor : C19Neighbor) : C19Neighbor :=
  ⟨match neighbor.val with
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
    | 6 => 9 | 7 => 8 | 8 => 7 | 9 => 6
    | 10 => 13 | 11 => 12 | 12 => 11 | 13 => 10
    | 14 => 17 | 15 => 16 | 16 => 15 | _ => 14,
    by
      have h := neighbor.isLt
      interval_cases neighbor.val <;> decide⟩

theorem c19_reverse_coord (axis : Fin 3) (neighbor : C19Neighbor) :
    c19Coord axis (c19Reverse neighbor) = -c19Coord axis neighbor := by
  fin_cases axis <;> fin_cases neighbor <;> rfl

theorem c19_reverse_involutive (neighbor : C19Neighbor) :
    c19Reverse (c19Reverse neighbor) = neighbor := by
  fin_cases neighbor <;> rfl

theorem c19_reverse_weight (neighbor : C19Neighbor) :
    c19Weight (c19Reverse neighbor) = c19Weight neighbor := by
  fin_cases neighbor <;> rfl

theorem c19_weight_positive (neighbor : C19Neighbor) :
    0 < c19Weight neighbor := by
  unfold c19Weight
  split <;> norm_num

/-- A C19 lattice on `Site`: a neighbor map for each of the eighteen C19 directions such that
stepping in a direction and then in the reverse direction returns to the starting site. -/
structure C19Lattice (Site : Type) where
  /-- The site reached from `site` by stepping in the given C19 direction. -/
  neighbor : Site → C19Neighbor → Site
  neighbor_reverse : ∀ site direction,
    neighbor (neighbor site direction) (c19Reverse direction) = site

/-- A directed C19 edge, given by its source site and the C19 direction it points in. -/
abbrev C19Edge (Site : Type) := Site × C19Neighbor

/-- The weighted bond of a directed C19 edge: from the source site to its neighbor in the edge's
direction, with weight `c19Weight` of that direction. -/
def c19Bond (geometry : C19Lattice Site) (edge : C19Edge Site) : Bond Site where
  source := edge.1
  target := geometry.neighbor edge.1 edge.2
  weight := c19Weight edge.2

theorem c19_bond_weight_positive (geometry : C19Lattice Site)
    (edge : C19Edge Site) :
    0 < (c19Bond geometry edge).weight :=
  c19_weight_positive edge.2

/-- The reversed directed C19 edge, starting at the target of `edge` and pointing in the reverse
direction. -/
def reverseC19Edge (geometry : C19Lattice Site)
    (edge : C19Edge Site) : C19Edge Site :=
  (geometry.neighbor edge.1 edge.2, c19Reverse edge.2)

theorem c19_reverse_bond_source (geometry : C19Lattice Site)
    (edge : C19Edge Site) :
    (c19Bond geometry (reverseC19Edge geometry edge)).source =
      (c19Bond geometry edge).target := by
  rfl

theorem c19_reverse_bond_target (geometry : C19Lattice Site)
    (edge : C19Edge Site) :
    (c19Bond geometry (reverseC19Edge geometry edge)).target =
      (c19Bond geometry edge).source := by
  exact geometry.neighbor_reverse edge.1 edge.2

theorem c19_reverse_bond_weight (geometry : C19Lattice Site)
    (edge : C19Edge Site) :
    (c19Bond geometry (reverseC19Edge geometry edge)).weight =
      (c19Bond geometry edge).weight := by
  exact c19_reverse_weight edge.2

/-- A site of the periodic cubic lattice of side `L`, given by three coordinates in `ZMod L`. -/
abbrev PeriodicCubicSite (L : ℕ) := Fin 3 → ZMod L

/-- The neighbor of `site` on the periodic cubic lattice of side `L`, obtained by adding the C19
offset vector of `neighbor` coordinatewise modulo `L`. -/
def periodicC19Neighbor (L : ℕ) (site : PeriodicCubicSite L)
    (neighbor : C19Neighbor) : PeriodicCubicSite L :=
  fun axis => site axis + (c19Coord axis neighbor : ℤ)

theorem periodic_c19_neighbor_reverse (L : ℕ)
    (site : PeriodicCubicSite L) (neighbor : C19Neighbor) :
    periodicC19Neighbor L (periodicC19Neighbor L site neighbor)
      (c19Reverse neighbor) = site := by
  funext axis
  simp [periodicC19Neighbor, c19_reverse_coord]

/-- The C19 lattice structure on the periodic cubic lattice of side `L`, with neighbors given by
`periodicC19Neighbor`. -/
def periodicC19Geometry (L : ℕ) : C19Lattice (PeriodicCubicSite L) where
  neighbor := periodicC19Neighbor L
  neighbor_reverse := periodic_c19_neighbor_reverse L

end LeanDirac

namespace LeanDirac.V2

/-- The weighted graph Laplacian on a complex scalar field for a C19 neighbor map. -/
def c19ScalarLaplacian {Site : Type} (geometry : C19Lattice Site)
    (field : Site → ℂ) (site : Site) : ℂ :=
  ∑ direction : C19Neighbor,
    (c19Weight direction : ℂ) * (field site - field (geometry.neighbor site direction))

/-- The scalar massive tangent force for a general C19 neighbor map. -/
def uniformScalarTangentAcceleration {Site : Type}
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℂ :=
  -(massSq : ℂ) * position site - 2 * c19ScalarLaplacian geometry position site

end LeanDirac.V2
