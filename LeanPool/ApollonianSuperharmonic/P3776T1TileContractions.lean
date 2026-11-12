/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore

-- [TABLET NODE: P3776T1TileContractions]

/-!
# P3776T1TileContractions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A contraction family for $P$ consists of a point $c_a\in I(T_a)$ and
a map $H_a:[0,1]\times I(T_a)\to I(T_a)$, continuous on this domain,
with $H_a(0,z)=c_a$ and $H_a(1,z)=z$. The ambiently defined functions
outside these domains have no prescribed behavior. The centers and
homotopies commute with lattice translation:
$c_{u+a}=c_a+[u]$ and $H_{u+a}(t,z+[u])=H_a(t,z)+[u]$.
-/
structure P3776T1TileContractions {ι : Type} (P : PeriodicTileCore ι) where
-- BODY
  /-- The equivariantly selected contraction center of each tile realization. -/
  center : ι → (Real × Real)
  /-- The equivariant homotopy from the selected center to the identity on each tile. -/
  homotopy : ι → Real → (Real × Real) → (Real × Real)
  center_mem : ∀ a, center a ∈ TileRealization (P.tile a)
  continuous : ∀ a, ContinuousOn (fun x : Real × (Real × Real) => homotopy a x.1 x.2)
    (Set.Icc (0 : Real) 1 ×ˢ TileRealization (P.tile a))
  zero : ∀ a z, z ∈ TileRealization (P.tile a) → homotopy a 0 z = center a
  one : ∀ a z, z ∈ TileRealization (P.tile a) → homotopy a 1 z = z
  support : ∀ a t, t ∈ Set.Icc (0 : Real) 1 → ∀ z,
    z ∈ TileRealization (P.tile a) → homotopy a t z ∈ TileRealization (P.tile a)
  center_periodic : ∀ u : P.lattice, ∀ a,
    center (P.shift u a) = center a + GaussianRealPoint u
  homotopy_periodic : ∀ u : P.lattice, ∀ a t z,
    t ∈ Set.Icc (0 : Real) 1 → z ∈ TileRealization (P.tile a) →
    homotopy (P.shift u a) t (z + GaussianRealPoint u) =
      homotopy a t z + GaussianRealPoint u

end ApollonianSuperharmonic

end
