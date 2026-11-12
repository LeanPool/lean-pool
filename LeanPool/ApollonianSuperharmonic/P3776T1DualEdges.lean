/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3776T1WalkMap
public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P3776T1DualEdges]

/-!
# P3776T1DualEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a core $P$, dual-edge data consist of an unordered-edge port $m_{ab}$
and paths $b_{f,ab}:[0,1]\to I(T_a)\cap I(T_b)$ for every incident
face $f$ of $ab$. The paths are continuous, start at $[\rho(f)]$, end at
$m_{ab}$, and are unchanged by exchanging $a,b$. For the other incident
face $g$ they are exactly
$b_{f,ab}(t)=\operatorname{P3776\_T1\_WalkMap}(P.\mathrm{facePath}(f,g),t/2)$.
The port belongs to both tile realizations, is symmetric in $a,b$, and
all ports and half paths commute with lattice translations. Fields on
nonedges or nonincident faces are unrestricted.
-/
structure P3776T1DualEdges {ι : Type} (P : PeriodicTileCore ι) where
-- BODY
  /-- The symmetric port on each common tile interface. -/
  port : ι → ι → (Real × Real)
  /-- The path from an incident face point to the edge port. -/
  half : P.plane.Face → ι → ι → Set.Icc (0 : Real) 1 → (Real × Real)
  port_symmetric : ∀ a b, P.plane.adjacent a b → port a b = port b a
  port_support : ∀ a b, P.plane.adjacent a b →
    port a b ∈ TileRealization (P.tile a) ∩ TileRealization (P.tile b)
  port_periodic : ∀ u : P.lattice, ∀ a b, P.plane.adjacent a b →
    port (P.shift u a) (P.shift u b) = port a b + GaussianRealPoint u
  half_spec : ∀ f a b, P.plane.adjacent a b →
    (∃ i, P.plane.faceVertex f i = a) →
    (∃ i, P.plane.faceVertex f i = b) →
    Continuous (half f a b) ∧
    half f a b ⟨0, by norm_num⟩ = GaussianRealPoint (P.rho f) ∧
    half f a b ⟨1, by norm_num⟩ = port a b ∧
    (∀ t, half f a b t ∈ TileRealization (P.tile a) ∩ TileRealization (P.tile b)) ∧
    (∀ t, half f a b t = half f b a t) ∧
    ∃ g, g ≠ f ∧ (∃ i, P.plane.faceVertex g i = a) ∧
      (∃ i, P.plane.faceVertex g i = b) ∧
      ∀ t, half f a b t = P3776T1WalkMap (P.facePath f g)
        ⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  half_periodic : ∀ u : P.lattice, ∀ f a b,
    P.plane.adjacent a b → (∃ i, P.plane.faceVertex f i = a) →
    (∃ i, P.plane.faceVertex f i = b) → ∀ t,
    half (P.faceShift u f) (P.shift u a) (P.shift u b) t =
      half f a b t + GaussianRealPoint u

end ApollonianSuperharmonic

end
