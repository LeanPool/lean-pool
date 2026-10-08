/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.BoundedMeasurableDomain
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import Mathlib.Topology.Sets.Opens

/-!
# Coarse-graining support: Support.Geometry.BoundedConvexDomain

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Open bounded convex domain adapters

This module keeps the repository's existing set-based predicate
`IsOpenBoundedConvexDomain U` as the domain carrier.  Given a nonempty carrier,
it supplies the positive-volume bounded measurable domain and open-set adapters
needed by normalized and Sobolev constructions.
-/

namespace HCPolySupport

open TopologicalSpace

namespace IsOpenBoundedConvexDomain

/-- A nonempty open bounded convex set is a bounded measurable domain of
strictly positive Lebesgue volume. -/
@[expose]
noncomputable def toBoundedMeasurableDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    BoundedMeasurableDomain d where
  carrier := U
  measurableSet := hU.isOpen.measurableSet
  isBoundedDomain := hU.isBoundedDomain
  volume_pos := IsOpen.measure_pos MeasureTheory.volume hU.isOpen hne

@[simp] theorem coe_toBoundedMeasurableDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    (hU.toBoundedMeasurableDomain hne : Set (Vec d)) = U :=
  rfl

/-- The open-set carrier associated with an open bounded convex domain. -/
@[expose]
def toOpens {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    Opens (Vec d) :=
  ⟨U, hU.isOpen⟩

@[simp] theorem coe_toOpens {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    (hU.toOpens : Set (Vec d)) = U :=
  rfl

end IsOpenBoundedConvexDomain

end HCPolySupport
