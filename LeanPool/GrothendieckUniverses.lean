/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckUniverses.Basic
public import LeanPool.GrothendieckUniverses.VonNeumann
public import LeanPool.GrothendieckUniverses.Classification
public import LeanPool.GrothendieckUniverses.Order

/-!
# Grothendieck universes

Source: url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/1783
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.GrothendieckUniverses.isGrothendieckUniverse_vonNeumann`,
  `LeanPool.GrothendieckUniverses.isGrothendieckUniverse_vonNeumann_omega0`,
  `LeanPool.GrothendieckUniverses.isGrothendieckUniverse_iff`,
  `LeanPool.GrothendieckUniverses.IsGrothendieckUniverse.isInaccessible_card`,
  `LeanPool.GrothendieckUniverses.IsGrothendieckUniverse.eq_vonNeumann_card`,
  `LeanPool.GrothendieckUniverses.IsGrothendieckUniverse.mem_or_eq_or_mem`,
  `LeanPool.GrothendieckUniverses.exists_least_isGrothendieckUniverse`,
  `LeanPool.GrothendieckUniverses.forall_exists_isGrothendieckUniverse_iff`
Tags: grothendieck-universes, inaccessible-cardinals, von-neumann-hierarchy, zfc
MSC: 03E10, 03E55, 18A15
-/

/-!
## Overview

Root module of the formalisation of the roadmap *Grothendieck universes* (proposed to Tau Ceti in
TauCetiProject/TauCetiRoadmap#1783, not merged), on Mathlib's carriers (`ZFSet`, `ZFSet.rank`,
`ZFSet.card`, the von Neumann hierarchy `ZFSet.vonNeumann` and `Cardinal.IsInaccessible`).
Target numbers such as 1.2 refer to that roadmap.

* `Basic`: the predicate `IsGrothendieckUniverse` and its closure properties (0.1, 0.2).
* `VonNeumann`: `V_ ω` and `V_ κ.ord`, `κ` inaccessible, are universes (1.1).
* `Classification`: Williams's theorem, the cardinal of a universe and Kruse's criterion
  (0.2, 1.2, 1.3).
* `Order`: universes are totally ordered, least universes, intersections, and the universe
  axiom (2.1, 2.2, 2.3).

All headline targets of the roadmap are formalised.

## References

* P. Gabriel, « Des catégories abéliennes », Bull. Soc. Math. France 90 (1962), 323–448.
* A. H. Kruse, « Grothendieck universes and the super-complete models of Shepherdson »,
  Compositio Math. 17 (1965), 96–101.
* N. H. Williams, « On Grothendieck universes », Compositio Math. 21 (1969), 1–3.
-/
