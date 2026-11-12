/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryFrame
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence

-- [TABLET NODE: P4458T1RestrictionFamily]

/-!
# P4458T1RestrictionFamily

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a boundary frame $F$, a restriction family consists of tiles $T_j^s$
and partial functions $h_j^s$, for $j\in\mathbb Z/3$ and $s\in\{-,+\}$.
Each is a tile odometer for $q_{j+1}$ and an actual signed
`BandSubtileOccurrence` of $F.T_0$ in the presentation $F.q$.
For every positive parent it records
$\operatorname{AncestorOdometer}(q_{j+1},F.C_0,T_j^s,F.T_0,h_j^s,F.h_0)$.
Put $P_j=F.q_{j+1}$ for $j\in\mathbb Z/3$,
$w_j=a(P_{j+2},P_{j+1})$, and let $\sigma_+=1$, $\sigma_-=-1$.
For each $j,s$ it records either zero parent curvature, or defined slopes
$p,p_j^s$ of $F.h_0,h_j^s$ with
$p_j^s-p=\sigma_s\tfrac12(w_j+\mathrm i w_j)$ in real coordinates.
The functions are literal restrictions, not independently affinely
normalized copies.
-/
structure P4458T1RestrictionFamily
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus) where
-- BODY
  /-- The six signed supports in the outer tile decomposition. -/
  tiles : Fin 3 → Bool → ProtoTile
  /-- The literal restriction odometers on those six supports. -/
  functions : Fin 3 → Bool → PartialOdometer
  odometers : ∀ j s, TileOdometer (F.q j.succ) (tiles j s) (functions j s)
  occurrences : ∀ j s, BandSubtileOccurrence F.q F.tile j s (tiles j s)
  domain_subset : ∀ j s, (functions j s).domain ⊆ F.odometer.domain
  value_eq : ∀ j s x, x ∈ (functions j s).domain →
    (functions j s).value x = F.odometer.value x
  ancestors : ∀ j s, 0 < (F.q j.succ).1 →
    AncestorOdometer (F.q j.succ) F.outer.1.1
      (tiles j s) F.tile (functions j s) F.odometer
  slopes : ∀ j s, (F.q j.succ).1 = 0 ∨
    ∃ p pj : ℝ × ℝ,
      PartialOdometerSlope F.odometer = some p ∧
      PartialOdometerSlope (functions j s) = some pj ∧
      pj.1 - p.1 = (if s = true then (1 : ℝ) else -1) * (1 / 2) *
        (((BandVectors.2 (F.q ((j + 2).succ)) (F.q ((j + 1).succ))).re : ℤ) -
          ((BandVectors.2 (F.q ((j + 2).succ)) (F.q ((j + 1).succ))).im : ℤ)) ∧
      pj.2 - p.2 = (if s = true then (1 : ℝ) else -1) * (1 / 2) *
        (((BandVectors.2 (F.q ((j + 2).succ)) (F.q ((j + 1).succ))).im : ℤ) +
          ((BandVectors.2 (F.q ((j + 2).succ)) (F.q ((j + 1).succ))).re : ℤ))

end ApollonianSuperharmonic

end
