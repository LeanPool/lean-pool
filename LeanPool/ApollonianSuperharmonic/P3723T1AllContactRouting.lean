/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1ContactPorts
public import LeanPool.ApollonianSuperharmonic.P3723T1PolygonalParameterization

-- [TABLET NODE: P3723T1AllContactRouting]

/-!
# P3723T1AllContactRouting

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a `PeriodicTileComplex` $P$, an all-contact routing
extends `P3723T1ContactPorts` by half-arc sets $J_{ab}$
and full-arc sets $A_{ab}$. Both sets are empty on noncontacts.
For every present port $q_{ab}$, $J_{ab}$ is interval-homeomorphic
with named endpoints $x_a,q_{ab}$ and is contained in
$\operatorname{int}I_a\cup\{q_{ab}\}$. Distinct contact half-arcs
incident to $a$ meet exactly in $\{x_a\}$.

Full arcs are symmetric and, on present ports, satisfy
$A_{ab}=J_{ab}\cup J_{ba}$. For every genuine contact they are
interval-homeomorphic with endpoints $x_a,x_b$. Distinct unordered
contact pairs satisfy the exact intersection law
$A_{ab}\cap A_{cd}=x(\{a,b\}\cap\{c,d\})$.
For every compact plane set $K$, the ordered contacts whose full arcs
meet $K$ form a finite set. Every half-arc at a present port and every
full contact arc also retain a continuous injective plane-valued
parametrization with that exact range, the stated endpoint values,
and a `P3723T1PolygonalParameterization` certificate.
Half- and full-arc sets translate equivariantly under all periods.
Here $I_a=\operatorname{TileRealization}(T_a)$ as in
`TileRealization`. These data retain
arcs for nonprescribed genuine contacts as public fields; no contact
classification or facial-region data are included.
-/
structure P3723T1AllContactRouting {ι : Type}
    (P : PeriodicTileComplex ι) extends P3723T1ContactPorts P where
-- BODY
  /-- The tile-interior half arc from a tile position to a genuine-contact port. -/
  halfArc : ι → ι → Set (Real × Real)
  /-- The full arc joining the positions of two genuinely contacting tiles. -/
  edgeArc : ι → ι → Set (Real × Real)
  noncontact_has_no_halfArc : ∀ a b, ¬ P3723T1EdgeContact P a b → halfArc a b = ∅
  noncontact_has_no_edgeArc : ∀ a b, ¬ P3723T1EdgeContact P a b → edgeArc a b = ∅
  halfArc_homeomorph : ∀ a b p, port a b = some p →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ halfArc a b,
      ((h ⟨0, by norm_num⟩ : halfArc a b) : Real × Real) =
          position a ∧
      ((h ⟨1, by norm_num⟩ : halfArc a b) : Real × Real) = p
  halfArc_supported : ∀ a b p, port a b = some p →
    halfArc a b ⊆ interior (TileRealization (P.tile a)) ∪ {p}
  incident_halfArc_intersections : ∀ a b c,
    P3723T1EdgeContact P a b → P3723T1EdgeContact P a c → b ≠ c →
      halfArc a b ∩ halfArc a c = {position a}
  edgeArc_symmetric : ∀ a b, edgeArc a b = edgeArc b a
  edgeArc_from_halfArcs : ∀ a b p, port a b = some p →
    edgeArc a b = halfArc a b ∪ halfArc b a
  edgeArc_homeomorph : ∀ a b, P3723T1EdgeContact P a b →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ edgeArc a b,
      ((h ⟨0, by norm_num⟩ : edgeArc a b) : Real × Real) =
          position a ∧
      ((h ⟨1, by norm_num⟩ : edgeArc a b) : Real × Real) =
          position b
  edgeArc_intersections : ∀ a b c d,
    P3723T1EdgeContact P a b → P3723T1EdgeContact P c d →
    ({a, b} : Set ι) ≠ ({c, d} : Set ι) →
      edgeArc a b ∩ edgeArc c d =
        position '' (({a, b} : Set ι) ∩ ({c, d} : Set ι))
  compact_local_finiteness : ∀ K : Set (Real × Real), IsCompact K →
    Set.Finite {e : ι × ι |
      P3723T1EdgeContact P e.1 e.2 ∧ (edgeArc e.1 e.2 ∩ K).Nonempty}
  halfArc_parameterization : ∀ a b p, port a b = some p →
    ∃ g : Set.Icc (0 : Real) 1 → Real × Real,
      Continuous g ∧ Function.Injective g ∧ Set.range g = halfArc a b ∧
      g ⟨0, by norm_num⟩ = position a ∧ g ⟨1, by norm_num⟩ = p ∧
      Nonempty (P3723T1PolygonalParameterization g)
  edgeArc_parameterization : ∀ a b, P3723T1EdgeContact P a b →
    ∃ g : Set.Icc (0 : Real) 1 → Real × Real,
      Continuous g ∧ Function.Injective g ∧ Set.range g = edgeArc a b ∧
      g ⟨0, by norm_num⟩ = position a ∧ g ⟨1, by norm_num⟩ = position b ∧
      Nonempty (P3723T1PolygonalParameterization g)
  halfArc_periodic : ∀ u : P.lattice, ∀ a b,
    halfArc (P.shift u a) (P.shift u b) =
      (fun p => p + GaussianRealPoint u) '' halfArc a b
  edgeArc_periodic : ∀ u : P.lattice, ∀ a b,
    edgeArc (P.shift u a) (P.shift u b) =
      (fun p => p + GaussianRealPoint u) '' edgeArc a b

end ApollonianSuperharmonic

end
