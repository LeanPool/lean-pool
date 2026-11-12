/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorTile
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: AncestorOdometer]

/-!
# AncestorOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $h'$ be a tile odometer on $T'$.  If $T$ is an
`AncestorTile` of $T'$, the ancestor restriction of $h'$ to $T$
is the partial odometer $h$ whose domain is exactly $\operatorname{foot}(T)$, whose
domain is contained in that of $h'$, and whose values there equal those of
$h'$.  The predicate *ancestor odometer* records these data, but does
not assume that $h$ is already a tile odometer; that is the content of the
ancestor-restriction lemma.  The reflexive ancestor gives the restriction
to the whole tile.
-/
def AncestorOdometer (C C' : CircleCoordinates) (T T' : ProtoTile)
    (h h' : PartialOdometer) : Prop :=
-- BODY
  TileOdometer C' T' h' ∧ AncestorTile C C' T T' ∧
    (h.domain : Set GaussianInt) = FootprintVertices T ∧
    h.domain ⊆ h'.domain ∧
    ∀ x, x ∈ h.domain → h.value x = h'.value x

end ApollonianSuperharmonic

end
