/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: P4261T2LiteralInterface]

/-!
# P4261T2LiteralInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For positive band circles $D,C$, literal supports $T,T'$ and functions
$h,h'$, a literal opposing interface consists of an orientation, a base,
two literal endpoint tiles $R^-,R^+$, forward and reverse tile lists and
function lists, and two functions $h^-,h^+$. The forward list
`OdometerStringRespect`s the string from $R^-$ to $R^+$ and the
reverse list respects the string from $R^+$ to $R^-$ on that same base.
Their head/last functions are respectively $(h^-,h^+)$ and $(h^+,h^-)$.
It also contains a repetition-free vertex list $P$ of length at least two.
Its vertex set is exactly $\operatorname{foot}(T)\cap\operatorname{foot}(T')$;
its consecutive unordered pairs are exactly $E(T)\cap E(T')$.
For each consecutive pair $x,y$ there are literal zipped entries $(U,g)$,
$(V,k)$ in the retained forward and reverse lists such that $\{x,y\}$
is an actual footprint edge of both supports, and
`AncestorOdometer` holds for $(U,g)$ in $(T,h)$ and for $(V,k)$
in $(T',h')$, with coordinates $D,C$. In particular these certificates
retain the domain inclusions and the actual restriction value equations.
-/
structure P4261T2LiteralInterface (D C : BandCircle)
    (T T' : ProtoTile) (h h' : PartialOdometer) where
-- BODY
  /-- The selected triangular completion used by both oriented tile strings. -/
  orientation : Bool
  /-- The common base tile of the regular family containing both strings. -/
  base : ProtoTile
  /-- The literal initial endpoint tile of the forward string. -/
  minus : ProtoTile
  /-- The literal terminal endpoint tile of the forward string. -/
  plus : ProtoTile
  /-- The forward ordered list of tiles along the complete interface. -/
  tiles : List ProtoTile
  /-- The reverse oriented tile list on the same regular-family base. -/
  reverseTiles : List ProtoTile
  /-- The literal partial odometers assigned to the forward tile list. -/
  functions : List PartialOdometer
  /-- The literal partial odometers assigned to the reverse tile list. -/
  reverseFunctions : List PartialOdometer
  /-- The partial odometer at the initial endpoint. -/
  hminus : PartialOdometer
  /-- The partial odometer at the terminal endpoint. -/
  hplus : PartialOdometer
  /-- The nontrivial simple lattice path covering the complete common interface. -/
  path : List GaussianInt
  forward : OdometerStringRespect D orientation base minus plus tiles functions
  backward : OdometerStringRespect D orientation base plus minus reverseTiles reverseFunctions
  head_forward : functions.head? = some hminus
  last_forward : functions.getLast? = some hplus
  head_backward : reverseFunctions.head? = some hplus
  last_backward : reverseFunctions.getLast? = some hminus
  nodup : path.Nodup
  length : 2 ≤ path.length
  vertices : FootprintVertices T ∩ FootprintVertices T' = (path.toFinset : Set GaussianInt)
  edges : ∀ edge, edge ∈ FootprintEdges T ∩ FootprintEdges T' ↔
    ∃ x y : GaussianInt, ∃ pre post : List GaussianInt,
      path = pre ++ x :: y :: post ∧ edge = {x, y}
  restrictions : ∀ x y : GaussianInt, ∀ pre post : List GaussianInt,
    path = pre ++ x :: y :: post →
    ∃ (U V : ProtoTile) (g k : PartialOdometer),
      (U, g) ∈ tiles.zip functions ∧
      (V, k) ∈ reverseTiles.zip reverseFunctions ∧
      {x, y} ∈ FootprintEdges U ∩ FootprintEdges V ∧
      AncestorOdometer D.1.1 C.1.1 U T g h ∧
      AncestorOdometer D.1.1 C.1.1 V T' k h'

end ApollonianSuperharmonic

end
