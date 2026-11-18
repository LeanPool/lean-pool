/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices

-- [TABLET NODE: ExceptionalConnectorSegments]

/-!
# ExceptionalConnectorSegments

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $O\subseteq A\cap B$.  Let $Q_2,Q_3$ be labelled child occurrences
contained in $A$, and let $S_3,S_2$ be their respectively labelled child
partners contained in $B$.  Thus $(Q_2,S_3)$ is the first labelled child
pair and $(Q_3,S_2)$ is the second.  For selected interface points $p_1,p_2$,
an *exceptional connector segmentation* consists of attachment vertices
$a,b$ and three oriented simple vertex lists
$$
 p_1\xrightarrow{\ Q_2\text{--}S_3\ }a,\qquad
 a\xrightarrow{\ (A\setminus O)\text{--}O\ }b,\qquad
 b\xrightarrow{\ Q_3\text{--}S_2\ }p_2.
$$
Every vertex of each list belongs to the displayed pair of footprints and
every consecutive edge has an actual supporting cell in both displayed
prototiles.  Their ordered walk is obtained by concatenating the left list,
the tail of the middle list, and the tail of the right list; every vertex
and edge of this walk is also retained in the common footprint of
$A\setminus O$ and $B$.  The point $a$
is the unique common boundary vertex of $Q_2,S_3,O$, and $b$ is the unique
common boundary vertex of $Q_3,S_2,O$; these are therefore the two uniquely
labelled cuts in the ordered walk.  When $O$ is empty they coincide at its
anchor.

The data also retain a loop-erasure as a sublist of this ordered walk.  This connector
has no repeated vertices, has endpoints $p_1,p_2$, lies in
$\operatorname{foot}(A\setminus O)\cap\operatorname{foot}(B)$ with actual common-footprint edge
support,
and every retained vertex occurs in the ordered walk.  Thus loop erasure
does not replace or forget the three segmented paths.  Its vertices retain
the corresponding three-piece support union, and the data retain two
distinct common vertices of the modified $A$ and $B$ footprints independently
of whether the selected connector is constant.
-/
structure ExceptionalConnectorSegments
    (A B O Q2 S3 Q3 S2 : ProtoTile) (p1 p2 : GaussianInt) where
-- BODY
  precursor_in_left : O.cells ⊆ A.cells
  precursor_in_right : O.cells ⊆ B.cells
  first_left_child : Q2.cells ⊆ A.cells
  first_right_child : S3.cells ⊆ B.cells
  second_left_child : Q3.cells ⊆ A.cells
  second_right_child : S2.cells ⊆ B.cells
  /-- The first attachment of the precursor to the labelled child interfaces. -/
  a : GaussianInt
  /-- The second attachment of the precursor to the labelled child interfaces. -/
  b : GaussianInt
  /-- The simple path from the first selected point to the first attachment. -/
  left : List GaussianInt
  /-- The simple precursor-boundary path between the two attachments. -/
  middle : List GaussianInt
  /-- The simple path from the second attachment to the second selected point. -/
  right : List GaussianInt
  /-- The ordered concatenation of the three retained path segments. -/
  walk : List GaussianInt
  /-- A loop erasure of the segmented walk with the same selected endpoints. -/
  connector : List GaussianInt
  left_nodup : left.Nodup
  middle_nodup : middle.Nodup
  right_nodup : right.Nodup
  left_head : left.head? = some p1
  left_last : left.getLast? = some a
  middle_head : middle.head? = some a
  middle_last : middle.getLast? = some b
  right_head : right.head? = some b
  right_last : right.getLast? = some p2
  walk_order : walk = left ++ middle.tail ++ right.tail
  walk_raw : ∀ x ∈ walk,
    x ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B
  walk_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    walk = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges (TileCellComplement A O) ∩ FootprintEdges B
  left_vertices : ∀ x ∈ left,
    x ∈ FootprintVertices Q2 ∩ FootprintVertices S3
  middle_vertices : ∀ x ∈ middle,
    x ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices O
  right_vertices : ∀ x ∈ right,
    x ∈ FootprintVertices Q3 ∩ FootprintVertices S2
  left_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    left = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges Q2 ∩ FootprintEdges S3
  middle_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    middle = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges (TileCellComplement A O) ∩ FootprintEdges O
  right_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    right = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges Q3 ∩ FootprintEdges S2
  first_cut_unique : ∀ x : GaussianInt,
    x ∈ BoundaryFootprintVertices Q2 ∧
      x ∈ BoundaryFootprintVertices S3 ∧
      x ∈ BoundaryFootprintVertices O ↔ x = a
  second_cut_unique : ∀ x : GaussianInt,
    x ∈ BoundaryFootprintVertices Q3 ∧
      x ∈ BoundaryFootprintVertices S2 ∧
      x ∈ BoundaryFootprintVertices O ↔ x = b
  empty_cut : O.cells = ∅ → a = b ∧ a = O.anchor
  connector_nodup : connector.Nodup
  connector_head : connector.head? = some p1
  connector_last : connector.getLast? = some p2
  connector_raw : ∀ x ∈ connector,
    x ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B
  connector_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    connector = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges (TileCellComplement A O) ∩ FootprintEdges B
  connector_from_walk : connector.Sublist walk
  connector_support : ∀ x ∈ connector,
    x ∈ (FootprintVertices Q2 ∩ FootprintVertices S3) ∪
      FootprintVertices O ∪
      (FootprintVertices Q3 ∩ FootprintVertices S2)
  common_vertices : ∃ x y : GaussianInt, x ≠ y ∧
    x ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B ∧
    y ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B

end ApollonianSuperharmonic

end
