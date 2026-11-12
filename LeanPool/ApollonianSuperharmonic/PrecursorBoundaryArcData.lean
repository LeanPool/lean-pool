/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: PrecursorBoundaryArcData]

/-!
# PrecursorBoundaryArcData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $D^+,D^-,O,O'$ be prototiles, where $O$ and $O'$ are the two
labelled occurrences of one precursor: they have the same cell set and,
when that set is empty, the same anchor.  Let $(Q_2,S_3)$ and
$(Q_3,S_2)$ be its two labelled attaching pairs.  Thus
$(Q_2,S_3,O)$ and $(Q_3,S_2,O)$ are `TouchingTriple`s, the
$Q_2,Q_3$ cell sets are contained in $D^+$, and the $S_3,S_2$ cell sets
are contained in $D^-$.  A *precursor
boundary-arc certificate* consists of two attachment vertices $a,b$ such
that $a$ is the unique common boundary vertex of $Q_2,S_3,O$ and $b$ is
the unique common boundary vertex of $Q_3,S_2,O$, together with one of the
following two alternatives.

If $O$ has a cell, the certificate contains simple vertex lists $K^+$ and
$K^-$, oriented from $a$ to $b$ and from $b$ to $a$, whose vertex sets are
exactly
$$
 \partial\operatorname{foot}(D^+)\cap\partial\operatorname{foot}(O),\qquad
 \partial\operatorname{foot}(D^-)\cap\partial\operatorname{foot}(O),
$$
and whose consecutive edges belong to the corresponding common boundary
edge sets.  These two arcs cover the entire boundary footprint of $O$,
their common vertices are exactly $\{a,b\}$, half-turn about $\operatorname{cent}(O)$
sends $a$ to $b$, and that half-turn sends the vertex set of $K^+$ exactly
onto the vertex set of $K^-$.  The lists have no repeated vertices.

If $O$ has no cells, then $a=b$ is the common anchor of $O$ and $O'$, and
both boundary footprints are exactly the singleton $\{a\}$.
-/
structure PrecursorBoundaryArcData
    (Dplus Dminus O O' Q2 S3 Q3 S2 : ProtoTile) where
-- BODY
  precursor_cells : O.cells = O'.cells
  precursor_anchor : O.cells = ∅ → O.anchor = O'.anchor
  first_touching : TouchingTriple Q2 S3 O
  second_touching : TouchingTriple Q3 S2 O
  first_plus_child : Q2.cells ⊆ Dplus.cells
  first_minus_child : S3.cells ⊆ Dminus.cells
  second_plus_child : Q3.cells ⊆ Dplus.cells
  second_minus_child : S2.cells ⊆ Dminus.cells
  /-- The unique attachment vertex of the first labelled child pair to the precursor. -/
  a : GaussianInt
  /-- The unique attachment vertex of the second labelled child pair to the precursor. -/
  b : GaussianInt
  first_transition : ∀ x : GaussianInt,
    x ∈ BoundaryFootprintVertices Q2 ∧
      x ∈ BoundaryFootprintVertices S3 ∧
      x ∈ BoundaryFootprintVertices O ↔ x = a
  second_transition : ∀ x : GaussianInt,
    x ∈ BoundaryFootprintVertices Q3 ∧
      x ∈ BoundaryFootprintVertices S2 ∧
      x ∈ BoundaryFootprintVertices O ↔ x = b
  branch :
    (O.cells.Nonempty ∧
      ∃ plusArc minusArc : List GaussianInt,
        plusArc.Nodup ∧ minusArc.Nodup ∧
        plusArc.head? = some a ∧ plusArc.getLast? = some b ∧
        minusArc.head? = some b ∧ minusArc.getLast? = some a ∧
        (plusArc.toFinset : Set GaussianInt) =
          BoundaryFootprintVertices Dplus ∩ BoundaryFootprintVertices O ∧
        (minusArc.toFinset : Set GaussianInt) =
          BoundaryFootprintVertices Dminus ∩ BoundaryFootprintVertices O ∧
        (∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
          plusArc = l1 ++ x :: y :: l2 →
            {x, y} ∈ BoundaryFootprintEdges Dplus ∩
              BoundaryFootprintEdges O) ∧
        (∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
          minusArc = l1 ++ x :: y :: l2 →
            {x, y} ∈ BoundaryFootprintEdges Dminus ∩
              BoundaryFootprintEdges O) ∧
        BoundaryFootprintVertices O =
          (plusArc.toFinset : Set GaussianInt) ∪
            (minusArc.toFinset : Set GaussianInt) ∧
        (plusArc.toFinset : Set GaussianInt) ∩
            (minusArc.toFinset : Set GaussianInt) = {a, b} ∧
        GaussianRealPoint b =
          (2 * (TileCentroid O).1 - (GaussianRealPoint a).1,
            2 * (TileCentroid O).2 - (GaussianRealPoint a).2) ∧
        (fun z : GaussianInt =>
            (2 * (TileCentroid O).1 - (GaussianRealPoint z).1,
              2 * (TileCentroid O).2 - (GaussianRealPoint z).2)) ''
              (plusArc.toFinset : Set GaussianInt) =
          GaussianRealPoint '' (minusArc.toFinset : Set GaussianInt)) ∨
    (O.cells = ∅ ∧ a = b ∧ a = O.anchor ∧ a = O'.anchor ∧
      BoundaryFootprintVertices O = {a} ∧
      BoundaryFootprintVertices O' = {a})

end ApollonianSuperharmonic

end
