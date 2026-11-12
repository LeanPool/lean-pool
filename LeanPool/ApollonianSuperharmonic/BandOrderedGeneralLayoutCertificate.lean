/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedCoreCertificate
public import LeanPool.ApollonianSuperharmonic.ExceptionalConnectorSegments
public import LeanPool.ApollonianSuperharmonic.PrecursorBoundaryArcData
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.TilingLattice

-- [TABLET NODE: BandOrderedGeneralLayoutCertificate]

/-!
# BandOrderedGeneralLayoutCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an ordered general configuration
$q=(C_0,C_1,C_2,C_3)$, a band circle represented by $C_0$, and a band
prototile $T_0$, an *ordered-general layout certificate* consists of
the following data, with every equality referring to the actual labelled
occurrences rather than merely to isomorphic copies.

It contains the outer family $P_i^\pm$ decomposing $T_0$, and two families
$Q_i^\pm,S_i^\pm$ decomposing $P_1^+$ and $P_1^-$ for the first predecessor
quadruple.  It contains a precursor $O$ equal to $Q_4^-$ in the chosen
indexing, with the same cells as $S_4^+$ and the same anchor when those
cells are empty.  Each of the six outer parent occurrences is retained as
a `LatticeTile` and as a `QuarterTurnSymmetric` tile.  The
two actual precursor complements
$P_1^+\setminus O$ and $P_1^-\setminus O$ are also retained as lattice
tiles; these are the smaller-T1 facts used when an original $P_1^+$
occurrence is restored from the modified one.  It records
$$
 u=v_{01},\qquad v=v_{02},\qquad
 L=\mathbb Zu+\mathbb Zv=i\Lambda_{C_0},
$$
the membership and unique-coordinate assertions for the incoming basis
$v_{10},v_{20}$ of the actual `TilingLattice`, the unique integral
coordinates in the layout basis $u,v$, and a complete $L$-coset
representative set $R$ of cardinality $c_0$.

The certificate further contains the actual
`BandUnmodifiedCoreCertificate`, including the $I_1,I_2$ selections
on the indicated $Q$--$S$ child interfaces and the $I_3$ selection on the
$Q_2^+$--$P_2^+$ child interface.  It retains the four exact
touching triples of the double decomposition and the two precursor
touching triples which join those selected interfaces through $O$; thus
their complete pairwise paths and common points remain available to later
label-sensitive arguments.  The certificate retains a
`PrecursorBoundaryArcData`: in the positive-area case its two
complement-contact arcs cover $\partial O$, are exchanged by half-turn, and
meet exactly at the two labelled precursor attachments; in the curvature-zero
case the two attachments coincide at the exact common anchor of
$Q_4^-=S_4^+$.  In the latter case it also records explicitly that the
precursor circle has curvature zero.

It also retains an `ExceptionalConnectorSegments` object containing,
in order, the actual $Q_2^+$--$S_3^-$ segment from $I_1$ to the first
attachment, the $(P_1^+\setminus O)$--$O$ segment between the attachments,
and the $Q_3^+$--$S_2^-$ segment from the second attachment to $I_2$.  The
two touching triples identify the cuts uniquely, and the segmented walk
retains actual common-edge support on each of its three pieces.  Its stored
loop-erasure is the certificate's legacy exceptional connector from the
selected $I_1$ point to the selected $I_2$ point, rather than merely an
unrelated path through the subsequently constructed periodic complex.
Separate fields record its two endpoints,
the membership of every vertex in
$\operatorname{foot}(P_1^+\setminus O)\cap\operatorname{foot}(P_1^-)$, actual common-footprint
support
for every consecutive edge, and the vertex support
$$
 (\operatorname{foot}(Q_2^+)\cap\operatorname{foot}(S_3^-))\cup\operatorname{foot}(O)\cup
 (\operatorname{foot}(Q_3^+)\cap\operatorname{foot}(S_2^-)).
$$
The connector has no repeated vertices, but it may be constant if its two
selected endpoints coincide.  Writing
$(A,B,C,D,E,F)=(P_1^+,P_1^-,P_2^+,P_2^-,P_3^+,P_3^-)$, it also retains
the eight translated outer touching triples
$$
\begin{gathered}
 (A,B_{0,1},E_{0,1}),\ (A,B_{0,1},F),
 (A,B_{1,1},C_{1,1}),\ (A,B_{1,1},D),\\
 (A,C_{1,1},E_{0,1}),\ (B,D_{-1,-1},F_{0,-1}),
 (C,D_{-1,0},E_{-1,0}),\ (C,D_{-1,0},F),
\end{gathered}
$$
as actual `TouchingTriple` data rather than discarding them after
the weak periodic core is constructed.  It also contains the independently
proved six-orbit area identity; and unique indexed membership for the
modified family obtained by replacing $P_1^+$ with $P_1^+\setminus O$.
Finally it contains the actual `PeriodicTileComplex` for this
modified family, identifies its lattice with $L$, its tile at every
$(X,m,n)$ with `ModifiedSubtileOccurrenceInterpretation`, its
selected point on every labelled face with the corresponding selected point
of the unmodified core, its combinatorial adjacency relation with the eighteen rows of
`AllowedSubtileIncidence` (without classifying isolated common
footprint vertices as graph edges), and its faces and face representatives
with the complete twelve-row `SixSubtileFaceVertices` ledger.  At
this stage the complex records only actual common-edge support on prescribed
edges and the selected contained face-to-face walks; it does not assert
that these are the complete raw interfaces.  It
also retains the translated isolated-precursor conclusion: every lattice
cell incident to a footprint vertex of $O_{m,n}$ belongs to the
corresponding original $A_{m,n}$ or $B_{m,n}$ occurrence.  This is the
local datum needed to compare original and modified interfaces after the
periodic complex has been constructed.
No disk, area, or complement conclusion about the outer tile $T_0$ is part
of this certificate.
-/
structure BandOrderedGeneralLayoutCertificate
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile) where
-- BODY
  child_eq : q 0 = C₀.1.1
  /-- The six signed parent occurrences decomposing the outer tile. -/
  P : Fin 3 → Bool → ProtoTile
  /-- The six signed children decomposing the positive first-parent occurrence. -/
  Q : Fin 3 → Bool → ProtoTile
  /-- The six signed children decomposing the negative first-parent occurrence. -/
  S : Fin 3 → Bool → ProtoTile
  /-- The literal common precursor selected from the two inner decompositions. -/
  O : ProtoTile
  outer_occurrence : ∀ i s, BandSubtileOccurrence q T i s (P i s)
  outer_union : ∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells
  parent_lattice : ∀ i s, LatticeTile (P i s)
  parent_quarter_turn : ∀ i s, QuarterTurnSymmetric (P i s)
  plus_occurrence : ∀ i s,
    BandSubtileOccurrence cfg.firstPredecessor (P 0 true) i s (Q i s)
  plus_union : ∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells
  minus_occurrence : ∀ i s,
    BandSubtileOccurrence cfg.firstPredecessor (P 0 false) i s (S i s)
  minus_union : ∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells
  precursor_eq : O = Q 0 false
  precursor_cells : O.cells = (S 0 true).cells
  precursor_anchor : O.cells = ∅ → O.anchor = (S 0 true).anchor
  precursor_complement_lattice :
    LatticeTile (TileCellComplement (P 0 true) O) ∧
      LatticeTile (TileCellComplement (P 0 false) O)
  /-- The first period vector of the six-type layout. -/
  u : GaussianInt
  /-- The second period vector of the six-type layout. -/
  v : GaussianInt
  period_u : u = BandVectors.1 (q 0) (q 1)
  period_v : v = BandVectors.1 (q 0) (q 2)
  /-- The additive period lattice generated by the two layout vectors. -/
  L : AddSubgroup GaussianInt
  lattice_eq : L = AddSubgroup.closure ({u, v} : Set GaussianInt)
  incoming_mem_first : BandVectors.1 (q 1) (q 0) ∈ TilingLattice C₀
  incoming_mem_second : BandVectors.1 (q 2) (q 0) ∈ TilingLattice C₀
  incoming_coordinates : ∀ w : TilingLattice C₀, ∃! mn : Int × Int,
    (mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) =
      (w : GaussianInt)
  lattice_rotation : ∀ z : GaussianInt, z ∈ L ↔
    ∃ w : GaussianInt, w ∈ TilingLattice C₀ ∧
      z = (⟨0, 1⟩ : GaussianInt) * w
  period_u_mem : u ∈ L
  period_v_mem : v ∈ L
  lattice_coordinates : ∀ w : L, ∃! mn : Int × Int,
    (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v =
      (w : GaussianInt)
  /-- The complete finite set of period-lattice coset representatives. -/
  R : Finset GaussianInt
  fundamental : LatticeFundamentalSet L R
  representative_count : R.card = C₀.1.1.1.natAbs
  /-- The original periodic core before deleting the precursor from the A occurrences. -/
  unmodified : BandUnmodifiedCoreCertificate P u v L
  inner_first :
    unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩) ∈
      FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)
  inner_second :
    unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩) ∈
      FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false)
  inner_third :
    unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩) ∈
      FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true)
  double_first : TouchingTriple (Q 1 true) (S 2 false) (P 1 true)
  double_second : TouchingTriple (Q 2 true) (S 1 false) (P 1 false)
  double_third : TouchingTriple (Q 1 true) (P 1 true) (P 2 false)
  double_fourth : TouchingTriple (S 1 false) (P 1 false) (P 2 true)
  outer_touching :
    TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
        (TileTranslation (P 2 true) v) ∧
    TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
        (P 2 false) ∧
    TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
        (TileTranslation (P 1 true) (u + v)) ∧
    TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
        (P 1 false) ∧
    TouchingTriple (P 0 true) (TileTranslation (P 1 true) (u + v))
        (TileTranslation (P 2 true) v) ∧
    TouchingTriple (P 0 false) (TileTranslation (P 1 false) (-u - v))
        (TileTranslation (P 2 false) (-v)) ∧
    TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
        (TileTranslation (P 2 true) (-u)) ∧
    TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
        (P 2 false)
  precursor_first : TouchingTriple (Q 1 true) (S 2 false) O
  precursor_second : TouchingTriple (Q 2 true) (S 1 false) O
  /-- The boundary-arc decomposition around the common precursor tile. -/
  precursorBoundary : PrecursorBoundaryArcData
    (TileCellComplement (P 0 true) O)
    (TileCellComplement (P 0 false) O) O (S 0 true)
    (Q 1 true) (S 2 false) (Q 2 true) (S 1 false)
  precursor_zero_curvature : O.cells = ∅ →
    (cfg.firstPredecessor 1).1 = 0
  /-- The exceptional connector segments between the two distinguished unmodified vertices. -/
  exceptionalSegments : ExceptionalConnectorSegments
    (P 0 true) (P 0 false) O
    (Q 1 true) (S 2 false) (Q 2 true) (S 1 false)
    (unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
    (unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩))
  /-- The retained loop-erased connector between the two selected inner interfaces. -/
  connector : List GaussianInt
  connector_segmented : connector = exceptionalSegments.connector
  connector_nodup : connector.Nodup
  connector_head : connector.head? = some
    (unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
  connector_last : connector.getLast? = some
    (unmodified.core.rho (unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩))
  connector_raw : ∀ x ∈ connector,
    x ∈ FootprintVertices (TileCellComplement (P 0 true) O) ∩
      FootprintVertices (P 0 false)
  connector_edges : ∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
    connector = l1 ++ x :: y :: l2 →
      {x, y} ∈ FootprintEdges (TileCellComplement (P 0 true) O) ∩
        FootprintEdges (P 0 false)
  connector_support : ∀ x ∈ connector,
    x ∈ (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
      FootprintVertices O ∪
      (FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false))
  orbit_area : TileArea (TileCellComplement (P 0 true) O) +
      TileArea (P 0 false) + TileArea (P 1 true) +
      TileArea (P 1 false) + TileArea (P 2 true) +
      TileArea (P 2 false) = R.card
  partition : ∀ x : LatticeCell, ∃! o : PeriodicSubtileIndex,
    x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells
  /-- The periodic complex with the precursor deleted from each A occurrence. -/
  modified : PeriodicTileComplex PeriodicSubtileIndex
  modified_lattice : modified.lattice = L
  modified_tile : ∀ o,
    modified.tile o = ModifiedSubtileOccurrenceInterpretation P O u v o
  modified_adjacency : ∀ a b,
    modified.plane.adjacent a b ↔ AllowedSubtileIncidence a b
  /-- Identify modified-complex faces with the fixed twelve-label periodic face ledger. -/
  modifiedFaceEquivalence : modified.plane.Face ≃ PeriodicSubtileFaceIndex
  modified_face_points : ∀ f : PeriodicSubtileFaceIndex,
    modified.rho (modifiedFaceEquivalence.symm f) =
      unmodified.core.rho (unmodified.faceEquiv.symm f)
  modified_face_vertices : ∀ f i,
    modified.plane.faceVertex f i =
      SixSubtileFaceVertices (modifiedFaceEquivalence f) i
  modified_face_reps : ∀ f, f ∈ modified.faceOrbitReps ↔
    (modifiedFaceEquivalence f).first = 0 ∧
      (modifiedFaceEquivalence f).second = 0
  precursor_isolated : ∀ m n : Int,
    ∀ x ∈ FootprintVertices
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)),
      ∀ a : GaussianInt,
        x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) →
        a ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨
          a ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells

end ApollonianSuperharmonic

end
