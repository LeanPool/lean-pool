/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PositiveCutCompanionRow

-- [TABLET NODE: BandOrderedGeneralInteriorWebRow]

/-!
# BandOrderedGeneralInteriorWebRow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix a `BandOrderedGeneralLayoutCertificate` and a lattice vertex
$x$.  For
$m\in\{0,1\}$, an \emph{ordered-general interior web row of mark $m$} is
one of the following twelve labelled rows.  In each of the first ten rows,
$x$ belongs to both displayed `FootprintVertices` sets and their
union contains the five-point star
$$
                 x,\qquad x+1,\qquad x-1,\qquad x+\mathrm{i},\qquad x-\mathrm{i}.
$$

Write $r^{(1)}$ and $r^{(2)}$ for the certificate's first and second
predecessor tuples.  There are six outer mixed rows with the following
geometric third owner and directed subtile data:
$$
\begin{array}{c|c|c|c|c}
\text{pair}&\text{coarse third}&\text{child}&(r,j)&s\ \hline
(P_1^+,P_2^-)&P_1^-&P_1^+&(r^{(1)},2)&3\\
(P_1^+,P_3^-)&P_2^+&P_1^+&(r^{(1)},3)&0\\
(P_2^+,P_1^-)&P_1^+&P_1^-&(r^{(1)},2)&1\\
(P_3^+,P_1^-)&P_2^-&P_1^-&(r^{(1)},3)&2\\
(P_2^+,P_3^-)&P_1^+&P_2^+&(r^{(2)},1)&3\\
(P_3^+,P_2^-)&P_1^-&P_2^-&(r^{(2)},1)&1 .
\end{array}
$$
For each mixed row, $x$ belongs to the displayed coarse third footprint if
and only if $m=1$.  This is only a zero-translate ownership assertion.  It
does not identify that owner with the web companion.

For the directed child $U$ in the same row, define literally
$$
 u_R=\mathrm{i}^s
 \begin{cases}
 \operatorname{BandVectors}_1(r_0,r_j),&s\text{ even},\\
 \operatorname{BandVectors}_1(r_j,r_0),&s\text{ odd}.
 \end{cases}
$$
The actual right companion of the directed subtile web is the
`TileTranslation` $U+u_R$, and
$$
 x\in\operatorname{FootprintVertices}(U+u_R)\quad\Longleftrightarrow\quad m=1.
$$
The coarse third owner and this translated child are retained as distinct
objects, even though their footprints both contain $x$ exactly in the
marked case.

There are two restricted right rows
$$
                     (Q_2^+,P_2^+),\qquad(S_2^-,P_2^-).
$$
For either row, the two tiles contain all four lattice cells incident with
$x$ if and only if $m=0$.

There are two largest-parent child rows
$$
                     (Q_2^+,S_3^-),\qquad(Q_3^+,S_2^-),
$$
whose right companions are respectively $P_2^+$ and $P_2^-$.  In either
row, $x$ belongs to the companion footprint if and only if $m=1$.

Finally there are a left positive-cut row and a right positive-cut row.
Both are available only with mark zero.  The left constructor requires
$x=a$, the first attachment vertex of the exceptional connector, and the
right constructor requires $x=b$, its second attachment vertex.  Each
carries a `PositiveCutCompanionRow` at that same $x$.  Thus neither
constructor chooses a fixed $Q/S$ pair.  Through its row it retains one
proper birth tuple, raw parent slot and rotation, the selected child and
parent, their cut memberships, an opposite pair of incident cells, the
five-point-star cover, and the computed right translate $U+u_R$ with
$x\notin\operatorname{foot}(U+u_R)$.  It also retains the literal eight-case tag and,
only in the two fixed $Q$--$S$ rows, the observable $P_2^\pm$ companion
identification.  No marked point, hidden parent, exact interface triple, or
endpoint identity is present.

This is geometric routing data only.  In particular, it contains no
right- or subtile-lattice adjacency assertion, no slope or odometer data,
and no Laplacian conclusion.
-/
inductive BandOrderedGeneralInteriorWebRow
    {q : Fin 4 → CircleCoordinates}
    {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (x : GaussianInt) (marked : Bool) : Prop where
-- BODY
  | outer12
      (left_mem : x ∈ FootprintVertices (cert.P 0 true))
      (right_mem : x ∈ FootprintVertices (cert.P 1 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 0 true) ∨
          y ∈ FootprintVertices (cert.P 1 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 0 false) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 0 true)
            ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
              (if Even (3 : Nat) then
                BandVectors.1 (cfg.firstPredecessor 0)
                  (cfg.firstPredecessor 2)
              else
                BandVectors.1 (cfg.firstPredecessor 2)
                  (cfg.firstPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | outer13
      (left_mem : x ∈ FootprintVertices (cert.P 0 true))
      (right_mem : x ∈ FootprintVertices (cert.P 2 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 0 true) ∨
          y ∈ FootprintVertices (cert.P 2 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 1 true) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 0 true)
            ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
              (if Even (0 : Nat) then
                BandVectors.1 (cfg.firstPredecessor 0)
                  (cfg.firstPredecessor 3)
              else
                BandVectors.1 (cfg.firstPredecessor 3)
                  (cfg.firstPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | outer21
      (left_mem : x ∈ FootprintVertices (cert.P 1 true))
      (right_mem : x ∈ FootprintVertices (cert.P 0 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 1 true) ∨
          y ∈ FootprintVertices (cert.P 0 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 0 true) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 0 false)
            ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
              (if Even (1 : Nat) then
                BandVectors.1 (cfg.firstPredecessor 0)
                  (cfg.firstPredecessor 2)
              else
                BandVectors.1 (cfg.firstPredecessor 2)
                  (cfg.firstPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | outer31
      (left_mem : x ∈ FootprintVertices (cert.P 2 true))
      (right_mem : x ∈ FootprintVertices (cert.P 0 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 2 true) ∨
          y ∈ FootprintVertices (cert.P 0 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 1 false) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 0 false)
            ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
              (if Even (2 : Nat) then
                BandVectors.1 (cfg.firstPredecessor 0)
                  (cfg.firstPredecessor 3)
              else
                BandVectors.1 (cfg.firstPredecessor 3)
                  (cfg.firstPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | outer23
      (left_mem : x ∈ FootprintVertices (cert.P 1 true))
      (right_mem : x ∈ FootprintVertices (cert.P 2 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 1 true) ∨
          y ∈ FootprintVertices (cert.P 2 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 0 true) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 1 true)
            ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
              (if Even (3 : Nat) then
                BandVectors.1 (cfg.secondPredecessor 0)
                  (cfg.secondPredecessor 1)
              else
                BandVectors.1 (cfg.secondPredecessor 1)
                  (cfg.secondPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | outer32
      (left_mem : x ∈ FootprintVertices (cert.P 2 true))
      (right_mem : x ∈ FootprintVertices (cert.P 1 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.P 2 true) ∨
          y ∈ FootprintVertices (cert.P 1 false))
      (coarseThird :
        x ∈ FootprintVertices (cert.P 0 false) ↔ marked = true)
      (webCompanion :
        x ∈ FootprintVertices
          (TileTranslation (cert.P 1 false)
            ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
              (if Even (1 : Nat) then
                BandVectors.1 (cfg.secondPredecessor 0)
                  (cfg.secondPredecessor 1)
              else
                BandVectors.1 (cfg.secondPredecessor 1)
                  (cfg.secondPredecessor 0)))) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | rightPositive
      (left_mem : x ∈ FootprintVertices (cert.Q 1 true))
      (right_mem : x ∈ FootprintVertices (cert.P 1 true))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 1 true) ∨
          y ∈ FootprintVertices (cert.P 1 true))
      (squares :
        (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
            z = x - 1 - ⟨0, 1⟩ →
          z ∈ (cert.Q 1 true).cells ∨ z ∈ (cert.P 1 true).cells) ↔
          marked = false) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | rightReflected
      (left_mem : x ∈ FootprintVertices (cert.S 1 false))
      (right_mem : x ∈ FootprintVertices (cert.P 1 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.S 1 false) ∨
          y ∈ FootprintVertices (cert.P 1 false))
      (squares :
        (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
            z = x - 1 - ⟨0, 1⟩ →
          z ∈ (cert.S 1 false).cells ∨ z ∈ (cert.P 1 false).cells) ↔
          marked = false) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | largestPositive
      (left_mem : x ∈ FootprintVertices (cert.Q 1 true))
      (right_mem : x ∈ FootprintVertices (cert.S 2 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 1 true) ∨
          y ∈ FootprintVertices (cert.S 2 false))
      (companion :
        x ∈ FootprintVertices (cert.P 1 true) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | largestReflected
      (left_mem : x ∈ FootprintVertices (cert.Q 2 true))
      (right_mem : x ∈ FootprintVertices (cert.S 1 false))
      (star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 2 true) ∨
          y ∈ FootprintVertices (cert.S 1 false))
      (companion :
        x ∈ FootprintVertices (cert.P 1 false) ↔ marked = true) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | leftPositiveCut
      (unmarked : marked = false)
      (at_cut : x = cert.exceptionalSegments.a)
      (geometry : PositiveCutCompanionRow cert x) :
      BandOrderedGeneralInteriorWebRow cert x marked
  | rightPositiveCut
      (unmarked : marked = false)
      (at_cut : x = cert.exceptionalSegments.b)
      (geometry : PositiveCutCompanionRow cert x) :
      BandOrderedGeneralInteriorWebRow cert x marked

end ApollonianSuperharmonic

end
