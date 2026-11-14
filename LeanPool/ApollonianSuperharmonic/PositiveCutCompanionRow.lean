/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: PositiveCutCompanionRow]

/-!
# PositiveCutCompanionRow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general layout certificate and one positive precursor cut
$x$.  A *positive-cut web row* records a proper birth
$p=(M,D,E,F)$, a raw parent slot $r\in\mathbb Z/3\mathbb Z$, a rotation
$s\in\mathbb Z/4\mathbb Z$, a selected whole-child occurrence $U$ for
$M$, and a selected parent occurrence $W$ for $p_{r+1}$.  The row includes
the certificate that the precursor $O$ has a nonempty cell set, the
corresponding `BandPrototile` certificates, and the two cut
memberships $x\in\operatorname{foot}(U)\cap\operatorname{foot}(W)$.  Some incident $U$-cell is
opposite an incident $W$-cell, and the two footprints contain the
five-point star
$$
                 x,\qquad x+1,\qquad x-1,\qquad x+\mathrm{i},\qquad x-\mathrm{i}.
$$

Put
$$
 u_R=\mathrm{i}^s\begin{cases}v_{0,r+1},&s\text{ even},\\
                       v_{r+1,0},&s\text{ odd}.
       \end{cases}
$$
The row records that translation closure makes $U+u_R$ a prototile for
$M$ and, crucially, that
$$
                         x\notin\operatorname{foot}(U+u_R).                 \tag{1}
$$
Thus the right companion is always the actual translated child prescribed
by the web rule, rather than an occurrence guessed from a circle label.

The literal tag is exactly one of the following eight alternatives:
$$
\begin{array}{c|c|c|c|c|c}
p&x&U&W&r&s\\ \hline
(C_2,D,C_3,C_4)&a&Q_2^+&S_3^-&1&1\\
(C_2,D,C_3,C_4)&a&Q_2^+&O&2&0\\
(C_2,D,C_3,C_4)&b&S_2^-&Q_3^+&1&3\\
(C_2,D,C_3,C_4)&b&S_2^-&O&2&2\\
(C_4,D,C_2,C_3)&a&O&Q_2^+&1&1\\
(C_4,D,C_2,C_3)&a&O&S_3^-&2&0\\
(C_4,D,C_2,C_3)&b&O&S_2^-&1&3\\
(C_4,D,C_2,C_3)&b&O&Q_3^+&2&2.
\end{array}                                                   \tag{2}
$$
For the first and third rows only, the row additionally records observable
equality, meaning equality of cell sets and equality of anchors when those
sets are empty, of $U+u_R$ with $P_2^+$ and $P_2^-$, respectively.  These
are the two fixed $Q$--$S$ companions identified in the manuscript.  No
literal support is asserted for the other six rows merely from their tags.
In particular the four $C_4$-birth rows do not identify their companions
with $Q_4^+$ or $S_4^-$.
-/
structure PositiveCutCompanionRow
    {q : Fin 4 → CircleCoordinates}
    {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (x : GaussianInt) where
-- BODY
  precursorNonempty : cert.O.cells.Nonempty
  /-- The proper birth presentation prescribed by the literal positive-cut row. -/
  birth : Fin 4 → CircleCoordinates
  /-- The parent slot fixed by that row in its birth presentation. -/
  parentIndex : Fin 3
  /-- The quarter-turn index fixed by that literal row. -/
  rotation : Fin 4
  /-- The selected whole-child occurrence through the precursor attachment. -/
  child : ProtoTile
  /-- The selected parent occurrence on the opposite side of the attachment. -/
  parent : ProtoTile
  proper : ProperBandQuadruple birth
  childPrototile : BandPrototile (birth 0) child
  parentPrototile : BandPrototile (birth parentIndex.succ) parent
  child_mem : x ∈ FootprintVertices child
  parent_mem : x ∈ FootprintVertices parent
  opposite : ∃ j : Fin 4,
    LatticeVertexIncidentCell x j ∈ child.cells ∧
      LatticeVertexIncidentCell x (j + 2) ∈ parent.cells
  star : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ FootprintVertices child ∨ y ∈ FootprintVertices parent
  rightPrototile :
    let uR := (⟨0, 1⟩ : GaussianInt) ^ rotation.val *
      (if Even rotation.val then
        BandVectors.1 (birth 0) (birth parentIndex.succ)
      else BandVectors.1 (birth parentIndex.succ) (birth 0))
    BandPrototile (birth 0) (TileTranslation child uR)
  rightAbsent :
    let uR := (⟨0, 1⟩ : GaussianInt) ^ rotation.val *
      (if Even rotation.val then
        BandVectors.1 (birth 0) (birth parentIndex.succ)
      else BandVectors.1 (birth parentIndex.succ) (birth 0))
    x ∉ FootprintVertices (TileTranslation child uR)
  fixedPlusCompanion :
    child = cert.Q 1 true → parent = cert.S 2 false →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ rotation.val *
        (if Even rotation.val then
          BandVectors.1 (birth 0) (birth parentIndex.succ)
        else BandVectors.1 (birth parentIndex.succ) (birth 0))
      (TileTranslation child uR).cells = (cert.P 1 true).cells ∧
        ((TileTranslation child uR).cells = ∅ →
          (TileTranslation child uR).anchor = (cert.P 1 true).anchor)
  fixedMinusCompanion :
    child = cert.S 1 false → parent = cert.Q 2 true →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ rotation.val *
        (if Even rotation.val then
          BandVectors.1 (birth 0) (birth parentIndex.succ)
        else BandVectors.1 (birth parentIndex.succ) (birth 0))
      (TileTranslation child uR).cells = (cert.P 1 false).cells ∧
        ((TileTranslation child uR).cells = ∅ →
          (TileTranslation child uR).anchor = (cert.P 1 false).anchor)
  literalRow :
    (birth = ![q 2, birth 1, q 3, cfg.firstPredecessor 1] ∧
      parentIndex = 1 ∧ rotation = 1 ∧
      x = cert.exceptionalSegments.a ∧
      child = cert.Q 1 true ∧ parent = cert.S 2 false) ∨
    (birth = ![q 2, birth 1, q 3, cfg.firstPredecessor 1] ∧
      parentIndex = 2 ∧ rotation = 0 ∧
      x = cert.exceptionalSegments.a ∧
      child = cert.Q 1 true ∧ parent = cert.O) ∨
    (birth = ![q 2, birth 1, q 3, cfg.firstPredecessor 1] ∧
      parentIndex = 1 ∧ rotation = 3 ∧
      x = cert.exceptionalSegments.b ∧
      child = cert.S 1 false ∧ parent = cert.Q 2 true) ∨
    (birth = ![q 2, birth 1, q 3, cfg.firstPredecessor 1] ∧
      parentIndex = 2 ∧ rotation = 2 ∧
      x = cert.exceptionalSegments.b ∧
      child = cert.S 1 false ∧ parent = cert.O) ∨
    (birth = ![cfg.firstPredecessor 1, birth 1, q 2, q 3] ∧
      parentIndex = 1 ∧ rotation = 1 ∧
      x = cert.exceptionalSegments.a ∧
      child = cert.O ∧ parent = cert.Q 1 true) ∨
    (birth = ![cfg.firstPredecessor 1, birth 1, q 2, q 3] ∧
      parentIndex = 2 ∧ rotation = 0 ∧
      x = cert.exceptionalSegments.a ∧
      child = cert.O ∧ parent = cert.S 2 false) ∨
    (birth = ![cfg.firstPredecessor 1, birth 1, q 2, q 3] ∧
      parentIndex = 1 ∧ rotation = 3 ∧
      x = cert.exceptionalSegments.b ∧
      child = cert.O ∧ parent = cert.S 1 false) ∨
    (birth = ![cfg.firstPredecessor 1, birth 1, q 2, q 3] ∧
      parentIndex = 2 ∧ rotation = 2 ∧
      x = cert.exceptionalSegments.b ∧
      child = cert.O ∧ parent = cert.Q 2 true)

end ApollonianSuperharmonic

end
