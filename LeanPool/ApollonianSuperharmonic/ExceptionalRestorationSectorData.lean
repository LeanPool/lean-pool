/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.ExceptionalConnectorSegments
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.TileCellComplement

-- [TABLET NODE: ExceptionalRestorationSectorData]

/-!
# ExceptionalRestorationSectorData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $O\subseteq A\cap B$, let $(Q_2,S_3)$ and $(Q_3,S_2)$ be the two
labelled child pairs, let $C,D$ be their respective primary companions,
and let $p_1,p_2$ and
$\mathcal E$ be an `ExceptionalConnectorSegments` certificate.
An *exceptional restoration-sector certificate* consists of the
following incident-cell assertions, with
$\operatorname{inc}$ as in `LatticeVertexIncidentCell`.

At every vertex $x$ of the oriented left segment satisfying
$O.\mathrm{cells}\ne\varnothing$ or $x\ne a$, the following assertions
hold.  If neither a $C$-cell nor an $O$-cell occurs at $x$, there is a
sector $j$ owned by $Q_2$ whose opposite sector $j+2$ is owned by $S_3$.
Every incident cell is owned by $Q_2$ or $S_3$, except that a $C$-cell may
occur only at $p_1$ and an $O$-cell may occur only at $a$; moreover, an
incident $C$-cell occurs at $x$ if and only if $x=p_1$.  A $C$-cell does
occur at $p_1$ unconditionally.
Among the three owners $Q_2,S_3,C$, some two own opposite sectors at
$p_1$.  When $O$ has a cell, an incident $O$-cell occurs on this segment
exactly at the cut $a$, and among $Q_2,S_3,O$ some two own opposite
sectors there.  The analogous guarded assertions hold on the right segment,
with guard $O.\mathrm{cells}\ne\varnothing$ or $x\ne b$, literal ordered
pair $(Q_3,S_2)$, companion $D$, marked endpoint
$p_2$, and cut $b$.

If $O$ has a cell, then $a\ne p_1$ and $b\ne p_2$; no incident
$C$-cell occurs at $a$, no incident $D$-cell occurs at $b$, and an
incident $O$-cell occurs at each cut.  If $O$ has no cells, then
$a=b=\operatorname{anchor}(O)$.

Finally, every proper internal vertex $x$ of the middle segment lies on
the common boundary of $A\setminus O$ and $B$.  After restoring $O$ to
$A$, all four cells incident with $x$ belong to $A$.  Consequently $x$ is
not on the common original boundary of $A$ and $B$.
-/
structure ExceptionalRestorationSectorData
    (A B O Q2 S3 Q3 S2 C D : ProtoTile)
    (p1 p2 : GaussianInt)
    (segments : ExceptionalConnectorSegments A B O Q2 S3 Q3 S2 p1 p2) where
-- BODY
  left_opposite : ∀ x ∈ segments.left,
    O.cells.Nonempty ∨ x ≠ segments.a →
    (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉ C.cells) →
    (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉ O.cells) →
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Q2.cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ S3.cells
  right_opposite : ∀ x ∈ segments.right,
    O.cells.Nonempty ∨ x ≠ segments.b →
    (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉ D.cells) →
    (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉ O.cells) →
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Q3.cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ S2.cells
  left_owners : ∀ x ∈ segments.left,
    O.cells.Nonempty ∨ x ≠ segments.a → ∀ j : Fin 4,
    LatticeVertexIncidentCell x j ∈ Q2.cells ∨
      LatticeVertexIncidentCell x j ∈ S3.cells ∨
      (x = p1 ∧ LatticeVertexIncidentCell x j ∈ C.cells) ∨
      (x = segments.a ∧ LatticeVertexIncidentCell x j ∈ O.cells)
  right_owners : ∀ x ∈ segments.right,
    O.cells.Nonempty ∨ x ≠ segments.b → ∀ j : Fin 4,
    LatticeVertexIncidentCell x j ∈ Q3.cells ∨
      LatticeVertexIncidentCell x j ∈ S2.cells ∨
      (x = p2 ∧ LatticeVertexIncidentCell x j ∈ D.cells) ∨
      (x = segments.b ∧ LatticeVertexIncidentCell x j ∈ O.cells)
  left_companion : ∀ x ∈ segments.left,
    O.cells.Nonempty ∨ x ≠ segments.a →
    ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ C.cells) ↔ x = p1)
  right_companion : ∀ x ∈ segments.right,
    O.cells.Nonempty ∨ x ≠ segments.b →
    ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ D.cells) ↔ x = p2)
  positive_left_precursor : O.cells.Nonempty → ∀ x ∈ segments.left,
    (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ O.cells) ↔
      x = segments.a
  positive_right_precursor : O.cells.Nonempty → ∀ x ∈ segments.right,
    (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ O.cells) ↔
      x = segments.b
  positive_cut_separation : O.cells.Nonempty →
    segments.a ≠ p1 ∧ segments.b ≠ p2
  positive_first_cut_no_companion : O.cells.Nonempty → ∀ j : Fin 4,
    LatticeVertexIncidentCell segments.a j ∉ C.cells
  positive_second_cut_no_companion : O.cells.Nonempty → ∀ j : Fin 4,
    LatticeVertexIncidentCell segments.b j ∉ D.cells
  first_marked_companion :
    ∃ j : Fin 4, LatticeVertexIncidentCell p1 j ∈ C.cells
  second_marked_companion :
    ∃ j : Fin 4, LatticeVertexIncidentCell p2 j ∈ D.cells
  first_marked_opposite :
    (∃ j : Fin 4, LatticeVertexIncidentCell p1 j ∈ Q2.cells ∧
      LatticeVertexIncidentCell p1 (j + 2) ∈ S3.cells) ∨
    (∃ j : Fin 4, LatticeVertexIncidentCell p1 j ∈ Q2.cells ∧
      LatticeVertexIncidentCell p1 (j + 2) ∈ C.cells) ∨
    (∃ j : Fin 4, LatticeVertexIncidentCell p1 j ∈ S3.cells ∧
      LatticeVertexIncidentCell p1 (j + 2) ∈ C.cells)
  second_marked_opposite :
    (∃ j : Fin 4, LatticeVertexIncidentCell p2 j ∈ Q3.cells ∧
      LatticeVertexIncidentCell p2 (j + 2) ∈ S2.cells) ∨
    (∃ j : Fin 4, LatticeVertexIncidentCell p2 j ∈ Q3.cells ∧
      LatticeVertexIncidentCell p2 (j + 2) ∈ D.cells) ∨
    (∃ j : Fin 4, LatticeVertexIncidentCell p2 j ∈ S2.cells ∧
      LatticeVertexIncidentCell p2 (j + 2) ∈ D.cells)
  positive_first_cut_precursor : O.cells.Nonempty →
    ∃ j : Fin 4, LatticeVertexIncidentCell segments.a j ∈ O.cells
  positive_second_cut_precursor : O.cells.Nonempty →
    ∃ j : Fin 4, LatticeVertexIncidentCell segments.b j ∈ O.cells
  positive_first_cut_opposite : O.cells.Nonempty →
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.a j ∈ Q2.cells ∧
        LatticeVertexIncidentCell segments.a (j + 2) ∈ S3.cells) ∨
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.a j ∈ Q2.cells ∧
        LatticeVertexIncidentCell segments.a (j + 2) ∈ O.cells) ∨
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.a j ∈ S3.cells ∧
        LatticeVertexIncidentCell segments.a (j + 2) ∈ O.cells)
  positive_second_cut_opposite : O.cells.Nonempty →
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.b j ∈ Q3.cells ∧
        LatticeVertexIncidentCell segments.b (j + 2) ∈ S2.cells) ∨
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.b j ∈ Q3.cells ∧
        LatticeVertexIncidentCell segments.b (j + 2) ∈ O.cells) ∨
    (∃ j : Fin 4,
      LatticeVertexIncidentCell segments.b j ∈ S2.cells ∧
        LatticeVertexIncidentCell segments.b (j + 2) ∈ O.cells)
  empty_cut : O.cells = ∅ →
    segments.a = segments.b ∧ segments.a = O.anchor
  proper_middle_modified_boundary : ∀ x ∈ segments.middle,
    x ≠ segments.a → x ≠ segments.b →
      x ∈ BoundaryFootprintVertices (TileCellComplement A O) ∩
        BoundaryFootprintVertices B
  proper_middle_restored_left : ∀ x ∈ segments.middle,
    x ≠ segments.a → x ≠ segments.b →
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ A.cells
  proper_middle_not_original_common : ∀ x ∈ segments.middle,
    x ≠ segments.a → x ≠ segments.b →
      x ∉ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B

end ApollonianSuperharmonic

end
