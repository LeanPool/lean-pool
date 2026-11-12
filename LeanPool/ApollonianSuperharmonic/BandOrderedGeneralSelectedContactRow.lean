/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileCentroid

-- [TABLET NODE: BandOrderedGeneralSelectedContactRow]

/-!
# BandOrderedGeneralSelectedContactRow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general layout certificate and write
$A,B,C,D,E,F$ for its six signed pieces and $X_{m,n}$ for the corresponding
literal periodic occurrence.  An *exact selected contact row* consists
of two distinct literal indices and their directed geometric presentation;
an $S$ constructor also designates the canonical signed old-companion piece.
Its constructors are the following.

The constructors are exactly the following eighteen exterior--central
rows.  Put $r=\mathit{cfg.firstPredecessor}$ and
$t=\mathit{cfg.secondPredecessor}$.  The entry $S_{b\to a}(s)$ stores the
directed child--parent centroid presentation with the displayed rotation
$s$: the rows $S_{2\to1}$ use $(r,1)$, the rows $S_{3\to1}$ use $(r,2)$,
and the rows $S_{3\to2}$ use $(t,0)$.  Thus the predecessor and parent slot
are part of the constructor, not freely chosen data.  In the six positive
$S$ rows, in displayed order, the constructors designate the signed old
companions $P_1^+,P_1^+,P_2^+,P_1^+,P_1^+,P_2^+$; the reflected
constructors designate respectively
$P_1^-,P_1^-,P_2^-,P_1^-,P_1^-,P_2^-$.  These labels and signs are likewise
fixed by the constructor.  The literal translation is derived later from
the row centroid identity.
$$
\begin{array}{c|c|c@{\qquad}c|c|c}
A_{-1,-1}&B_{0,0}&L(-v_{21})&B_{1,1}&A_{0,0}&L(+v_{21})\\
A_{-1,-1}&C_{0,0}&S_{2\to1}(0)&B_{1,1}&D_{0,0}&S_{2\to1}(2)\\
A_{0,-1}&B_{0,0}&L(-v_{31})&B_{0,1}&A_{0,0}&L(+v_{31})\\
A_{0,-1}&E_{0,0}&S_{3\to1}(3)&B_{0,1}&F_{0,0}&S_{3\to1}(1)\\
C_{1,0}&D_{0,0}&L(-v_{32})&D_{-1,0}&C_{0,0}&L(+v_{32})\\
C_{1,0}&E_{0,0}&S_{3\to2}(0)&D_{-1,0}&F_{0,0}&S_{3\to2}(2)\\
C_{1,1}&A_{0,0}&S_{2\to1}(0)&D_{-1,-1}&B_{0,0}&S_{2\to1}(2)\\
E_{0,1}&A_{0,0}&S_{3\to1}(3)&F_{0,-1}&B_{0,0}&S_{3\to1}(1)\\
E_{-1,0}&C_{0,0}&S_{3\to2}(0)&F_{1,0}&D_{0,0}&S_{3\to2}(2).
\end{array}
$$
Thus the row data names a literal row before any endpoint, point, touching,
or sector-ownership assertion is made.  In particular it contains no mark
membership claim.
-/
inductive BandOrderedGeneralSelectedContactRow
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    PeriodicSubtileIndex → PeriodicSubtileIndex → Type where
-- BODY
  | positiveL1
      (hne : (⟨.A, -1, -1⟩ : PeriodicSubtileIndex) ≠ ⟨.B, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.A, -1, -1⟩) -
        TileCentroid (cert.P 0 false) =
          -GaussianRealPoint (BandVectors.1 (q 2) (q 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.A, -1, -1⟩ ⟨.B, 0, 0⟩
  | positiveS1
      (presentation : TileCentroid (cert.P 1 true) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.A, -1, -1⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.A, -1, -1⟩ ⟨.C, 0, 0⟩
  | positiveL2
      (hne : (⟨.A, 0, -1⟩ : PeriodicSubtileIndex) ≠ ⟨.B, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.A, 0, -1⟩) -
        TileCentroid (cert.P 0 false) =
          -GaussianRealPoint (BandVectors.1 (q 3) (q 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.A, 0, -1⟩ ⟨.B, 0, 0⟩
  | positiveS2
      (presentation : TileCentroid (cert.P 2 true) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.A, 0, -1⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.A, 0, -1⟩ ⟨.E, 0, 0⟩
  | positiveL3
      (hne : (⟨.C, 1, 0⟩ : PeriodicSubtileIndex) ≠ ⟨.D, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.C, 1, 0⟩) -
        TileCentroid (cert.P 1 false) =
          -GaussianRealPoint (BandVectors.1 (q 3) (q 2))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.C, 1, 0⟩ ⟨.D, 0, 0⟩
  | positiveS3
      (presentation : TileCentroid (cert.P 2 true) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.C, 1, 0⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.C, 1, 0⟩ ⟨.E, 0, 0⟩
  | positiveS4
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.C, 1, 1⟩) -
        TileCentroid (cert.P 0 true) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
            BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.C, 1, 1⟩ ⟨.A, 0, 0⟩
  | positiveS5
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.E, 0, 1⟩) -
        TileCentroid (cert.P 0 true) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.E, 0, 1⟩ ⟨.A, 0, 0⟩
  | positiveS6
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.E, -1, 0⟩) -
        TileCentroid (cert.P 1 true) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
            BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.E, -1, 0⟩ ⟨.C, 0, 0⟩
  | reflectedL1
      (hne : (⟨.B, 1, 1⟩ : PeriodicSubtileIndex) ≠ ⟨.A, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, 1, 1⟩) -
        TileCentroid (cert.P 0 true) =
          GaussianRealPoint (BandVectors.1 (q 2) (q 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.B, 1, 1⟩ ⟨.A, 0, 0⟩
  | reflectedS1
      (presentation : TileCentroid (cert.P 1 false) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, 1, 1⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.B, 1, 1⟩ ⟨.D, 0, 0⟩
  | reflectedL2
      (hne : (⟨.B, 0, 1⟩ : PeriodicSubtileIndex) ≠ ⟨.A, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, 0, 1⟩) -
        TileCentroid (cert.P 0 true) =
          GaussianRealPoint (BandVectors.1 (q 3) (q 1))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.B, 0, 1⟩ ⟨.A, 0, 0⟩
  | reflectedS2
      (presentation : TileCentroid (cert.P 2 false) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.B, 0, 1⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.B, 0, 1⟩ ⟨.F, 0, 0⟩
  | reflectedL3
      (hne : (⟨.D, -1, 0⟩ : PeriodicSubtileIndex) ≠ ⟨.C, 0, 0⟩)
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.D, -1, 0⟩) -
        TileCentroid (cert.P 1 true) =
          GaussianRealPoint (BandVectors.1 (q 3) (q 2))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.D, -1, 0⟩ ⟨.C, 0, 0⟩
  | reflectedS3
      (presentation : TileCentroid (cert.P 2 false) -
        TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.D, -1, 0⟩) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
              BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.D, -1, 0⟩ ⟨.F, 0, 0⟩
  | reflectedS4
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.D, -1, -1⟩) -
        TileCentroid (cert.P 0 false) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 2)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.D, -1, -1⟩ ⟨.B, 0, 0⟩
  | reflectedS5
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.F, 0, -1⟩) -
        TileCentroid (cert.P 0 false) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
            (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 0) +
              BandVectors.1 (cfg.firstPredecessor 0) (cfg.firstPredecessor 3)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.F, 0, -1⟩ ⟨.B, 0, 0⟩
  | reflectedS6
      (presentation : TileCentroid
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨.F, 1, 0⟩) -
        TileCentroid (cert.P 1 false) =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            (BandVectors.1 (cfg.secondPredecessor 1) (cfg.secondPredecessor 0) +
              BandVectors.1 (cfg.secondPredecessor 0) (cfg.secondPredecessor 1)))) :
      BandOrderedGeneralSelectedContactRow q cfg C₀ T cert ⟨.F, 1, 0⟩ ⟨.D, 0, 0⟩

end ApollonianSuperharmonic

end
