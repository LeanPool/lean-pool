/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.P5064T3OrderedPredecessor
public import LeanPool.ApollonianSuperharmonic.P5064T3LiteralLocalization
public import LeanPool.ApollonianSuperharmonic.P5064T3RectangleContacts
public import LeanPool.ApollonianSuperharmonic.P5064T3CrossParentSupport
public import LeanPool.ApollonianSuperharmonic.P5064T3PrecursorSupport

-- [TABLET NODE: FordBaseT6]

/-!
# FordBaseT6

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordBaseT6 (P : FordFareyParameter) (hq : 1 < P.q)
    (r : Fin 4 → CircleCoordinates) (hr : ProperBandQuadruple r)
    (hr0 : r 0 = (FordRecursiveQuadruple P) 1)
    (hr2 : r 2 = (FordRecursiveQuadruple P) 2)
    (hr3 : r 3 = (FordRecursiveQuadruple P) 3)
    (h12 : ((FordRecursiveQuadruple P) 2).1 ≤
      ((FordRecursiveQuadruple P) 1).1)
    (h2large : 1 < ((FordRecursiveQuadruple P) 2).1)
    (S Q R : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i s, BandSubtileOccurrence (FordRecursiveQuadruple P)
      (FordTile P.q) i s (S i s))
    (hQ : ∀ i s, BandSubtileOccurrence r (S 0 true) i s (Q i s))
    (hR : ∀ i s, BandSubtileOccurrence r (S 0 false) i s (R i s)) :
    let q := FordRecursiveQuadruple P
    let u := BandVectors.1 (q 0) (q 1)
    let v := BandVectors.1 (q 0) (q 2)
    (∀ a b : PeriodicSubtileIndex, a ≠ b →
      ((FootprintEdges (SubtileOccurrenceInterpretation S u v a) ∩
          FootprintEdges (SubtileOccurrenceInterpretation S u v b)).Nonempty →
        AllowedSubtileIncidence a b) ∧
      (¬ AllowedSubtileIncidence a b →
        FootprintVertices (SubtileOccurrenceInterpretation S u v a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation S u v b) = ∅ ∨
          (FootprintVertices (SubtileOccurrenceInterpretation S u v a) ∩
            FootprintVertices
              (SubtileOccurrenceInterpretation S u v b)).Subsingleton)) ∧
    FootprintVertices (S 0 true) ∩ FootprintVertices (S 1 true) ⊆
      FootprintVertices (Q 1 true) ∩ FootprintVertices (S 1 true) ∧
    FootprintVertices (S 0 true) ∩ FootprintVertices (S 0 false) ⊆
      (FootprintVertices (Q 1 true) ∩ FootprintVertices (R 2 false)) ∪
        FootprintVertices (Q 0 false) ∪
        (FootprintVertices (Q 2 true) ∩
          FootprintVertices (R 1 false)) := by
-- BODY
  classical
  obtain ⟨hs, hrs, hd, P₁, hp, hq₁, hp₁, hd₁, hp₂, hs₂, heq⟩ :=
    P5064T3OrderedPredecessor P r hr hr0 hr2 hr3 h12 h2large
  have zeroTrans (T : ProtoTile) : TileTranslation T 0 = T := by
    have hz : GaussianTranslation 0 = id := by
      funext z
      exact add_zero z
    simp only [TileTranslation, hz, Finset.image_id, id_eq]
  have loc := P5064T3LiteralLocalization P hq (FordTile P.q) 0
    (by rw [zeroTrans]) S hS
  simp only [zeroTrans] at loc
  have locQ := P5064T3LiteralLocalization P₁ (by omega) (S 0 true) 0
    (by simpa [zeroTrans, hq₁, P5064T3Rectangles]
      using (loc 0 true).2.2.2.2) Q
    (by intro i b; simpa only [← heq] using hQ i b)
  simp only [hd₁, hs₂, zeroTrans] at locQ
  have locR := P5064T3LiteralLocalization P₁ (by omega) (S 0 false)
    ⟨(P.q₂ : Int), (P.q₂ : Int)⟩
    (by simpa [P5064T3Rectangles, hq₁] using (loc 0 false).2.2.2.2) R
    (by intro i b; simpa only [← heq] using hR i b)
  simp only [hd₁, hs₂] at locR
  have sf (i : Fin 3) (b : Bool) := (loc i b).2.2.1
  have se (i : Fin 3) (b : Bool) := (loc i b).2.2.2.1
  have qf (i : Fin 3) (b : Bool) := (locQ i b).2.2.1
  have rm : FootprintVertices (R 0 true) =
      FootprintVertices (P5064T3Rectangles (P.q₁ - P.q₂) P.q₂ 0 false) := by
    simpa [P5064T3Rectangles] using (locR 0 true).2.2.1
  have shared : FootprintVertices (Q 0 false) = FootprintVertices (R 0 true) :=
    (qf 0 false).trans rm.symm
  have transFoot (T : ProtoTile) (d : GaussianInt) :=
    (TileTranslationFormulas T d).2.2.2.2.2.1
  have transEdge (T : ProtoTile) (d : GaussianInt) :=
    (TileTranslationFormulas T d).2.2.2.2.2.2.1
  let u : GaussianInt := ⟨-(P.q₁ : Int), (P.q : Int)⟩
  let v : GaussianInt := ⟨-(P.q₂ : Int), -(P.q : Int)⟩
  obtain ⟨hproper, hin1, hin2, _⟩ := (FordCoordinateConfiguration P).2 hq
  have reversals := (VectorRecursionLaws _ hproper.1).2.2.2.2 hproper
  have hu : BandVectors.1 ((FordRecursiveQuadruple P) 0)
      ((FordRecursiveQuadruple P) 1) = ⟨-(P.q₁ : Int), (P.q : Int)⟩ := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 ((FordRecursiveQuadruple P) 1)
            ((FordRecursiveQuadruple P) 0) := (reversals 0).1
      _ = _ := by rw [hin1]; ext <;> simp
  have hv : BandVectors.1 ((FordRecursiveQuadruple P) 0)
      ((FordRecursiveQuadruple P) 2) = ⟨-(P.q₂ : Int), -(P.q : Int)⟩ := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 ((FordRecursiveQuadruple P) 2)
            ((FordRecursiveQuadruple P) 0) := (reversals 1).1
      _ = _ := by rw [hin2]; ext <;> simp
  have pf (o : PeriodicSubtileIndex) :
      FootprintVertices (SubtileOccurrenceInterpretation S u v o) =
        FootprintVertices
          (SubtileOccurrenceInterpretation (P5064T3Rectangles P.q₁ P.q₂) u v o) := by
    cases h : o.label <;> simp only [SubtileOccurrenceInterpretation, h,
      transFoot, sf]
  have pe (o : PeriodicSubtileIndex) :
      FootprintEdges (SubtileOccurrenceInterpretation S u v o) =
        FootprintEdges
          (SubtileOccurrenceInterpretation (P5064T3Rectangles P.q₁ P.q₂) u v o) := by
    cases h : o.label <;> simp only [SubtileOccurrenceInterpretation, h,
      transEdge, se]
  have contacts := P5064T3RectangleContacts P.q₁ P.q₂ hs hrs
  dsimp only at contacts
  rw [← P.sum_q] at contacts
  dsimp only
  rw [hu, hv]
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rw [pe a, pe b, pf a, pf b]
    exact contacts a b hab
  · rw [sf 0 true, sf 1 true, qf 1 true]
    exact (P5064T3CrossParentSupport P.q₁ P.q₂ (by omega) hrs).2
  · intro z hz
    rw [sf 0 true, sf 0 false,
      (P5064T3PrecursorSupport P.q₁ P.q₂ (by omega) hrs).2, ← rm] at hz
    exact Or.inl (Or.inr (by rwa [shared]))

end ApollonianSuperharmonic

end
