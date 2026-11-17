/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeRow
public import LeanPool.ApollonianSuperharmonic.P4733T1RowIncidence
public import LeanPool.ApollonianSuperharmonic.P4733T1ContainedWalk
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance

-- [TABLET NODE: P4733T1RepresentativeWalks]

/-!
# P4733T1RepresentativeWalks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1RepresentativeWalks
    (P Q S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
    (hQcells : (Q 1 true).cells ⊆ (P 0 true).cells)
    (hScells : (S 1 false).cells ⊆ (P 0 false).cells)
    (hQfoot : FootprintVertices (Q 1 true) ⊆ FootprintVertices (P 0 true))
    (hSfoot : FootprintVertices (S 1 false) ⊆ FootprintVertices (P 0 false))
    (hAC : TileTouching (Q 1 true) (P 1 true))
    (hBD : TileTouching (S 1 false) (P 1 false))
    (houter :
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
          (P 2 false))
    (rho : PeriodicSubtileFaceIndex → GaussianInt)
    (hcommon : ∀ f i, rho f ∈ FootprintVertices
      (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i)))
    (hI1 : rho ⟨.I1, 0, 0⟩ ∈ FootprintVertices (Q 1 true))
    (hI2 : rho ⟨.I2, 0, 0⟩ ∈ FootprintVertices (S 1 false))
    (hI3 : rho ⟨.I3, 0, 0⟩ ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true))
    (hI4 : rho ⟨.I4, 0, 0⟩ ∈ FootprintVertices (S 1 false) ∩ FootprintVertices (P 1 false))
    (htouch : ∀ (T U : ProtoTile) (x y : GaussianInt), TileTouching T U →
      x ∈ FootprintVertices T ∩ FootprintVertices U →
      y ∈ FootprintVertices T ∩ FootprintVertices U →
      ∃ p, P4733T1ContainedWalk T U x y p)
    (hAB : ∃ p, P4733T1ContainedWalk (P 0 true) (P 0 false)
      (rho ⟨.I1, 0, 0⟩) (rho ⟨.I2, 0, 0⟩) p) :
    ∀ r : Fin 18, ∃ p : List GaussianInt,
      P4733T1ContainedWalk
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.1)
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.2)
        (rho (P4733T1EdgeRow r).2.1) (rho (P4733T1EdgeRow r).2.2) p := by
-- BODY
  classical
  have translate_zero (T : ProtoTile) : TileTranslation T 0 = T := by
    cases T with
    | mk cells anchor =>
      simp only [TileTranslation]
      rw [ProtoTile.mk.injEq]
      constructor
      · ext z
        simp [GaussianTranslation]
      · simp [GaussianTranslation]
  have translate_comp (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) := by
    cases T with
    | mk cells anchor =>
      simp only [TileTranslation]
      rw [ProtoTile.mk.injEq]
      constructor
      · rw [Finset.image_image]
        congr 1
        funext x
        simp [GaussianTranslation, add_assoc]
      · simp [GaussianTranslation, add_assoc]
  have skip (T U V : ProtoTile) (h : TouchingTriple T U V) : TileTouching T V :=
    ((TouchingTriplePermutations T U V).mp h).1.1
  have lift (T T' U : ProtoTile) (hc : T.cells ⊆ T'.cells)
      (hv : FootprintVertices T ⊆ FootprintVertices T')
      (x y : GaussianInt) (p : List GaussianInt)
      (h : P4733T1ContainedWalk T U x y p) :
      P4733T1ContainedWalk T' U x y p := by
    refine ⟨h.1, h.2.1, ?_, ?_⟩
    · intro z hz
      exact ⟨hv (h.2.2.1 z hz).1, (h.2.2.1 z hz).2⟩
    · intro a b l₁ l₂ hp
      obtain ⟨ht, hu⟩ := h.2.2.2 a b l₁ l₂ hp
      rcases ht with ⟨c, hc', he⟩
      exact ⟨⟨c, hc hc', he⟩, hu⟩
  have outerWalk (r : Fin 18)
      (h : TileTouching
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.1)
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.2)) :
      ∃ p, P4733T1ContainedWalk
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.1)
        (SubtileOccurrenceInterpretation P u v (P4733T1EdgeRow r).1.2)
        (rho (P4733T1EdgeRow r).2.1) (rho (P4733T1EdgeRow r).2.2) p := by
    obtain ⟨_, _, ⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩, ⟨l, hl⟩⟩ :=
      P4733T1RowIncidence r
    apply htouch _ _ _ _ h
    · exact ⟨hi ▸ hcommon _ i, hj ▸ hcommon _ j⟩
    · exact ⟨hk ▸ hcommon _ k, hl ▸ hcommon _ l⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := houter
  intro r
  fin_cases r
  · simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using hAB
  · apply outerWalk 1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using h1.1
  · apply outerWalk 2
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using h3.1
  · have hx : rho ⟨.I1, 0, 0⟩ ∈ FootprintVertices (P 1 true) := by
      simpa [SixSubtileFaceVertices, SubtileOccurrenceInterpretation, translate_zero]
        using hcommon ⟨.I1, 0, 0⟩ 2
    obtain ⟨p, hp⟩ := htouch _ _ _ _ hAC ⟨hI1, hx⟩ hI3
    have h := lift _ _ _ hQcells hQfoot _ _ p hp
    exact ⟨p, by simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation,
      translate_zero] using h⟩
  · apply outerWalk 4
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using h5.1
  · apply outerWalk 5
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using skip _ _ _ h4
  · apply outerWalk 6
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using skip _ _ _ h1
  · apply outerWalk 7
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using skip _ _ _ h2
  · apply outerWalk 8
    have h := (TileTouchingCovariance _ _ (-u - v)).1.mp h3.2.1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_comp,
      translate_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  · apply outerWalk 9
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero,
      sub_eq_add_neg] using h6.1
  · have hx : rho ⟨.I2, 0, 0⟩ ∈ FootprintVertices (P 1 false) := by
      simpa [SixSubtileFaceVertices, SubtileOccurrenceInterpretation, translate_zero]
        using hcommon ⟨.I2, 0, 0⟩ 2
    obtain ⟨p, hp⟩ := htouch _ _ _ _ hBD ⟨hI2, hx⟩ hI4
    have h := lift _ _ _ hScells hSfoot _ _ p hp
    exact ⟨p, by simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation,
      translate_zero] using h⟩
  · apply outerWalk 11
    have h := (TileTouchingCovariance _ _ (-v)).1.mp h1.2.1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_comp,
      translate_zero] using h
  · apply outerWalk 12
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using skip _ _ _ h6
  · apply outerWalk 13
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using h7.1
  · apply outerWalk 14
    have h := (TileTouchingCovariance _ _ (-u - v)).1.mp h5.2.1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_comp,
      translate_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  · apply outerWalk 15
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_zero] using skip _ _ _ h8
  · apply outerWalk 16
    have h := (TileTouchingCovariance _ _ u).1.mp h7.2.1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_comp,
      translate_zero] using h
  · apply outerWalk 17
    have h := (TileTouchingCovariance _ _ u).1.mp h8.2.1
    simpa [P4733T1EdgeRow, SubtileOccurrenceInterpretation, translate_comp,
      translate_zero] using h

end ApollonianSuperharmonic

end
