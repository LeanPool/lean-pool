/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4733T1RepresentativeWalks
public import LeanPool.ApollonianSuperharmonic.P4733T1FacePairNormalForm
public import LeanPool.ApollonianSuperharmonic.P4733T1WalkExtension
public import LeanPool.ApollonianSuperharmonic.P4733T1WalkTransport
public import LeanPool.ApollonianSuperharmonic.P4733T1OccurrenceTranslation

-- [TABLET NODE: P4677T2PeriodicWalkAssembly]

/-!
# P4677T2PeriodicWalkAssembly

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4677T2PeriodicWalkAssembly
    (P Q S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (D : P4677T2DrawingData u v L)
    (hQcells : forall i s, (Q i s).cells ⊆ (P 0 true).cells)
    (hScells : forall i s, (S i s).cells ⊆ (P 0 false).cells)
    (hQfoot : forall i s,
      FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true))
    (hSfoot : forall i s,
      FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false))
    (hinner :
      TouchingTriple (Q 1 true) (S 2 false) (P 1 true) ∧
      TouchingTriple (Q 2 true) (S 1 false) (P 1 false) ∧
      TouchingTriple (Q 1 true) (P 1 true) (P 2 false) ∧
      TouchingTriple (S 1 false) (P 1 false) (P 2 true))
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
    (hperiodic : ∀ w f, rho (D.faceShift w f) = rho f + (w : GaussianInt))
    (hI1 : rho ⟨.I1, 0, 0⟩ ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false))
    (hI2 : rho ⟨.I2, 0, 0⟩ ∈ FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false))
    (hI3 : rho ⟨.I3, 0, 0⟩ ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true))
    (hI4 : rho ⟨.I4, 0, 0⟩ ∈ FootprintVertices (S 1 false) ∩ FootprintVertices (P 1 false))
    (htouch : ∀ (T U : ProtoTile) (x y : GaussianInt),
      TileTouching T U →
      x ∈ FootprintVertices T ∩ FootprintVertices U →
      y ∈ FootprintVertices T ∩ FootprintVertices U →
      ∃ p : List GaussianInt,
        p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ FootprintVertices T ∩ FootprintVertices U) ∧
        ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
          p = l₁ ++ a :: b :: l₂ →
          {a, b} ∈ FootprintEdges T ∩ FootprintEdges U)
    (hAB : ∃ p : List GaussianInt,
      p.head? = some (rho ⟨.I1, 0, 0⟩) ∧
      p.getLast? = some (rho ⟨.I2, 0, 0⟩) ∧
      (∀ z ∈ p, z ∈ FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false)) ∧
      ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ →
        {a, b} ∈ FootprintEdges (P 0 true) ∩ FootprintEdges (P 0 false)) :
    ∃ path : PeriodicSubtileFaceIndex → PeriodicSubtileFaceIndex → List GaussianInt,
      (∀ f g, path g f = (path f g).reverse) ∧
      (∀ w f g, path (D.faceShift w f) (D.faceShift w g) =
        (path f g).map (fun x => x + (w : GaussianInt))) ∧
      ∀ a b, AllowedSubtileIncidence a b →
        ∀ f g, f ≠ g →
        (∃ i, SixSubtileFaceVertices f i = a) →
        (∃ i, SixSubtileFaceVertices f i = b) →
        (∃ i, SixSubtileFaceVertices g i = a) →
        (∃ i, SixSubtileFaceVertices g i = b) →
        (path f g).head? = some (rho f) ∧
        (path f g).getLast? = some (rho g) ∧
        (∀ x ∈ path f g, x ∈
          FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v b)) ∧
        ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
          path f g = l₁ ++ x :: y :: l₂ →
          {x, y} ∈ FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
            FootprintEdges (SubtileOccurrenceInterpretation P u v b) := by
-- BODY
  classical
  obtain ⟨hnormal, hcover⟩ := P4733T1FacePairNormalForm D
  have hrows := P4733T1RepresentativeWalks P Q S u v
    (hQcells 1 true) (hScells 1 false) (hQfoot 1 true) (hSfoot 1 false)
    hinner.2.2.1.1 hinner.2.2.2.1 houter rho hcommon hI1.1 hI2.2 hI3 hI4 htouch hAB
  choose p hp using hrows
  obtain ⟨path, hreverse, htranslate, honrow, _⟩ :=
    P4733T1WalkExtension D hnormal p
  refine ⟨path, hreverse, htranslate, ?_⟩
  intro a b hab f g hfg hfa hfb hga hgb
  obtain ⟨⟨r, w, s⟩, hfaces, hedge⟩ :=
    hcover a b hab f g hfg hfa hfb hga hgb
  have hwalk := (P4733T1WalkTransport _ _ _ _ (p r) (hp r)).2 (w : GaussianInt)
  rw [← P4733T1OccurrenceTranslation P D w (P4733T1EdgeRow r).1.1,
    ← P4733T1OccurrenceTranslation P D w (P4733T1EdgeRow r).1.2,
    ← hperiodic w (P4733T1EdgeRow r).2.1,
    ← hperiodic w (P4733T1EdgeRow r).2.2] at hwalk
  have hfinal : P4733T1ContainedWalk
      (SubtileOccurrenceInterpretation P u v (D.shift w (P4733T1EdgeRow r).1.1))
      (SubtileOccurrenceInterpretation P u v (D.shift w (P4733T1EdgeRow r).1.2))
      (rho f) (rho g) (path f g) := by
    cases s
    · have hf : D.faceShift w (P4733T1EdgeRow r).2.2 = f :=
        congrArg Prod.fst hfaces
      have hg : D.faceShift w (P4733T1EdgeRow r).2.1 = g :=
        congrArg Prod.snd hfaces
      have hr := (P4733T1WalkTransport _ _ _ _ _ hwalk).1
      have hpath := honrow (r, w, false)
      rw [hfaces] at hpath
      rw [hpath]
      simpa [hf, hg] using hr
    · have hf : D.faceShift w (P4733T1EdgeRow r).2.1 = f :=
        congrArg Prod.fst hfaces
      have hg : D.faceShift w (P4733T1EdgeRow r).2.2 = g :=
        congrArg Prod.snd hfaces
      have hpath := honrow (r, w, true)
      rw [hfaces] at hpath
      rw [hpath]
      simpa [hf, hg] using hwalk
  rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hfinal
  · simpa only [P4733T1ContainedWalk, Set.inter_comm] using hfinal

end ApollonianSuperharmonic

end
