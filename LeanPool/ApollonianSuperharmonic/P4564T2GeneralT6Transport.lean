/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRawSupport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhaseUnique
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.P4055T1PackingGridEquivalence

-- [TABLET NODE: P4564T2GeneralT6Transport]

/-!
# P4564T2GeneralT6Transport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace GeneralT6Geometry

private theorem normalized23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin 3), ∀ (g : BandPackingSymmetry),
            (BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q 0, q
            a.succ, q (a + 1).succ, q (a + 2).succ])) → (((BandPackingSymmetryQuadrupleAction g
            ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]) 3).1 <
            ((BandPackingSymmetryQuadrupleAction g ![q 0, q a.succ, q (a + 1).succ, q (a +
            2).succ]) 2).1) ) := by
  classical
  intro q a g cfg
  have hs := cfg.secondProper.2 0
  change (cfg.secondPredecessor 1).1 < (cfg.secondPredecessor 0).1 at hs
  simpa only [cfg.secondChild, cfg.secondParentOne] using hs

private theorem order_forces :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (a : Fin 3),
            ∀ (g : BandPackingSymmetry),
              (q (2 : Fin (4 : ℕ))).1 ≤ (q (1 : Fin (4 : ℕ))).1 →
                (q (3 : Fin (4 : ℕ))).1 ≤ (q (2 : Fin (4 : ℕ))).1 →
                  (∀ (C : CircleCoordinates),
                      (BandPackingSymmetryCircleAction g C).1 = C.1) →
                    (BandPackingSymmetryQuadrupleAction g
                            ![q (0 : Fin (4 : ℕ)), q a.succ,
                              q (a + (1 : Fin (3 : ℕ))).succ,
                              q (a + (2 : Fin (3 : ℕ))).succ]
                            (2 : Fin (4 : ℕ))).1 <
                        (BandPackingSymmetryQuadrupleAction g
                            ![q (0 : Fin (4 : ℕ)), q a.succ,
                              q (a + (1 : Fin (3 : ℕ))).succ,
                              q (a + (2 : Fin (3 : ℕ))).succ]
                            (1 : Fin (4 : ℕ))).1 →
                      ((BandPackingSymmetryQuadrupleAction g
                                ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ])
                              3).1 <
                          ((BandPackingSymmetryQuadrupleAction g
                                ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ])
                              2).1 →
                        a = 0 ∧ BandPackingSymmetryReversesOrientation g = false
    ) := by
  classical
  intro q a g h12 h23 curvature normalized12 normalized23
  cases hg : BandPackingSymmetryReversesOrientation g <;> fin_cases a <;>
    simp [BandPackingSymmetryQuadrupleAction, hg, curvature] at normalized12 normalized23 ⊢ <;>
    omega

private theorem hrotate :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (![q 0, q (0 : Fin 3).succ, q (0 + 1 : Fin 3).succ, q
            (0 + 2 : Fin 3).succ] : Fin 4 → CircleCoordinates) = q ) := by
  classical
  intro q
  funext i
  fin_cases i <;> rfl

private theorem action :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation g = false) → (∀ (p :
            Fin 4 → CircleCoordinates), ∀ (i : Fin 4), BandPackingSymmetryQuadrupleAction g p i =
            BandPackingSymmetryCircleAction g (p i)) ) := by
  classical
  intro g hg p i
  fin_cases i <;> simp [BandPackingSymmetryQuadrupleAction, hg]

private theorem transport :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation g = false) → (∀ (p :
            Fin 4 → CircleCoordinates), ∀ (X : ProtoTile), ∀ (F : Fin 3 → Bool → ProtoTile),
            (ProperBandQuadruple p) → ((BandPrototile (p 0) X) → ((∀ i, ∀ s,
            BandSubtileOccurrence p X i s (F i s)) → ((∀ x, x ∈ X.cells ↔ ∃ i s, x ∈ (F i
            s).cells) → ((BandPackingSymmetryScopedPhase g p false) → (∀ i, ∀ s,
            BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g p)
            (BandPackingSymmetryTileAction g X) i s (BandPackingSymmetryTileAction g (F i
            s)))))))) ) := by
  classical
  intro g hg p X F hp hX hF hFu hph
  obtain ⟨d, e, F', hd, he, hF', ho, hu⟩ :=
    (BandPackingSymmetryCovariance g).2.2 p X F hp hX hF hFu
  have hd0 := BandPackingSymmetryScopedPhaseUnique g p hp d false hd hph
  subst d
  have heq (i : Fin 3) (s : Bool) : e (i, s) = (i, s) := by
    simpa [hg] using he i s
  intro i s
  have hid : F' i s = BandPackingSymmetryTileAction g (F i s) := by
    simpa only [heq] using hF' i s
  simpa only [hid] using ho i s

private theorem predecessor :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (g : BandPackingSymmetry), ∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), (ProperBandQuadruple r) → ((r (0 : Fin (4 : ℕ)) = q (1 : Fin (4 :
            ℕ))) → ((r (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → ((r (3 : Fin (4 : ℕ)) = q (3 :
            Fin (4 : ℕ))) → (((BandPackingSymmetryQuadrupleAction g q (3 : Fin (4 : ℕ))).1 <
            (BandPackingSymmetryQuadrupleAction g q (2 : Fin (4 : ℕ))).1) → (∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), (∀ (p :
                Fin 4 → CircleCoordinates), ∀ (i :
            Fin 4), BandPackingSymmetryQuadrupleAction g p i = BandPackingSymmetryCircleAction g
            (p i)) → (BandPackingSymmetryQuadrupleAction g r = cfg.firstPredecessor)))))) ) := by
  classical
  intro q g r hr hr0 hr2 hr3 normalized23 cfg action
  have child : BandPackingSymmetryQuadrupleAction g r 0 = cfg.firstPredecessor 0 := by
    rw [action, hr0, cfg.firstChild, action]
  obtain ⟨k, hk, _⟩ := BandPredecessorNoCollision
    (BandPackingSymmetryQuadrupleAction g r) cfg.firstPredecessor
    (BandPackingSymmetryProperCovariance g r hr) cfg.firstProper child
  have hk0 : k = 0 := by
    fin_cases k
    · rfl
    · have he := hk 1
      change cfg.firstPredecessor 2 = BandPackingSymmetryQuadrupleAction g r 3 at he
      rw [cfg.firstParentTwo, action r 3, hr3, ← action q 3] at he
      have hc := congrArg Prod.fst he
      omega
    · have he := hk 2
      change cfg.firstPredecessor 3 = BandPackingSymmetryQuadrupleAction g r 2 at he
      rw [cfg.firstParentThree, action r 2, hr2, ← action q 2] at he
      have hc := congrArg Prod.fst he
      omega
  subst k
  funext i
  fin_cases i
  · exact child
  · exact (hk 0).symm
  · exact (hk 1).symm
  · exact (hk 2).symm

private theorem compare :
    (by
      classical
      exact
        ∀ (p : Fin 4 → CircleCoordinates), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (i : Fin 3), ∀ (s : Bool), (BandSubtileOccurrence p
            X i s U) → ((BandSubtileOccurrence p Y i s V) → ((TileCentroid X = TileCentroid Y) →
            (U.cells = V.cells ∧ (U.cells = ∅ → U.anchor = V.anchor) ∧ FootprintVertices U =
            FootprintVertices V ∧ TileCentroid U = TileCentroid V))) ) := by
  classical
  intro p X Y U V i s hU hV hXY
  have hc : TileCentroid U = TileCentroid V := by
    have hu := hU.2.2
    rw [hXY] at hu
    exact sub_left_injective (hu.trans hV.2.2.symm)
  obtain ⟨hcell, hanchor⟩ := BandPrototileCentroidUnique (p i.succ) U V hU.1 hV.1 hc
  exact ⟨hcell, hanchor, (ProtoTileObservableExtensionality U V hcell hanchor).1, hc⟩

private theorem translated :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (w : GaussianInt), (X.cells = Y.cells) →
            ((FootprintVertices X = FootprintVertices Y) → (FootprintVertices (TileTranslation X
            w) = FootprintVertices (TileTranslation Y w) ∧ FootprintEdges (TileTranslation X w) =
            FootprintEdges (TileTranslation Y w))) ) := by
  classical
  intro X Y w hc hv
  have he : FootprintEdges X = FootprintEdges Y := by
    unfold FootprintEdges
    rw [hc]
  exact ⟨by rw [(TileTranslationFormulas X w).2.2.2.2.2.1,
    (TileTranslationFormulas Y w).2.2.2.2.2.1, hv],
    by rw [(TileTranslationFormulas X w).2.2.2.2.2.2.1,
      (TileTranslationFormulas Y w).2.2.2.2.2.2.1, he]⟩

private theorem samePeriodic :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let P' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (P i s)
        (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (BandPackingSymmetryTileAction g (P i s)).cells =
            (cert.P i s).cells ∧ ((BandPackingSymmetryTileAction g (P i s)).cells = ∅ →
            (BandPackingSymmetryTileAction g (P i s)).anchor = (cert.P i s).anchor) ∧
            FootprintVertices (BandPackingSymmetryTileAction g (P i s)) = FootprintVertices
            (cert.P i s) ∧ TileCentroid (BandPackingSymmetryTileAction g (P i s)) = TileCentroid
            (cert.P i s)) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (w : GaussianInt), (X.cells
            = Y.cells) → ((FootprintVertices X = FootprintVertices Y) → (FootprintVertices
            (TileTranslation X w) = FootprintVertices (TileTranslation Y w) ∧ FootprintEdges
            (TileTranslation X w) = FootprintEdges (TileTranslation Y w)))) → (∀ (o :
            PeriodicSubtileIndex), FootprintVertices (SubtileOccurrenceInterpretation P' cert.u
            cert.v o) = FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            o) ∧ FootprintEdges (SubtileOccurrenceInterpretation P' cert.u cert.v o) =
            FootprintEdges (SubtileOccurrenceInterpretation cert.P cert.u cert.v o))) ) := by
  classical
  intro q T g C P cfg cert P' sameP translated o
  cases o with
  | mk label m n =>
    cases label <;> apply translated <;>
      first | exact (sameP _ _).1 | exact (sameP _ _).2.2.1

private theorem callerClassification :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let P' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (P i s)
        (∀ (o : PeriodicSubtileIndex), FootprintVertices (SubtileOccurrenceInterpretation P'
            cert.u cert.v o) = FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v o) ∧ FootprintEdges (SubtileOccurrenceInterpretation P' cert.u cert.v o) =
            FootprintEdges (SubtileOccurrenceInterpretation cert.P cert.u cert.v o)) → ((
        let u := cert.u;
        let v := cert.v; ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b →
            ((FootprintEdges (SubtileOccurrenceInterpretation cert.P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation cert.P u v b)).Nonempty → AllowedSubtileIncidence a
            b) ∧ (¬AllowedSubtileIncidence a b → FootprintVertices
            (SubtileOccurrenceInterpretation cert.P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation cert.P u v b) = ∅ ∨ (FootprintVertices
            (SubtileOccurrenceInterpretation cert.P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation cert.P u v b)).Subsingleton)) → (∀ (o :
            PeriodicSubtileIndex), ∀ (p : PeriodicSubtileIndex), (o ≠ p) → (((FootprintEdges
            (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P' cert.u cert.v p)).Nonempty →
            AllowedSubtileIncidence o p) ∧ (¬ AllowedSubtileIncidence o p → FootprintVertices
            (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P' cert.u cert.v p) = ∅ ∨ (FootprintVertices
            (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P' cert.u cert.v p)).Subsingleton)))) ) := by
  classical
  intro q T g C P cfg cert P' samePeriodic classification o p hop
  simpa only [(samePeriodic o).1, (samePeriodic p).1,
    (samePeriodic o).2, (samePeriodic p).2] using classification o p hop

private theorem callerRaw :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let P' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (P i s)
        let Q' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (Q i s)
        let S' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (S i s)
        (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (BandPackingSymmetryTileAction g (P i s)).cells =
            (cert.P i s).cells ∧ ((BandPackingSymmetryTileAction g (P i s)).cells = ∅ →
            (BandPackingSymmetryTileAction g (P i s)).anchor = (cert.P i s).anchor) ∧
            FootprintVertices (BandPackingSymmetryTileAction g (P i s)) = FootprintVertices
            (cert.P i s) ∧ TileCentroid (BandPackingSymmetryTileAction g (P i s)) = TileCentroid
            (cert.P i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (BandPackingSymmetryTileAction g
            (Q i s)).cells = (cert.Q i s).cells ∧ ((BandPackingSymmetryTileAction g (Q i
            s)).cells = ∅ → (BandPackingSymmetryTileAction g (Q i s)).anchor = (cert.Q i
            s).anchor) ∧ FootprintVertices (BandPackingSymmetryTileAction g (Q i s)) =
            FootprintVertices (cert.Q i s) ∧ TileCentroid (BandPackingSymmetryTileAction g (Q i
            s)) = TileCentroid (cert.Q i s)) → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            (BandPackingSymmetryTileAction g (S i s)).cells = (cert.S i s).cells ∧
            ((BandPackingSymmetryTileAction g (S i s)).cells = ∅ → (BandPackingSymmetryTileAction
            g (S i s)).anchor = (cert.S i s).anchor) ∧ FootprintVertices
            (BandPackingSymmetryTileAction g (S i s)) = FootprintVertices (cert.S i s) ∧
            TileCentroid (BandPackingSymmetryTileAction g (S i s)) = TileCentroid (cert.S i s)) →
            ((FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (1 :
            Fin (3 : ℕ)) true) ⊆ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∧ FootprintVertices (cert.P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ⊆
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (2 :
            Fin (3 : ℕ)) false) ∪ FootprintVertices (cert.Q (0 : Fin (3 : ℕ)) false) ∪
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (1 :
            Fin (3 : ℕ)) false)) → (FootprintVertices (P' 0 true) ∩ FootprintVertices (P' 1 true)
            ⊆ FootprintVertices (Q' 1 true) ∩ FootprintVertices (P' 1 true) ∧ FootprintVertices
            (P' 0 true) ∩ FootprintVertices (P' 0 false) ⊆ (FootprintVertices (Q' 1 true) ∩
            FootprintVertices (S' 2 false)) ∪ FootprintVertices (Q' 0 false) ∪ (FootprintVertices
            (Q' 2 true) ∩ FootprintVertices (S' 1 false)))))) ) := by
  classical
  intro q T g C P Q S cfg cert P' Q' S' sameP sameQ sameS raw
  simpa only [P', Q', S', (sameP _ _).2.2.1, (sameQ _ _).2.2.1,
    (sameS _ _).2.2.1] using raw

private theorem period_u :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), (BandPackingSymmetryReversesOrientation g = false) →
            ((BandPackingSymmetryScopedPhase g q false) → (∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let L := BandPackingSymmetryVectorAction g
        cert.u = L (BandVectors.1 (q 0) (q 1)))) ) := by
  classical
  intro q T g C hg hphase cfg cert L
  rw [cert.period_u]
  simpa [BandPackingSymmetryScopedPhase, hg, L] using (hphase 0).2.1

private theorem period_v :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), (BandPackingSymmetryReversesOrientation g = false) →
            ((BandPackingSymmetryScopedPhase g q false) → (∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let L := BandPackingSymmetryVectorAction g
        cert.v = L (BandVectors.1 (q 0) (q 2)))) ) := by
  classical
  intro q T g C hg hphase cfg cert L
  rw [cert.period_v]
  simpa [BandPackingSymmetryScopedPhase, hg, L] using (hphase 1).2.1

private theorem occurrence_image :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (g : BandPackingSymmetry), ∀ (C :
            BandCircle), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (cfg :
            BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g q)), ∀ (cert :
            BandOrderedGeneralLayoutCertificate (BandPackingSymmetryQuadrupleAction g q) cfg C
                (BandPackingSymmetryTileAction g T)),
        let P' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (P i s)
        let L := BandPackingSymmetryVectorAction g
        (cert.u = L (BandVectors.1 (q 0) (q 1))) → ((cert.v = L (BandVectors.1 (q 0) (q 2))) →
            ((∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀
            (o : PeriodicSubtileIndex), BandPackingSymmetryTileAction g
            (SubtileOccurrenceInterpretation S u v o) = SubtileOccurrenceInterpretation (fun (i :
            Fin (3 : ℕ)) (s : Bool) => BandPackingSymmetryTileAction g (S i s))
            (BandPackingSymmetryVectorAction g u) (BandPackingSymmetryVectorAction g v) o) → (∀
            (o : PeriodicSubtileIndex), BandPackingSymmetryTileAction g
            (SubtileOccurrenceInterpretation P (BandVectors.1 (q 0) (q 1)) (BandVectors.1 (q 0)
            (q 2)) o) = SubtileOccurrenceInterpretation P' cert.u cert.v o))) ) := by
  classical
  intro q T g C P cfg cert P' L period_u period_v occurrence_transport o
  rw [occurrence_transport, period_u, period_v]

private theorem linj :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let L := BandPackingSymmetryVectorAction g
        ∀ (f : GaussianInt ≃ GaussianInt), (∀ (z : GaussianInt), (f : GaussianInt → GaussianInt)
            z = BandPackingSymmetryVectorAction g z) → (Function.Injective L) ) := by
  classical
  intro g L f hf x y hxy
  apply f.injective
  simpa only [hf] using hxy

private theorem mem_vertices :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let L := BandPackingSymmetryVectorAction g
        (∀ (T : ProtoTile), FootprintVertices (BandPackingSymmetryTileAction g T) =
            BandPackingSymmetryVectorAction g '' FootprintVertices T) → ((Function.Injective L) →
            (∀ (X : ProtoTile), ∀ (x : GaussianInt), L x ∈ FootprintVertices
            (BandPackingSymmetryTileAction g X) ↔ x ∈ FootprintVertices X)) ) := by
  classical
  intro g L vertices_image linj X x
  rw [vertices_image]
  constructor
  · rintro ⟨z, hz, he⟩
    exact linj he ▸ hz
  · intro hx
    exact ⟨x, hx, rfl⟩

end GeneralT6Geometry

theorem P4564T2GeneralT6Transport (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (T : ProtoTile) (hT : BandPrototile (q 0) T)
    (a : Fin 3) (g : BandPackingSymmetry)
    (hphase : BandPackingSymmetryScopedPhase g
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] false)
    (hpredecessor : ∀ r : Fin 4 → CircleCoordinates, ProperBandQuadruple r →
      r 0 = (![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] : Fin 4 → CircleCoordinates) 1 →
      r 2 = (![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] : Fin 4 → CircleCoordinates) 2 →
      r 3 = (![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] : Fin 4 → CircleCoordinates) 3 →
      BandPackingSymmetryScopedPhase g r false)
    (cfg : BandOrderedGeneralConfiguration
      (BandPackingSymmetryQuadrupleAction g ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]))
    (C : BandCircle)
    (cert : BandOrderedGeneralLayoutCertificate
      (BandPackingSymmetryQuadrupleAction g ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]) cfg C
      (BandPackingSymmetryTileAction g T)) :
    (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r →
      r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
      (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
      1 < (q 2).1 →
      ∀ (P Q S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence q T i s (P i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
      (∀ i s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
      (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
      (∀ i s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
      (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
      (let u := BandVectors.1 (q 0) (q 1)
       let v := BandVectors.1 (q 0) (q 2)
       (∀ a b : PeriodicSubtileIndex, a ≠ b →
         ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
             FootprintEdges
               (SubtileOccurrenceInterpretation P u v b)).Nonempty →
           AllowedSubtileIncidence a b) ∧
         (¬ AllowedSubtileIncidence a b →
           FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
               FootprintVertices
                 (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
             (FootprintVertices
                  (SubtileOccurrenceInterpretation P u v a) ∩
                FootprintVertices
                  (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
         FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
         (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
           FootprintVertices (Q 0 false) ∪
           (FootprintVertices (Q 2 true) ∩
             FootprintVertices (S 1 false)))) := by
-- BODY
  classical
  intro r hr hr0 hr2 hr3 h12 h23 hlarge P Q S hP hPu hQ hQu hS hSu
  -- Strict normalized curvature order fixes the cyclic and orientation choices.
  have curvature := (BandPackingSymmetryCovariance g).1
  have normalized12 := cfg.order12
  have normalized23 :
      ((BandPackingSymmetryQuadrupleAction g
        ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]) 3).1 <
      ((BandPackingSymmetryQuadrupleAction g
        ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]) 2).1 := GeneralT6Geometry.normalized23
            q a g cfg
  have order_forces : a = 0 ∧ BandPackingSymmetryReversesOrientation g = false :=
      GeneralT6Geometry.order_forces q a g h12 h23 curvature
      normalized12 normalized23
  obtain ⟨rfl, hg⟩ := order_forces
  have hrotate :
      (![q 0, q (0 : Fin 3).succ, q (0 + 1 : Fin 3).succ,
        q (0 + 2 : Fin 3).succ] : Fin 4 → CircleCoordinates) = q := GeneralT6Geometry.hrotate q
  rw [hrotate] at hphase hpredecessor normalized23
  revert cert cfg
  rw [hrotate]
  intro cfg cert
  have action (p : Fin 4 → CircleCoordinates) (i : Fin 4) :
      BandPackingSymmetryQuadrupleAction g p i =
        BandPackingSymmetryCircleAction g (p i) := GeneralT6Geometry.action g hg p i
  -- The supplied phase fixes signs independently of orientation parity.
  have transport (p : Fin 4 → CircleCoordinates) (X : ProtoTile)
      (F : Fin 3 → Bool → ProtoTile) (hp : ProperBandQuadruple p)
      (hX : BandPrototile (p 0) X)
      (hF : ∀ i s, BandSubtileOccurrence p X i s (F i s))
      (hFu : ∀ x, x ∈ X.cells ↔ ∃ i s, x ∈ (F i s).cells)
      (hph : BandPackingSymmetryScopedPhase g p false) :
      ∀ i s, BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g p)
        (BandPackingSymmetryTileAction g X) i s
        (BandPackingSymmetryTileAction g (F i s)) := GeneralT6Geometry.transport g hg p X F hp hX
            hF hFu hph
  let P' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (P i s)
  let Q' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (Q i s)
  let S' : Fin 3 → Bool → ProtoTile := fun i s => BandPackingSymmetryTileAction g (S i s)
  have hP' := transport q T P hq hT hP hPu hphase
  have hrphase : BandPackingSymmetryScopedPhase g r false :=
    hpredecessor r hr (by simpa using hr0) (by simpa using hr2) (by simpa using hr3)
  have hQ' := transport r (P 0 true) Q hr (by simpa [hr0] using (hP 0 true).1)
    hQ hQu hrphase
  have hS' := transport r (P 0 false) S hr (by simpa [hr0] using (hP 0 false).1)
    hS hSu hrphase
  -- Strict order excludes the two nontrivial predecessor rotations.
  have predecessor : BandPackingSymmetryQuadrupleAction g r = cfg.firstPredecessor :=
      GeneralT6Geometry.predecessor q g r hr hr0 hr2 hr3 normalized23 cfg action
  rw [predecessor] at hQ' hS'
  -- Compare observables without asserting equality of nonempty records.
  have compare (p : Fin 4 → CircleCoordinates) (X Y U V : ProtoTile)
      (i : Fin 3) (s : Bool)
      (hU : BandSubtileOccurrence p X i s U)
      (hV : BandSubtileOccurrence p Y i s V)
      (hXY : TileCentroid X = TileCentroid Y) :
      U.cells = V.cells ∧ (U.cells = ∅ → U.anchor = V.anchor) ∧
        FootprintVertices U = FootprintVertices V ∧ TileCentroid U = TileCentroid V :=
            GeneralT6Geometry.compare p X Y U V i s hU hV hXY
  have sameP (i : Fin 3) (s : Bool) :=
    compare _ _ _ _ _ i s (hP' i s) (cert.outer_occurrence i s) rfl
  have sameQ (i : Fin 3) (s : Bool) :=
    compare _ _ _ _ _ i s (hQ' i s) (cert.plus_occurrence i s) (sameP 0 true).2.2.2
  have sameS (i : Fin 3) (s : Bool) :=
    compare _ _ _ _ _ i s (hS' i s) (cert.minus_occurrence i s) (sameP 0 false).2.2.2
  have translated (X Y : ProtoTile) (w : GaussianInt)
      (hc : X.cells = Y.cells) (hv : FootprintVertices X = FootprintVertices Y) :
      FootprintVertices (TileTranslation X w) = FootprintVertices (TileTranslation Y w) ∧
      FootprintEdges (TileTranslation X w) = FootprintEdges (TileTranslation Y w) :=
          GeneralT6Geometry.translated X Y w hc hv
  have samePeriodic (o : PeriodicSubtileIndex) :
      FootprintVertices (SubtileOccurrenceInterpretation P' cert.u cert.v o) =
        FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v o) ∧
      FootprintEdges (SubtileOccurrenceInterpretation P' cert.u cert.v o) =
        FootprintEdges (SubtileOccurrenceInterpretation cert.P cert.u cert.v o) :=
            GeneralT6Geometry.samePeriodic q T g C P cfg cert sameP translated o
  -- Original periodic classification and raw support are separate inputs.
  have classification := BandOriginalOccurrenceIntersectionClassification _ cfg C _ cert
  have raw := BandOrderedGeneralRawSupport _ cfg C _ cert
  have callerClassification (o p : PeriodicSubtileIndex) (hop : o ≠ p) :
      ((FootprintEdges (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P' cert.u cert.v p)).Nonempty →
        AllowedSubtileIncidence o p) ∧
      (¬ AllowedSubtileIncidence o p →
        FootprintVertices (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩
            FootprintVertices (SubtileOccurrenceInterpretation P' cert.u cert.v p) = ∅ ∨
          (FootprintVertices (SubtileOccurrenceInterpretation P' cert.u cert.v o) ∩
            FootprintVertices (SubtileOccurrenceInterpretation P' cert.u cert.v p)).Subsingleton)
                := GeneralT6Geometry.callerClassification q T g C P cfg cert samePeriodic
                classification o p hop
  have callerRaw :
      FootprintVertices (P' 0 true) ∩ FootprintVertices (P' 1 true) ⊆
        FootprintVertices (Q' 1 true) ∩ FootprintVertices (P' 1 true) ∧
      FootprintVertices (P' 0 true) ∩ FootprintVertices (P' 0 false) ⊆
        (FootprintVertices (Q' 1 true) ∩ FootprintVertices (S' 2 false)) ∪
          FootprintVertices (Q' 0 false) ∪
          (FootprintVertices (Q' 2 true) ∩ FootprintVertices (S' 1 false)) :=
              GeneralT6Geometry.callerRaw q T g C P Q S cfg cert sameP sameQ sameS raw
  -- Use the same false phase for the ordered periods before pulling back.
  let L := BandPackingSymmetryVectorAction g
  have period_u : cert.u = L (BandVectors.1 (q 0) (q 1)) := GeneralT6Geometry.period_u q T g C hg
      hphase cfg cert
  have period_v : cert.v = L (BandVectors.1 (q 0) (q 2)) := GeneralT6Geometry.period_v q T g C hg
      hphase cfg cert
  obtain ⟨_, _, _, _, _, _, _, vertices_image, edges_image, subsingleton_transport,
    occurrence_transport⟩ := BandPackingSymmetryTilingTransport g
  have occurrence_image (o : PeriodicSubtileIndex) :
      BandPackingSymmetryTileAction g
        (SubtileOccurrenceInterpretation P (BandVectors.1 (q 0) (q 1))
          (BandVectors.1 (q 0) (q 2)) o) =
      SubtileOccurrenceInterpretation P' cert.u cert.v o := GeneralT6Geometry.occurrence_image q
          T g C P cfg cert period_u period_v occurrence_transport o
  obtain ⟨f, hf, _, _⟩ := P4055T1PackingGridEquivalence g
  have linj : Function.Injective L := GeneralT6Geometry.linj g f hf
  have mem_vertices (X : ProtoTile) (x : GaussianInt) :
      L x ∈ FootprintVertices (BandPackingSymmetryTileAction g X) ↔
        x ∈ FootprintVertices X := GeneralT6Geometry.mem_vertices g vertices_image linj X x
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro o p hop
    obtain ⟨hallowed, hraw⟩ := callerClassification o p hop
    rw [← occurrence_image o, ← occurrence_image p] at hallowed hraw
    constructor
    · rintro ⟨e, heo, hep⟩
      apply hallowed
      rw [edges_image, edges_image]
      exact ⟨e.image L, ⟨e, heo, rfl⟩, ⟨e, hep, rfl⟩⟩
    · intro hnot
      rcases hraw hnot with hempty | hsub
      · left
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hm := And.intro ((mem_vertices _ x).mpr hx.1)
          ((mem_vertices _ x).mpr hx.2)
        change L x ∈ FootprintVertices (BandPackingSymmetryTileAction g
            (SubtileOccurrenceInterpretation P (BandVectors.1 (q 0) (q 1))
              (BandVectors.1 (q 0) (q 2)) o)) ∩
          FootprintVertices (BandPackingSymmetryTileAction g
            (SubtileOccurrenceInterpretation P (BandVectors.1 (q 0) (q 1))
              (BandVectors.1 (q 0) (q 2)) p)) at hm
        rw [hempty] at hm
        exact hm
      · right
        exact (subsingleton_transport _ _).mpr hsub
  · intro x hx
    have hm := callerRaw.1
      ⟨(mem_vertices (P 0 true) x).mpr hx.1, (mem_vertices (P 1 true) x).mpr hx.2⟩
    exact ⟨(mem_vertices (Q 1 true) x).mp hm.1, (mem_vertices (P 1 true) x).mp hm.2⟩
  · intro x hx
    have hm := callerRaw.2
      ⟨(mem_vertices (P 0 true) x).mpr hx.1, (mem_vertices (P 0 false) x).mpr hx.2⟩
    rcases hm with (hm | hm) | hm
    · exact Or.inl (Or.inl
        ⟨(mem_vertices (Q 1 true) x).mp hm.1, (mem_vertices (S 2 false) x).mp hm.2⟩)
    · exact Or.inl (Or.inr ((mem_vertices (Q 0 false) x).mp hm))
    · exact Or.inr
        ⟨(mem_vertices (Q 2 true) x).mp hm.1, (mem_vertices (S 1 false) x).mp hm.2⟩

end ApollonianSuperharmonic

end
