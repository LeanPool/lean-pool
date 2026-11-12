/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightInterfaceCertificate
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceDisjointCompanionEndpoints
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileT3TranslateTouching
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations

-- [TABLET NODE: BandOrderedGeneralRightInterfaceCertificateExists]

/-!
# BandOrderedGeneralRightInterfaceCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightInterfaceCertificateGeometry

private theorem tileTouchingRetarget :
    (by
      classical
      exact
        forall (A A' B B' : ProtoTile), A.cells = A'.cells -> (A.cells = ∅ -> A.anchor =
            A'.anchor) -> B.cells = B'.cells -> (B.cells = ∅ -> B.anchor = B'.anchor) ->
            TileTouching A B -> TileTouching A' B' ) := by
  classical
  intro A A' B B' hAc hAa hBc hBa ht
  have hAo := ProtoTileObservableExtensionality A A' hAc hAa
  have hBo := ProtoTileObservableExtensionality B B' hBc hBa
  rcases ht with ht | ht | ht
  · left
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hAc] using ht.1
    · simpa [hBc] using ht.2.1
    · simpa [hAc, hBc] using ht.2.2.1
    · simpa [hAo.2.1, hAo.2.2.1, hBo.2.1, hBo.2.2.1] using ht.2.2.2
  · right; left
    refine ⟨?_, ?_⟩
    · simpa [hAc] using ht.1
    · rw [← hAa ht.1, ← hBo.2.1]
      exact ht.2
  · right; right
    refine ⟨?_, ?_⟩
    · simpa [hBc] using ht.1
    · rw [← hBa ht.1, ← hAo.2.1]
      exact ht.2

private theorem touchingRetarget :
    (by
      classical
      exact
        (forall (A A' B B' : ProtoTile), A.cells = A'.cells -> (A.cells = ∅ -> A.anchor =
            A'.anchor) -> B.cells = B'.cells -> (B.cells = ∅ -> B.anchor = B'.anchor) ->
            TileTouching A B -> TileTouching A' B') → (forall (A A' B B' D D' : ProtoTile),
            A.cells = A'.cells -> (A.cells = ∅ -> A.anchor = A'.anchor) -> B.cells = B'.cells ->
            (B.cells = ∅ -> B.anchor = B'.anchor) -> D.cells = D'.cells -> (D.cells = ∅ ->
            D.anchor = D'.anchor) -> TouchingTriple A B D -> TouchingTriple A' B' D') ) := by
  classical
  intro tileTouchingRetarget A A' B B' D D' hAc hAa hBc hBa hDc hDa ht
  have hAo := ProtoTileObservableExtensionality A A' hAc hAa
  have hBo := ProtoTileObservableExtensionality B B' hBc hBa
  have hDo := ProtoTileObservableExtensionality D D' hDc hDa
  rcases ht with ⟨hAB, hBD, hDA, p, hp, hpu⟩
  refine ⟨tileTouchingRetarget A A' B B' hAc hAa hBc hBa hAB,
    tileTouchingRetarget B B' D D' hBc hBa hDc hDa hBD,
    tileTouchingRetarget D D' A A' hDc hDa hAc hAa hDA, p, ?_, ?_⟩
  · simpa [← hAo.2.1, ← hBo.2.1, ← hDo.2.1] using hp
  · intro y hy
    apply hpu y
    simpa [← hAo.2.1, ← hBo.2.1, ← hDo.2.1] using hy

private theorem hAeAt211 :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), (A.cells = A'.cells) → (FootprintEdges A =
            FootprintEdges A') ) := by
  classical
  intro A A' hAc
  simp only [FootprintEdges]
  rw [hAc]

private theorem quarterTranslate :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (u : GaussianInt), TileTranslation
            (TileQuarterTurn (TileTranslation A a)) u = TileTranslation (TileTranslation
            (TileQuarterTurn A) u) (GaussianQuarterTurn a) ) := by
  classical
  intro A a u
  rcases A with ⟨cells, anchor⟩
  rw [ProtoTile.mk.injEq]
  constructor
  · ext z
    simp only [TileTranslation, TileQuarterTurn, Finset.mem_image,
      GaussianTranslation]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨w, hw, rfl⟩
      rcases hw with ⟨v, hv, rfl⟩
      refine ⟨GaussianQuarterTurn v - 1 + u, ?_, ?_⟩
      · refine ⟨GaussianQuarterTurn v - 1, ?_, rfl⟩
        exact ⟨v, hv, rfl⟩
      · cases a; cases v; cases u
        apply Zsqrtd.ext <;>
          simp [GaussianQuarterTurn] <;> omega
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨w, hw, rfl⟩
      rcases hw with ⟨v, hv, rfl⟩
      refine ⟨GaussianQuarterTurn (GaussianTranslation a v) - 1, ?_, ?_⟩
      · exact ⟨GaussianTranslation a v, ⟨v, hv, rfl⟩, rfl⟩
      · cases a; cases v; cases u
        apply Zsqrtd.ext <;>
          simp [GaussianQuarterTurn, GaussianTranslation] <;> omega
  · ext <;> simp [TileTranslation, TileQuarterTurn, GaussianTranslation,
      GaussianQuarterTurn] <;> omega

private theorem translateObs :
    (by
      classical
      exact
        forall (A A' : ProtoTile) (d : GaussianInt), A.cells = A'.cells -> (A.cells = ∅ ->
            A.anchor = A'.anchor) -> (TileTranslation A d).cells = (TileTranslation A' d).cells
            /\ ((TileTranslation A d).cells = ∅ -> (TileTranslation A d).anchor =
            (TileTranslation A' d).anchor) ) := by
  classical
  intro A A' d hc ha
  constructor
  · simp [TileTranslation, hc]
  · intro he
    have hAe : A.cells = ∅ :=
      (TileTranslationFormulas A d).2.2.1.mp he
    simp [TileTranslation, ha hAe]

private theorem centeredTurnTouching :
    (by
      classical
      exact
        (forall (A A' B B' D D' : ProtoTile), A.cells = A'.cells -> (A.cells = ∅ -> A.anchor =
            A'.anchor) -> B.cells = B'.cells -> (B.cells = ∅ -> B.anchor = B'.anchor) -> D.cells
            = D'.cells -> (D.cells = ∅ -> D.anchor = D'.anchor) -> TouchingTriple A B D ->
            TouchingTriple A' B' D') → ((∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (u :
            GaussianInt), TileTranslation (TileQuarterTurn (TileTranslation A a)) u =
            TileTranslation (TileTranslation (TileQuarterTurn A) u) (GaussianQuarterTurn a)) →
            ((forall (A A' : ProtoTile) (d : GaussianInt), A.cells = A'.cells -> (A.cells = ∅ ->
            A.anchor = A'.anchor) -> (TileTranslation A d).cells = (TileTranslation A' d).cells
            /\ ((TileTranslation A d).cells = ∅ -> (TileTranslation A d).anchor =
            (TileTranslation A' d).anchor)) → (forall (A : ProtoTile) (a b : GaussianInt),
            QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a) (TileTranslation A
            b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn a)) (TileTranslation A
            (GaussianQuarterTurn b))))) ) := by
  classical
  intro touchingRetarget quarterTranslate translateObs A a b hsym ht
  obtain ⟨u, hu, hcell, hanchor, hvert, hcent⟩ :=
    QuarterTurnSymmetricCenteredTransport A hsym
  have hanchor' : (TileTranslation (TileQuarterTurn A) u).cells = ∅ ->
      (TileTranslation (TileQuarterTurn A) u).anchor = A.anchor := by
    intro he
    apply hanchor
    rw [← hcell]
    exact he
  have hq := (TouchingTripleCovariance A (TileTranslation A a)
    (TileTranslation A b) u).2.1.mp ht
  have hqt := (TouchingTripleCovariance (TileQuarterTurn A)
    (TileQuarterTurn (TileTranslation A a))
    (TileQuarterTurn (TileTranslation A b)) u).1.mp hq
  rw [quarterTranslate A a u, quarterTranslate A b u] at hqt
  have ha := translateObs (TileTranslation (TileQuarterTurn A) u) A
    (GaussianQuarterTurn a) hcell hanchor'
  have hb := translateObs (TileTranslation (TileQuarterTurn A) u) A
    (GaussianQuarterTurn b) hcell hanchor'
  exact touchingRetarget
    (TileTranslation (TileQuarterTurn A) u) A
    (TileTranslation (TileTranslation (TileQuarterTurn A) u)
      (GaussianQuarterTurn a))
    (TileTranslation A (GaussianQuarterTurn a))
    (TileTranslation (TileTranslation (TileQuarterTurn A) u)
      (GaussianQuarterTurn b))
    (TileTranslation A (GaussianQuarterTurn b))
    hcell hanchor' ha.1 ha.2 hb.1 hb.2 hqt

private theorem centeredTurnExact :
    (by
      classical
      exact
        forall (A : ProtoTile) (a b : GaussianInt), QuarterTurnSymmetric A ->
            ExactTileInterfaceTriple A (TileTranslation A a) (TileTranslation A b) -> Nonempty
            (ExactTileInterfaceTriple A (TileTranslation A (GaussianQuarterTurn a))
            (TileTranslation A (GaussianQuarterTurn b))) ) := by
  classical
  intro A a b hsym E
  obtain ⟨u, hu, E', hp, hab, hbc, hca⟩ :=
    QuarterTurnSymmetricExactInterfaceTransport A a b E hsym
  exact ⟨E'⟩

private theorem thirdTurnExact :
    (by
      classical
      exact
        (forall (A : ProtoTile) (a b : GaussianInt), QuarterTurnSymmetric A
            -> ExactTileInterfaceTriple A (TileTranslation A a) (TileTranslation A b) -> Nonempty
            (ExactTileInterfaceTriple A (TileTranslation A (GaussianQuarterTurn a))
            (TileTranslation A (GaussianQuarterTurn b)))) →  forall (A : ProtoTile) (a b :
            GaussianInt), QuarterTurnSymmetric A -> ExactTileInterfaceTriple A (TileTranslation A
            a) (TileTranslation A b) -> Nonempty (ExactTileInterfaceTriple A (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation
            A (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))) ) := by
  classical
  intro centeredTurnExact A a b hsym E
  obtain ⟨E1⟩ := centeredTurnExact A a b hsym E
  obtain ⟨E2⟩ := centeredTurnExact A (GaussianQuarterTurn a)
    (GaussianQuarterTurn b) hsym E1
  exact centeredTurnExact A (GaussianQuarterTurn (GaussianQuarterTurn a))
    (GaussianQuarterTurn (GaussianQuarterTurn b)) hsym E2

private theorem thirdTurnTouching :
    (by
      classical
      exact
        (forall (A : ProtoTile) (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A
            (TileTranslation A a) (TileTranslation A b) -> TouchingTriple A (TileTranslation A
            (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn b))) → (forall (A :
            ProtoTile) (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A
            (TileTranslation A a) (TileTranslation A b) -> TouchingTriple A (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation
            A (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))) ) := by
  classical
  intro centeredTurnTouching A a b hsym ht
  exact centeredTurnTouching A _ _ hsym
    (centeredTurnTouching A _ _ hsym
      (centeredTurnTouching A a b hsym ht))

private theorem turn_flip :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (∀ (s : Fin 3), GaussianQuarterTurn
            (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q 0) (q s.succ)) ) := by
  classical
  intro C T N h k x normalization q flip s
  rw [(flip s).1]
  rcases BandVectors.1 (q s.succ) (q 0) with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

private theorem turn_neg :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (-z) = -GaussianQuarterTurn z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

private theorem turn_three :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z)) =
            -GaussianQuarterTurn z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

private theorem turn_two :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn z) = -z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]

private theorem touch0p :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn a))
            (TileTranslation A (GaussianQuarterTurn b))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (0 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((0 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q 2)) → (TouchingTriple F
            (TileTranslation F (BandVectors.1 (q 0) (q 1))) (TileTranslation F (-BandVectors.1 (q
            0) (q 2)))))))) ) := by
  classical
  intro C T N h k x normalization centeredTurnTouching q F touch0 turn_neg turn0 turn1
  simpa [turn0, turn1, turn_neg] using centeredTurnTouching F _ _
    normalization.fixed_quarter_turn touch0

private theorem touch1p :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn a))
            (TileTranslation A (GaussianQuarterTurn b))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (1 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((1 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q 2)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0) (q 3)) → (TouchingTriple F
            (TileTranslation F (BandVectors.1 (q 0) (q 2))) (TileTranslation F (-BandVectors.1 (q
            0) (q 3)))))))) ) := by
  classical
  intro C T N h k x normalization centeredTurnTouching q F touch1 turn_neg turn1 turn2
  simpa [turn1, turn2, turn_neg] using centeredTurnTouching F _ _
    normalization.fixed_quarter_turn touch1

private theorem touch2p :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn a))
            (TileTranslation A (GaussianQuarterTurn b))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (2 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((2 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0) (q 3)) → (TouchingTriple F
            (TileTranslation F (BandVectors.1 (q 0) (q 3))) (TileTranslation F (-BandVectors.1 (q
            0) (q 1)))))))) ) := by
  classical
  intro C T N h k x normalization centeredTurnTouching q F touch2 turn_neg turn0 turn2
  simpa [turn2, turn0, turn_neg] using centeredTurnTouching F _ _
    normalization.fixed_quarter_turn touch2

private theorem touch0m :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (0 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((0 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (GaussianQuarterTurn z) = -z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q 2)) → (TouchingTriple F
            (TileTranslation F (-BandVectors.1 (q 0) (q 1))) (TileTranslation F (BandVectors.1 (q
            0) (q 2))))))))) ) := by
  classical
  intro C T N h k x normalization thirdTurnTouching q F touch0 turn_neg turn_two turn0 turn1
  simpa [turn_three, turn_two, turn0, turn1, turn_neg] using
    thirdTurnTouching F _ _ normalization.fixed_quarter_turn touch0

private theorem touch1m :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (1 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((1 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (GaussianQuarterTurn z) = -z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q 2)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0) (q 3)) → (TouchingTriple F
            (TileTranslation F (-BandVectors.1 (q 0) (q 2))) (TileTranslation F (BandVectors.1 (q
            0) (q 3))))))))) ) := by
  classical
  intro C T N h k x normalization thirdTurnTouching q F touch1 turn_neg turn_two turn1 turn2
  simpa [turn_three, turn_two, turn1, turn2, turn_neg] using
    thirdTurnTouching F _ _ normalization.fixed_quarter_turn touch1

private theorem touch2m :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A : ProtoTile)
            (a b : GaussianInt), QuarterTurnSymmetric A -> TouchingTriple A (TileTranslation A a)
            (TileTranslation A b) -> TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))) → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (TouchingTriple F (TileTranslation F (BandVectors.1 (q (Fin.succ (2 : Fin (3 : ℕ)))) (q
            (0 : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q ((2 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (GaussianQuarterTurn z) = -z) → ((GaussianQuarterTurn
            (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) → ((GaussianQuarterTurn
            (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0) (q 3)) → (TouchingTriple F
            (TileTranslation F (-BandVectors.1 (q 0) (q 3))) (TileTranslation F (BandVectors.1 (q
            0) (q 1))))))))) ) := by
  classical
  intro C T N h k x normalization thirdTurnTouching q F touch2 turn_neg turn_two turn0 turn2
  simpa [turn_three, turn_two, turn2, turn0, turn_neg] using
    thirdTurnTouching F _ _ normalization.fixed_quarter_turn touch2

private theorem incoming_relation :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) + BandVectors.1 (q (1 : Fin (4
            : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 :
            ℕ))) = (0 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))
            + BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + BandVectors.2 (q (2 :
            Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin
            (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4
            : ℕ))) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) =
            BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) ∧
            (ProperBandQuadruple q → ∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))))) → (BandVectors.1 (q
            1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) ) := by
  classical
  intro C T N h k x normalization q laws
  let r : Fin 4 -> CircleCoordinates := ![q 0, q 2, q 3, q 1]
  have hr : SemiProperQuadruple r := by
    simpa [r] using SemiProperQuadruple.rotate
      normalization.configuration.proper.1
  let s : Fin 4 -> CircleCoordinates := ![r 0, r 2, r 3, r 1]
  have hs : SemiProperQuadruple s := by
    simpa [s] using SemiProperQuadruple.rotate hr
  have second := VectorRecursionLaws r hr
  have third := VectorRecursionLaws s hs
  have e0 := laws.2.2.1
  have e1 := second.2.2.1
  have e2 := third.2.2.1
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Int.reduceNeg,
      Matrix.cons_val, r, s] at e1 e2
  rw [e0, e1, e2]
  calc
    _ = (1 - (⟨0, 1⟩ : GaussianInt)) *
        (BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
          BandVectors.1 (q 2) (q 1)) := by ring
    _ = 0 := by rw [laws.1]; simp

private theorem outgoing_relation :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) →
            ((GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q 2)) →
            ((GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0) (q 3)) →
            ((BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) =
            0) → (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q
            3) = 0)))) ) := by
  classical
  intro C T N h k x normalization q turn0 turn1 turn2 incoming_relation
  rw [← turn0, ← turn1, ← turn2]
  calc
    _ = GaussianQuarterTurn (BandVectors.1 (q 1) (q 0) +
        BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0)) := by
          rcases BandVectors.1 (q 1) (q 0) with ⟨a0, b0⟩
          rcases BandVectors.1 (q 2) (q 0) with ⟨a1, b1⟩
          rcases BandVectors.1 (q 3) (q 0) with ⟨a2, b2⟩
          apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]; ring
    _ = GaussianQuarterTurn 0 := congrArg GaussianQuarterTurn incoming_relation
    _ = 0 := by rfl

private theorem period2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q 3) = 0) →
            ((BandVectors.1 (q 0) (q 1) = normalization.layout.u) → ((BandVectors.1 (q 0) (q 2) =
            normalization.layout.v) → (BandVectors.1 (q 0) (q 3) = -normalization.layout.u -
            normalization.layout.v))) ) := by
  classical
  intro C T N h k x normalization q outgoing_relation period0 period1
  rw [← period0, ← period1]
  have h : BandVectors.1 (q 0) (q 3) =
      -(BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2)) :=
    eq_neg_of_add_eq_zero_left (by
      simpa [add_assoc, add_comm, add_left_comm] using outgoing_relation)
  calc
    _ = -(BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2)) := h
    _ = _ := by abel

private theorem finish :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (forall (A A' B B' D D'
            : ProtoTile), A.cells = A'.cells -> (A.cells = ∅ -> A.anchor =
            A'.anchor) -> B.cells = B'.cells -> (B.cells = ∅ -> B.anchor = B'.anchor) -> D.cells
            = D'.cells -> (D.cells = ∅ -> D.anchor = D'.anchor) -> TouchingTriple A B D ->
            TouchingTriple A' B' D') → (
        let F := normalization.normalizedFixed
        (∀ (m : ℤ), ∀ (n : ℤ), ∀ (r : ℤ), ∀ (s : ℤ), (m, n) ≠ (r, s) → Disjoint (TileTranslation
            F ((↑m : GaussianInt) * normalization.layout.u + (↑n : GaussianInt) *
            normalization.layout.v)).cells (TileTranslation F ((↑r : GaussianInt) *
            normalization.layout.u + (↑s : GaussianInt) * normalization.layout.v)).cells) →
            (forall (uStart uEnd : GaussianInt) (mR nR mS nS mE nE : Int),
            normalization.rightNeighborDisplacement = (mR : GaussianInt) * normalization.layout.u
            + (nR : GaussianInt) * normalization.layout.v -> uStart = (mS : GaussianInt) *
            normalization.layout.u + (nS : GaussianInt) * normalization.layout.v -> uEnd = (mE :
            GaussianInt) * normalization.layout.u + (nE : GaussianInt) * normalization.layout.v
            -> (0, 0) ≠ (mR, nR) -> (0, 0) ≠ (mS, nS) -> (0, 0) ≠ (mE, nE) -> (mR, nR) ≠ (mS, nS)
            -> (mR, nR) ≠ (mE, nE) -> (mS, nS) ≠ (mE, nE) -> ExactTileInterfaceTriple F
            (TileTranslation F normalization.rightNeighborDisplacement) (TileTranslation F
            uStart) -> ExactTileInterfaceTriple F (TileTranslation F uEnd) (TileTranslation F
            normalization.rightNeighborDisplacement) -> TouchingTriple F (TileTranslation F
            normalization.rightNeighborDisplacement) (TileTranslation F uStart) -> TouchingTriple
            F (TileTranslation F uEnd) (TileTranslation F
            normalization.rightNeighborDisplacement) -> Nonempty
            (BandOrderedGeneralRightInterfaceCertificate normalization)))) := by
  classical
  intro C T N h k x normalization touchingRetarget F blocks uStart uEnd mR nR mS nS mE nE hR hS
      hE hFR hFS hFE hRS hRE hSE exactStart exactEnd touchStart touchEnd
  let swapAB : forall (A B D : ProtoTile),
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple B A D := by
    intro A B D E
    exact
      { point := E.point
        otherAB := E.otherAB
        otherBC := E.otherCA
        otherCA := E.otherBC
        pathAB := by simpa [Set.inter_comm] using E.pathAB
        pathBC := by simpa [Set.inter_comm] using E.pathCA
        pathCA := by simpa [Set.inter_comm] using E.pathBC
        unique_common := by
          intro y
          simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
            E.unique_common y }
  have cycleCAB : forall (A B D : ProtoTile),
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple D A B := by
    intro A B D E
    exact
      { point := E.point
        otherAB := E.otherCA
        otherBC := E.otherAB
        otherCA := E.otherBC
        pathAB := E.pathCA
        pathBC := E.pathAB
        pathCA := E.pathBC
        unique_common := by
          intro y
          simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
            E.unique_common y }
  have retargetFirst : forall (A A' B D : ProtoTile),
      A.cells = A'.cells -> (A.cells = ∅ -> A.anchor = A'.anchor) ->
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple A' B D := by
    intro A A' B D hAc hAa E
    have hAo := ProtoTileObservableExtensionality A A' hAc hAa
    have hAe : FootprintEdges A = FootprintEdges A' := by
      simp only [FootprintEdges]
      rw [hAc]
    exact
      { point := E.point
        otherAB := E.otherAB
        otherBC := E.otherBC
        otherCA := E.otherCA
        pathAB := by simpa [hAo.1, hAe] using E.pathAB
        pathBC := E.pathBC
        pathCA := by simpa [hAo.1, hAe] using E.pathCA
        unique_common := by
          intro y
          simpa [hAo.1] using E.unique_common y }
  let q := normalization.normalizedPresentation
  let oldRoot := TileTranslation F normalization.rightNeighborDisplacement
  let startCompanion := TileTranslation F uStart
  let endCompanion := TileTranslation F uEnd
  have oldCells : oldRoot.cells = normalization.normalizedRoot.cells :=
    normalization.right_neighbor_cells.symm
  have oldAnchor : oldRoot.cells = ∅ ->
      oldRoot.anchor = normalization.normalizedRoot.anchor := by
    intro he
    apply (normalization.right_neighbor_empty_anchor ?_).symm
    rw [normalization.right_neighbor_cells]
    exact he
  let start0 := swapAB F oldRoot startCompanion exactStart
  let end0 := cycleCAB F endCompanion oldRoot exactEnd
  let startData := retargetFirst oldRoot normalization.normalizedRoot F
    startCompanion oldCells oldAnchor start0
  let endData := retargetFirst oldRoot normalization.normalizedRoot F
    endCompanion oldCells oldAnchor end0
  have touchStart0 : TouchingTriple oldRoot F startCompanion :=
    (TouchingTriplePermutations F oldRoot startCompanion).mp touchStart |>.2.1
  have touchEnd0 : TouchingTriple oldRoot F endCompanion :=
    (TouchingTriplePermutations F endCompanion oldRoot).mp touchEnd |>.2.2.2.1
  have startTouching : TouchingTriple normalization.normalizedRoot F
      startCompanion := touchingRetarget oldRoot normalization.normalizedRoot
    F F startCompanion startCompanion oldCells oldAnchor rfl (by simp)
      rfl (by simp) touchStart0
  have endTouching : TouchingTriple normalization.normalizedRoot F
      endCompanion := touchingRetarget oldRoot normalization.normalizedRoot
    F F endCompanion endCompanion oldCells oldAnchor rfl (by simp)
      rfl (by simp) touchEnd0
  have latticeStart : LatticeTile startCompanion :=
    (TileDiskAreaCovariance F uStart).1.mp normalization.normalized_fixed_lattice
  have latticeEnd : LatticeTile endCompanion :=
    (TileDiskAreaCovariance F uEnd).1.mp normalization.normalized_fixed_lattice
  have transZero : (TileTranslation F 0).cells = F.cells := by
    ext z
    simp [TileTranslation, GaussianTranslation]
  have disjFR : Disjoint F.cells oldRoot.cells := by
    rw [← transZero]
    simpa [oldRoot, hR] using blocks 0 0 mR nR hFR
  have disjFS : Disjoint F.cells startCompanion.cells := by
    rw [← transZero]
    simpa [startCompanion, hS] using blocks 0 0 mS nS hFS
  have disjFE : Disjoint F.cells endCompanion.cells := by
    rw [← transZero]
    simpa [endCompanion, hE] using blocks 0 0 mE nE hFE
  have disjRS : Disjoint oldRoot.cells startCompanion.cells := by
    simpa [oldRoot, startCompanion, hR, hS] using blocks mR nR mS nS hRS
  have disjRE : Disjoint oldRoot.cells endCompanion.cells := by
    simpa [oldRoot, endCompanion, hR, hE] using blocks mR nR mE nE hRE
  have disjSE : Disjoint startCompanion.cells endCompanion.cells := by
    simpa [startCompanion, endCompanion, hS, hE] using blocks mS nS mE nE hSE
  have rootFixed : Disjoint normalization.normalizedRoot.cells F.cells := by
    rw [← oldCells]
    exact disjFR.symm
  have rootStart : Disjoint normalization.normalizedRoot.cells
      startCompanion.cells := by rw [← oldCells]; exact disjRS
  have rootEnd : Disjoint normalization.normalizedRoot.cells
      endCompanion.cells := by rw [← oldCells]; exact disjRE
  have crossed := ExactTileInterfaceDisjointCompanionEndpoints
    normalization.normalizedRoot F startCompanion endCompanion
    startData endData normalization.normalized_root_lattice
    normalization.normalized_fixed_lattice latticeStart latticeEnd
    startTouching endTouching rootStart disjFS disjSE
  have rootPositive : 0 < (q 0).1 := by
    dsimp [q]
    have hc := normalization.configuration.childLarge
    omega
  have pointRoot : normalization.normalizedPoint ∈
      FootprintVertices normalization.normalizedRoot := by
    rw [← PositiveCurvatureTileOdometerDomain _ _ _ rootPositive
      normalization.normalized_root_odometer]
    exact normalization.normalized_point_root_domain
  have pointFixed : normalization.normalizedPoint ∈ FootprintVertices F := by
    rw [← PositiveCurvatureTileOdometerDomain _ _ _
      normalization.normalizedFixedCircle.property
      normalization.normalized_fixed_odometer]
    exact normalization.normalized_point_fixed_domain
  exact ⟨
    { startCompanion := startCompanion
      endCompanion := endCompanion
      startData := startData
      endData := endData
      normalized_point_on_start_path := ⟨pointRoot, pointFixed⟩
      interface_endpoints := crossed.2
      root_lattice := normalization.normalized_root_lattice
      fixed_lattice := normalization.normalized_fixed_lattice
      start_lattice := latticeStart
      end_lattice := latticeEnd
      root_fixed_disjoint := rootFixed
      root_start_disjoint := rootStart
      fixed_start_disjoint := disjFS
      root_end_disjoint := rootEnd
      fixed_end_disjoint := disjFE
      start_end_disjoint := disjSE
      start_touching := startTouching
      end_touching := endTouching }⟩

private theorem hRAt632 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (2 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = false) →
            (normalization.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 3))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

private theorem hRAt651 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (2 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = true) →
            (normalization.rightNeighborDisplacement = BandVectors.1 (q 0) (q 3))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

private theorem hRAt674 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (0 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = false) →
            (normalization.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 1))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

private theorem hRAt694 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (0 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = true) →
            (normalization.rightNeighborDisplacement = BandVectors.1 (q 0) (q 1))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

private theorem hRAt716 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (1 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = false) →
            (normalization.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 2))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

private theorem hRAt736 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (normalization.rightDirectionSlot = (1 : Fin (3 : ℕ))) →
            ((normalization.rightNeighborPositive = true) →
            (normalization.rightNeighborDisplacement = BandVectors.1 (q 0) (q 2))) ) := by
  classical
  intro C T N h k x normalization q hk hpos
  simpa [hpos, hk] using normalization.right_neighbor_displacement

end RightInterfaceCertificateGeometry

namespace RightInterfaceCertificateConclusion

private theorem rightInterfaceCertificate :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), (∀ (A : ProtoTile), ∀
            (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (D : ProtoTile), ∀ (D' :
            ProtoTile), A.cells = A'.cells → (A.cells = ∅ → A.anchor =
            A'.anchor) → B.cells = B'.cells → (B.cells = ∅ → B.anchor = B'.anchor) → D.cells =
            D'.cells → (D.cells = ∅ → D.anchor = D'.anchor) → TouchingTriple A B D →
            TouchingTriple A' B' D') → (
        let q := normalization.normalizedPresentation
        let F := normalization.normalizedFixed
        (∀ (z : GaussianInt), GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (z :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z)) = -GaussianQuarterTurn z) → ((∀ (z : GaussianInt),
                GaussianQuarterTurn (GaussianQuarterTurn z) = -z) → ((GaussianQuarterTurn
                (BandVectors.1 (q 1) (q 0)) = BandVectors.1 (q 0) (q 1)) → ((GaussianQuarterTurn
                (BandVectors.1 (q 2) (q 0)) = BandVectors.1 (q 0) (q
            2)) → ((GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) = BandVectors.1 (q 0)
            (q 3)) → ((ExactTileInterfaceTriple F (TileTranslation F (GaussianQuarterTurn
            (BandVectors.1 (q (Fin.succ (0 : Fin (3 : ℕ)))) (q (0 : Fin (4 : ℕ))))))
            (TileTranslation F (GaussianQuarterTurn (-BandVectors.1 (q ((0 : Fin (3 : ℕ)) + (1 :
            Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))) → ((ExactTileInterfaceTriple F
            (TileTranslation F (GaussianQuarterTurn (BandVectors.1 (q (Fin.succ (1 : Fin (3 :
            ℕ)))) (q (0 : Fin (4 : ℕ)))))) (TileTranslation F (GaussianQuarterTurn
            (-BandVectors.1 (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ))))))) → ((ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn (BandVectors.1 (q (Fin.succ (2 : Fin (3 : ℕ)))) (q (0 : Fin (4 :
            ℕ)))))) (TileTranslation F (GaussianQuarterTurn (-BandVectors.1 (q ((2 : Fin (3 : ℕ))
            + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))) → ((ExactTileInterfaceTriple F
                (TileTranslation F (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q (Fin.succ (0 : Fin (3 :
            ℕ)))) (q (0 : Fin (4 : ℕ)))))))) (TileTranslation F (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q ((0 : Fin (3 : ℕ)) + (1
            : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))))) → ((ExactTileInterfaceTriple
            F (TileTranslation F (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (BandVectors.1 (q (Fin.succ (1 : Fin (3 : ℕ)))) (q (0 : Fin (4 : ℕ))))))))
            (TileTranslation F (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (-BandVectors.1 (q ((1 : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ))))))))) → ((ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q
            (Fin.succ (2 : Fin (3 : ℕ)))) (q (0 : Fin (4 : ℕ)))))))) (TileTranslation F
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q ((2
            : Fin (3 : ℕ)) + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))))) →
                ((TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q 1)))
                (TileTranslation F
            (-BandVectors.1 (q 0) (q 2)))) → ((TouchingTriple F (TileTranslation F (BandVectors.1
            (q 0) (q 2))) (TileTranslation F (-BandVectors.1 (q 0) (q 3)))) → ((TouchingTriple F
            (TileTranslation F (BandVectors.1 (q 0) (q 3))) (TileTranslation F (-BandVectors.1 (q
            0) (q 1)))) → ((TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q 1)))
            (TileTranslation F (BandVectors.1 (q 0) (q 2)))) → ((TouchingTriple F
            (TileTranslation F (-BandVectors.1 (q 0) (q 2))) (TileTranslation F (BandVectors.1 (q
            0) (q 3)))) → ((TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q 3)))
            (TileTranslation F (BandVectors.1 (q 0) (q 1)))) → ((BandVectors.1 (q 0) (q 1) =
            normalization.layout.u) → ((BandVectors.1 (q 0) (q 2) = normalization.layout.v) →
            ((BandVectors.1 (q 0) (q 3) = -normalization.layout.u - normalization.layout.v) →
            (Nonempty (BandOrderedGeneralRightInterfaceCertificate
                normalization)))))))))))))))))))))))) := by
  classical
  intro C T N h k x normalization touchingRetarget q F turn_neg turn_three turn_two turn0 turn1
      turn2 X0p0 X1p0 X2p0 X0m0 X1m0 X2m0 touch0p touch1p touch2p touch0m touch1m touch2m period0
      period1 period2
  let X0p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 2))) := by
    simpa [turn0, turn1, turn_neg] using X0p0
  have X1p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 3))) := by
    simpa [turn1, turn2, turn_neg] using X1p0
  have X2p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 1))) := by
    simpa [turn2, turn0, turn_neg] using X2p0
  have X0m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (BandVectors.1 (q 0) (q 2))) := by
    simpa [turn_three, turn_two, turn0, turn1, turn_neg] using X0m0
  have X1m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (BandVectors.1 (q 0) (q 3))) := by
    simpa [turn_three, turn_two, turn1, turn2, turn_neg] using X1m0
  have X2m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (BandVectors.1 (q 0) (q 1))) := by
    simpa [turn_three, turn_two, turn2, turn0, turn_neg] using X2m0
  have blocks := (BandOrderedGeneralPeriodicBlockCells q
    normalization.configuration normalization.normalizedCircle F
      normalization.layout).2
  have finish := RightInterfaceCertificateGeometry.finish C T N h k x normalization
      touchingRetarget blocks
  rcases normalization.right_slots_cyclic with hslots | hslots | hslots
  · rcases hslots with ⟨hi, hj, hk⟩
    cases hpos : normalization.rightNeighborPositive
    · have hR : normalization.rightNeighborDisplacement =
          -BandVectors.1 (q 0) (q 3) := RightInterfaceCertificateGeometry.hRAt632 C T N h k x
              normalization hk hpos
      apply finish (BandVectors.1 (q 0) (q 1))
        (BandVectors.1 (q 0) (q 2)) 1 1 1 0 0 1
      · rw [hR, period2]
        ring
      · simp [period0]
      · simp [period1]
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X2m
      · simpa [hR] using X1p
      · simpa [hR] using touch2m
      · simpa [hR] using touch1p
    · have hR : normalization.rightNeighborDisplacement =
          BandVectors.1 (q 0) (q 3) := RightInterfaceCertificateGeometry.hRAt651 C T N h k x
              normalization hk hpos
      apply finish (-BandVectors.1 (q 0) (q 1))
        (-BandVectors.1 (q 0) (q 2)) (-1) (-1) (-1) 0 0 (-1)
      · rw [hR, period2]
        ring
      · rw [period0]
        simp
      · rw [period1]
        simp
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X2p
      · simpa [hR] using X1m
      · simpa [hR] using touch2p
      · simpa [hR] using touch1m
  · rcases hslots with ⟨hi, hj, hk⟩
    cases hpos : normalization.rightNeighborPositive
    · have hR : normalization.rightNeighborDisplacement =
          -BandVectors.1 (q 0) (q 1) := RightInterfaceCertificateGeometry.hRAt674 C T N h k x
              normalization hk hpos
      apply finish (BandVectors.1 (q 0) (q 2))
        (BandVectors.1 (q 0) (q 3)) (-1) 0 0 1 (-1) (-1)
      · rw [hR, period0]
        simp
      · simp [period1]
      · rw [period2]
        ring
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X0m
      · simpa [hR] using X2p
      · simpa [hR] using touch0m
      · simpa [hR] using touch2p
    · have hR : normalization.rightNeighborDisplacement =
          BandVectors.1 (q 0) (q 1) := RightInterfaceCertificateGeometry.hRAt694 C T N h k x
              normalization hk hpos
      apply finish (-BandVectors.1 (q 0) (q 2))
        (-BandVectors.1 (q 0) (q 3)) 1 0 0 (-1) 1 1
      · simp [hR, period0]
      · rw [period1]
        simp
      · rw [period2]
        ring
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X0p
      · simpa [hR] using X2m
      · simpa [hR] using touch0p
      · simpa [hR] using touch2m
  · rcases hslots with ⟨hi, hj, hk⟩
    cases hpos : normalization.rightNeighborPositive
    · have hR : normalization.rightNeighborDisplacement =
          -BandVectors.1 (q 0) (q 2) := RightInterfaceCertificateGeometry.hRAt716 C T N h k x
              normalization hk hpos
      apply finish (BandVectors.1 (q 0) (q 3))
        (BandVectors.1 (q 0) (q 1)) 0 (-1) (-1) (-1) 1 0
      · rw [hR, period1]
        simp
      · rw [period2]
        ring
      · simp [period0]
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X1m
      · simpa [hR] using X0p
      · simpa [hR] using touch1m
      · simpa [hR] using touch0p
    · have hR : normalization.rightNeighborDisplacement =
          BandVectors.1 (q 0) (q 2) := RightInterfaceCertificateGeometry.hRAt736 C T N h k x
              normalization hk hpos
      apply finish (-BandVectors.1 (q 0) (q 3))
        (-BandVectors.1 (q 0) (q 1)) 0 1 1 1 (-1) 0
      · simp [hR, period1]
      · rw [period2]
        ring
      · rw [period0]
        simp
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · simpa [hR] using X1p
      · simpa [hR] using X0m
      · simpa [hR] using touch1p
      · simpa [hR] using touch0m

end RightInterfaceCertificateConclusion

theorem BandOrderedGeneralRightInterfaceCertificateExists
    {C : BandCircle} {T N : ProtoTile} {h k : PartialOdometer}
    {x : GaussianInt}
    (normalization :
      BandOrderedGeneralRightNormalizationCertificate C T N h k x) :
    Nonempty (BandOrderedGeneralRightInterfaceCertificate normalization) := by
-- BODY
  classical
  have touchingRetarget := RightInterfaceCertificateGeometry.touchingRetarget
      (RightInterfaceCertificateGeometry.tileTouchingRetarget)
  have swapAB : forall (A B D : ProtoTile),
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple B A D := by
    intro A B D E
    exact
      { point := E.point
        otherAB := E.otherAB
        otherBC := E.otherCA
        otherCA := E.otherBC
        pathAB := by simpa [Set.inter_comm] using E.pathAB
        pathBC := by simpa [Set.inter_comm] using E.pathCA
        pathCA := by simpa [Set.inter_comm] using E.pathBC
        unique_common := by
          intro y
          simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
            E.unique_common y }
  have cycleCAB : forall (A B D : ProtoTile),
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple D A B := by
    intro A B D E
    exact
      { point := E.point
        otherAB := E.otherCA
        otherBC := E.otherAB
        otherCA := E.otherBC
        pathAB := E.pathCA
        pathBC := E.pathAB
        pathCA := E.pathBC
        unique_common := by
          intro y
          simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
            E.unique_common y }
  have retargetFirst : forall (A A' B D : ProtoTile),
      A.cells = A'.cells -> (A.cells = ∅ -> A.anchor = A'.anchor) ->
      ExactTileInterfaceTriple A B D -> ExactTileInterfaceTriple A' B D := by
    intro A A' B D hAc hAa E
    have hAo := ProtoTileObservableExtensionality A A' hAc hAa
    have hAe : FootprintEdges A = FootprintEdges A' := RightInterfaceCertificateGeometry.hAeAt211
        A A' hAc
    exact
      { point := E.point
        otherAB := E.otherAB
        otherBC := E.otherBC
        otherCA := E.otherCA
        pathAB := by simpa [hAo.1, hAe] using E.pathAB
        pathBC := E.pathBC
        pathCA := by simpa [hAo.1, hAe] using E.pathCA
        unique_common := by
          intro y
          simpa [hAo.1] using E.unique_common y }
  have centeredTurnTouching := RightInterfaceCertificateGeometry.centeredTurnTouching
      touchingRetarget
            (RightInterfaceCertificateGeometry.quarterTranslate)
                (RightInterfaceCertificateGeometry.translateObs)
  have centeredTurnExact := RightInterfaceCertificateGeometry.centeredTurnExact
  have thirdTurnExact := RightInterfaceCertificateGeometry.thirdTurnExact centeredTurnExact
  have thirdTurnTouching := RightInterfaceCertificateGeometry.thirdTurnTouching centeredTurnTouching
  let q := normalization.normalizedPresentation
  let F := normalization.normalizedFixed
  have child := BandOrderedGeneralChildInterfaces q normalization.configuration
    normalization.normalizedCircle F normalization.layout
      normalization.fixed_quarter_turn
  obtain ⟨X0⟩ := child.1 (0 : Fin 3)
  obtain ⟨X1⟩ := child.1 (1 : Fin 3)
  obtain ⟨X2⟩ := child.1 (2 : Fin 3)
  have touch0 := TileT3TranslateTouching q normalization.configuration
    normalization.normalizedCircle F normalization.layout
      normalization.fixed_quarter_turn (0 : Fin 3)
  have touch1 := TileT3TranslateTouching q normalization.configuration
    normalization.normalizedCircle F normalization.layout
      normalization.fixed_quarter_turn (1 : Fin 3)
  have touch2 := TileT3TranslateTouching q normalization.configuration
    normalization.normalizedCircle F normalization.layout
      normalization.fixed_quarter_turn (2 : Fin 3)
  have laws := VectorRecursionLaws q normalization.configuration.proper.1
  have flip := laws.2.2.2.2 normalization.configuration.proper
  have turn_flip (s : Fin 3) :
      GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) =
        BandVectors.1 (q 0) (q s.succ) := RightInterfaceCertificateGeometry.turn_flip C T N h k x
            normalization flip s
  have turn_neg (z : GaussianInt) :
      GaussianQuarterTurn (-z) = -GaussianQuarterTurn z :=
          RightInterfaceCertificateGeometry.turn_neg z
  have turn_three (z : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z)) =
        -GaussianQuarterTurn z := RightInterfaceCertificateGeometry.turn_three z
  have turn_two (z : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn z) = -z :=
          RightInterfaceCertificateGeometry.turn_two z
  have turn0 : GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) =
      BandVectors.1 (q 0) (q 1) := by simpa using turn_flip (0 : Fin 3)
  have turn1 : GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) =
      BandVectors.1 (q 0) (q 2) := by simpa using turn_flip (1 : Fin 3)
  have turn2 : GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) =
      BandVectors.1 (q 0) (q 3) := by simpa using turn_flip (2 : Fin 3)
  obtain ⟨X0p0⟩ := centeredTurnExact F
    (BandVectors.1 (q (0 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((0 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X0
  obtain ⟨X1p0⟩ := centeredTurnExact F
    (BandVectors.1 (q (1 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((1 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X1
  obtain ⟨X2p0⟩ := centeredTurnExact F
    (BandVectors.1 (q (2 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((2 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X2
  obtain ⟨X0m0⟩ := thirdTurnExact F
    (BandVectors.1 (q (0 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((0 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X0
  obtain ⟨X1m0⟩ := thirdTurnExact F
    (BandVectors.1 (q (1 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((1 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X1
  obtain ⟨X2m0⟩ := thirdTurnExact F
    (BandVectors.1 (q (2 : Fin 3).succ) (q 0))
    (-BandVectors.1 (q (((2 : Fin 3) + 1).succ)) (q 0))
    normalization.fixed_quarter_turn X2
  have X0p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 2))) := by
    simpa [turn0, turn1, turn_neg] using X0p0
  have X1p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 3))) := by
    simpa [turn1, turn2, turn_neg] using X1p0
  have X2p : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 1))) := by
    simpa [turn2, turn0, turn_neg] using X2p0
  have X0m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (BandVectors.1 (q 0) (q 2))) := by
    simpa [turn_three, turn_two, turn0, turn1, turn_neg] using X0m0
  have X1m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (BandVectors.1 (q 0) (q 3))) := by
    simpa [turn_three, turn_two, turn1, turn2, turn_neg] using X1m0
  have X2m : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (BandVectors.1 (q 0) (q 1))) := by
    simpa [turn_three, turn_two, turn2, turn0, turn_neg] using X2m0
  have touch0p : TouchingTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 2))) :=
          RightInterfaceCertificateGeometry.touch0p C T N h k x normalization
          centeredTurnTouching touch0 turn_neg turn0 turn1
  have touch1p : TouchingTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 3))) :=
          RightInterfaceCertificateGeometry.touch1p C T N h k x normalization
          centeredTurnTouching touch1 turn_neg turn1 turn2
  have touch2p : TouchingTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (-BandVectors.1 (q 0) (q 1))) :=
          RightInterfaceCertificateGeometry.touch2p C T N h k x normalization
          centeredTurnTouching touch2 turn_neg turn0 turn2
  have touch0m : TouchingTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 1)))
      (TileTranslation F (BandVectors.1 (q 0) (q 2))) :=
          RightInterfaceCertificateGeometry.touch0m C T N h k x normalization thirdTurnTouching
          touch0 turn_neg turn_two turn0 turn1
  have touch1m : TouchingTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 2)))
      (TileTranslation F (BandVectors.1 (q 0) (q 3))) :=
          RightInterfaceCertificateGeometry.touch1m C T N h k x normalization thirdTurnTouching
          touch1 turn_neg turn_two turn1 turn2
  have touch2m : TouchingTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q 3)))
      (TileTranslation F (BandVectors.1 (q 0) (q 1))) :=
          RightInterfaceCertificateGeometry.touch2m C T N h k x normalization thirdTurnTouching
          touch2 turn_neg turn_two turn0 turn2
  have period0 : BandVectors.1 (q 0) (q 1) = normalization.layout.u :=
    normalization.layout.period_u.symm
  have period1 : BandVectors.1 (q 0) (q 2) = normalization.layout.v :=
    normalization.layout.period_v.symm
  have period2 : BandVectors.1 (q 0) (q 3) =
      -normalization.layout.u - normalization.layout.v :=
          RightInterfaceCertificateGeometry.period2 C T N h k x normalization
              (RightInterfaceCertificateGeometry.outgoing_relation C T N h k x normalization
              turn0 turn1 turn2 (RightInterfaceCertificateGeometry.incoming_relation C T N h k x
              normalization laws))
          period0 period1
  have rightInterfaceCertificate :
    Nonempty (BandOrderedGeneralRightInterfaceCertificate normalization) :=
        RightInterfaceCertificateConclusion.rightInterfaceCertificate C T N h k x normalization
        touchingRetarget turn_neg turn_three turn_two turn0 turn1 turn2 X0p0 X1p0 X2p0 X0m0 X1m0
        X2m0 touch0p touch1p touch2p touch0m touch1m touch2m period0 period1 period2
  exact rightInterfaceCertificate


end ApollonianSuperharmonic

end
