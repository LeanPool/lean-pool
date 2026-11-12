/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentRightEndpoint
public import LeanPool.ApollonianSuperharmonic.P3045T1RightBoundaryDisplacementAlgebra
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: P5635T1RightBoundaryInterfaceRecords]

/-!
# P5635T1RightBoundaryInterfaceRecords

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightBoundaryRecordsGeometry

private theorem translatedPieceCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        ∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), ∀ (z : GaussianInt), ((if s then (1 -
            (⟨0, 1⟩ : GaussianInt)) else
              -((1 - (⟨0, 1⟩ : GaussianInt)))) *
                BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)) +
                2 * d = z) → (TileCentroid (TileTranslation (placement.layout.P i s) d) -
                    TileCentroid F = (1 / 2 : Real) • GaussianRealPoint z) ) := by
  classical
  intro C D T N h k x bundle placement q F i s d z hdisp
  let I : GaussianInt := ⟨0, 1⟩
  let edge := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  have hcent := (placement.layout.outer_occurrence i s).2.2
  have hcent' : TileCentroid (placement.layout.P i s) - TileCentroid F =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          (GaussianRealPoint edge -
            (-(GaussianRealPoint edge).2, (GaussianRealPoint edge).1))) := by
    simpa [edge, F, q] using hcent
  have gpEdge (x : GaussianInt) :
      GaussianRealPoint x - (-(GaussianRealPoint x).2, (GaussianRealPoint x).1) =
        GaussianRealPoint ((1 - I) * x) := by
    rcases x with ⟨a, b⟩
    apply Prod.ext <;> simp [GaussianRealPoint, I]; ring
  have gpEdgeNeg (x : GaussianInt) :
      -(GaussianRealPoint x - (-(GaussianRealPoint x).2, (GaussianRealPoint x).1)) =
        GaussianRealPoint (-((1 - I) * x)) := by
    rw [gpEdge]
    rcases x with ⟨a, b⟩
    apply Prod.ext <;> simp [GaussianRealPoint, I]
  have gpAdd (x y : GaussianInt) :
      GaussianRealPoint (x + y) = GaussianRealPoint x + GaussianRealPoint y := by
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, e⟩
    apply Prod.ext <;> simp [GaussianRealPoint]
  have gpTwo (x : GaussianInt) :
      GaussianRealPoint ((2 : GaussianInt) * x) =
        (2 : Real) • GaussianRealPoint x := by
    rcases x with ⟨a, b⟩
    apply Prod.ext <;> simp [GaussianRealPoint]
  have negHalf (p : Real × Real) :
      (-1 : Real) • ((1 / 2 : Real) • p) = (1 / 2 : Real) • (-p) := by
    apply Prod.ext <;> simp [smul_eq_mul]
  have hmul (x : GaussianInt) : I * x - x = -x + x * I := by ring
  have hleft (x : GaussianInt) : -((1 - I) * x) = I * x - x := by ring
  have hright (x : GaussianInt) : -(1 - I) * x = -x + x * I := by ring
  have hassoc : TileCentroid (placement.layout.P i s) + GaussianRealPoint d -
      TileCentroid F =
      (TileCentroid (placement.layout.P i s) - TileCentroid F) +
        GaussianRealPoint d := by
    apply Prod.ext <;> simp <;> ring
  rw [(TileTranslationFormulas (placement.layout.P i s) d).2.2.2.2.1]
  change TileCentroid (placement.layout.P i s) + GaussianRealPoint d -
    TileCentroid F = _
  rw [hassoc, hcent']
  have hdisp' : (if s then (1 - I) else -(1 - I)) * edge + 2 * d = z := by
    simpa [edge, I] using hdisp
  rw [← hdisp']
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hcent ⊢
    rw [negHalf]
    rw [gpEdgeNeg]
    rw [gpAdd, gpTwo]
    rw [hleft, hright, hmul]
    apply Prod.ext <;> simp [smul_eq_mul]
  · simp only [ite_true] at hcent ⊢
    rw [gpEdge]
    rw [gpAdd, gpTwo]
    apply Prod.ext <;> simp

private theorem rNext :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightFirstSlot + 1 = placement.rightSecondSlot )
            := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ |
    ⟨hr, ht, hk⟩ <;> simp [hr, ht]

private theorem rPrev :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightFirstSlot + 2 = placement.rightDirectionSlot
            ) := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ |
    ⟨hr, ht, hk⟩ <;> simp [hr, hk]

private theorem tNext :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightSecondSlot + 1 = placement.rightDirectionSlot
            ) := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ |
    ⟨hr, ht, hk⟩ <;> simp [ht, hk]

private theorem tPrev :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), placement.rightSecondSlot + 2 = placement.rightFirstSlot )
            := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ |
    ⟨hr, ht, hk⟩ <;> simp [ht, hr]

private theorem cyclicVectorRecurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (fixedFunction : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h fixedFunction x),
        let q := bundle.normalizedPresentation
        ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), ((i = 0 ∧ j = 1 ∧ k = 2) ∨
            (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1)) → (BandVectors.1 (q k.succ) (q
                j.succ) + BandVectors.1 (q i.succ) (q k.succ) + BandVectors.1 (q j.succ) (q
                i.succ) = 0 ∧ BandVectors.1 (q i.succ) (q 0) = BandVectors.1 (q i.succ) (q
                k.succ) - (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q i.succ) ∧
                BandVectors.1 (q j.succ) (q 0) = BandVectors.1 (q j.succ) (q i.succ) - (⟨0, 1⟩ :
                GaussianInt) * BandVectors.1 (q k.succ) (q j.succ) ∧ BandVectors.1 (q k.succ) (q
                0) = BandVectors.1 (q k.succ) (q j.succ) - (⟨0, 1⟩ : GaussianInt) * BandVectors.1
                (q i.succ) (q k.succ)) ) := by
  classical
  intro C D T N h fixedFunction x bundle q i j k hcyc
  let cfg := bundle.configuration
  let qs : Fin 4 → CircleCoordinates := ![q 0, q i.succ, q j.succ, q k.succ]
  have hqs : SemiProperQuadruple qs := by
    rcases hcyc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · change SemiProperQuadruple ![q 0, q 1, q 2, q 3]
      convert cfg.proper.1 using 1; funext x; fin_cases x <;> rfl
    · change SemiProperQuadruple ![q 0, q 2, q 3, q 1]
      convert SemiProperQuadruple.rotate cfg.proper.1 using 1;
    · change SemiProperQuadruple ![q 0, q 3, q 1, q 2]
      convert SemiProperQuadruple.rotate
        (SemiProperQuadruple.rotate cfg.proper.1) using 1;
        funext x; fin_cases x <;> rfl
  let qs1 : Fin 4 → CircleCoordinates := ![qs 0, qs 2, qs 3, qs 1]
  let qs2 : Fin 4 → CircleCoordinates := ![qs 0, qs1 2, qs1 3, qs1 1]
  have hqs1 : SemiProperQuadruple qs1 := by
    simpa [qs1] using SemiProperQuadruple.rotate hqs
  have hqs2 : SemiProperQuadruple qs2 := by
    simpa [qs2, qs1] using SemiProperQuadruple.rotate hqs1
  have laws0 := VectorRecursionLaws qs hqs
  have laws1 := VectorRecursionLaws qs1 hqs1
  have laws2 := VectorRecursionLaws qs2 hqs2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [qs, add_comm, add_left_comm, add_assoc] using laws0.1
  · simpa [qs] using laws0.2.2.1
  · simpa [qs1, qs] using laws1.2.2.1
  · simpa [qs2, qs1, qs] using laws2.2.2.1

private theorem aux1Alg :
    (by
      classical
      exact
        ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1) → (((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) = -⟨0,
            1⟩) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), (a + b + c = 0)
            → ((1 - (⟨0, 1⟩ : GaussianInt)) * b + 2 * (-(⟨0, 1⟩ : GaussianInt) * c) = (⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) * ((c - (⟨0, 1⟩ : GaussianInt) * a) - (⟨0, 1⟩ : GaussianInt)
            * (c - (⟨0, 1⟩ : GaussianInt) * a))))) ) := by
  classical
  intro hI2 hI3 a b c hs
  rw [hI3]
  linear_combination (1 - (⟨0, 1⟩ : GaussianInt)) * hs +
    a * hI3 - a * hI2 - c * hI2

private theorem aux2Alg :
    (by
      classical
      exact
        ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀
            (c : GaussianInt), (a + b + c = 0) → (-(1 - (⟨0, 1⟩ : GaussianInt)) * a + 2 * (-c) =
            (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * ((⟨0, 1⟩ : GaussianInt) * (b - (⟨0, 1⟩ :
            GaussianInt) * c) - (b - (⟨0, 1⟩ : GaussianInt) * c)))) ) := by
  classical
  intro hI2 a b c hs
  rw [hI2]
  linear_combination ((⟨0, 1⟩ : GaussianInt) - 1) * hs - c * hI2

private theorem aux3Alg :
    (by
      classical
      exact
        ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) = ⟨0, 1⟩) → (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (c : GaussianInt), (a + b + c = 0) → (-(1 - (⟨0, 1⟩ : GaussianInt)) *
            b + 2 * ((⟨0, 1⟩ : GaussianInt) * c) = (⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * ((c -
            (⟨0, 1⟩ : GaussianInt) * a) - (⟨0, 1⟩ : GaussianInt) * (c - (⟨0, 1⟩ : GaussianInt) *
            a)))) ) := by
  classical
  intro hI1 a b c hs
  rw [hI1]
  have hI2' : (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1 := by decide +kernel
  have hI3' : (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) = -⟨0, 1⟩ := by decide +kernel
  linear_combination ((⟨0, 1⟩ : GaussianInt) - 1) * hs +
    a * hI2' - a * hI3' + c * hI2'

private theorem aux4Alg :
    (by
      classical
      exact
        ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) = 1) → (((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1) →
            (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), (a + b + c = 0) → ((1
            - (⟨0, 1⟩ : GaussianInt)) * a + 2 * c = (⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * ((⟨0, 1⟩
            : GaussianInt) * (b - (⟨0, 1⟩ : GaussianInt) * c) - (b - (⟨0, 1⟩ : GaussianInt) *
            c))))) ) := by
  classical
  intro hI0 hI2 a b c hs
  rw [hI0]
  linear_combination (1 - (⟨0, 1⟩ : GaussianInt)) * hs + c * hI2

private theorem auxiliaryDisplacements :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (fixedFunction : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h fixedFunction x),
        let q := bundle.normalizedPresentation
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → ((∀ (i : Fin 3), ∀ (j : Fin 3), ∀
            (k : Fin 3), ((i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k
            = 1)) → (BandVectors.1 (q k.succ) (q j.succ) + BandVectors.1 (q i.succ) (q k.succ) +
            BandVectors.1 (q j.succ) (q i.succ) = 0 ∧ BandVectors.1 (q i.succ) (q 0) =
            BandVectors.1 (q i.succ) (q k.succ) - (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q
            j.succ) (q i.succ) ∧ BandVectors.1 (q j.succ) (q 0) = BandVectors.1 (q j.succ) (q
            i.succ) - (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q k.succ) (q j.succ) ∧
            BandVectors.1 (q k.succ) (q 0) = BandVectors.1 (q k.succ) (q j.succ) - (⟨0, 1⟩ :
            GaussianInt) * BandVectors.1 (q i.succ) (q k.succ))) → (((⟨0, 1⟩ : GaussianInt) ^ (1
            : Nat) = ⟨0, 1⟩) → (((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1) → (((⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) = -⟨0, 1⟩) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀
            (c : GaussianInt), (a + b + c = 0) → ((1 - (⟨0, 1⟩ : GaussianInt)) * b + 2 * (-(⟨0,
            1⟩ : GaussianInt) * c) = (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * ((c - (⟨0, 1⟩ :
            GaussianInt) * a) - (⟨0, 1⟩ : GaussianInt) * (c - (⟨0, 1⟩ : GaussianInt) * a)))) →
            ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), (a + b + c = 0) →
            (-(1 - (⟨0, 1⟩ : GaussianInt)) * a + 2 * (-c) = (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            ((⟨0, 1⟩ : GaussianInt) * (b - (⟨0, 1⟩ : GaussianInt) * c) - (b - (⟨0, 1⟩ :
            GaussianInt) * c)))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c :
            GaussianInt), (a + b + c = 0) → (-(1 - (⟨0, 1⟩ : GaussianInt)) * b + 2 * ((⟨0, 1⟩ :
            GaussianInt) * c) = (⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * ((c - (⟨0, 1⟩ : GaussianInt)
            * a) - (⟨0, 1⟩ : GaussianInt) * (c - (⟨0, 1⟩ : GaussianInt) * a)))) → ((∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), (a + b + c = 0) → ((1 - (⟨0,
            1⟩ : GaussianInt)) * a + 2 * c = (⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * ((⟨0, 1⟩ :
            GaussianInt) * (b - (⟨0, 1⟩ : GaussianInt) * c) - (b - (⟨0, 1⟩ : GaussianInt) * c))))
            → (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), ((i = 0 ∧ j = 1 ∧ k = 2) ∨
            (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1)) → (((1 - (⟨0, 1⟩ : GaussianInt)) *
                BandVectors.1 (q ((j + 2).succ)) (q ((j + 1).succ)) + 2 * (-((⟨0, 1⟩ :
                GaussianInt) * BandVectors.1 (q j.succ) (q i.succ))) = (⟨0, 1⟩ : GaussianInt) ^
                (3 : Nat) * (BandVectors.1 (q j.succ) (q 0) - BandVectors.1 (q 0) (q j.succ))) ∧
                (-(1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (q ((i + 2).succ)) (q ((i +
                1).succ)) + 2 * (-BandVectors.1 (q j.succ) (q i.succ)) = (⟨0, 1⟩ : GaussianInt) ^
                (2 : Nat) * (BandVectors.1 (q 0) (q i.succ) - BandVectors.1 (q i.succ) (q 0))) ∧
                (-(1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1 (q ((j + 2).succ)) (q ((j +
                1).succ)) + 2 * ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q i.succ)) =
                (⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (BandVectors.1 (q j.succ) (q 0) -
                BandVectors.1 (q 0) (q j.succ))) ∧ ((1 - (⟨0, 1⟩ : GaussianInt)) * BandVectors.1
                (q ((i + 2).succ)) (q ((i + 1).succ)) + 2 * BandVectors.1 (q j.succ) (q i.succ) =
                (⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * (BandVectors.1 (q 0) (q i.succ) -
                BandVectors.1 (q i.succ) (q 0))))))))))))) ) := by
  classical
  intro C D T N h fixedFunction x bundle q turnFlip cyclicVectorRecurrence hI1 hI2 hI3 aux1Alg
      aux2Alg aux3Alg
      aux4Alg i j k hcyc
  obtain ⟨hsum, hi, hj, hk⟩ := cyclicVectorRecurrence i j k hcyc
  let a := BandVectors.1 (q k.succ) (q j.succ)
  let b := BandVectors.1 (q i.succ) (q k.succ)
  let c := BandVectors.1 (q j.succ) (q i.succ)
  have habc : a + b + c = 0 := by
    simpa [a, b, c, add_comm, add_left_comm, add_assoc] using hsum
  have hi' : BandVectors.1 (q i.succ) (q 0) = b - (⟨0, 1⟩ : GaussianInt) * c := by
    simpa [a, b, c] using hi
  have hj' : BandVectors.1 (q j.succ) (q 0) = c - (⟨0, 1⟩ : GaussianInt) * a := by
    simpa [a, b, c] using hj
  have hfi' : BandVectors.1 (q 0) (q i.succ) =
      (⟨0, 1⟩ : GaussianInt) * (b - (⟨0, 1⟩ : GaussianInt) * c) := by
    rw [(turnFlip i).1, hi']
  have hfj' : BandVectors.1 (q 0) (q j.succ) =
      (⟨0, 1⟩ : GaussianInt) * (c - (⟨0, 1⟩ : GaussianInt) * a) := by
    rw [(turnFlip j).1, hj']
  rcases hcyc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hj', hfj']
      simpa [a, b, c, hI3, Fin.add_def, Nat.reduceAdd, Nat.reduceMod] using
        aux1Alg a b c habc
    · rw [hi', hfi']
      simpa [a, b, c, hI2, Fin.add_def, Nat.reduceAdd, Nat.reduceMod] using
        aux2Alg a b c habc
    · rw [hj', hfj']
      simpa [a, b, c, hI1, Fin.add_def, Nat.reduceAdd, Nat.reduceMod] using
        aux3Alg a b c habc
    · rw [hi', hfi']
      simpa [a, b, c, Fin.add_def, Nat.reduceAdd, Nat.reduceMod] using
        aux4Alg a b c habc

private theorem firstPositiveCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), ∀ (z : GaussianInt), ((if s then (1 -
            (⟨0, 1⟩ : GaussianInt)) else -((1 - (⟨0, 1⟩ : GaussianInt)))) * BandVectors.1 (q ((i
            + 2).succ)) (q ((i + 1).succ)) + 2 * d = z) → (TileCentroid (TileTranslation
            (placement.layout.P i s) d) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint z))
            → ((placement.rightFirstSlot + 1 = placement.rightSecondSlot) →
            ((placement.rightFirstSlot + 2 = placement.rightDirectionSlot) → (((⟨0, 1⟩ :
            GaussianInt) ^ (3 : Nat) = -⟨0, 1⟩) → ((((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) * BandVectors.1 (q placement.rightDirectionSlot.succ) (q
            placement.rightSecondSlot.succ) + (2 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q placement.rightDirectionSlot.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.1 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) →
            ((placement.rightNeighborPositive = true) → (TileCentroid (TileTranslation
            (placement.layout.P placement.rightFirstSlot true)
            placement.rightNeighborDisplacement) - TileCentroid F = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) * (BandVectors.1 (q
            placement.rightFirstSlot.succ) (q 0) + BandVectors.1 (q 0) (q
            placement.rightFirstSlot.succ))))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedPieceCentroid rNext rPrev hI3 vFirst hpos
  have hR : placement.rightNeighborDisplacement =
      BandVectors.1 (q 0) (q placement.rightDirectionSlot.succ) := by
    simpa [hpos] using placement.right_neighbor_displacement
  have hdisp : (1 - (⟨0, 1⟩ : GaussianInt)) *
      BandVectors.1 (q ((placement.rightFirstSlot + 2).succ))
        (q ((placement.rightFirstSlot + 1).succ)) +
      2 * placement.rightNeighborDisplacement =
      (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
        (BandVectors.1 (q placement.rightFirstSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightFirstSlot.succ)) := by
    calc
      _ = - (⟨0, 1⟩ : GaussianInt) *
          (BandVectors.1 (q placement.rightFirstSlot.succ) (q 0) +
            BandVectors.1 (q 0) (q placement.rightFirstSlot.succ)) := by
        rw [rPrev, rNext, hR]
        exact vFirst
      _ = _ := by simp [hI3]
  exact translatedPieceCentroid placement.rightFirstSlot true
    placement.rightNeighborDisplacement _ hdisp

private theorem secondPositiveCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), ∀ (z : GaussianInt), ((if s then (1 -
            (⟨0, 1⟩ : GaussianInt)) else -((1 - (⟨0, 1⟩ : GaussianInt)))) * BandVectors.1 (q ((i
            + 2).succ)) (q ((i + 1).succ)) + 2 * d = z) → (TileCentroid (TileTranslation
            (placement.layout.P i s) d) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint z))
            → ((placement.rightSecondSlot + 1 = placement.rightDirectionSlot) →
            ((placement.rightSecondSlot + 2 = placement.rightFirstSlot) → (((⟨0, 1⟩ :
            GaussianInt) ^ (2 : Nat) = -1) → ((-((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) * BandVectors.1 (q placement.rightFirstSlot.succ) (q
            placement.rightDirectionSlot.succ) + (2 : GaussianInt) * BandVectors.1 (q (0 : Fin (4
            : ℕ))) (q placement.rightDirectionSlot.succ) = -(BandVectors.1 (q
            placement.rightSecondSlot.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4
            : ℕ))) (q placement.rightSecondSlot.succ))) → ((∀ (a : GaussianInt), ∀ (z :
            GaussianInt), -a * z = -(a * z)) → ((placement.rightNeighborPositive = true) →
            (TileCentroid (TileTranslation (placement.layout.P placement.rightSecondSlot false)
            placement.rightNeighborDisplacement) - TileCentroid F = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * (BandVectors.1 (q
            placement.rightSecondSlot.succ) (q 0) + BandVectors.1 (q 0) (q
            placement.rightSecondSlot.succ)))))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedPieceCentroid tNext tPrev hI2 vSecond
      gaussianNegMul hpos
  have hR : placement.rightNeighborDisplacement =
      BandVectors.1 (q 0) (q placement.rightDirectionSlot.succ) := by
    simpa [hpos] using placement.right_neighbor_displacement
  have hdisp : -((1 - (⟨0, 1⟩ : GaussianInt)) *
      BandVectors.1 (q ((placement.rightSecondSlot + 2).succ))
        (q ((placement.rightSecondSlot + 1).succ))) +
      2 * placement.rightNeighborDisplacement =
      (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
        (BandVectors.1 (q placement.rightSecondSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightSecondSlot.succ)) := by
    calc
      _ = -(BandVectors.1 (q placement.rightSecondSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightSecondSlot.succ)) := by
        rw [tPrev, tNext, hR]
        convert vSecond using 1; ring
      _ = _ := by simp [hI2]
  have hdisp' : (-(1 - (⟨0, 1⟩ : GaussianInt))) *
      BandVectors.1 (q ((placement.rightSecondSlot + 2).succ))
        (q ((placement.rightSecondSlot + 1).succ)) +
      2 * placement.rightNeighborDisplacement =
      (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
        (BandVectors.1 (q placement.rightSecondSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightSecondSlot.succ)) := by
    rw [gaussianNegMul]
    exact hdisp
  exact translatedPieceCentroid placement.rightSecondSlot false
    placement.rightNeighborDisplacement _ hdisp'

private theorem firstReflectedCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), ∀ (z : GaussianInt), ((if s then (1 -
            (⟨0, 1⟩ : GaussianInt)) else -((1 - (⟨0, 1⟩ : GaussianInt)))) * BandVectors.1 (q ((i
            + 2).succ)) (q ((i + 1).succ)) + 2 * d = z) → (TileCentroid (TileTranslation
            (placement.layout.P i s) d) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint z))
            → ((placement.rightFirstSlot + 1 = placement.rightSecondSlot) →
            ((placement.rightFirstSlot + 2 = placement.rightDirectionSlot) → (((⟨0, 1⟩ :
            GaussianInt) ^ (1 : Nat) = ⟨0, 1⟩) → ((-((1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) * BandVectors.1 (q placement.rightDirectionSlot.succ) (q
            placement.rightSecondSlot.succ) - (2 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q placement.rightDirectionSlot.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            (BandVectors.1 (q placement.rightFirstSlot.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q placement.rightFirstSlot.succ))) → ((∀ (a :
            GaussianInt), ∀ (z : GaussianInt), -a * z = -(a * z)) →
            ((placement.rightNeighborPositive = false) → (TileCentroid (TileTranslation
            (placement.layout.P placement.rightFirstSlot false)
            placement.rightNeighborDisplacement) - TileCentroid F = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) * (BandVectors.1 (q
            placement.rightFirstSlot.succ) (q 0) + BandVectors.1 (q 0) (q
            placement.rightFirstSlot.succ)))))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedPieceCentroid rNext rPrev hI1 vRefFirst
      gaussianNegMul hpos
  have hR : placement.rightNeighborDisplacement =
      -BandVectors.1 (q 0) (q placement.rightDirectionSlot.succ) := by
    simpa [hpos] using placement.right_neighbor_displacement
  have hdisp : -((1 - (⟨0, 1⟩ : GaussianInt)) *
      BandVectors.1 (q ((placement.rightFirstSlot + 2).succ))
        (q ((placement.rightFirstSlot + 1).succ))) +
      2 * placement.rightNeighborDisplacement =
      (⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
        (BandVectors.1 (q placement.rightFirstSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightFirstSlot.succ)) := by
    calc
      _ = (⟨0, 1⟩ : GaussianInt) *
          (BandVectors.1 (q placement.rightFirstSlot.succ) (q 0) +
            BandVectors.1 (q 0) (q placement.rightFirstSlot.succ)) := by
        rw [rPrev, rNext, hR]
        convert vRefFirst using 1; ring
      _ = _ := by simp [hI1]
  apply translatedPieceCentroid placement.rightFirstSlot false
    placement.rightNeighborDisplacement _
  rw [← gaussianNegMul] at hdisp
  exact hdisp

private theorem secondReflectedCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (d : GaussianInt), ∀ (z : GaussianInt), ((if s then (1 -
            (⟨0, 1⟩ : GaussianInt)) else -((1 - (⟨0, 1⟩ : GaussianInt)))) * BandVectors.1 (q ((i
            + 2).succ)) (q ((i + 1).succ)) + 2 * d = z) → (TileCentroid (TileTranslation
            (placement.layout.P i s) d) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint z))
            → ((placement.rightSecondSlot + 1 = placement.rightDirectionSlot) →
            ((placement.rightSecondSlot + 2 = placement.rightFirstSlot) → ((((1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) * BandVectors.1 (q placement.rightFirstSlot.succ)
            (q placement.rightDirectionSlot.succ) - (2 : GaussianInt) * BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q placement.rightDirectionSlot.succ) = BandVectors.1 (q
            placement.rightSecondSlot.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4
            : ℕ))) (q placement.rightSecondSlot.succ)) → ((placement.rightNeighborPositive =
            false) → (TileCentroid (TileTranslation (placement.layout.P placement.rightSecondSlot
            true) placement.rightNeighborDisplacement) - TileCentroid F = (1 / 2 : Real) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * (BandVectors.1 (q
            placement.rightSecondSlot.succ) (q 0) + BandVectors.1 (q 0) (q
            placement.rightSecondSlot.succ)))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedPieceCentroid tNext tPrev vRefSecond hpos
  have hR : placement.rightNeighborDisplacement =
      -BandVectors.1 (q 0) (q placement.rightDirectionSlot.succ) := by
    simpa [hpos] using placement.right_neighbor_displacement
  have hdisp : (1 - (⟨0, 1⟩ : GaussianInt)) *
      BandVectors.1 (q ((placement.rightSecondSlot + 2).succ))
        (q ((placement.rightSecondSlot + 1).succ)) +
      2 * placement.rightNeighborDisplacement =
      (⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
        (BandVectors.1 (q placement.rightSecondSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightSecondSlot.succ)) := by
    calc
      _ = BandVectors.1 (q placement.rightSecondSlot.succ) (q 0) +
          BandVectors.1 (q 0) (q placement.rightSecondSlot.succ) := by
        rw [tPrev, tNext, hR]
        convert vRefSecond using 1; ring
      _ = _ := by simp []
  exact translatedPieceCentroid placement.rightSecondSlot true
    placement.rightNeighborDisplacement _ hdisp

private theorem childPositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        ∀ (i : Fin 3), 0 < (q i.succ).1 ) := by
  classical
  intro C D T N h k x bundle q i
  let cfg := bundle.configuration
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 i
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · exact hpos
  · exact (cfg.noLine i.succ (by simpa [q] using hzero.symm)).elim

private theorem hJprev :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        j - 1 = i) ) := by
  classical
  intro C D T N h k x bundle placement hcyc i j
  rcases hcyc with ⟨hi0, hj0, hk0⟩ | ⟨hi0, hj0, hk0⟩ |
    ⟨hi0, hj0, hk0⟩
  all_goals
    apply Fin.ext
    simp [i, j, hi0, hj0]

private theorem hZ1' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
        (¬ Even (3 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (BandPrototile (q j.succ) (TileTranslation (placement.layout.P j true) (-((⟨0, 1⟩ :
            GaussianInt) * c)))) → (BandPrototile (q (if Even (3 : Nat) then i - 1 else i +
            1).succ) (TileTranslation (placement.layout.P j true) (-((⟨0, 1⟩ : GaussianInt) *
            c)))))) ) := by
  classical
  intro C D T N h k x bundle placement hcyc q hEven3 i j c hZ1
  rcases hcyc with ⟨hi0, hj0, hk0⟩ | ⟨hi0, hj0, hk0⟩ |
    ⟨hi0, hj0, hk0⟩ <;>
    simpa [i, j, hi0, hj0, hEven3] using hZ1

private theorem hZ2' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (Even (2 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (j - 1 = i) → ((BandPrototile (q i.succ) (TileTranslation (placement.layout.P i false)
            (-c))) → (BandPrototile (q (if Even (2 : Nat) then j - 1 else j + 1).succ)
            (TileTranslation (placement.layout.P i false) (-c))))) ) := by
  classical
  intro C D T N h k x bundle placement q hEven2 i j c hJprev hZ2
  simpa [hEven2, hJprev] using hZ2

private theorem hZ3' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
        (¬ Even (1 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (BandPrototile (q j.succ) (TileTranslation (placement.layout.P j false) ((⟨0, 1⟩ :
            GaussianInt) * c))) → (BandPrototile (q (if Even (1 : Nat) then i - 1 else i +
            1).succ) (TileTranslation (placement.layout.P j false) ((⟨0, 1⟩ : GaussianInt) *
            c))))) ) := by
  classical
  intro C D T N h k x bundle placement hcyc q hEven1 i j c hZ3
  rcases hcyc with ⟨hi0, hj0, hk0⟩ | ⟨hi0, hj0, hk0⟩ |
    ⟨hi0, hj0, hk0⟩ <;>
    simpa [i, j, hi0, hj0, hEven1] using hZ3

private theorem hZ4' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (Even (0 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (j - 1 = i) → ((BandPrototile (q i.succ) (TileTranslation (placement.layout.P i true) c))
            → (BandPrototile (q (if Even (0 : Nat) then j - 1 else j + 1).succ) (TileTranslation
            (placement.layout.P i true) c)))) ) := by
  classical
  intro C D T N h k x bundle placement q hEven0 i j c hJprev hZ4
  simpa [hEven0, hJprev] using hZ4

private theorem hZcent1' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (¬ Even (3 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (TileCentroid (TileTranslation (placement.layout.P j true) (-((⟨0, 1⟩ : GaussianInt) *
            c))) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            (3 : Nat) * (BandVectors.1 (q j.succ) (q 0) - BandVectors.1 (q 0) (q j.succ)))) →
            (TileCentroid (TileTranslation (placement.layout.P j true) (-((⟨0, 1⟩ : GaussianInt)
            * c))) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt)
            ^ (3 : Nat) * (if Even (3 : Nat) then BandVectors.1 (q 0) (q (i - 1).succ) -
            BandVectors.1 (q (i - 1).succ) (q 0) else BandVectors.1 (q (i + 1).succ) (q 0) -
            BandVectors.1 (q 0) (q (i + 1).succ)))))) ) := by
  classical
  intro C D T N h k x bundle placement hcyc q F hEven3 i j c hZcent1
  rcases hcyc with ⟨hi0, hj0, hk0⟩ | ⟨hi0, hj0, hk0⟩ |
    ⟨hi0, hj0, hk0⟩ <;>
    simpa [i, j, hi0, hj0, hEven3] using hZcent1

private theorem hZcent2' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (Even (2 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (j - 1 = i) → ((TileCentroid (TileTranslation (placement.layout.P i false) (-c)) -
            TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (2 :
            Nat) * (BandVectors.1 (q 0) (q i.succ) - BandVectors.1 (q i.succ) (q 0)))) →
            (TileCentroid (TileTranslation (placement.layout.P i false) (-c)) - TileCentroid F =
            (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) * (if Even (2
            : Nat) then BandVectors.1 (q 0) (q (j - 1).succ) - BandVectors.1 (q (j - 1).succ) (q
            0) else BandVectors.1 (q (j + 1).succ) (q 0) - BandVectors.1 (q 0) (q (j +
            1).succ)))))) ) := by
  classical
  intro C D T N h k x bundle placement q F hEven2 i j c hJprev hZcent2
  simpa [hEven2, hJprev] using hZcent2

private theorem hZcent3' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (¬ Even (1 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (TileCentroid (TileTranslation (placement.layout.P j false) ((⟨0, 1⟩ : GaussianInt) * c))
            - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (1 :
            Nat) * (BandVectors.1 (q j.succ) (q 0) - BandVectors.1 (q 0) (q j.succ)))) →
            (TileCentroid (TileTranslation (placement.layout.P j false) ((⟨0, 1⟩ : GaussianInt) *
            c)) - TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^
            (1 : Nat) * (if Even (1 : Nat) then BandVectors.1 (q 0) (q (i - 1).succ) -
            BandVectors.1 (q (i - 1).succ) (q 0) else BandVectors.1 (q (i + 1).succ) (q 0) -
            BandVectors.1 (q 0) (q (i + 1).succ)))))) ) := by
  classical
  intro C D T N h k x bundle placement hcyc q F hEven1 i j c hZcent3
  rcases hcyc with ⟨hi0, hj0, hk0⟩ | ⟨hi0, hj0, hk0⟩ |
    ⟨hi0, hj0, hk0⟩ <;>
    simpa [i, j, hi0, hj0, hEven1] using hZcent3

private theorem hZcent4' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (Even (0 : Nat)) → (
        let i := placement.rightFirstSlot
        let j := placement.rightSecondSlot
        let c := BandVectors.1 (q j.succ) (q i.succ)
        (j - 1 = i) → ((TileCentroid (TileTranslation (placement.layout.P i true) c) -
            TileCentroid F = (1 / 2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (0 :
            Nat) * (BandVectors.1 (q 0) (q i.succ) - BandVectors.1 (q i.succ) (q 0)))) →
            (TileCentroid (TileTranslation (placement.layout.P i true) c) - TileCentroid F = (1 /
            2 : Real) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) * (if Even (0 :
            Nat) then BandVectors.1 (q 0) (q (j - 1).succ) - BandVectors.1 (q (j - 1).succ) (q 0)
            else BandVectors.1 (q (j + 1).succ) (q 0) - BandVectors.1 (q 0) (q (j + 1).succ))))))
            ) := by
  classical
  intro C D T N h k x bundle placement q F hEven0 i j c hJprev hZcent4
  simpa [hEven0, hJprev] using hZcent4

end RightBoundaryRecordsGeometry

theorem P5635T1RightBoundaryInterfaceRecords
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection)
      (hcyc : (placement.rightFirstSlot = 0 ∧ placement.rightSecondSlot = 1 ∧
          placement.rightDirectionSlot = 2) ∨
        (placement.rightFirstSlot = 1 ∧ placement.rightSecondSlot = 2 ∧
          placement.rightDirectionSlot = 0) ∨
        (placement.rightFirstSlot = 2 ∧ placement.rightSecondSlot = 0 ∧
          placement.rightDirectionSlot = 1)) :
      (placement.rightNeighborPositive = true →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightFirstSlot.succ)))
          (TileTranslation (placement.layout.P placement.rightFirstSlot true)
            placement.rightNeighborDisplacement)) ∧
        Nonempty (ExactTileInterfaceTriple bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
          (TileTranslation (placement.layout.P placement.rightSecondSlot false)
            placement.rightNeighborDisplacement))) ∧
      (placement.rightNeighborPositive = false →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightFirstSlot.succ)))
          (TileTranslation (placement.layout.P placement.rightFirstSlot false)
            placement.rightNeighborDisplacement)) ∧
        Nonempty (ExactTileInterfaceTriple bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
          (TileTranslation (placement.layout.P placement.rightSecondSlot true)
            placement.rightNeighborDisplacement))) := by
-- BODY
  classical
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  change
      (placement.rightNeighborPositive = true →
     Nonempty (ExactTileInterfaceTriple F
       (TileTranslation F (-BandVectors.1 (q 0)
         (q placement.rightFirstSlot.succ)))
       (TileTranslation (placement.layout.P placement.rightFirstSlot true)
         placement.rightNeighborDisplacement)) ∧
     Nonempty (ExactTileInterfaceTriple F
       (TileTranslation F (-BandVectors.1 (q 0)
         (q placement.rightSecondSlot.succ)))
       (TileTranslation (placement.layout.P placement.rightSecondSlot false)
         placement.rightNeighborDisplacement))) ∧
      (placement.rightNeighborPositive = false →
     Nonempty (ExactTileInterfaceTriple F
       (TileTranslation F (BandVectors.1 (q 0)
         (q placement.rightFirstSlot.succ)))
       (TileTranslation (placement.layout.P placement.rightFirstSlot false)
         placement.rightNeighborDisplacement)) ∧
     Nonempty (ExactTileInterfaceTriple F
       (TileTranslation F (BandVectors.1 (q 0)
         (q placement.rightSecondSlot.succ)))
       (TileTranslation (placement.layout.P placement.rightSecondSlot true)
         placement.rightNeighborDisplacement)))
  have vectorLaws := VectorRecursionLaws q cfg.proper.1
  have turnFlip := vectorLaws.2.2.2.2 cfg.proper
  have translatedPieceCentroid := RightBoundaryRecordsGeometry.translatedPieceCentroid C D T N h
      k x bundle placement
  have rNext := RightBoundaryRecordsGeometry.rNext C D T N h k x bundle placement
  have rPrev := RightBoundaryRecordsGeometry.rPrev C D T N h k x bundle placement
  have tNext := RightBoundaryRecordsGeometry.tNext C D T N h k x bundle placement
  have tPrev := RightBoundaryRecordsGeometry.tPrev C D T N h k x bundle placement
  have cyclicVectorRecurrence := RightBoundaryRecordsGeometry.cyclicVectorRecurrence C D T N h k x
      bundle
  have hI0 : (⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) = 1 := by decide +kernel
  have hI1 : (⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) = ⟨0, 1⟩ := by decide +kernel
  have hI2 : (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) = -1 := by decide +kernel
  have hI3 : (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) = -⟨0, 1⟩ := by decide +kernel
  have auxiliaryDisplacements := RightBoundaryRecordsGeometry.auxiliaryDisplacements C D T N h k x
      bundle turnFlip cyclicVectorRecurrence hI1 hI2 hI3 (RightBoundaryRecordsGeometry.aux1Alg
      hI2 hI3) (RightBoundaryRecordsGeometry.aux2Alg hI2) (RightBoundaryRecordsGeometry.aux3Alg
      hI1) (RightBoundaryRecordsGeometry.aux4Alg hI0 hI2)
  obtain ⟨vFirst, vSecond, vRefFirst, vRefSecond, _, _, _, _, _⟩ :=
    P3045T1RightBoundaryDisplacementAlgebra q cfg.proper
      placement.rightFirstSlot placement.rightSecondSlot
      placement.rightDirectionSlot placement.right_slots_cyclic
  have gaussianNegMul (a z : GaussianInt) : -a * z = -(a * z) := by ring
  have firstPositiveCentroid := RightBoundaryRecordsGeometry.firstPositiveCentroid C D T N h k x
      bundle placement translatedPieceCentroid rNext rPrev hI3 vFirst
  have secondPositiveCentroid := RightBoundaryRecordsGeometry.secondPositiveCentroid C D T N h k
      x bundle placement translatedPieceCentroid tNext tPrev hI2 vSecond gaussianNegMul
  have firstReflectedCentroid := RightBoundaryRecordsGeometry.firstReflectedCentroid C D T N h k
      x bundle placement translatedPieceCentroid rNext rPrev hI1 vRefFirst gaussianNegMul
  have secondReflectedCentroid := RightBoundaryRecordsGeometry.secondReflectedCentroid C D T N h
      k x bundle placement translatedPieceCentroid tNext tPrev vRefSecond
  have childPositive := RightBoundaryRecordsGeometry.childPositive C D T N h k x bundle
  have hEven3 : ¬ Even (3 : Nat) := by decide
  have hEven2 : Even (2 : Nat) := by decide
  have hEven1 : ¬ Even (1 : Nat) := by decide
  have hEven0 : Even (0 : Nat) := by decide
  have fixedPositive : 0 < (q 0).1 :=
    (ProperBandCurvatureStructure q cfg.proper).1
  have fixedBand : BandPrototile (q 0) F :=
    TileOdometerBandPrototile (q 0) F bundle.normalizedFixedFunction
      (by
        change TileOdometer (bundle.normalizedPresentation 0) F
          bundle.normalizedFixedFunction
        rw [bundle.normalized_circle_eq]
        exact placement.adjacency.2.1)
  let i := placement.rightFirstSlot
  let j := placement.rightSecondSlot
  let directionSlot := placement.rightDirectionSlot
  obtain ⟨hsum, hi, hj, hk⟩ := cyclicVectorRecurrence i j directionSlot hcyc
  let a := BandVectors.1 (q directionSlot.succ) (q j.succ)
  let b := BandVectors.1 (q i.succ) (q directionSlot.succ)
  let c := BandVectors.1 (q j.succ) (q i.succ)
  have aux := auxiliaryDisplacements i j directionSlot hcyc
  have hJprev := RightBoundaryRecordsGeometry.hJprev C D T N h k x bundle placement hcyc
  have hBi : BandPrototile (q i.succ) (placement.layout.P i true) :=
    (placement.layout.outer_occurrence i true).1
  have hBj : BandPrototile (q j.succ) (placement.layout.P j true) :=
    (placement.layout.outer_occurrence j true).1
  have hBi' : BandPrototile (q i.succ) (placement.layout.P i false) :=
    (placement.layout.outer_occurrence i false).1
  have hBj' : BandPrototile (q j.succ) (placement.layout.P j false) :=
    (placement.layout.outer_occurrence j false).1
  have hWi : BandPrototile (q i.succ)
      (TileTranslation (placement.layout.P i true)
        placement.rightNeighborDisplacement) :=
    BandPrototileTranslation _ _ _ hBi
  have hWj : BandPrototile (q j.succ)
      (TileTranslation (placement.layout.P j false)
        placement.rightNeighborDisplacement) :=
    BandPrototileTranslation _ _ _ hBj'
  have hWi' : BandPrototile (q i.succ)
      (TileTranslation (placement.layout.P i false)
        placement.rightNeighborDisplacement) :=
    BandPrototileTranslation _ _ _ hBi'
  have hWj' : BandPrototile (q j.succ)
      (TileTranslation (placement.layout.P j true)
        placement.rightNeighborDisplacement) :=
    BandPrototileTranslation _ _ _ hBj
  have hZ1 : BandPrototile (q j.succ)
      (TileTranslation (placement.layout.P j true)
        (-((⟨0, 1⟩ : GaussianInt) * c))) :=
    BandPrototileTranslation _ _ _ hBj
  have hZ2 : BandPrototile (q i.succ)
      (TileTranslation (placement.layout.P i false) (-c)) :=
    BandPrototileTranslation _ _ _ hBi'
  have hZ3 : BandPrototile (q j.succ)
      (TileTranslation (placement.layout.P j false)
        ((⟨0, 1⟩ : GaussianInt) * c)) :=
    BandPrototileTranslation _ _ _ hBj'
  have hZ4 : BandPrototile (q i.succ)
      (TileTranslation (placement.layout.P i true) c) :=
    BandPrototileTranslation _ _ _ hBi
  have hZcent1 : TileCentroid
      (TileTranslation (placement.layout.P j true)
        (-((⟨0, 1⟩ : GaussianInt) * c))) - TileCentroid F =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
          (BandVectors.1 (q j.succ) (q 0) -
            BandVectors.1 (q 0) (q j.succ))) :=
    translatedPieceCentroid j true (-((⟨0, 1⟩ : GaussianInt) * c)) _ aux.1
  have hZcent2 : TileCentroid
      (TileTranslation (placement.layout.P i false) (-c)) - TileCentroid F =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
          (BandVectors.1 (q 0) (q i.succ) -
            BandVectors.1 (q i.succ) (q 0))) :=
    translatedPieceCentroid i false (-c) _ aux.2.1
  have hZcent3 : TileCentroid
      (TileTranslation (placement.layout.P j false)
        ((⟨0, 1⟩ : GaussianInt) * c)) - TileCentroid F =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (1 : Nat) *
          (BandVectors.1 (q j.succ) (q 0) -
            BandVectors.1 (q 0) (q j.succ))) :=
    translatedPieceCentroid j false ((⟨0, 1⟩ : GaussianInt) * c) _ aux.2.2.1
  have hZcent4 : TileCentroid
      (TileTranslation (placement.layout.P i true) c) - TileCentroid F =
      (1 / 2 : Real) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ (0 : Nat) *
          (BandVectors.1 (q 0) (q i.succ) -
            BandVectors.1 (q i.succ) (q 0))) :=
    translatedPieceCentroid i true c _ aux.2.2.2
  have hUpos := fixedPositive
  refine ⟨?_, ?_⟩
  · intro hpos
    have hWcent1 := firstPositiveCentroid hpos
    have hWcent2 := secondPositiveCentroid hpos
    refine ⟨?_, ?_⟩
    · have E := BandOrientedChildParentRightEndpoint q cfg.proper i 3 F
        (TileTranslation (placement.layout.P i true)
          placement.rightNeighborDisplacement)
        (TileTranslation (placement.layout.P j true)
        (-((⟨0, 1⟩ : GaussianInt) * c))) fixedBand hWi (RightBoundaryRecordsGeometry.hZ1' C D T N
            h k x bundle placement hcyc hEven3 hZ1)
        hUpos (childPositive i) hWcent1 (RightBoundaryRecordsGeometry.hZcent1' C D T N h k x
            bundle placement hcyc hEven3 hZcent1)
      simpa [i, j, directionSlot, hI2, hI3, hEven3, (turnFlip i).1] using E
    · have E := BandOrientedChildParentRightEndpoint q cfg.proper j 2 F
        (TileTranslation (placement.layout.P j false)
          placement.rightNeighborDisplacement)
        (TileTranslation (placement.layout.P i false) (-c)) fixedBand hWj
            (RightBoundaryRecordsGeometry.hZ2' C D T N h k x bundle placement hEven2 hJprev hZ2)
        hUpos (childPositive j) hWcent2 (RightBoundaryRecordsGeometry.hZcent2' C D T N h k x
            bundle placement hEven2 hJprev hZcent2)
      simpa [i, j, directionSlot, hI2, hEven2, (turnFlip j).1] using E
  · intro hneg
    have hWcent3 := firstReflectedCentroid hneg
    have hWcent4 := secondReflectedCentroid hneg
    refine ⟨?_, ?_⟩
    · have E := BandOrientedChildParentRightEndpoint q cfg.proper i 1 F
        (TileTranslation (placement.layout.P i false)
          placement.rightNeighborDisplacement)
        (TileTranslation (placement.layout.P j false)
        ((⟨0, 1⟩ : GaussianInt) * c)) fixedBand hWi' (RightBoundaryRecordsGeometry.hZ3' C D T N h
            k x bundle placement hcyc hEven1 hZ3)
        hUpos (childPositive i) hWcent3 (RightBoundaryRecordsGeometry.hZcent3' C D T N h k x
            bundle placement hcyc hEven1 hZcent3)
      simpa [i, j, directionSlot, hI1, hI2, hEven1, (turnFlip i).1] using E
    · have E := BandOrientedChildParentRightEndpoint q cfg.proper j 0 F
        (TileTranslation (placement.layout.P j true)
          placement.rightNeighborDisplacement)
        (TileTranslation (placement.layout.P i true) c) fixedBand hWj'
            (RightBoundaryRecordsGeometry.hZ4' C D T N h k x bundle placement hEven0 hJprev hZ4)
        hUpos (childPositive j) hWcent4 (RightBoundaryRecordsGeometry.hZcent4' C D T N h k x
            bundle placement hEven0 hJprev hZcent4)
      simpa [i, j, directionSlot, hI0, hEven0, (turnFlip j).1] using E

end ApollonianSuperharmonic

end
