/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5260T1LiteralPlacement
public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.P5260T1UnitInterfaces
public import LeanPool.ApollonianSuperharmonic.P5260T1PredecessorInterfaces
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage

-- [TABLET NODE: DiamondOrientedChildParentEndpoints]

/-!
# DiamondOrientedChildParentEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondOrientedChildParentEndpoints (K : DiamondParameter) :
    let q := DiamondRecursiveQuadruple K
    ∀ (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile),
      BandPrototile (q 0) U →
      BandPrototile (q i.succ) W →
      BandPrototile
        (q ((if Even s.val then i - 1 else i + 1).succ)) Z →
      0 < (q 0).1 → 0 < (q i.succ).1 →
      0 < (q ((if Even s.val then i - 1 else i + 1).succ)).1 →
      TileCentroid W - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0)
            else
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q i.succ) (q 0)
          else BandVectors.1 (q 0) (q i.succ))
      ∃ rightData : ExactTileInterfaceTriple U (TileTranslation U uR) W,
        ∃ incomingData : ExactTileInterfaceTriple U (TileTranslation U uL) W,
          ∃ adjacentData : ExactTileInterfaceTriple U W Z,
            rightData.point ≠ incomingData.point ∧
            adjacentData.point = incomingData.point ∧
            rightData.otherCA = incomingData.point ∧
            incomingData.otherCA = rightData.point ∧
            adjacentData.otherAB = rightData.point := by
-- BODY
  dsimp only
  intro i s U W Z hU hW hZ hposU hposW hposZ hcentW hcentZ
  let b : Bool := decide (s.val % 2 = 1)
  let M := P5260T1PlacementLedger K.1 i b
  let D := DiamondTile K.1
  obtain ⟨hreg, a, hf, hstep, hv, he⟩ :=
    P5260T1LiteralPlacement K i s U W Z hU hW hZ
      hposU hposW hposZ hcentW hcentZ
  let f := fun z : GaussianInt =>
    a + (if s.val < 2 then z else ⟨0, 2 * (K.1 : Int)⟩ - z)
  have canonical :
      ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
        ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
          ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
            R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
            A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
            I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
            M.2.2.1 ≠ M.2.2.2 := by
    by_cases hi : i = 2
    · subst i
      have hk : 1 < K.1 := by
        rcases hreg with hk | ⟨hi, _⟩ | ⟨hi, _⟩
        · exact hk
        · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) hi)
        · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) hi)
      exact P5260T1PredecessorInterfaces K.1 hk b
    · exact P5260T1UnitInterfaces K.1 K.2 i b hi hreg
  obtain ⟨R, I, A, hRp, hIp, hAp, hRca, hIca, hAab, hxy⟩ := canonical
  obtain ⟨R', hRp', _, _, hRca'⟩ :=
    P4055T1ExactTripleImage f hf hstep _ _ _ _ _ _
      (hv 0) (hv 1) (hv 3) (he 0) (he 1) (he 3) R
  obtain ⟨I', hIp', _, _, hIca'⟩ :=
    P4055T1ExactTripleImage f hf hstep _ _ _ _ _ _
      (hv 0) (hv 2) (hv 3) (he 0) (he 2) (he 3) I
  obtain ⟨A', hAp', hAab', _, _⟩ :=
    P4055T1ExactTripleImage f hf hstep _ _ _ _ _ _
      (hv 0) (hv 3) (hv 4) (he 0) (he 3) (he 4) A
  refine ⟨R', I', A', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRp', hIp', hRp, hIp]
    exact fun h => hxy (hf h)
  · rw [hAp', hIp', hAp, hIp]
  · rw [hRca', hIp', hRca, hIp]
  · rw [hIca', hRp', hIca, hRp]
  · rw [hAab', hRp', hAab, hRp]

end ApollonianSuperharmonic

end
