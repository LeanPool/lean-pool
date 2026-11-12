/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.P5124T1ParentPlacement
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.P5300T1CanonicalRowArithmetic
public import LeanPool.ApollonianSuperharmonic.P5300T1CenteredCellGeometry
public import LeanPool.ApollonianSuperharmonic.P5300T1AffineCellObservables

-- [TABLET NODE: P5260T1LiteralPlacement]

/-!
# P5260T1LiteralPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5260T1LiteralPlacement :
    ∀ (K : DiamondParameter), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W : ProtoTile),
        ∀ (Z : ProtoTile), (BandPrototile ((DiamondRecursiveQuadruple K) 0) U) → ((BandPrototile
        ((DiamondRecursiveQuadruple K) i.succ) W) → ((BandPrototile
      ((DiamondRecursiveQuadruple K)
        ((if Even s.val then i - 1 else i + 1).succ)) Z) → ((0 < ((DiamondRecursiveQuadruple K)
            0).1) → ((0 < ((DiamondRecursiveQuadruple K) i.succ).1) → ((0 <
            ((DiamondRecursiveQuadruple K)
      ((if Even s.val then i - 1 else i + 1).succ)).1) → ((TileCentroid W - TileCentroid U = (1 /
          2 : Real) •
      GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.1 ((DiamondRecursiveQuadruple K) i.succ)
            ((DiamondRecursiveQuadruple K) 0) +
          BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
            ((DiamondRecursiveQuadruple K) i.succ)))) → ((TileCentroid Z - TileCentroid U = (1 /
                2 : Real) •
      GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then
          BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
              ((DiamondRecursiveQuadruple K) ((i - 1).succ)) -
            BandVectors.1 ((DiamondRecursiveQuadruple K) ((i - 1).succ))
              ((DiamondRecursiveQuadruple K) 0)
        else BandVectors.1 ((DiamondRecursiveQuadruple K) ((i + 1).succ))
              ((DiamondRecursiveQuadruple K) 0) -
            BandVectors.1 ((DiamondRecursiveQuadruple K) 0)
              ((DiamondRecursiveQuadruple K) ((i + 1).succ))))) → (
    let q := DiamondRecursiveQuadruple K
    let b : Bool := decide (s.val % 2 = 1)
    let M := P5260T1PlacementLedger K.1 i b
    let D := DiamondTile K.1
    let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (q 0) (q i.succ)
        else BandVectors.1 (q i.succ) (q 0))
    let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (q i.succ) (q 0)
        else BandVectors.1 (q 0) (q i.succ))
    let source : Fin 5 → ProtoTile :=
      ![D, TileTranslation D M.2.1.1, TileTranslation D M.2.1.2, M.1.1, M.1.2]
    let target : Fin 5 → ProtoTile :=
      ![U, TileTranslation U uR, TileTranslation U uL, W, Z]
    (1 < K.1 ∨ (i = 1 ∧ b = false) ∨ (i = 0 ∧ b = true)) ∧
      ∃ a : GaussianInt,
        let f := fun z : GaussianInt =>
          a + (if s.val < 2 then z else ⟨0, 2 * (K.1 : Int)⟩ - z)
        Function.Injective f ∧
        (∀ x y : GaussianInt,
          (y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) →
          (f y = f x + 1 ∨ f y = f x - 1 ∨
            f y = f x + ⟨0, 1⟩ ∨ f y = f x - ⟨0, 1⟩)) ∧
        (∀ j, FootprintVertices (target j) = f '' FootprintVertices (source j)) ∧
        (∀ j, FootprintEdges (target j) =
          (fun e : Finset GaussianInt => e.image f) '' FootprintEdges (source j)))))))))) := by
  intro K i s U W Z hU hW hZ hposU hposW hposZ hcentW hcentZ
-- BODY
  classical
  dsimp only
  let q := DiamondRecursiveQuadruple K
  let b : Bool := decide (s.val % 2 = 1)
  let j : Fin 3 := if Even s.val then i - 1 else i + 1
  let M := P5260T1PlacementLedger K.1 i b
  let D := DiamondTile K.1
  let C : GaussianInt := ⟨0, 2 * (K.1 : Int)⟩
  let c : Fin 3 → GaussianInt :=
    ![⟨1, 4 * (K.1 : Int) + 1⟩,
      ⟨-2 * (K.1 : Int) - 1, 2 * (K.1 : Int) - 1⟩,
      ⟨2 * (K.1 : Int), 0⟩]
  let P := fun t => P5124T1ParentModel K.1 t true
  let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
    (if Even s.val then BandVectors.1 (q 0) (q i.succ)
     else BandVectors.1 (q i.succ) (q 0))
  let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
    (if Even s.val then BandVectors.1 (q i.succ) (q 0)
     else BandVectors.1 (q 0) (q i.succ))
  obtain ⟨hcase, hR, hL, tW, tZ, hMW, hMZ, hCW, hCZ⟩ :=
    P5300T1CanonicalRowArithmetic K i s hposW hposZ
  obtain ⟨hnD, hsymD, hparents⟩ := P5300T1CenteredCellGeometry K
  obtain ⟨a, hcU, haU⟩ := BandPrototileTranslationNormalForm _ U D hU
    (DiamondTileRecursiveIdentification K).1
  have hcentU : TileCentroid U = TileCentroid (TileTranslation D a) :=
    (ProtoTileObservableExtensionality _ _ hcU haU).2.2.2.2
  let g := fun z : GaussianInt =>
    a + (if s.val < 2 then z else C - z - 1 - ⟨0, 1⟩)
  let f := fun z : GaussianInt => a + (if s.val < 2 then z else C - z)
  have image_place (S : Finset GaussianInt) (center v : GaussianInt)
      (hsym : S.image (fun z => center - z - 1 - ⟨0, 1⟩) = S) :
      (S.image (GaussianTranslation
        (if s.val < 2 then v else C - v - center))).image (GaussianTranslation a) =
        (S.image (GaussianTranslation v)).image g := by
    by_cases hs : s.val < 2
    · simp only [ite_eq_left hs, Finset.image_image, g]
      congr 1
      funext z
      simp [GaussianTranslation, add_comm]
    · simp only [ite_eq_right hs, Finset.image_image]
      calc
        S.image (GaussianTranslation a ∘ GaussianTranslation (C - v - center)) =
            (S.image (fun z => center - z - 1 - ⟨0, 1⟩)).image
              (g ∘ GaussianTranslation v) := by
          rw [Finset.image_image]
          congr 1
          funext z
          dsimp [GaussianTranslation, g]
          rw [ite_eq_right hs]
          abel
        _ = S.image (g ∘ GaussianTranslation v) := by rw [hsym]
  have hUmap : U.cells = D.cells.image g := by
    have h := image_place D.cells C 0 hsymD
    have h' : (TileTranslation D a).cells = D.cells.image g := by
      have hzero : D.cells.image (GaussianTranslation 0) = D.cells := by
        ext z
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨w, hw, he⟩
          have : w = z := by simpa only [GaussianTranslation, add_zero] using he
          exact this ▸ hw
        · intro hz
          exact ⟨z, hz, add_zero z⟩
      change D.cells.image (GaussianTranslation a) = D.cells.image g
      simpa only [sub_zero, sub_self, ite_self, hzero] using h
    exact hcU.trans h'
  have parent_match (t : Fin 3) (A B : ProtoTile) (v : GaussianInt)
      (hp : 0 < (q t.succ).1) (hB : BandPrototile (q t.succ) B)
      (hA : A.cells = (TileTranslation (P t) v).cells)
      (hcent : TileCentroid B - TileCentroid U =
        TileCentroid (TileTranslation (P t)
          (if s.val < 2 then v else C - v - c t)) - TileCentroid D) :
      A.cells.Nonempty ∧ B.cells = A.cells.image g := by
    let V := TileTranslation (P t) (if s.val < 2 then v else C - v - c t)
    have hV : BandPrototile (q t.succ) V :=
      BandPrototileTranslation _ _ _ (P5124T1ParentPlacement K t true).1
    have hn := (hparents t hp).1
    have hsym := (hparents t hp).2
    have hnA : A.cells.Nonempty := by
      rw [hA]
      exact hn.image _
    have hCB : TileCentroid B = TileCentroid (TileTranslation V a) := by
      rw [(TileTranslationFormulas V a).2.2.2.2.1]
      have hcu := hcentU
      rw [(TileTranslationFormulas D a).2.2.2.2.1] at hcu
      apply Prod.ext
      · have h1 := congrArg Prod.fst hcent
        have h2 := congrArg Prod.fst hcu
        dsimp [V] at h1 h2 ⊢
        linarith
      · have h1 := congrArg Prod.snd hcent
        have h2 := congrArg Prod.snd hcu
        dsimp [V] at h1 h2 ⊢
        linarith
    have hcells := (BandPrototileCentroidUnique _ B (TileTranslation V a)
      hB (BandPrototileTranslation _ _ _ hV) hCB).1
    refine ⟨hnA, hcells.trans ?_⟩
    rw [hA]
    exact image_place (P t).cells (c t) v hsym
  have hWdiff : TileCentroid W - TileCentroid U =
      TileCentroid (TileTranslation (P i)
        (if s.val < 2 then tW else C - tW - c i)) - TileCentroid D :=
    hcentW.trans hCW.symm
  have hZdiff : TileCentroid Z - TileCentroid U =
      TileCentroid (TileTranslation (P j)
        (if s.val < 2 then tZ else C - tZ - c j)) - TileCentroid D :=
    hcentZ.trans hCZ.symm
  obtain ⟨hnMW, hWmap⟩ := parent_match i M.1.1 W tW hposW hW hMW hWdiff
  obtain ⟨hnMZ, hZmap⟩ := parent_match j M.1.2 Z tZ hposZ hZ hMZ hZdiff
  have translated (v w : GaussianInt)
      (hw : w = if s.val < 2 then v else -v) :
      (TileTranslation U w).cells = (TileTranslation D v).cells.image g := by
    change U.cells.image (GaussianTranslation w) =
      (D.cells.image (GaussianTranslation v)).image g
    rw [hUmap, Finset.image_image, Finset.image_image]
    congr 1
    funext z
    dsimp [GaussianTranslation, g]
    by_cases hs : s.val < 2 <;> simp only [hs, ite_true, ite_false] at hw ⊢ <;>
      rw [hw] <;> abel
  have all_cells : ∀ n : Fin 5,
      (![U, TileTranslation U uR, TileTranslation U uL, W, Z] n).cells =
        (![D, TileTranslation D M.2.1.1, TileTranslation D M.2.1.2,
          M.1.1, M.1.2] n).cells.image g := by
    intro n
    fin_cases n
    · exact hUmap
    · exact translated _ _ hR
    · exact translated _ _ hL
    · exact hWmap
    · exact hZmap
  have all_nonempty : ∀ n : Fin 5,
      (![D, TileTranslation D M.2.1.1, TileTranslation D M.2.1.2,
        M.1.1, M.1.2] n).cells.Nonempty := by
    intro n
    fin_cases n
    · exact hnD
    · exact hnD.image _
    · exact hnD.image _
    · exact hnMW
    · exact hnMZ
  have obs (n : Fin 5) := P5300T1AffineCellObservables _ _ a C
    (decide (¬s.val < 2)) (all_nonempty n)
    (by by_cases hs : s.val < 2 <;> simpa [g, hs] using all_cells n)
  refine ⟨hcase, a, ?_, ?_, ?_, ?_⟩
  · intro x y h
    by_cases hs : s.val < 2
    · simpa [hs] using h
    · have h' := add_left_cancel h
      simp only [ite_eq_right hs] at h'
      exact sub_right_injective h'
  · intro x y h
    rcases h with rfl | rfl | rfl | rfl <;> by_cases hs : s.val < 2
    · exact Or.inl (by simp only [ite_eq_left hs]; abel)
    · exact Or.inr (Or.inl (by simp only [ite_eq_right hs]; abel))
    · exact Or.inr (Or.inl (by simp only [ite_eq_left hs]; abel))
    · exact Or.inl (by simp only [ite_eq_right hs]; abel)
    · exact Or.inr (Or.inr (Or.inl (by simp only [ite_eq_left hs]; abel)))
    · exact Or.inr (Or.inr (Or.inr (by simp only [ite_eq_right hs]; abel)))
    · exact Or.inr (Or.inr (Or.inr (by simp only [ite_eq_left hs]; abel)))
    · exact Or.inr (Or.inr (Or.inl (by simp only [ite_eq_right hs]; abel)))
  · intro n
    by_cases hs : s.val < 2 <;>
      simpa [hs, C, D, M, b, uR, uL, q] using (obs n).1
  · intro n
    by_cases hs : s.val < 2 <;>
      simpa [hs, C, D, M, b, uR, uL, q] using (obs n).2

end ApollonianSuperharmonic

end
