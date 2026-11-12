/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralMixedAggregatePatches
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage

-- [TABLET NODE: P4055T1OrderedGeneralOppositeEndpoints]

/-!
# P4055T1OrderedGeneralOppositeEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def pairedEndpointPackage (r : Fin 4 → CircleCoordinates) (T : ProtoTile)
    (i : Fin 3) (s : Fin 4) (W Z : ProtoTile) : Prop :=
  let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
    (if Even s.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
    (if Even s.val then BandVectors.1 (r i.succ) (r 0)
      else BandVectors.1 (r 0) (r i.succ))
  ∃ (rightData : ExactTileInterfaceTriple T (TileTranslation T uR) W)
      (incomingData : ExactTileInterfaceTriple T (TileTranslation T uL) W)
      (t5Data : ExactTileInterfaceTriple T W Z),
    rightData.point = t5Data.point ∧ incomingData.point ≠ t5Data.point ∧
      incomingData.otherCA = t5Data.point ∧ rightData.otherCA = incomingData.point ∧
      t5Data.otherAB = incomingData.point

namespace OppositeEndpointGeometry

private theorem haUre :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt), (GaussianRealPoint aU = ((TileCentroid U).1 +
            (TileCentroid U).2, (TileCentroid U).2 - (TileCentroid U).1)) → ((aU.re : Real) =
            (TileCentroid U).1 + (TileCentroid U).2) ) := by
  classical
  intro U aU haU
  have h := congrArg Prod.fst haU
  simpa [GaussianRealPoint] using h

private theorem haUim :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt), (GaussianRealPoint aU = ((TileCentroid U).1 +
            (TileCentroid U).2, (TileCentroid U).2 - (TileCentroid U).1)) → ((aU.im : Real) =
            (TileCentroid U).2 - (TileCentroid U).1) ) := by
  classical
  intro U aU haU
  have h := congrArg Prod.snd haU
  simpa [GaussianRealPoint] using h

private theorem haWre :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aW : GaussianInt), (GaussianRealPoint aW = ((TileCentroid W).1 +
            (TileCentroid W).2, (TileCentroid W).2 - (TileCentroid W).1)) → ((aW.re : Real) =
            (TileCentroid W).1 + (TileCentroid W).2) ) := by
  classical
  intro W aW haW
  have h := congrArg Prod.fst haW
  simpa [GaussianRealPoint] using h

private theorem haWim :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aW : GaussianInt), (GaussianRealPoint aW = ((TileCentroid W).1 +
            (TileCentroid W).2, (TileCentroid W).2 - (TileCentroid W).1)) → ((aW.im : Real) =
            (TileCentroid W).2 - (TileCentroid W).1) ) := by
  classical
  intro W aW haW
  have h := congrArg Prod.snd haW
  simpa [GaussianRealPoint] using h

private theorem haZre :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aZ : GaussianInt), (GaussianRealPoint aZ = ((TileCentroid Z).1 +
            (TileCentroid Z).2, (TileCentroid Z).2 - (TileCentroid Z).1)) → ((aZ.re : Real) =
            (TileCentroid Z).1 + (TileCentroid Z).2) ) := by
  classical
  intro Z aZ haZ
  have h := congrArg Prod.fst haZ
  simpa [GaussianRealPoint] using h

private theorem haZim :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aZ : GaussianInt), (GaussianRealPoint aZ = ((TileCentroid Z).1 +
            (TileCentroid Z).2, (TileCentroid Z).2 - (TileCentroid Z).1)) → ((aZ.im : Real) =
            (TileCentroid Z).2 - (TileCentroid Z).1) ) := by
  classical
  intro Z aZ haZ
  have h := congrArg Prod.snd haZ
  simpa [GaussianRealPoint] using h

private theorem hWpCent :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (W : ProtoTile), ∀ (aU : GaussianInt), ∀ (aW : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        ((aU.re : Real) = (TileCentroid U).1 + (TileCentroid U).2) → (((aU.im : Real) =
            (TileCentroid U).2 - (TileCentroid U).1) → (((aW.re : Real) = (TileCentroid W).1 +
            (TileCentroid W).2) → (((aW.im : Real) = (TileCentroid W).2 - (TileCentroid W).1) →
            (TileCentroid Wp - TileCentroid U = (-(TileCentroid W - TileCentroid U).2,
            (TileCentroid W - TileCentroid U).1))))) ) := by
  classical
  intro U W aU aW Wp haUre haUim haWre haWim
  rw [(TileTranslationFormulas W (aU - aW)).2.2.2.2.1]
  ext <;> simp only []
  all_goals simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Int.cast_sub]
  all_goals rw [haUre, haUim, haWre, haWim]
  all_goals dsimp; ring

private theorem hZpCent :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (Z : ProtoTile), ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt),
        let Zp := TileTranslation Z (aU - aZ)
        ((aU.re : Real) = (TileCentroid U).1 + (TileCentroid U).2) → (((aU.im : Real) =
            (TileCentroid U).2 - (TileCentroid U).1) → (((aZ.re : Real) = (TileCentroid Z).1 +
            (TileCentroid Z).2) → (((aZ.im : Real) = (TileCentroid Z).2 - (TileCentroid Z).1) →
            (TileCentroid Zp - TileCentroid U = (-(TileCentroid Z - TileCentroid U).2,
            (TileCentroid Z - TileCentroid U).1))))) ) := by
  classical
  intro U Z aU aZ Zp haUre haUim haZre haZim
  rw [(TileTranslationFormulas Z (aU - aZ)).2.2.2.2.1]
  ext <;> simp only []
  all_goals simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Int.cast_sub]
  all_goals rw [haUre, haUim, haZre, haZim]
  all_goals dsimp; ring

private theorem hWrot :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile), ∀ (W : ProtoTile), (TileCentroid W - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r
            i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) → (
        let q : GaussianInt := ⟨0, 1⟩
        (-(TileCentroid W - TileCentroid U).2, (TileCentroid W - TileCentroid U).1) = (1 / 2 :
            Real) • GaussianRealPoint (q * (q ^ s.val * (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ))))) ) := by
  classical
  intro r i s U W hWcent q
  rw [hWcent]
  simp [q, GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

private theorem hq2 :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        q ^ 2 = -1 ) := by
  classical
  intro q
  rw [pow_two]
  ext <;> simp [q, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem hq4 :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 2 = -1) → (q ^ 4 = 1) ) := by
  classical
  intro q hq2
  calc
    q ^ 4 = q ^ 2 * q ^ 2 := by ring
    _ = (-1 : GaussianInt) * -1 := by rw [hq2]
    _ = 1 := by norm_num

private theorem hq3 :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 2 = -1) → (q ^ 3 = -q) ) := by
  classical
  intro q hq2
  calc
    q ^ 3 = q ^ 2 * q := by rw [pow_succ]
    _ = (-1 : GaussianInt) * q := by rw [hq2]
    _ = -q := by ring

private theorem hq6 :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 2 = -1) → (q ^ 6 = -1) ) := by
  classical
  intro q hq2
  calc
    q ^ 6 = (q ^ 2) ^ 3 := by ring
    _ = (-1 : GaussianInt) ^ 3 := by rw [hq2]
    _ = -1 := by norm_num

private theorem hq2act :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 2 = -1) → (∀ (x : GaussianInt), q * (q * x) = -x) ) := by
  classical
  intro q hq2 x
  calc
    q * (q * x) = (q * q) * x := by ring
    _ = q ^ 2 * x := by rw [pow_two]
    _ = -x := by rw [hq2]; ring

private theorem hq4act :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 4 = 1) → (∀ (x : GaussianInt), q ^ 4 * x = x) ) := by
  classical
  intro q hq4 x
  rw [hq4]
  simp

private theorem hq6act :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 6 = -1) → (∀ (x : GaussianInt), q ^ 6 * x = -x) ) := by
  classical
  intro q hq6 x
  rw [hq6]
  simp

private theorem hpower :
    (by
      classical
        exact
        ∀ (s : Fin (4 : ℕ)),
          (let q : GaussianInt := ⟨0, 1⟩;
          (let t : Fin 4 := s + 1;
          ((q ^ 2 = -1) → ((q ^ 4 = 1) → (q ^ t.val = q * q ^ s.val)))))) := by
  classical
  intro s q t hq2 hq4
  fin_cases s
  · simp [t]
  · simp [t, pow_succ]
  · change q ^ 3 = q * q ^ 2
    rw [pow_succ, hq2]
    simp []
  · change (1 : GaussianInt) = q * q ^ 3
    have h : q * q ^ 3 = q ^ 4 := by
      rw [pow_succ]
      ring
    rw [h, hq4]

private theorem hWsrc :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile), ∀ (W : ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt), ∀ (aW : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        (TileCentroid Wp - TileCentroid U = (-(TileCentroid W - TileCentroid U).2, (TileCentroid
            W - TileCentroid U).1)) → (((-(TileCentroid W - TileCentroid U).2, (TileCentroid W -
            TileCentroid U).1) = (1 / 2 : Real) • GaussianRealPoint (q * (q ^ s.val *
            (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))) → (
        let t : Fin 4 := s + 1
        (q ^ t.val = q * q ^ s.val) → (TileCentroid Wp - TileCentroid U = (1 / 2 : Real) •
            GaussianRealPoint (q ^ t.val * (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0)
            (r i.succ)))))) ) := by
  classical
  intro r i s U W q aU aW Wp hWpCent hWrot t hpower
  rw [hWpCent, hWrot]
  congr 1
  rw [hpower]
  simp [mul_assoc]

private theorem hZrot :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile), ∀ (Z : ProtoTile), (TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if (Even s.val)
            then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) -
            BandVectors.1 (r (i - (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) else
            BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) - BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 : ℕ))).succ))) → (
        let q : GaussianInt := ⟨0, 1⟩
        (-(TileCentroid Z - TileCentroid U).2, (TileCentroid Z - TileCentroid U).1) = (1 / 2 :
            Real) • GaussianRealPoint (q * (q ^ s.val * (if Even s.val then BandVectors.1 (r 0)
            (r ((i - 1).succ)) - BandVectors.1 (r ((i - 1).succ)) (r 0) else BandVectors.1 (r ((i
            + 1).succ)) (r 0) - BandVectors.1 (r 0) (r ((i + 1).succ)))))) ) := by
  classical
  intro r i s U Z hZcent q
  rw [hZcent]
  by_cases hs : Even s.val
  · simp [hs, q, GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
  · simp [hs, q, GaussianRealPoint, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

private theorem hZsrc :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile), ∀ (Z : ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt),
        let Zp := TileTranslation Z (aU - aZ)
        (TileCentroid Zp - TileCentroid U = (-(TileCentroid Z - TileCentroid U).2, (TileCentroid
            Z - TileCentroid U).1)) → (
        let t : Fin 4 := s + 1
        (Even t.val ↔ ¬ Even s.val) → ((q ^ t.val = q * q ^ s.val) → (((-(TileCentroid Z -
            TileCentroid U).2, (TileCentroid Z - TileCentroid U).1) = (1 / 2 : Real) •
            GaussianRealPoint (q * (q ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r ((i -
            1).succ)) - BandVectors.1 (r ((i - 1).succ)) (r 0) else BandVectors.1 (r ((i +
            1).succ)) (r 0) - BandVectors.1 (r 0) (r ((i + 1).succ)))))) → (TileCentroid Zp -
            TileCentroid U = (1 / 2 : Real) • GaussianRealPoint (q ^ t.val * (if Even t.val then
            BandVectors.1 (r ((i + 1).succ)) (r 0) - BandVectors.1 (r 0) (r ((i + 1).succ)) else
            BandVectors.1 (r 0) (r ((i - 1).succ)) - BandVectors.1 (r ((i - 1).succ)) (r 0)))))))
            ) := by
  classical
  intro r i s U Z q aU aZ Zp hZpCent t htpar hpower hZrot
  rw [hZpCent, hZrot]
  have hvectors : q * (q ^ s.val *
      (if Even s.val then
        BandVectors.1 (r 0) (r ((i - 1).succ)) -
          BandVectors.1 (r ((i - 1).succ)) (r 0)
      else
        BandVectors.1 (r ((i + 1).succ)) (r 0) -
          BandVectors.1 (r 0) (r ((i + 1).succ)))) =
    q ^ t.val *
      (if Even t.val then
        BandVectors.1 (r ((i + 1).succ)) (r 0) -
          BandVectors.1 (r 0) (r ((i + 1).succ))
      else
        BandVectors.1 (r 0) (r ((i - 1).succ)) -
          BandVectors.1 (r ((i - 1).succ)) (r 0)) := by
    rw [hpower]
    by_cases hs : Even s.val
    · have ht : ¬ Even t.val := by
        intro ht
        exact (htpar.mp ht) hs
      simp [hs, ht, mul_assoc]
    · have ht : Even t.val := htpar.mpr hs
      simp [hs, ht, mul_assoc]
  rw [hvectors]

private theorem hZlabel :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)),
        let t : Fin 4 := s + 1
        (Even t.val ↔ ¬ Even s.val) → ((r ((if Even t.val then i + 1 else i - 1).succ)) = (r ((if
            Even s.val then i - 1 else i + 1).succ))) ) := by
  classical
  intro r i s t htpar
  by_cases hs : Even s.val
  · have ht : ¬ Even t.val := by
      intro ht
      exact (htpar.mp ht) hs
    simp [hs, ht]
  · have ht : Even t.val := htpar.mpr hs
    simp [hs, ht]

private theorem hf :
    (by
      classical
      exact
        ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (x : GaussianInt), F (f x) = x) → (Function.Injective f) ) := by
  classical
  intro aU F f hfF x y h
  have := congrArg F h
  simpa only [hfF] using this

private theorem hUedges :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt), ((TileTranslation (TileQuarterTurn U) aU).cells
            = U.cells) → (FootprintEdges (TileTranslation (TileQuarterTurn U) aU) =
            FootprintEdges U) ) := by
  classical
  intro U aU hUc
  ext e
  simp only [FootprintEdges, Set.mem_ofPred_eq, hUc]

private theorem hWedges :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aW : GaussianInt), ((TileTranslation (TileQuarterTurn W) aW).cells
            = W.cells) → (FootprintEdges (TileTranslation (TileQuarterTurn W) aW) =
            FootprintEdges W) ) := by
  classical
  intro W aW hWc
  ext e
  simp only [FootprintEdges, Set.mem_ofPred_eq, hWc]

private theorem hZedges :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aZ : GaussianInt), ((TileTranslation (TileQuarterTurn Z) aZ).cells
            = Z.cells) → (FootprintEdges (TileTranslation (TileQuarterTurn Z) aZ) =
            FootprintEdges Z) ) := by
  classical
  intro Z aZ hZc
  ext e
  simp only [FootprintEdges, Set.mem_ofPred_eq, hZc]

private theorem hFvU :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt), (FootprintVertices (TileTranslation
            (TileQuarterTurn U) aU) = FootprintVertices U) → (
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        FootprintVertices U = F '' FootprintVertices U) ) := by
  classical
  intro U aU hUv F
  conv_lhs => rw [← hUv]
  rw [(TileTranslationFormulas (TileQuarterTurn U) aU).2.2.2.2.2.1,
    (TileQuarterTurnFormulas U).2.2.2.2.2.1]
  simp only [Set.image_image]
  change (GaussianTranslation aU ∘ GaussianQuarterTurn) ''
      FootprintVertices U = F '' FootprintVertices U
  congr 1

private theorem hFeU :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (FootprintEdges (TileTranslation (TileQuarterTurn U) aU) = FootprintEdges U) →
            (FootprintEdges U = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges U) )
            := by
  classical
  intro U aU F hUedges
  conv_lhs => rw [← hUedges]
  rw [(TileTranslationFormulas (TileQuarterTurn U) aU).2.2.2.2.2.2.1,
    (TileQuarterTurnFormulas U).2.2.2.2.2.2.1]
  simp only [Set.image_image, Finset.image_image]
  change (fun e : Finset GaussianInt => e.image
    (GaussianTranslation aU ∘ GaussianQuarterTurn)) '' FootprintEdges U =
    (fun e : Finset GaussianInt => e.image F) '' FootprintEdges U
  congr 1

private theorem hFvW :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aU : GaussianInt), ∀ (aW : GaussianInt), (FootprintVertices
            (TileTranslation (TileQuarterTurn W) aW) = FootprintVertices W) → (
        let Wp := TileTranslation W (aU - aW)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        FootprintVertices Wp = F '' FootprintVertices W) ) := by
  classical
  intro W aU aW hWv Wp F
  rw [(TileTranslationFormulas W (aU - aW)).2.2.2.2.2.1]
  conv_lhs => rw [← hWv]
  rw [
    (TileTranslationFormulas (TileQuarterTurn W) aW).2.2.2.2.2.1,
    (TileQuarterTurnFormulas W).2.2.2.2.2.1]
  simp only [Set.image_image]
  congr 1
  funext x
  simp [F, GaussianTranslation]

private theorem hFvZ :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt), (FootprintVertices
            (TileTranslation (TileQuarterTurn Z) aZ) = FootprintVertices Z) → (
        let Zp := TileTranslation Z (aU - aZ)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        FootprintVertices Zp = F '' FootprintVertices Z) ) := by
  classical
  intro Z aU aZ hZv Zp F
  rw [(TileTranslationFormulas Z (aU - aZ)).2.2.2.2.2.1]
  conv_lhs => rw [← hZv]
  rw [
    (TileTranslationFormulas (TileQuarterTurn Z) aZ).2.2.2.2.2.1,
    (TileQuarterTurnFormulas Z).2.2.2.2.2.1]
  simp only [Set.image_image]
  congr 1
  funext x
  simp [F, GaussianTranslation]

private theorem hFeW :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aU : GaussianInt), ∀ (aW : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (FootprintEdges (TileTranslation (TileQuarterTurn W) aW) = FootprintEdges W) →
            (FootprintEdges Wp = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges W) )
            := by
  classical
  intro W aU aW Wp F hWedges
  rw [(TileTranslationFormulas W (aU - aW)).2.2.2.2.2.2.1]
  conv_lhs => rw [← hWedges]
  rw [
    (TileTranslationFormulas (TileQuarterTurn W) aW).2.2.2.2.2.2.1,
    (TileQuarterTurnFormulas W).2.2.2.2.2.2.1]
  simp only [Set.image_image, Finset.image_image]
  congr 1
  funext e
  ext x
  simp [F, GaussianTranslation]

private theorem hFeZ :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt),
        let Zp := TileTranslation Z (aU - aZ)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (FootprintEdges (TileTranslation (TileQuarterTurn Z) aZ) = FootprintEdges Z) →
            (FootprintEdges Zp = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges Z) )
            := by
  classical
  intro Z aU aZ Zp F hZedges
  rw [(TileTranslationFormulas Z (aU - aZ)).2.2.2.2.2.2.1]
  conv_lhs => rw [← hZedges]
  rw [
    (TileTranslationFormulas (TileQuarterTurn Z) aZ).2.2.2.2.2.2.1,
    (TileQuarterTurnFormulas Z).2.2.2.2.2.2.1]
  simp only [Set.image_image, Finset.image_image]
  congr 1
  funext e
  ext x
  simp [F, GaussianTranslation]

private theorem hinvV :
    (by
      classical
      exact
        ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (x : GaussianInt), f (F x) = x) → (∀ (S : Set GaussianInt), f '' (F '' S) = S) ) := by
  classical
  intro aU F f hFf S
  rw [Set.image_image]
  ext x
  simp [hFf]

private theorem hinvE :
    (by
      classical
      exact
        ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (x : GaussianInt), f (F x) = x) → (∀ (E : Set (Finset GaussianInt)), (fun e : Finset
            GaussianInt => e.image f) '' ((fun e : Finset GaussianInt => e.image F) '' E) = E) )
            := by
  classical
  intro aU F f hFf E
  rw [Set.image_image]
  simp only [Finset.image_image]
  change (fun e : Finset GaussianInt => e.image (f ∘ F)) '' E = E
  ext e
  simp [Function.comp_def, hFf]

private theorem hFtranslate :
    (by
      classical
      exact
        ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        ∀ (v : GaussianInt), F ∘ GaussianTranslation v = GaussianTranslation (GaussianQuarterTurn
            v) ∘ F ) := by
  classical
  intro aU F v
  funext x
  ext <;> simp [F, GaussianTranslation, GaussianQuarterTurn] <;> abel

private theorem hFtranslateE :
    (by
      classical
      exact
        ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (∀ (v : GaussianInt), F ∘ GaussianTranslation v = GaussianTranslation
            (GaussianQuarterTurn v) ∘ F) → (∀ (v : GaussianInt), (fun e : Finset GaussianInt =>
            e.image F) ∘ (fun e : Finset GaussianInt => e.image (GaussianTranslation v)) = (fun e
            : Finset GaussianInt => e.image (GaussianTranslation (GaussianQuarterTurn v))) ∘ (fun
            e : Finset GaussianInt => e.image F)) ) := by
  classical
  intro aU F hFtranslate v
  funext e
  change (e.image (GaussianTranslation v)).image F =
    (e.image F).image (GaussianTranslation (GaussianQuarterTurn v))
  rw [Finset.image_image, Finset.image_image]
  congr 1
  funext x
  exact congrFun (hFtranslate v) x

private theorem setImageComp :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ (g : β → γ), ∀ (h : α → β), ∀ (S : Set α), g
            '' (h '' S) = (g ∘ h) '' S ) := by
  classical
  intro α β γ g h S
  ext x
  simp []

private theorem hFchildV :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (FootprintVertices U = F '' FootprintVertices U) → ((∀ (v : GaussianInt), F ∘
            GaussianTranslation v = GaussianTranslation (GaussianQuarterTurn v) ∘ F) → ((∀
            {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ (g : β → γ), ∀ (h : α → β), ∀ (S : Set α),
            g '' (h '' S) = (g ∘ h) '' S) → (∀ (v : GaussianInt), FootprintVertices
            (TileTranslation U (GaussianQuarterTurn v)) = F '' FootprintVertices (TileTranslation
            U v)))) ) := by
  classical
  intro U aU F hFvU hFtranslate setImageComp v
  rw [(TileTranslationFormulas U (GaussianQuarterTurn v)).2.2.2.2.2.1,
    (TileTranslationFormulas U v).2.2.2.2.2.1]
  calc
    GaussianTranslation (GaussianQuarterTurn v) '' FootprintVertices U =
        GaussianTranslation (GaussianQuarterTurn v) ''
          (F '' FootprintVertices U) :=
            congrArg (fun S : Set GaussianInt =>
              GaussianTranslation (GaussianQuarterTurn v) '' S) hFvU
    _ = (GaussianTranslation (GaussianQuarterTurn v) ∘ F) ''
        FootprintVertices U := setImageComp _ _ _
    _ = (F ∘ GaussianTranslation v) '' FootprintVertices U := by
      exact congrArg (fun g : GaussianInt → GaussianInt =>
        g '' FootprintVertices U) (hFtranslate v).symm
    _ = F '' (GaussianTranslation v '' FootprintVertices U) := by
      exact (setImageComp F (GaussianTranslation v) _).symm

private theorem hFchildE :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        (FootprintEdges U = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges U) → ((∀
            (v : GaussianInt), (fun e : Finset GaussianInt => e.image F) ∘ (fun e : Finset
            GaussianInt => e.image (GaussianTranslation v)) = (fun e : Finset GaussianInt =>
            e.image (GaussianTranslation (GaussianQuarterTurn v))) ∘ (fun e : Finset GaussianInt
            => e.image F)) → ((∀ {α : Type}, ∀ {β : Type}, ∀ {γ : Type}, ∀ (g : β → γ), ∀ (h : α
            → β), ∀ (S : Set α), g '' (h '' S) = (g ∘ h) '' S) → (∀ (v : GaussianInt),
            FootprintEdges (TileTranslation U (GaussianQuarterTurn v)) = (fun e : Finset
            GaussianInt => e.image F) '' FootprintEdges (TileTranslation U v)))) ) := by
  classical
  intro U aU F hFeU hFtranslateE setImageComp v
  rw [(TileTranslationFormulas U (GaussianQuarterTurn v)).2.2.2.2.2.2.1,
    (TileTranslationFormulas U v).2.2.2.2.2.2.1]
  calc
    (fun e : Finset GaussianInt => e.image
        (GaussianTranslation (GaussianQuarterTurn v))) '' FootprintEdges U =
      (fun e => e.image (GaussianTranslation (GaussianQuarterTurn v))) ''
        ((fun e => e.image F) '' FootprintEdges U) :=
          congrArg (fun E : Set (Finset GaussianInt) =>
            (fun e => e.image (GaussianTranslation (GaussianQuarterTurn v))) '' E) hFeU
    _ = ((fun e => e.image (GaussianTranslation (GaussianQuarterTurn v))) ∘
        (fun e => e.image F)) '' FootprintEdges U :=
          setImageComp _ _ _
    _ = ((fun e => e.image F) ∘
        (fun e => e.image (GaussianTranslation v))) '' FootprintEdges U := by
      exact congrArg (fun g : Finset GaussianInt → Finset GaussianInt =>
        g '' FootprintEdges U) (hFtranslateE v).symm
    _ = (fun e => e.image F) ''
        ((fun e => e.image (GaussianTranslation v)) '' FootprintEdges U) := by
      exact (setImageComp (fun e : Finset GaussianInt => e.image F)
        (fun e : Finset GaussianInt => e.image (GaussianTranslation v))
        (FootprintEdges U)).symm

private theorem hQq3 :
    (by
      classical
      exact
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        ∀ (x : GaussianInt), GaussianQuarterTurn (q3 x) = x ) := by
  classical
  intro q3 x
  rcases x with ⟨xr, xi⟩
  simp [q3, GaussianQuarterTurn]

private theorem hbaseV :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintVertices U = F '' FootprintVertices U) → ((∀ (S : Set GaussianInt), f '' (F ''
            S) = S) → (FootprintVertices U = f '' FootprintVertices U)) ) := by
  classical
  intro U aU F f hFvU hinvV
  calc
    FootprintVertices U = f '' (F '' FootprintVertices U) :=
      (hinvV _).symm
    _ = f '' FootprintVertices U := by rw [← hFvU]

private theorem hbaseE :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintEdges U = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges U) → ((∀
            (E : Set (Finset GaussianInt)), (fun e : Finset GaussianInt => e.image f) '' ((fun e
            : Finset GaussianInt => e.image F) '' E) = E) → (FootprintEdges U = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges U)) ) := by
  classical
  intro U aU F f hFeU hinvE
  calc
    FootprintEdges U = (fun e : Finset GaussianInt => e.image f) ''
        ((fun e : Finset GaussianInt => e.image F) '' FootprintEdges U) :=
      (hinvE _).symm
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges U := by
      rw [← hFeU]

private theorem hparentWV :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aU : GaussianInt), ∀ (aW : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintVertices Wp = F '' FootprintVertices W) → ((∀ (S : Set GaussianInt), f '' (F ''
            S) = S) → (FootprintVertices W = f '' FootprintVertices Wp)) ) := by
  classical
  intro W aU aW Wp F f hFvW hinvV
  calc
    FootprintVertices W = f '' (F '' FootprintVertices W) :=
      (hinvV _).symm
    _ = f '' FootprintVertices Wp := by rw [hFvW]

private theorem hparentZV :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt),
        let Zp := TileTranslation Z (aU - aZ)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintVertices Zp = F '' FootprintVertices Z) → ((∀ (S : Set GaussianInt), f '' (F ''
            S) = S) → (FootprintVertices Z = f '' FootprintVertices Zp)) ) := by
  classical
  intro Z aU aZ Zp F f hFvZ hinvV
  calc
    FootprintVertices Z = f '' (F '' FootprintVertices Z) :=
      (hinvV _).symm
    _ = f '' FootprintVertices Zp := by rw [hFvZ]

private theorem hparentWE :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (aU : GaussianInt), ∀ (aW : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintEdges Wp = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges W) → ((∀
            (E : Set (Finset GaussianInt)), (fun e : Finset GaussianInt => e.image f) '' ((fun e
            : Finset GaussianInt => e.image F) '' E) = E) → (FootprintEdges W = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges Wp)) ) := by
  classical
  intro W aU aW Wp F f hFeW hinvE
  calc
    FootprintEdges W = (fun e : Finset GaussianInt => e.image f) ''
        ((fun e : Finset GaussianInt => e.image F) '' FootprintEdges W) :=
      (hinvE _).symm
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Wp := by
      rw [hFeW]

private theorem hparentZE :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (aU : GaussianInt), ∀ (aZ : GaussianInt),
        let Zp := TileTranslation Z (aU - aZ)
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (FootprintEdges Zp = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges Z) → ((∀
            (E : Set (Finset GaussianInt)), (fun e : Finset GaussianInt => e.image f) '' ((fun e
            : Finset GaussianInt => e.image F) '' E) = E) → (FootprintEdges Z = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges Zp)) ) := by
  classical
  intro Z aU aZ Zp F f hFeZ hinvE
  calc
    FootprintEdges Z = (fun e : Finset GaussianInt => e.image f) ''
        ((fun e : Finset GaussianInt => e.image F) '' FootprintEdges Z) :=
      (hinvE _).symm
    _ = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Zp := by
      rw [hFeZ]

private theorem hchildV :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (S : Set GaussianInt), f '' (F '' S) = S) → ((∀ (v : GaussianInt), FootprintVertices
            (TileTranslation U (GaussianQuarterTurn v)) = F '' FootprintVertices (TileTranslation
            U v)) → (
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (x : GaussianInt), GaussianQuarterTurn (q3 x) = x) → (∀ (v : GaussianInt),
            FootprintVertices (TileTranslation U (q3 v)) = f '' FootprintVertices
            (TileTranslation U v)))) ) := by
  classical
  intro U aU F f hinvV hFchildV q3 hQq3 v
  calc
    FootprintVertices (TileTranslation U (q3 v)) =
        f '' (F '' FootprintVertices (TileTranslation U (q3 v))) :=
      (hinvV _).symm
    _ = f '' FootprintVertices (TileTranslation U v) := by
      rw [← hFchildV (q3 v), hQq3]

private theorem hchildE :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (aU : GaussianInt),
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (E : Set (Finset GaussianInt)), (fun e : Finset GaussianInt => e.image f) '' ((fun e :
            Finset GaussianInt => e.image F) '' E) = E) → ((∀ (v : GaussianInt), FootprintEdges
            (TileTranslation U (GaussianQuarterTurn v)) = (fun e : Finset GaussianInt => e.image
            F) '' FootprintEdges (TileTranslation U v)) → (
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (x : GaussianInt), GaussianQuarterTurn (q3 x) = x) → (∀ (v : GaussianInt),
            FootprintEdges (TileTranslation U (q3 v)) = (fun e : Finset GaussianInt => e.image f)
            '' FootprintEdges (TileTranslation U v)))) ) := by
  classical
  intro U aU F f hinvE hFchildE q3 hQq3 v
  calc
    FootprintEdges (TileTranslation U (q3 v)) =
        (fun e : Finset GaussianInt => e.image f) ''
          ((fun e : Finset GaussianInt => e.image F) ''
            FootprintEdges (TileTranslation U (q3 v))) :=
      (hinvE _).symm
    _ = (fun e : Finset GaussianInt => e.image f) ''
        FootprintEdges (TileTranslation U v) := by
      rw [← hFchildE (q3 v), hQq3]

private theorem notEven1 :
    (by
      classical
      exact
        (Fin (4 : ℕ) → CircleCoordinates) → ((Fin (3 : ℕ)) → ((Fin (4 : ℕ)) → (¬ Even (1 :
            Nat)))) ) := by
  classical
  intro r i s
  rintro ⟨n, hn⟩
  omega

private theorem notEven3 :
    (by
      classical
      exact
        (Fin (4 : ℕ) → CircleCoordinates) → ((Fin (3 : ℕ)) → ((Fin (4 : ℕ)) → (¬ Even (3 :
            Nat)))) ) := by
  classical
  intro r i s
  rintro ⟨n, hn⟩
  omega

private theorem hq3mul :
    (by
      classical
      exact
        let q : GaussianInt := ⟨0, 1⟩
        (q ^ 3 = -q) → (
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        ∀ (x : GaussianInt), q3 x = q ^ 3 * x) ) := by
  classical
  intro q hq3 q3 x
  rcases x with ⟨xr, xi⟩
  rw [hq3]
  ext <;> simp [q3, q, GaussianQuarterTurn, Zsqrtd.re_mul,
    Zsqrtd.im_mul]

private theorem hdispR :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)),
          let q := { re := (0 : ℤ), im := (1 : ℤ) };
          let t := s + (1 : Fin (4 : ℕ));
          q ^ (2 : ℕ) = (-1 : GaussianInt) →
            q ^ (3 : ℕ) = -q →
              (∀ (x : GaussianInt), q * (q * x) = -x) →
                let uL :=
                  q ^ (↑s : ℕ) *
                    if Even (↑s : ℕ) then
                      BandVectors.1 (r i.succ)
                        (r (0 : Fin (4 : ℕ)))
                    else
                      BandVectors.1 (r (0 : Fin (4 : ℕ)))
                        (r i.succ);
                let q3 := fun (x : GaussianInt) =>
                  GaussianQuarterTurn
                    (GaussianQuarterTurn
                      (GaussianQuarterTurn x));
                let vR :=
                  q ^ (↑t : ℕ) *
                    if Even (↑t : ℕ) then
                      BandVectors.1 (r (0 : Fin (4 : ℕ)))
                        (r i.succ)
                    else
                      BandVectors.1 (r i.succ)
                        (r (0 : Fin (4 : ℕ)));
                Even (0 : ℕ) →
                  Even (2 : ℕ) →
                    ¬Even (1 : ℕ) →
                      ¬Even (3 : ℕ) →
                        (∀ (x : GaussianInt), q3 x = q ^ (3 : ℕ) * x) → q3 vR = uL) := by
  classical
  intro r i s q t hq2 hq3 hq2act uL q3 vR even0 even2 notEven1 notEven3 hq3mul
  let uR : GaussianInt := q ^ s.val *
    (if Even s.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  rw [hq3mul]
  fin_cases s <;> simp [vR, uL, t,
    even0, even2, notEven1, notEven3, hq2, hq3] <;>
    try simp [hq2act]

private theorem hdispL :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)),
          let q := { re := (0 : ℤ), im := (1 : ℤ) };
          let t := s + (1 : Fin (4 : ℕ));
          q ^ (2 : ℕ) = (-1 : GaussianInt) →
            q ^ (3 : ℕ) = -q →
              (∀ (x : GaussianInt), q * (q * x) = -x) →
                let uR :=
                  q ^ (↑s : ℕ) *
                    if Even (↑s : ℕ) then
                      BandVectors.1 (r (0 : Fin (4 : ℕ)))
                        (r i.succ)
                    else
                      BandVectors.1 (r i.succ)
                        (r (0 : Fin (4 : ℕ)));
                let q3 := fun (x : GaussianInt) =>
                  GaussianQuarterTurn
                    (GaussianQuarterTurn
                      (GaussianQuarterTurn x));
                let vL :=
                  q ^ (↑t : ℕ) *
                    if Even (↑t : ℕ) then
                      BandVectors.1 (r i.succ)
                        (r (0 : Fin (4 : ℕ)))
                    else
                      BandVectors.1 (r (0 : Fin (4 : ℕ)))
                        (r i.succ);
                Even (0 : ℕ) →
                  Even (2 : ℕ) →
                    ¬Even (1 : ℕ) →
                      ¬Even (3 : ℕ) →
                        (∀ (x : GaussianInt), q3 x = q ^ (3 : ℕ) * x) → q3 vL = uR) := by
  classical
  intro r i s q t hq2 hq3 hq2act uR q3 vL even0 even2 notEven1 notEven3 hq3mul
  rw [hq3mul]
  fin_cases s <;> simp [vL, uR, t,
    even0, even2, notEven1, notEven3, hq2, hq3] <;>
    try simp [hq2act]

private theorem hstep :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile), ∀ (W : ProtoTile), ∀ (Z : ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt), (GaussianRealPoint aU = ((TileCentroid U).1 + (TileCentroid U).2,
            (TileCentroid U).2 - (TileCentroid U).1)) → (((TileTranslation (TileQuarterTurn U)
            aU).cells = U.cells) → ((U.cells = ∅ → (TileTranslation (TileQuarterTurn U)
            aU).anchor = U.anchor) → ((FootprintVertices (TileTranslation (TileQuarterTurn U) aU)
            = FootprintVertices U) → (∀ (aW : GaussianInt), ∀ (aZ : GaussianInt),
        let Wp := TileTranslation W (aU - aW)
        let Zp := TileTranslation Z (aU - aZ)
        (BandPrototile (r i.succ) Wp) → ((BandPrototile (r ((if Even s.val then i - 1 else i +
            1).succ)) Zp) → (((aU.re : Real) = (TileCentroid U).1 + (TileCentroid U).2) →
            (((aU.im : Real) = (TileCentroid U).2 - (TileCentroid U).1) → ((TileCentroid Wp -
            TileCentroid U = (-(TileCentroid W - TileCentroid U).2, (TileCentroid W -
            TileCentroid U).1)) → ((TileCentroid Zp - TileCentroid U = (-(TileCentroid Z -
            TileCentroid U).2, (TileCentroid Z - TileCentroid U).1)) → (
        let t : Fin 4 := s + 1
        (TileCentroid Wp - TileCentroid U = (1 / 2 : Real) • GaussianRealPoint (q ^ t.val *
            (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ)))) → ((TileCentroid
            Zp - TileCentroid U = (1 / 2 : Real) • GaussianRealPoint (q ^ t.val * (if Even t.val
            then BandVectors.1 (r ((i + 1).succ)) (r 0) - BandVectors.1 (r 0) (r ((i + 1).succ))
            else BandVectors.1 (r 0) (r ((i - 1).succ)) - BandVectors.1 (r ((i - 1).succ)) (r
            0)))) → (
        ((pairedEndpointPackage r U) i t Wp
            Zp) → (
        let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        (∀ (x : GaussianInt), f (F x) = x) → ((∀ (x : GaussianInt), F (f x) = x) →
            ((Function.Injective f) → ((FootprintEdges (TileTranslation (TileQuarterTurn U) aU) =
            FootprintEdges U) → ((FootprintVertices U = F '' FootprintVertices U) →
            ((FootprintEdges U = (fun e : Finset GaussianInt => e.image F) '' FootprintEdges U) →
            ((FootprintVertices Wp = F '' FootprintVertices W) → ((FootprintVertices Zp = F ''
            FootprintVertices Z) → ((FootprintEdges Wp = (fun e : Finset GaussianInt => e.image
            F) '' FootprintEdges W) → ((FootprintEdges Zp = (fun e : Finset GaussianInt =>
            e.image F) '' FootprintEdges Z) → ((∀ (S : Set GaussianInt), f '' (F '' S) = S) → ((∀
            (E : Set (Finset GaussianInt)), (fun e : Finset GaussianInt => e.image f) '' ((fun e
            : Finset GaussianInt => e.image F) '' E) = E) → ((∀ (v : GaussianInt), F ∘
            GaussianTranslation v = GaussianTranslation (GaussianQuarterTurn v) ∘ F) → ((∀ (v :
            GaussianInt), (fun e : Finset GaussianInt => e.image F) ∘ (fun e : Finset GaussianInt
            => e.image (GaussianTranslation v)) = (fun e : Finset GaussianInt => e.image
            (GaussianTranslation (GaussianQuarterTurn v))) ∘ (fun e : Finset GaussianInt =>
            e.image F)) → ((∀ (v : GaussianInt), FootprintVertices (TileTranslation U
            (GaussianQuarterTurn v)) = F '' FootprintVertices (TileTranslation U v)) → ((∀ (v :
            GaussianInt), FootprintEdges (TileTranslation U (GaussianQuarterTurn v)) = (fun e :
            Finset GaussianInt => e.image F) '' FootprintEdges (TileTranslation U v)) → (
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (FootprintVertices U = f '' FootprintVertices U) → ((FootprintEdges U = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges U) → ((FootprintVertices W = f ''
            FootprintVertices Wp) → ((FootprintVertices Z = f '' FootprintVertices Zp) →
            ((FootprintEdges W = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges Wp)
            → ((FootprintEdges Z = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges
            Zp) → ((∀ (v : GaussianInt), FootprintVertices (TileTranslation U (q3 v)) = f ''
            FootprintVertices (TileTranslation U v)) → ((∀ (v : GaussianInt), FootprintEdges
            (TileTranslation U (q3 v)) = (fun e : Finset GaussianInt => e.image f) ''
            FootprintEdges (TileTranslation U v)) → (∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1
            ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (f b = f a + 1 ∨ f b = f a - 1 ∨ f b = f a + ⟨0,
            1⟩ ∨ f b = f a - ⟨0, 1⟩)))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z q aU haU hUc hUa hUv aW aZ Wp Zp hWp hZp haUre haUim hWpCent hZpCent t hWsrc
      hZsrc sourceData F f hFf hfF hf hUedges hFvU hFeU hFvW hFvZ hFeW hFeZ hinvV hinvE
      hFtranslate hFtranslateE hFchildV hFchildE q3 hbaseV hbaseE hparentWV hparentZV hparentWE
      hparentZE hchildV hchildE a b hab
  let uR : GaussianInt := q ^ s.val *
    (if Even s.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  let uL : GaussianInt := q ^ s.val *
    (if Even s.val then BandVectors.1 (r i.succ) (r 0)
      else BandVectors.1 (r 0) (r i.succ))
  rcases hab with h | h | h | h
  · subst b
    right
    right
    right
    rcases a with ⟨ar, ai⟩
    rcases aU with ⟨ur, ui⟩
    ext <;> simp [f, GaussianQuarterTurn]; omega
  · subst b
    right
    right
    left
    rcases a with ⟨ar, ai⟩
    rcases aU with ⟨ur, ui⟩
    ext <;> simp [f, GaussianQuarterTurn]; omega
  · subst b
    left
    rcases a with ⟨ar, ai⟩
    rcases aU with ⟨ur, ui⟩
    ext <;> simp [f, GaussianQuarterTurn]; omega
  · subst b
    right
    left
    rcases a with ⟨ar, ai⟩
    rcases aU with ⟨ur, ui⟩
    ext <;> simp [f, GaussianQuarterTurn]; omega

private theorem hchildVR :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt),
        let t : Fin 4 := s + 1
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (v : GaussianInt), FootprintVertices (TileTranslation U (q3 v)) = f ''
            FootprintVertices (TileTranslation U v)) → (
        let vR : GaussianInt := q ^ t.val *
          (if Even t.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        let uL : GaussianInt := q ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        (q3 vR = uL) → (FootprintVertices (TileTranslation U uL) = f '' FootprintVertices
            (TileTranslation U vR))) ) := by
  classical
  intro r i s U q aU t f q3 hchildV vR uL hdispR
  simpa [hdispR] using hchildV vR

private theorem hchildER :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt),
        let t : Fin 4 := s + 1
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (v : GaussianInt), FootprintEdges (TileTranslation U (q3 v)) = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges (TileTranslation U v)) → (
        let vR : GaussianInt := q ^ t.val *
          (if Even t.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        let uL : GaussianInt := q ^ s.val *
          (if Even s.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        (q3 vR = uL) → (FootprintEdges (TileTranslation U uL) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges (TileTranslation U vR))) ) := by
  classical
  intro r i s U q aU t f q3 hchildE vR uL hdispR
  simpa [hdispR] using hchildE vR

private theorem hchildVI :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt),
        let t : Fin 4 := s + 1
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (v : GaussianInt), FootprintVertices (TileTranslation U (q3 v)) = f ''
            FootprintVertices (TileTranslation U v)) → (
        let vL : GaussianInt := q ^ t.val *
          (if Even t.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        let uR : GaussianInt := q ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        (q3 vL = uR) → (FootprintVertices (TileTranslation U uR) = f '' FootprintVertices
            (TileTranslation U vL))) ) := by
  classical
  intro r i s U q aU t f q3 hchildV vL uR hdispL
  simpa [hdispL] using hchildV vL

private theorem hchildEI :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U :
            ProtoTile),
        let q : GaussianInt := ⟨0, 1⟩
        ∀ (aU : GaussianInt),
        let t : Fin 4 := s + 1
        let f : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
        let q3 : GaussianInt → GaussianInt := fun x =>
          GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
        (∀ (v : GaussianInt), FootprintEdges (TileTranslation U (q3 v)) = (fun e : Finset
            GaussianInt => e.image f) '' FootprintEdges (TileTranslation U v)) → (
        let vL : GaussianInt := q ^ t.val *
          (if Even t.val then BandVectors.1 (r i.succ) (r 0)
            else BandVectors.1 (r 0) (r i.succ))
        let uR : GaussianInt := q ^ s.val *
          (if Even s.val then BandVectors.1 (r 0) (r i.succ)
            else BandVectors.1 (r i.succ) (r 0))
        (q3 vL = uR) → (FootprintEdges (TileTranslation U uR) = (fun e : Finset GaussianInt =>
            e.image f) '' FootprintEdges (TileTranslation U vL))) ) := by
  classical
  intro r i s U q aU t f q3 hchildE vL uR hdispL
  simpa [hdispL] using hchildE vL

end OppositeEndpointGeometry

theorem P4055T1OrderedGeneralOppositeEndpoints :
    ∀ (r : Fin 4 → CircleCoordinates), (ProperBandQuadruple r) → (∀ (cfg :
        BandOrderedGeneralConfiguration r), ∀ (C₀ : BandCircle), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀
        (U : ProtoTile), ∀ (W : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r 0) U) →
        ((BandPrototile (r i.succ) W) → ((BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Z) → ((0 < (r 0).1) → ((0 < (r i.succ).1)
          → ((0 < (r ((if Even s.val then i - 1 else i + 1).succ)).1) → ((TileCentroid W -
          TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ)))) → ((TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (r 0) (r ((i - 1).succ)) -
              BandVectors.1 (r ((i - 1).succ)) (r 0)
          else
            BandVectors.1 (r ((i + 1).succ)) (r 0) -
              BandVectors.1 (r 0) (r ((i + 1).succ))))) → ((BandOrderedGeneralLayoutCertificate r
                  cfg C₀ U) → ((QuarterTurnSymmetric U) → ((QuarterTurnSymmetric W) →
                  ((QuarterTurnSymmetric Z) → (
    let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r 0) (r i.succ)
        else BandVectors.1 (r i.succ) (r 0))
    let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r i.succ) (r 0)
        else BandVectors.1 (r 0) (r i.succ))
    ∃ rightData : ExactTileInterfaceTriple U (TileTranslation U uR) W,
      ∃ incomingData : ExactTileInterfaceTriple U (TileTranslation U uL) W,
        ∃ adjacentData : ExactTileInterfaceTriple U W Z,
          rightData.point ≠ incomingData.point ∧
          adjacentData.point = incomingData.point ∧
          rightData.otherCA = incomingData.point ∧
          incomingData.otherCA = rightData.point ∧
          adjacentData.otherAB = rightData.point))))))))))))) := by
  intro r hproper cfg C₀ i s U W Z hU hW hZ hUpos hWpos hZpos hWcent hZcent cert hsymU hsymW hsymZ
-- BODY
  classical
  let q : GaussianInt := ⟨0, 1⟩
  obtain ⟨aU, haU, hUc, hUa, hUv, _⟩ :=
    (QuarterTurnSymmetricCenteredTransport U) hsymU
  obtain ⟨aW, haW, hWc, hWa, hWv, _⟩ :=
    (QuarterTurnSymmetricCenteredTransport W) hsymW
  obtain ⟨aZ, haZ, hZc, hZa, hZv, _⟩ :=
    (QuarterTurnSymmetricCenteredTransport Z) hsymZ
  let Wp := TileTranslation W (aU - aW)
  let Zp := TileTranslation Z (aU - aZ)
  have hWp : BandPrototile (r i.succ) Wp :=
    BandPrototileTranslation _ _ _ hW
  have hZp : BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Zp :=
    BandPrototileTranslation _ _ _ hZ
  have haUre := OppositeEndpointGeometry.haUre U aU haU
  have haUim := OppositeEndpointGeometry.haUim U aU haU
  have hWpCent := OppositeEndpointGeometry.hWpCent U W aU aW haUre
            haUim (OppositeEndpointGeometry.haWre W aW haW) (OppositeEndpointGeometry.haWim W aW
                haW)
  have hZpCent := OppositeEndpointGeometry.hZpCent U Z aU aZ haUre
            haUim (OppositeEndpointGeometry.haZre Z aZ haZ) (OppositeEndpointGeometry.haZim Z aZ
                haZ)
  have hWrot := OppositeEndpointGeometry.hWrot r i s U W hWcent
  let t : Fin 4 := s + 1
  have htpar : Even t.val ↔ ¬ Even s.val := by
    fin_cases s <;> decide
  have hq2 := OppositeEndpointGeometry.hq2
  have hq4 := OppositeEndpointGeometry.hq4 hq2
  have hq3 := OppositeEndpointGeometry.hq3 hq2
  have hq2act := OppositeEndpointGeometry.hq2act hq2
  have hq4act := OppositeEndpointGeometry.hq4act hq4
  have hq6act := OppositeEndpointGeometry.hq6act (OppositeEndpointGeometry.hq6 hq2)
  have hpower := OppositeEndpointGeometry.hpower s hq2 hq4
  have hWsrc : TileCentroid Wp - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint (q ^ t.val *
        (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) :=
            OppositeEndpointGeometry.hWsrc r i s U W aU aW hWpCent hWrot hpower
  have hZrot := OppositeEndpointGeometry.hZrot r i s U Z
                hZcent
  have hZsrc : TileCentroid Zp - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint (q ^ t.val *
        (if Even t.val then
          BandVectors.1 (r ((i + 1).succ)) (r 0) -
            BandVectors.1 (r 0) (r ((i + 1).succ))
        else
          BandVectors.1 (r 0) (r ((i - 1).succ)) -
            BandVectors.1 (r ((i - 1).succ)) (r 0))) := OppositeEndpointGeometry.hZsrc r i s U Z
                aU aZ hZpCent htpar hpower hZrot
  have hZlabel :
      (r ((if Even t.val then i + 1 else i - 1).succ)) =
        (r ((if Even s.val then i - 1 else i + 1).succ)) := OppositeEndpointGeometry.hZlabel r i
            s htpar
  have sourceData :=
    (BandOrderedGeneralMixedAggregatePatches r cfg C₀ U cert hsymU).2.2
      i t Wp Zp hWp (by rw [hZlabel]; exact hZp) hWsrc hZsrc
  let F : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x + aU
  let f : GaussianInt → GaussianInt := fun x =>
    GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (x - aU)))
  have hFf (x : GaussianInt) : f (F x) = x := by
    rcases x with ⟨xr, xi⟩
    rcases aU with ⟨ar, ai⟩
    simp [f, F, GaussianQuarterTurn]
  have hfF (x : GaussianInt) : F (f x) = x := by
    rcases x with ⟨xr, xi⟩
    rcases aU with ⟨ar, ai⟩
    simp [f, F, GaussianQuarterTurn]
  have hf := OppositeEndpointGeometry.hf aU hfF
  have hUedges := OppositeEndpointGeometry.hUedges U aU hUc
  have hFvU := OppositeEndpointGeometry.hFvU U
      aU hUv
  have hFeU := OppositeEndpointGeometry.hFeU U aU hUedges
  have hFvW := OppositeEndpointGeometry.hFvW W
      aU aW hWv
  have hFvZ := OppositeEndpointGeometry.hFvZ Z
      aU aZ hZv
  have hFeW := OppositeEndpointGeometry.hFeW W aU aW (OppositeEndpointGeometry.hWedges W aW hWc)
  have hFeZ := OppositeEndpointGeometry.hFeZ Z aU aZ (OppositeEndpointGeometry.hZedges Z aZ hZc)
  have hinvV := OppositeEndpointGeometry.hinvV aU hFf
  have hinvE := OppositeEndpointGeometry.hinvE aU hFf
  have hFtranslate := OppositeEndpointGeometry.hFtranslate aU
  have hFtranslateE := OppositeEndpointGeometry.hFtranslateE aU hFtranslate
  have setImageComp {α β γ : Type} (g : β → γ) (h : α → β)
      (S : Set α) := OppositeEndpointGeometry.setImageComp (α :=
          α) (β := β) (γ := γ) g h S
  have hFchildV := OppositeEndpointGeometry.hFchildV U aU hFvU hFtranslate setImageComp
  have hFchildE := OppositeEndpointGeometry.hFchildE U aU hFeU hFtranslateE setImageComp
  let q3 : GaussianInt → GaussianInt := fun x =>
    GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn x))
  have hQq3 := OppositeEndpointGeometry.hQq3
  have hbaseV := OppositeEndpointGeometry.hbaseV
      U aU hFvU hinvV
  have hbaseE := OppositeEndpointGeometry.hbaseE U aU hFeU hinvE
  have hparentWV := OppositeEndpointGeometry.hparentWV W aU aW hFvW hinvV
  have hparentZV := OppositeEndpointGeometry.hparentZV Z aU aZ hFvZ hinvV
  have hparentWE := OppositeEndpointGeometry.hparentWE W aU aW hFeW hinvE
  have hparentZE := OppositeEndpointGeometry.hparentZE Z aU aZ hFeZ hinvE
  have hchildV := OppositeEndpointGeometry.hchildV U aU hinvV hFchildV hQq3
  have hchildE := OppositeEndpointGeometry.hchildE U aU hinvE hFchildE hQq3
  let vR : GaussianInt := q ^ t.val *
    (if Even t.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  let vL : GaussianInt := q ^ t.val *
    (if Even t.val then BandVectors.1 (r i.succ) (r 0)
      else BandVectors.1 (r 0) (r i.succ))
  let uR : GaussianInt := q ^ s.val *
    (if Even s.val then BandVectors.1 (r 0) (r i.succ)
      else BandVectors.1 (r i.succ) (r 0))
  let uL : GaussianInt := q ^ s.val *
    (if Even s.val then BandVectors.1 (r i.succ) (r 0)
      else BandVectors.1 (r 0) (r i.succ))
  have even0 : Even (0 : Nat) := ⟨0, rfl⟩
  have even2 : Even (2 : Nat) := ⟨1, by omega⟩
  have notEven1 := OppositeEndpointGeometry.notEven1 r i s
  have notEven3 := OppositeEndpointGeometry.notEven3 r i s
  have hq3mul := OppositeEndpointGeometry.hq3mul hq3
  have hdispR := OppositeEndpointGeometry.hdispR r i s hq2 hq3 hq2act even0
      even2 notEven1 notEven3 hq3mul
  have hdispL := OppositeEndpointGeometry.hdispL r i s hq2 hq3 hq2act even0
      even2 notEven1 notEven3 hq3mul
  have hstep := OppositeEndpointGeometry.hstep r i s U W Z aU
            haU hUc hUa hUv aW aZ hWp hZp haUre haUim hWpCent hZpCent hWsrc hZsrc sourceData hFf
            hfF hf hUedges hFvU hFeU hFvW hFvZ hFeW hFeZ hinvV hinvE hFtranslate hFtranslateE
            hFchildV hFchildE hbaseV hbaseE hparentWV hparentZV hparentWE hparentZE hchildV hchildE
  rcases sourceData with ⟨Rsrc, Isrc, Asrc, hRsrc, hIneq, hICA, hRCA, hAAB⟩
  have hchildVR := OppositeEndpointGeometry.hchildVR r i s U
          aU hchildV hdispR
  have hchildER := OppositeEndpointGeometry.hchildER r i s U aU
            hchildE hdispR
  have hchildVI := OppositeEndpointGeometry.hchildVI r i s U
          aU hchildV hdispL
  have hchildEI := OppositeEndpointGeometry.hchildEI r i s U aU
            hchildE hdispL
  obtain ⟨R, hRpoint, _, _, hRca⟩ := P4055T1ExactTripleImage
    f hf hstep U (TileTranslation U vL) Wp U (TileTranslation U uR) W
    hbaseV hchildVI hparentWV hbaseE hchildEI hparentWE Isrc
  obtain ⟨I, hIpoint, _, _, hIca⟩ := P4055T1ExactTripleImage
    f hf hstep U (TileTranslation U vR) Wp U (TileTranslation U uL) W
    hbaseV hchildVR hparentWV hbaseE hchildER hparentWE Rsrc
  obtain ⟨A, hApoint, hAab, _, _⟩ := P4055T1ExactTripleImage
    f hf hstep U Wp Zp U W Z
    hbaseV hparentWV hparentZV hbaseE hparentWE hparentZE Asrc
  -- The centered turns provide integral shifts; their cell equations are
  -- used below only through observable images, never as record equalities.
  refine ⟨R, I, A, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hIneq
    apply hf
    calc
      f Isrc.point = R.point := hRpoint.symm
      _ = I.point := he
      _ = f Rsrc.point := hIpoint
      _ = f Asrc.point := congrArg f hRsrc
  · calc
      A.point = f Asrc.point := hApoint
      _ = f Rsrc.point := congrArg f hRsrc.symm
      _ = I.point := hIpoint.symm
  · calc
      R.otherCA = f Isrc.otherCA := hRca
      _ = f Asrc.point := congrArg f hICA
      _ = f Rsrc.point := congrArg f hRsrc.symm
      _ = I.point := hIpoint.symm
  · calc
      I.otherCA = f Rsrc.otherCA := hIca
      _ = f Isrc.point := congrArg f hRCA
      _ = R.point := hRpoint.symm
  · calc
      A.otherAB = f Asrc.otherAB := hAab
      _ = f Isrc.point := congrArg f hAAB
      _ = R.point := hRpoint.symm

end ApollonianSuperharmonic

end
