/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P4638T1EmptyCurvature
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidBounds
public import LeanPool.ApollonianSuperharmonic.GaussianRealPointProperties

public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPrototileReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.DiamondTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification

-- [TABLET NODE: BandPrototileExists]

/-!
# BandPrototileExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PrototileConstruction

private abbrev emptyCurv := ApollonianSuperharmonic.P4638T1EmptyCurvature

private theorem positiveNonempty :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T → T.cells = ∅ → C.1 = 0)
            → (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), (0 < C.1) → ((BandPrototile C T) →
            (T.cells.Nonempty))) ) := by
  classical
  intro emptyCurv C T hpos hT
  by_contra hne
  have hEmpty : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hz := emptyCurv C T hT hEmpty
  omega

private theorem hcurvAt165 :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (C : BandCircle), (C.1.1.1.toNat = n) → ((n = (1 : ℕ)) → (C.1.1.1 = 1)) ) := by
  classical
  intro n C hc hone
  have hpos : 0 < C.1.1.1 := C.2
  omega

private theorem hgt :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (C : BandCircle), (C.1.1.1.toNat = n) → ((¬n = (1 : ℕ)) → (1 < n)) ) := by
  classical
  intro n C hc hone
  have hpos : 0 < C.1.1.1 := C.2
  have : 0 < n := by omega
  omega

private theorem hproper :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (SemiProperQuadruple q) →
            ((∀ (j : Fin (3 : ℕ)), (q j.succ).1 < C.1.1.1) → ((q 0 = C.1.1) →
            (ProperBandQuadruple q))) ) := by
  classical
  intro C q hq hless hroot
  refine ⟨hq, ?_⟩
  intro j
  have hj := hless j
  simpa [hroot] using hj

private theorem hqbase :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry),
        (
        let q' := BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1
            : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (ProperBandQuadruple ![q 0, q r.succ, q (r
            + 1).succ, q (r + 2).succ])) ) := by
  classical
  intro q hproper r g regime
  fin_cases r
  · have heq : ![q 0, q 1, q 2, q 3] = q := by
      funext i
      fin_cases i <;> rfl
    simpa [heq] using hproper
  · refine ⟨SemiProperQuadruple.rotate hproper.1, ?_⟩
    intro j
    fin_cases j
    · simpa using hproper.2 1
    · simpa using hproper.2 2
    · simpa using hproper.2 0
  · refine ⟨SemiProperQuadruple.rotate
      (SemiProperQuadruple.rotate hproper.1), ?_⟩
    intro j
    fin_cases j
    · simpa using hproper.2 2
    · simpa using hproper.2 0
    · simpa using hproper.2 1

private theorem hrootFord :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (P : FordFareyParameter), (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)),
            q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ] =
            FordRecursiveQuadruple P) → (q' 0 = FordCircleCoordinate P.p P.q) ) := by
  classical
  intro q r g q' P hEq
  have he := congrFun hEq 0
  simpa [q', FordRecursiveQuadruple] using he

private theorem hpos1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 :
            ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])) →
            ((∀ (k : Fin (4 : ℕ)), (0 : ℤ) ≤ (q' k).1) → (0 < (q' 1).1)) ) := by
  classical
  intro q r g q' cfg hnonneg
  have hn := hnonneg 1
  have hne := cfg.noLine 1
  rcases eq_or_lt_of_le hn with hz | hp
  · exact (hne hz.symm).elim
  · exact hp

private theorem hlt1 :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (C : BandCircle), (C.1.1.1.toNat = n) → (∀ (q : Fin (4 : ℕ) →
            CircleCoordinates), (q 0 = C.1.1) → (∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (ProperBandQuadruple q') → ((∀ (k : Fin (4 : ℕ)), (0 : ℤ) ≤ (q' k).1) → ((q' 1).1.toNat <
            n)))) ) := by
  classical
  intro n C hc q hroot r g q' hq' hnonneg
  have hrootcurv : (q' 0).1.toNat = n := by
    have he : q' 0 = BandPackingSymmetryCircleAction g (q 0) := by
      simp [q', BandPackingSymmetryQuadrupleAction]
    rw [he, (BandPackingSymmetryCovariance g).1]
    simpa [hroot] using hc
  have hl := hq'.2 0
  have hnat1 : ((q' 1).1.toNat : Int) = (q' 1).1 :=
    Int.toNat_of_nonneg (hnonneg 1)
  have hnat0 : ((q' 0).1.toNat : Int) = (q' 0).1 :=
    Int.toNat_of_nonneg (hnonneg 0)
  have hlcast : ((q' 1).1.toNat : Int) < ((q' 0).1.toNat : Int) := by
    rw [hnat1, hnat0]
    exact hl
  have hcast : ((q' 0).1.toNat : Int) = (n : Int) := by
    exact_mod_cast hrootcurv
  have hltcast : ((q' 1).1.toNat : Int) < (n : Int) := by
    rw [← hcast]
    exact hlcast
  exact_mod_cast hltcast

private theorem hT1' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hq' : ProperBandQuadruple q'), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (hpos1 : 0 < (q' 1).1),
        let C1 : BandCircle := ⟨
          ⟨q' 1, ⟨Or.inl hpos1, ⟨q', hq'.1, ⟨1, rfl⟩⟩⟩⟩, hpos1⟩
        ∀ (T1 : ProtoTile), (BandPrototile C1.1.1 T1) → (BandPrototile (cfg.firstPredecessor 0)
            T1) ) := by
  classical
  intro q r g q' hq' cfg hpos1 C1 T1 hT1
  rw [cfg.firstChild]
  exact hT1

private theorem hparents :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (hq' : ProperBandQuadruple q'), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (hpos1 : 0 < (q' 1).1),
        let C1 : BandCircle := ⟨
          ⟨q' 1, ⟨Or.inl hpos1, ⟨q', hq'.1, ⟨1, rfl⟩⟩⟩⟩, hpos1⟩
        ∀ (T1 : ProtoTile), (BandPrototile C1.1.1 T1) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence cfg.firstPredecessor T1 i s
            (S i s)) → (
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        ∀ i, ∀ s, BandPrototile (q' i.succ) (U i s))) ) := by
  classical
  intro q r g q' hq' cfg hpos1 C1 T1 hT1 S hocc a U i s
  fin_cases i <;> cases s
  · simpa [U, C1] using hT1
  · simpa [U, C1] using BandPrototileTranslation _ _ (a - ⟨0, 1⟩ * a) hT1
  · have h := (hocc 1 false).1
    change BandPrototile (cfg.firstPredecessor 2) _ at h
    rw [cfg.firstParentTwo] at h
    simpa [U] using BandPrototileTranslation _ _ (-⟨0, 1⟩ * a) h
  · have h := (hocc 1 true).1
    change BandPrototile (cfg.firstPredecessor 2) _ at h
    rw [cfg.firstParentTwo] at h
    simpa [U] using BandPrototileTranslation _ _ a h
  · have h := (hocc 2 false).1
    change BandPrototile (cfg.firstPredecessor 3) _ at h
    rw [cfg.firstParentThree] at h
    simpa [U] using BandPrototileTranslation _ _ a h
  · have h := (hocc 2 true).1
    change BandPrototile (cfg.firstPredecessor 3) _ at h
    rw [cfg.firstParentThree] at h
    simpa [U] using BandPrototileTranslation _ _ (-⟨0, 1⟩ * a) h

private theorem hcells0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        ∀ (x : GaussianInt), x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells ) := by
  classical
  intro q r g q' T1 S a U T0 x
  simp only [Fintype.univ_bool, Finset.biUnion_insert, Finset.singleton_biUnion,
      Finset.mem_biUnion, Finset.mem_univ, Finset.mem_union, true_and, Bool.exists_bool, T0]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inl hi⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inl hi⟩

private theorem hfoot :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), (0 < C.1) → ((BandPrototile C T) →
            (T.cells.Nonempty))) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 :
            ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])) →
            ((∀ (k : Fin (4 : ℕ)), (0 : ℤ) ≤ (q' k).1) → (∀ (T1 : ProtoTile), (T1.cells.Nonempty)
            → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        (∀ i, ∀ s, BandPrototile (q' i.succ) (U i s)) → (
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        (∀ (x : GaussianInt), x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells) → (∀ i, ∀ s,
            FootprintVertices (U i s) ⊆ FootprintVertices T0)))))) ) := by
  classical
  intro positiveNonempty q r g q' cfg hnonneg T1 hT1ne S a U hparents T0 hcells0 i s v hv
  have hposChild : 0 < (q' i.succ).1 := by
    have hnn := hnonneg i.succ
    have hne := cfg.noLine i.succ
    rcases eq_or_lt_of_le hnn with hzero | hp
    · exact (hne hzero.symm).elim
    · exact hp
  have hUne : (U i s).cells.Nonempty :=
    positiveNonempty (q' i.succ) (U i s) hposChild (hparents i s)
  have hT0ne : T0.cells.Nonempty := by
    rcases hT1ne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact (hcells0 x).2 ⟨0, false, by simpa [U] using hx⟩
  simp only [FootprintVertices, ite_eq_left hUne, ite_eq_left hT0ne,
    Set.mem_ofPred_eq] at hv ⊢
  obtain ⟨x, hx, hvertex⟩ := hv
  exact ⟨x, (hcells0 x).2 ⟨i, s, hx⟩, hvertex⟩


private theorem pointI :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (z : GaussianInt), GaussianRealPoint (I * z) = (-(GaussianRealPoint z).2,
            (GaussianRealPoint z).1) ) := by
  classical
  intro I z
  ext <;> simp [I, GaussianRealPoint]

private theorem rRotateV :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])),
        let I : GaussianInt := ⟨0, 1⟩
        BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2) ) := by
  classical
  intro q r g cfg I
  simpa [I] using
    (VectorRecursionLaws _
      (SemiProperQuadruple.rotate cfg.firstProper.1)).2.2.1

private theorem hv21 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 0) = BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) - I * BandVectors.1
            (cfg.firstPredecessor 3) (cfg.firstPredecessor 2)) → (BandVectors.1
            (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = v + I * a) ) := by
  classical
  intro q r g q' cfg a I v rRotateV
  rw [cfg.firstParentThree, cfg.firstParentTwo, cfg.firstChild] at rRotateV
  rw [cfg.firstParentTwo]
  dsimp [v, a, I] at rRotateV ⊢
  linear_combination -rRotateV

private theorem hv13 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = v + I * a) →
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -v - (1 + I) * a)
            ) := by
  classical
  intro q r g q' cfg a I v hv21
  have hsum :=
    (VectorRecursionLaws cfg.firstPredecessor cfg.firstProper.1).1
  rw [cfg.firstParentThree, cfg.firstParentTwo] at hsum
  have h21 := hv21
  rw [cfg.firstParentTwo] at h21
  rw [h21] at hsum
  rw [cfg.firstParentThree]
  dsimp [v, a, I] at hsum ⊢
  linear_combination hsum

private theorem hq13 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        (ProperBandQuadruple q') → (
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        BandVectors.1 (q' 1) (q' 3) = -a - v) ) := by
  classical
  intro q r g q' hq' a v
  have hsum := (VectorRecursionLaws q' hq'.1).1
  dsimp [a, v] at hsum ⊢
  linear_combination hsum

private theorem dIdent1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -v - (1 + I) * a) →
            ((BandVectors.1 (q' 1) (q' 3) = -a - v) → (d (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) + GaussianRealPoint a - d a = d (BandVectors.1 (q' 1) (q'
            3)))) ) := by
  classical
  intro q r g q' cfg a I d v hv13 hq13
  rw [hv13, hq13]
  ext <;> norm_num [d, GaussianRealPoint, I] <;> ring

private theorem dIdent2 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3) = -v - (1 + I) * a) →
            ((BandVectors.1 (q' 1) (q' 3) = -a - v) → (-d (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3)) - GaussianRealPoint (I * a) - d a = -d (BandVectors.1 (q'
            1) (q' 3)))) ) := by
  classical
  intro q r g q' cfg a I d v hv13 hq13
  rw [hv13, hq13]
  ext <;> norm_num [d, GaussianRealPoint, I] <;> ring

private theorem dIdent3 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = v + I * a) → (d
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)) - GaussianRealPoint
            (I * a) - d a = d v) ) := by
  classical
  intro q r g q' cfg a I d v hv21
  rw [hv21]
  ext <;> norm_num [d, GaussianRealPoint, I] <;> ring

private theorem dIdent4 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1) = v + I * a) → (-d
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)) + GaussianRealPoint
            a - d a = -d v) ) := by
  classical
  intro q r g q' cfg a I d v hv21
  rw [hv21]
  ext <;> norm_num [d, GaussianRealPoint, I] <;> ring

private theorem hs1m :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (T1 : ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence cfg.firstPredecessor T1 i s (S i s)) → (
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (S 1 false) - TileCentroid T1 = -d (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))) ) := by
  classical
  intro q r g cfg T1 S hocc d
  simpa [d] using (hocc 1 false).2.2

private theorem hs1p :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (T1 : ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence cfg.firstPredecessor T1 i s (S i s)) → (
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (S 1 true) - TileCentroid T1 = d (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))) ) := by
  classical
  intro q r g cfg T1 S hocc d
  simpa [d] using (hocc 1 true).2.2

private theorem hs2m :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (T1 : ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence cfg.firstPredecessor T1 i s (S i s)) → (
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (S 2 false) - TileCentroid T1 = -d (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))) ) := by
  classical
  intro q r g cfg T1 S hocc d
  simpa [d] using (hocc 2 false).2.2

private theorem hs2p :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry), ∀ (cfg : BandOrderedGeneralConfiguration
            (BandPackingSymmetryQuadrupleAction g ![q (0 : Fin (4 : ℕ)), q r.succ, q (r + (1 :
            Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 : ℕ))).succ])), ∀ (T1 : ProtoTile), ∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence cfg.firstPredecessor T1 i s (S i s)) → (
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (S 2 true) - TileCentroid T1 = d (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))) ) := by
  classical
  intro q r g cfg T1 S hocc d
  simpa [d] using (hocc 2 true).2.2

private theorem transCent :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation V z) = TileCentroid
            V + GaussianRealPoint z ) := by
  classical
  intro V z
  rw [(TileTranslationFormulas V z).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem hcent' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (cfg : BandOrderedGeneralConfiguration (BandPackingSymmetryQuadrupleAction g ![q (0 :
            Fin (4 : ℕ)), q r.succ, q (r + (1 : Fin (3 : ℕ))).succ, q (r + (2 : Fin (3 :
            ℕ))).succ])), ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        (∀ (z : GaussianInt), GaussianRealPoint (-z) = -GaussianRealPoint z) → ((∀ (z :
            GaussianInt), GaussianRealPoint (I * z) = (-(GaussianRealPoint z).2,
            (GaussianRealPoint z).1)) → (
        let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
        (d (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) + GaussianRealPoint
            a - d a = d (BandVectors.1 (q' 1) (q' 3))) → ((-d (BandVectors.1
            (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)) - GaussianRealPoint (I * a) - d a
            = -d (BandVectors.1 (q' 1) (q' 3))) → ((d (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1)) - GaussianRealPoint (I * a) - d a = d v) → ((-d
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1)) + GaussianRealPoint
            a - d a = -d v) → (
        let p0 : Real × Real := TileCentroid T1 + d a
        (TileCentroid (S 1 false) - TileCentroid T1 = -d (BandVectors.1 (cfg.firstPredecessor 1)
            (cfg.firstPredecessor 3))) → ((TileCentroid (S 1 true) - TileCentroid T1 = d
            (BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3))) → ((TileCentroid
            (S 2 false) - TileCentroid T1 = -d (BandVectors.1 (cfg.firstPredecessor 2)
            (cfg.firstPredecessor 1))) → ((TileCentroid (S 2 true) - TileCentroid T1 = d
            (BandVectors.1 (cfg.firstPredecessor 2) (cfg.firstPredecessor 1))) → ((∀ (V :
            ProtoTile), ∀ (z : GaussianInt), TileCentroid (TileTranslation V z) = TileCentroid V
            + GaussianRealPoint z) → (∀ i, ∀ s, TileCentroid (U i s) - p0 = (if s = true then (1
            : Real) else -1) • d (BandVectors.1 (q' ((i + 2).succ)) (q' ((i +
            1).succ)))))))))))))) ) := by
  classical
  intro q r g q' cfg T1 S a U I d pointNeg pointI v dIdent1 dIdent2 dIdent3 dIdent4 p0 hs1m hs1p
      hs2m hs2p transCent i s
  fin_cases i <;> cases s
  · simp [U, p0, a]
  · simp only [Fin.isValue, Int.reduceNeg, neg_mul, Fin.zero_eta, ↓reduceIte, zero_add,
      Fin.reduceSucc, Fin.succ_one_eq_two, one_smul, U, p0]
    change TileCentroid (TileTranslation T1 (a - I * a)) -
      p0 = d a
    rw [transCent]
    dsimp [p0]
    ext <;> simp [d, I, GaussianRealPoint] <;> ring
  · simp only [Fin.isValue, Int.reduceNeg, neg_mul, Fin.mk_one, one_ne_zero, ↓reduceIte,
      Bool.false_eq_true, Fin.reduceAdd, Fin.succ_zero_eq_one, Fin.reduceSucc, neg_smul,
      one_smul, U, p0]
    change TileCentroid (TileTranslation (S 1 false) (-((⟨0, 1⟩ : GaussianInt) *
        a))) -
      p0 = -d (BandVectors.1 (q' 1) (q' 3))
    rw [transCent]
    rw [show GaussianRealPoint (-((⟨0, 1⟩ : GaussianInt) * a)) =
      -GaussianRealPoint (I * a) by simpa [I] using pointNeg (I * a)]
    rw [pointI]
    dsimp [p0]
    apply Prod.ext
    · have hh := congrArg Prod.fst hs1m
      have hd := congrArg Prod.fst dIdent2
      rw [pointI] at hd
      dsimp [d] at hh hd ⊢
      linarith
    · have hh := congrArg Prod.snd hs1m
      have hd := congrArg Prod.snd dIdent2
      rw [pointI] at hd
      dsimp [d] at hh hd ⊢
      linarith
  · simp only [Fin.isValue, Int.reduceNeg, neg_mul, Fin.mk_one, one_ne_zero, ↓reduceIte,
      Fin.reduceAdd, Fin.succ_zero_eq_one, Fin.reduceSucc, one_smul, U, p0]
    change TileCentroid (TileTranslation (S 1 true) a) -
      p0 = d (BandVectors.1 (q' 1) (q' 3))
    rw [transCent]
    dsimp [p0]
    apply Prod.ext
    · have hh := congrArg Prod.fst hs1p
      have hd := congrArg Prod.fst dIdent1
      simp [GaussianRealPoint] at hh hd ⊢
      linarith
    · have hh := congrArg Prod.snd hs1p
      have hd := congrArg Prod.snd dIdent1
      simp [GaussianRealPoint] at hh hd ⊢
      linarith
  · simp only [Fin.isValue, Int.reduceNeg, neg_mul, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
      Bool.false_eq_true, Fin.reduceAdd, Fin.succ_one_eq_two, Fin.succ_zero_eq_one, neg_smul,
      one_smul, U, p0]
    change TileCentroid (TileTranslation (S 2 false) a) -
      p0 = -d v
    rw [transCent]
    dsimp [p0]
    apply Prod.ext
    · have hh := congrArg Prod.fst hs2m
      have hd := congrArg Prod.fst dIdent4
      simp [GaussianRealPoint] at hh hd ⊢
      linarith
    · have hh := congrArg Prod.snd hs2m
      have hd := congrArg Prod.snd dIdent4
      simp [GaussianRealPoint] at hh hd ⊢
      linarith
  · simp only [Fin.isValue, Int.reduceNeg, neg_mul, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
      Fin.reduceAdd, Fin.succ_one_eq_two, Fin.succ_zero_eq_one, one_smul, U, p0]
    change TileCentroid (TileTranslation (S 2 true) (-((⟨0, 1⟩ : GaussianInt) *
        a))) -
      p0 = d v
    rw [transCent]
    rw [show GaussianRealPoint (-((⟨0, 1⟩ : GaussianInt) * a)) =
      -GaussianRealPoint (I * a) by simpa [I] using pointNeg (I * a)]
    rw [pointI]
    dsimp [p0]
    apply Prod.ext
    · have hh := congrArg Prod.fst hs2p
      have hd := congrArg Prod.fst dIdent3
      rw [pointI] at hd
      dsimp [d] at hh hd ⊢
      linarith
    · have hh := congrArg Prod.snd hs2p
      have hd := congrArg Prod.snd dIdent3
      rw [pointI] at hd
      dsimp [d] at hh hd ⊢
      linarith

private theorem hboundRe :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty), ∀ p ∈ TileRealization T1, (↑(reCells.min' reNe) : Real) ≤
            p.1 ∧ p.1 ≤ (↑(reCells.max' reNe) : Real) + 1 ) := by
  classical
  intro T1 reCells reNe p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · exact le_trans (by exact_mod_cast
      (Finset.min'_le (T1.cells.image fun x => x.re) x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))) hpx.1.1
  · have hh := Finset.le_max' (T1.cells.image fun x => x.re) x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hh' : (x.re : Real) ≤ (reCells.max' reNe : Real) := by
      exact_mod_cast hh
    linarith [hh', hpx.2.1]

private theorem reflect1 :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let c1 := TileCentroid T1
        (CentrallyReflectedAt c1 T1 T1) → (∀ p ∈ TileRealization T1, (2 * c1.1 - p.1, 2 * c1.2 -
            p.2) ∈ TileRealization T1) ) := by
  classical
  intro T1 c1 hcentral1 p hp
  rw [hcentral1]
  exact ⟨p, hp, rfl⟩

private theorem minReCell :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty),
        let mRe := reCells.min' reNe
        ∃ x ∈ T1.cells, x.re = mRe ) := by
  classical
  intro T1 reCells reNe mRe
  rcases Finset.mem_image.mp (Finset.min'_mem reCells reNe) with ⟨x, hx, he⟩
  exact ⟨x, hx, he⟩

private theorem maxReCell :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty),
        let MRe := reCells.max' reNe
        ∃ x ∈ T1.cells, x.re = MRe ) := by
  classical
  intro T1 reCells reNe MRe
  rcases Finset.mem_image.mp (Finset.max'_mem reCells reNe) with ⟨x, hx, he⟩
  exact ⟨x, hx, he⟩

private theorem centerRe :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let c1 := TileCentroid T1
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        ∀ (reNe : reCells.Nonempty), (∀ p ∈ TileRealization T1, (↑(reCells.min' reNe) : Real) ≤
            p.1 ∧ p.1 ≤ (↑(reCells.max' reNe) : Real) + 1) → ((∀ p ∈ TileRealization T1, (2 *
            c1.1 - p.1, 2 * c1.2 - p.2) ∈ TileRealization T1) → (
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        (∃ x ∈ T1.cells, x.re = mRe) → ((∃ x ∈ T1.cells, x.re = MRe) → (2 * c1.1 = (mRe : Real) +
            MRe + 1)))) ) := by
  classical
  intro T1 c1 reCells reNe hboundRe reflect1 mRe MRe minReCell maxReCell
  rcases minReCell with ⟨xmin, hxmin, hxminre⟩
  rcases maxReCell with ⟨xmax, hmax, hmaxre⟩
  have pmin : ((mRe : Real), (xmin.im : Real)) ∈ TileRealization T1 := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmin, hxmin, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hxminre], by simp []⟩,
      ⟨by simp [hxminre], by simp⟩⟩
  have pmax : (((MRe : Real) + 1), (xmax.im : Real)) ∈ TileRealization T1 := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmax, hmax, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hmaxre], by simp⟩,
      ⟨by simp [hmaxre], by simp⟩⟩
  have bmin := hboundRe _ (reflect1 _ pmin)
  have bmax := hboundRe _ (reflect1 _ pmax)
  dsimp at bmin bmax
  norm_num at bmin bmax ⊢
  linarith [bmin.2, bmax.1]

private theorem hboundIm :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (imNe : imCells.Nonempty), ∀ p ∈ TileRealization T1, (↑(imCells.min' imNe) : Real) ≤
            p.2 ∧ p.2 ≤ (↑(imCells.max' imNe) : Real) + 1 ) := by
  classical
  intro T1 imCells imNe p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · exact le_trans (Int.cast_le.mpr
      (Finset.min'_le _ x.im (Finset.mem_image.mpr ⟨x, hx, rfl⟩))) hpx.1.2
  · have hh := Finset.le_max' (T1.cells.image fun x => x.im) x.im
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hh' : (x.im : Real) ≤ (imCells.max' imNe : Real) := by
      exact_mod_cast hh
    linarith [hpx.2.2]

private theorem minImCell :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (imNe : imCells.Nonempty),
        let mIm := imCells.min' imNe
        ∃ x ∈ T1.cells, x.im = mIm ) := by
  classical
  intro T1 imCells imNe mIm
  rcases Finset.mem_image.mp (Finset.min'_mem imCells imNe) with ⟨x, hx, he⟩
  exact ⟨x, hx, he⟩

private theorem maxImCell :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (imNe : imCells.Nonempty),
        let MIm := imCells.max' imNe
        ∃ x ∈ T1.cells, x.im = MIm ) := by
  classical
  intro T1 imCells imNe MIm
  rcases Finset.mem_image.mp (Finset.max'_mem imCells imNe) with ⟨x, hx, he⟩
  exact ⟨x, hx, he⟩

private abbrev centerIm :=
  BandPrototileCentroidBounds.imaginaryCenter

private theorem ht1 :
    (by
      classical
      exact
        ∀ (T1 : ProtoTile),
        let c1 := TileCentroid T1
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        (2 * c1.1 = (mRe : Real) + MRe + 1) → (
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        (2 * c1.2 = (mIm : Real) + MIm + 1) → (
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        GaussianRealPoint t1 = (2 * c1.1, 2 * c1.2))) ) := by
  classical
  intro T1 c1 reCells imCells reNe imNe mRe MRe centerRe mIm MIm centerIm t1
  apply Prod.ext
  · simp [t1, GaussianRealPoint]
    linarith [centerRe]
  · simp [t1, GaussianRealPoint]
    linarith [centerIm]

private theorem ht0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let c1 := TileCentroid T1
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        (GaussianRealPoint t1 = (2 * c1.1, 2 * c1.2)) → (
        let t0 : GaussianInt := t1 + a - I * a
        GaussianRealPoint t0 = (2 : Real) • p0) ) := by
  classical
  intro q r g q' T1 a I d p0 c1 reCells imCells reNe imNe mRe MRe mIm MIm t1 ht1 t0
  apply Prod.ext
  · have ht := congrArg Prod.fst ht1
    dsimp [t0, p0, d, I, GaussianRealPoint] at ht ⊢
    norm_num at ht ⊢
    linarith
  · have ht := congrArg Prod.snd ht1
    dsimp [t0, p0, d, I, GaussianRealPoint] at ht ⊢
    norm_num at ht ⊢
    linarith

private theorem hsigned :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        (∀ i, ∀ s, BandPrototile (q' i.succ) (U i s)) → (
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        (∀ i, ∀ s, TileCentroid (U i s) - p0 = (if s = true then (1 : Real) else -1) • d
            (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)))) → (∀ (i : Fin (3 : ℕ)),
        let w := BandVectors.1 (q' (i + (2 : Fin (3 : ℕ))).succ) (q' (i + (1 : Fin (3 : ℕ))).succ);
        let u := GaussianQuarterTurn w - w; (TileTranslation (U i true) u).cells = (U i
            false).cells ∧ ((U i true).cells = ∅ → (TileTranslation (U i true) u).anchor = (U i
            false).anchor) ∧ FootprintVertices (TileTranslation (U i true) u) = FootprintVertices
            (U i false) ∧ TileCentroid (TileTranslation (U i true) u) = TileCentroid (U i false)
            ∧ TileArea (U i true) = TileArea (U i false) ∧ CentrallyReflectedAt p0 (U i true) (U
            i false))) ) := by
  classical
  intro q r g q' T1 S a U hparents d p0 hcent'
  exact BandSignedOccurrenceHalfTurn q' p0 U hparents (by
    intro i s
    simpa [d] using hcent' i s)

private theorem pairEq :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        (∀ (i : Fin (3 : ℕ)),
        let w := BandVectors.1 (q' (i + (2 : Fin (3 : ℕ))).succ) (q' (i + (1 : Fin (3 : ℕ))).succ);
        let u := GaussianQuarterTurn w - w; (TileTranslation (U i true) u).cells = (U i
            false).cells ∧ ((U i true).cells = ∅ → (TileTranslation (U i true) u).anchor = (U i
            false).anchor) ∧ FootprintVertices (TileTranslation (U i true) u) = FootprintVertices
            (U i false) ∧ TileCentroid (TileTranslation (U i true) u) = TileCentroid (U i false)
            ∧ TileArea (U i true) = TileArea (U i false) ∧ CentrallyReflectedAt p0 (U i true) (U
            i false)) → (∀ (i : Fin 3), TileRealization (U i false) = R '' TileRealization (U i
            true)) ) := by
  classical
  intro q r g q' T1 S a U d p0 R hsigned i
  simpa [R, CentrallyReflectedAt] using (hsigned i).2.2.2.2.2

private theorem pairMem :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        (∀ (p : Real × Real), R (R p) = p) → ((∀ (i : Fin 3), TileRealization (U i false) = R ''
            TileRealization (U i true)) → (∀ (i : Fin 3), ∀ (p : Real × Real), (p ∈
            TileRealization (U i false) ↔ R p ∈ TileRealization (U i true)))) ) := by
  classical
  intro q r g q' T1 S a U d p0 R hRinv pairEq i p
  constructor
  · intro hp
    rw [pairEq i] at hp
    rcases hp with ⟨q, hq, hqp⟩
    have heq : R p = q := by
      calc R p = R (R q) := congrArg R hqp.symm
           _ = q := hRinv q
    rw [heq]
    exact hq
  · intro hp
    have hp' : p = R (R p) := (hRinv p).symm
    rw [hp']
    rw [pairEq i]
    exact ⟨R p, hp, rfl⟩

private theorem pairMem' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        (∀ (p : Real × Real), R (R p) = p) → ((∀ (i : Fin 3), ∀ (p : Real × Real), (p ∈
            TileRealization (U i false) ↔ R p ∈ TileRealization (U i true))) → (∀ (i : Fin 3), ∀
            (p : Real × Real), (p ∈ TileRealization (U i true) ↔ R p ∈ TileRealization (U i
            false)))) ) := by
  classical
  intro q r g q' T1 S a U d p0 R hRinv pairMem i p
  simpa [hRinv] using (pairMem i (R p)).symm

private theorem realization0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        (∀ (x : GaussianInt), x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells) → (TileRealization T0 = ⋃
            i : Fin 3, ⋃ s : Bool, TileRealization (U i s)) ) := by
  classical
  intro q r g q' T1 S a U T0 hcells0
  ext p
  simp only [TileRealization, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases (hcells0 x).mp hx with ⟨i, s, hs⟩
    exact ⟨i, s, x, hs, hp⟩
  · rintro ⟨i, s, x, hx, hp⟩
    exact ⟨x, (hcells0 x).mpr ⟨i, s, hx⟩, hp⟩

private theorem hcentral0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        (∀ (p : Real × Real), R (R p) = p) → ((∀ (i : Fin 3), ∀ (p : Real × Real), (p ∈
            TileRealization (U i false) ↔ R p ∈ TileRealization (U i true))) → ((∀ (i : Fin 3), ∀
            (p : Real × Real), (p ∈ TileRealization (U i true) ↔ R p ∈ TileRealization (U i
            false))) → ((TileRealization T0 = ⋃ i : Fin 3, ⋃ s : Bool, TileRealization (U i s)) →
            (CentrallyReflectedAt p0 T0 T0)))) ) := by
  classical
  intro q r g q' T1 S a U T0 d p0 R hRinv pairMem pairMem' realization0
  rw [CentrallyReflectedAt, realization0]
  ext p
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, s, hp⟩
    cases s
    · have hh := (pairMem i p).mp hp
      refine ⟨R p, ⟨i, true, hh⟩, ?_⟩
      exact hRinv p
    · have hh := (pairMem' i p).mp hp
      exact ⟨R p, ⟨i, false, hh⟩, hRinv p⟩
  · rintro ⟨x, ⟨i, s, hx⟩, hxp⟩
    have hx' : R p ∈ TileRealization (U i s) := by
      have he : x = R p := by
        calc x = R (R x) := (hRinv x).symm
             _ = R p := congrArg R hxp
      rw [← he]
      exact hx
    cases s
    · exact ⟨i, true, (pairMem' i p).mpr hx'⟩
    · exact ⟨i, false, (pairMem i p).mpr hx'⟩

private theorem gridCenter :
    (by
      classical
        exact
        (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry),
              let q' : Fin 4 → CircleCoordinates :=
                BandPackingSymmetryQuadrupleAction g
                  ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ];
              ∀ (T1 : ProtoTile),
                ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                  let a : GaussianInt := BandVectors.1 (q' 3) (q' 2);
                  let U : Fin 3 → Bool → ProtoTile := fun i s =>
                    if i = 0 then
                      if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
                    else
                      if i = 1 then
                        if s then TileTranslation (S 1 s) a
                        else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
                      else
                        if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
                        else TileTranslation (S 2 s) a;
                  let T0 : ProtoTile :=
                    ⟨Finset.univ.biUnion
                        (fun i : Fin 3 =>
                          Finset.univ.biUnion (fun s : Bool => (U i s).cells)),
                      T1.anchor⟩;
                  (∀ (x : GaussianInt),
                    ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) ∈
                        TileRealization T0 ↔
                      x ∈ T0.cells))) := by
  classical
  intro q r g q' T1 S a U T0 x
  constructor
  · intro hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    rcases hp with ⟨y, hy, hsq⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hsq
    have hyx : y = x := by
      apply Zsqrtd.ext
      · have h1 : (y.re : Real) < (x.re : Real) + 1 := by linarith [hsq.1.1]
        have h2 : (x.re : Real) < (y.re : Real) + 1 := by linarith [hsq.2.1]
        have h1' : y.re < x.re + 1 := by exact_mod_cast h1
        have h2' : x.re < y.re + 1 := by exact_mod_cast h2
        omega
      · have h1 : (y.im : Real) < (x.im : Real) + 1 := by linarith [hsq.1.2]
        have h2 : (x.im : Real) < (y.im : Real) + 1 := by linarith [hsq.2.2]
        have h1' : y.im < x.im + 1 := by exact_mod_cast h1
        have h2' : x.im < y.im + 1 := by exact_mod_cast h2
        omega
    simpa [hyx] using hy
  · intro hx
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    norm_num [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]

private theorem tau_center :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        (GaussianRealPoint t0 = (2 : Real) • p0) → (
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        ∀ (x : GaussianInt), R ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) = (((tau x).re :
            Real) + 1 / 2, ((tau x).im : Real) + 1 / 2)) ) := by
  classical
  intro q r g q' T1 a I d p0 reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 ht0 R tau x
  apply Prod.ext
  · have hr := congrArg Prod.fst ht0
    have htr : (t0.re : Real) = 2 * p0.1 := by
      simpa [GaussianRealPoint] using hr
    have htau : (tau x).re = t0.re - x.re - 1 := by
      simp [tau, I]
    change 2 * p0.1 - ((x.re : Real) + 1 / 2) =
      ((tau x).re : Real) + 1 / 2
    rw [← htr, htau]
    push_cast
    ring
  · have hi := congrArg Prod.snd ht0
    have hti : (t0.im : Real) = 2 * p0.2 := by
      simpa [GaussianRealPoint] using hi
    have htau : (tau x).im = t0.im - x.im - 1 := by
      simp [tau, I]
    change 2 * p0.2 - ((x.im : Real) + 1 / 2) =
      ((tau x).im : Real) + 1 / 2
    rw [← hti, htau]
    push_cast
    ring

private theorem tau_cells :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let I : GaussianInt := ⟨0, 1⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        let R : Real × Real → Real × Real := fun p =>
          (2 * p0.1 - p.1, 2 * p0.2 - p.2)
        (CentrallyReflectedAt p0 T0 T0) → ((∀ (x : GaussianInt), ((x.re : Real) + 1 / 2, (x.im :
            Real) + 1 / 2) ∈ TileRealization T0 ↔ x ∈ T0.cells) → (
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        (∀ (x : GaussianInt), R ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) = (((tau x).re :
            Real) + 1 / 2, ((tau x).im : Real) + 1 / 2)) → (∀ (x : GaussianInt), (x ∈ T0.cells) →
            (tau x ∈ T0.cells)))) ) := by
  classical
  intro q r g q' T1 S a U T0 I d p0 reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 R hcentral0
      gridCenter tau tau_center x hx
  apply (gridCenter (tau x)).mp
  rw [← tau_center]
  rw [CentrallyReflectedAt] at hcentral0
  have hc : (R ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2)) ∈
      TileRealization T0 := by
    rw [hcentral0]
    exact ⟨((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2),
      (gridCenter x).mpr hx, rfl⟩
  exact hc

private theorem hT0neAt738 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), (T1.cells.Nonempty) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        (∀ (x : GaussianInt), x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells) → (T0.cells.Nonempty)) )
            := by
  classical
  intro q r g q' T1 hT1ne S a U T0 hcells0
  rcases hT1ne with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply (hcells0 x).mpr
  refine ⟨0, false, ?_⟩
  simpa [U] using hx

private theorem sumRe :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let I : GaussianInt := ⟨0, 1⟩
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        (∀ (x : GaussianInt), tau (tau x) = x) → ((∀ (x : GaussianInt), (x ∈ T0.cells) → (tau x ∈
            T0.cells)) → (T0.cells.sum (fun x => (x.re : Real)) = T0.cells.sum (fun x => ((tau
            x).re : Real)))) ) := by
  classical
  intro q r g q' T1 S a U T0 I reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 tau tau_invol
      tau_cells
  apply Finset.sum_bij (fun x _ => tau x)
  · intro x hx
    exact tau_cells x hx
  · intro x hx y hy he
    have hh := congrArg tau he
    simpa [tau_invol] using hh
  · intro y hy
    exact ⟨tau y, tau_cells y hy, tau_invol y⟩
  · intro x hx
    exact (congrArg (fun z => (z.re : Real)) (tau_invol x)).symm

private theorem sumIm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let I : GaussianInt := ⟨0, 1⟩
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        (∀ (x : GaussianInt), tau (tau x) = x) → ((∀ (x : GaussianInt), (x ∈ T0.cells) → (tau x ∈
            T0.cells)) → (T0.cells.sum (fun x => (x.im : Real)) = T0.cells.sum (fun x => ((tau
            x).im : Real)))) ) := by
  classical
  intro q r g q' T1 S a U T0 I reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 tau tau_invol
      tau_cells
  apply Finset.sum_bij (fun x _ => tau x)
  · intro x hx
    exact tau_cells x hx
  · intro x hx y hy he
    have hh := congrArg tau he
    simpa [tau_invol] using hh
  · intro y hy
    exact ⟨tau y, tau_cells y hy, tau_invol y⟩
  · intro x hx
    exact (congrArg (fun z => (z.im : Real)) (tau_invol x)).symm

private theorem sRe :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let I : GaussianInt := ⟨0, 1⟩
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        (T0.cells.sum (fun x => (x.re : Real)) = T0.cells.sum (fun x => ((tau x).re : Real))) →
            ((∀ x, ((tau x).re : Real) = (t0.re : Real) - (x.re : Real) - 1) → (2 * T0.cells.sum
            (fun x => (x.re : Real)) = (T0.cells.card : Real) * (t0.re : Real) - T0.cells.card))
            ) := by
  classical
  intro q r g q' T1 S a U T0 I reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 tau sumRe hre
  have hs := sumRe
  simp_rw [hre] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.sum_const] at hs
  simp only [Int.reduceNeg, GaussianInt.intCast_re, nsmul_eq_mul, mul_one] at hs
  have hEq : T0.cells.sum (fun x => (x.re : Real)) =
      T0.cells.sum (fun x => (GaussianInt.toComplex x).re) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact GaussianInt.intCast_re x
  have hs' : T0.cells.sum (fun x => (x.re : Real)) =
      (T0.cells.card : Real) * (GaussianInt.toComplex t0).re -
        T0.cells.sum (fun x => (x.re : Real)) - T0.cells.card := by
    rw [hEq]
    simpa using hs
  rw [show (GaussianInt.toComplex t0).re = (t0.re : Real) by
    exact (GaussianInt.intCast_re t0).symm] at hs'
  nlinarith [hs']

private theorem sIm :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let I : GaussianInt := ⟨0, 1⟩
        let reCells : Finset Int := T1.cells.image (fun x => x.re)
        let imCells : Finset Int := T1.cells.image (fun x => x.im)
        ∀ (reNe : reCells.Nonempty), ∀ (imNe : imCells.Nonempty),
        let mRe := reCells.min' reNe
        let MRe := reCells.max' reNe
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
        let t0 : GaussianInt := t1 + a - I * a
        let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
        (T0.cells.sum (fun x => (x.im : Real)) = T0.cells.sum (fun x => ((tau x).im : Real))) →
            ((∀ x, ((tau x).im : Real) = (t0.im : Real) - (x.im : Real) - 1) → (2 * T0.cells.sum
            (fun x => (x.im : Real)) = (T0.cells.card : Real) * (t0.im : Real) - T0.cells.card))
            ) := by
  classical
  intro q r g q' T1 S a U T0 I reCells imCells reNe imNe mRe MRe mIm MIm t1 t0 tau sumIm him
  have hs := sumIm
  simp_rw [him] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.sum_const] at hs
  simp only [Int.reduceNeg, GaussianInt.intCast_im, nsmul_eq_mul, mul_one] at hs
  have hEq : T0.cells.sum (fun x => (x.im : Real)) =
      T0.cells.sum (fun x => (GaussianInt.toComplex x).im) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact GaussianInt.intCast_im x
  have hs' : T0.cells.sum (fun x => (x.im : Real)) =
      (T0.cells.card : Real) * (GaussianInt.toComplex t0).im -
        T0.cells.sum (fun x => (x.im : Real)) - T0.cells.card := by
    rw [hEq]
    simpa using hs
  rw [show (GaussianInt.toComplex t0).im = (t0.im : Real) by
    exact (GaussianInt.intCast_im t0).symm] at hs'
  nlinarith [hs']

private theorem hcentroid0 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        (T0.cells.Nonempty) → (TileCentroid T0 = (((T0.cells.sum fun x => (x.re : Real)) /
            T0.cells.card) + 1 / 2, ((T0.cells.sum fun x => (x.im : Real)) / T0.cells.card) + 1 /
            2)) ) := by
  classical
  intro q r g q' T1 S a U T0 hT0ne
  simp [TileCentroid, hT0ne]

private theorem hcent :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (T1 : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
        let U : Fin 3 → Bool → ProtoTile := fun i s =>
          if i = 0 then
            if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
          else if i = 1 then
            if s then TileTranslation (S 1 s) a
            else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
          else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
            else TileTranslation (S 2 s) a
        let T0 : ProtoTile :=
          ⟨Finset.univ.biUnion (fun i : Fin 3 =>
            Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
        let d : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        let p0 : Real × Real := TileCentroid T1 + d a
        (∀ i, ∀ s, TileCentroid (U i s) - p0 = (if s = true then (1 : Real) else -1) • d
            (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)))) → ((TileCentroid T0 = p0) →
            (∀ i, ∀ s, TileCentroid (U i s) - TileCentroid T0 = (if s = true then (1 : Real) else
            -1) • ((1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i
            + 1).succ))) - (-((GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i +
            1).succ)))).2), (GaussianRealPoint (BandVectors.1 (q' ((i + 2).succ)) (q' ((i +
            1).succ)))).1))))) ) := by
  classical
  intro q r g q' T1 S a U T0 d p0 hcent' hrootCent i s
  rw [hrootCent]
  simpa [d, p0] using hcent' i s

private theorem hq0 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q 0 = C.1.1) → (∀ (r : Fin
            (3 : ℕ)), ∀ (g : BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (inverse : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction inverse (BandPackingSymmetryCircleAction g C) = C) →
            (BandPackingSymmetryCircleAction inverse (q' 0) = C.1.1)) ) := by
  classical
  intro C q hroot r g q' inverse hinvC
  have hq0' : q' 0 = BandPackingSymmetryCircleAction g (C.1.1) := by
    simp [q', BandPackingSymmetryQuadrupleAction, hroot]
  rw [hq0']
  exact hinvC _

private theorem hresult' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (g :
            BandPackingSymmetry),
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        ∀ (normalized : ∃ T : ProtoTile, BandPrototile (q' 0) T), ∀ (inverse :
            BandPackingSymmetry), (BandPrototile (BandPackingSymmetryCircleAction inverse (q' (0
            : Fin (4 : ℕ)))) (BandPackingSymmetryTileAction inverse normalized.choose)) →
            ((BandPackingSymmetryCircleAction inverse (q' 0) = C.1.1) → (BandPrototile (C.1.1)
            (BandPackingSymmetryTileAction inverse normalized.choose))) ) := by
  classical
  intro C q r g q' normalized inverse hresult hq0
  simpa only [hq0] using hresult

end PrototileConstruction

namespace PrototileAssembly

private theorem hrootCent :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (r : Fin (3 : ℕ)),
            ∀ (g : BandPackingSymmetry),
              let q' : Fin 4 → CircleCoordinates :=
                BandPackingSymmetryQuadrupleAction g
                  ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
              ∀ (T1 : ProtoTile),
                T1.cells.Nonempty →
                  ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
                    let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
                    let U : Fin 3 → Bool → ProtoTile := fun i s =>
                      if i = 0 then if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
                      else
                        if i = 1 then
                          if s then TileTranslation (S 1 s) a
                          else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
                        else
                          if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
                          else TileTranslation (S 2 s) a
                    (∀ i, ∀ s, BandPrototile (q' i.succ) (U i s)) →
                      let T0 : ProtoTile :=
                        ⟨Finset.univ.biUnion fun i : Fin 3 =>
                            Finset.univ.biUnion fun s : Bool => (U i s).cells,
                          T1.anchor⟩
                      (∀ (x : GaussianInt), x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells) →
                        let d : GaussianInt → Real × Real := fun z =>
                          (1 / 2 : Real) •
                            (GaussianRealPoint z -
                              (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
                        let p0 : Real × Real := TileCentroid T1 + d a
                        (∀ i,
                            ∀ s,
                              TileCentroid (U i s) - p0 =
                                (if s = true then (1 : Real) else -1) •
                                d (BandVectors.1 (q' (i + 2).succ) (q' (i + 1).succ))) →
                          let c1 := TileCentroid T1
                          let reCells : Finset Int := T1.cells.image fun x => x.re
                          let imCells : Finset Int := T1.cells.image fun x => x.im
                          ∀ (reNe : reCells.Nonempty),
                            ∀ (imNe : imCells.Nonempty),
                              let mRe := reCells.min' reNe
                              let MRe := reCells.max' reNe
                              (∃ x ∈ T1.cells, x.re = mRe) →
                                (∃ x ∈ T1.cells, x.re = MRe) →
                                let mIm := imCells.min' imNe
                              let MIm := imCells.max' imNe
                              (∃ x ∈ T1.cells, x.im = mIm) →
                                (∃ x ∈ T1.cells, x.im = MIm) →
                                let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
                              GaussianRealPoint t1 = (2 * c1.1, 2 * c1.2) →
                                TileCentroid T0 = p0
    ) := by
  classical
  intro q r g q' T1 hT1ne S a U hparents T0 hcells0 d p0 hcent' c1 reCells imCells reNe imNe mRe
      MRe minReCell maxReCell mIm MIm minImCell maxImCell t1 ht1
  let I : GaussianInt := ⟨0, 1⟩
  let t0 : GaussianInt := t1 + a - I * a
  have ht0 : GaussianRealPoint t0 = (2 : Real) • p0 := PrototileConstruction.ht0
      q r g T1 reNe imNe ht1
  let R : Real × Real → Real × Real := fun p =>
    (2 * p0.1 - p.1, 2 * p0.2 - p.2)
  have hRinv (p : Real × Real) : R (R p) = p := by
    apply Prod.ext <;> dsimp [R] <;> ring
  have hsigned := PrototileConstruction.hsigned q r g T1 S hparents hcent'
  have pairEq (i : Fin 3) :
      TileRealization (U i false) = R '' TileRealization (U i true) :=
          PrototileConstruction.pairEq q r g T1 S hsigned i
  have pairMem (i : Fin 3) (p : Real × Real) :
      (p ∈ TileRealization (U i false) ↔
        R p ∈ TileRealization (U i true)) := PrototileConstruction.pairMem q r g
            T1 S hRinv pairEq i p
  have pairMem' (i : Fin 3) (p : Real × Real) :
      (p ∈ TileRealization (U i true) ↔
        R p ∈ TileRealization (U i false)) := PrototileConstruction.pairMem' q r
            g T1 S hRinv pairMem i p
  have realization0 : TileRealization T0 =
      ⋃ i : Fin 3, ⋃ s : Bool, TileRealization (U i s) :=
          PrototileConstruction.realization0 q r g T1 S hcells0
  have hcentral0 : CentrallyReflectedAt p0 T0 T0 :=
      PrototileConstruction.hcentral0 q r g T1 S hRinv pairMem pairMem' realization0
  have gridCenter (x : GaussianInt) :
      ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) ∈
        TileRealization T0 ↔ x ∈ T0.cells := PrototileConstruction.gridCenter
            q r g T1 S x
  let tau : GaussianInt → GaussianInt := fun x => t0 - x - 1 - I
  have tau_invol (x : GaussianInt) : tau (tau x) = x := by
    apply Zsqrtd.ext <;> simp [tau, I] <;> omega
  have tau_center (x : GaussianInt) :
      R ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) =
        (((tau x).re : Real) + 1 / 2, ((tau x).im : Real) + 1 / 2) :=
            PrototileConstruction.tau_center q r g T1 reNe imNe ht0 x
  have tau_cells (x : GaussianInt) (hx : x ∈ T0.cells) :
      tau x ∈ T0.cells := PrototileConstruction.tau_cells q r g T1 S reNe imNe
          hcentral0 gridCenter tau_center x hx
  have hT0ne : T0.cells.Nonempty := PrototileConstruction.hT0neAt738 q r g T1
      hT1ne S hcells0
  have sumRe : T0.cells.sum (fun x => (x.re : Real)) =
      T0.cells.sum (fun x => ((tau x).re : Real)) := PrototileConstruction.sumRe
          q r g T1 S reNe imNe tau_invol tau_cells
  have sumIm : T0.cells.sum (fun x => (x.im : Real)) =
      T0.cells.sum (fun x => ((tau x).im : Real)) := PrototileConstruction.sumIm
          q r g T1 S reNe imNe tau_invol tau_cells
  have hre : ∀ x, ((tau x).re : Real) =
      (t0.re : Real) - (x.re : Real) - 1 := (show
          ∀ x, ((tau x).re : Real) = (t0.re : Real) - (x.re : Real) - 1
        from by
          classical
          intro x
          simp [tau, I])
  have him : ∀ x, ((tau x).im : Real) =
      (t0.im : Real) - (x.im : Real) - 1 := (show
          ∀ x, ((tau x).im : Real) = (t0.im : Real) - (x.im : Real) - 1
        from by
          classical
          intro x
          simp [tau, I])
  have sRe : 2 * T0.cells.sum (fun x => (x.re : Real)) =
      (T0.cells.card : Real) * (t0.re : Real) - T0.cells.card :=
          PrototileConstruction.sRe q r g T1 S reNe imNe sumRe hre
  have sIm : 2 * T0.cells.sum (fun x => (x.im : Real)) =
      (T0.cells.card : Real) * (t0.im : Real) - T0.cells.card :=
          PrototileConstruction.sIm q r g T1 S reNe imNe sumIm him
  have hcentroid0 : TileCentroid T0 =
      (((T0.cells.sum fun x => (x.re : Real)) / T0.cells.card) + 1 / 2,
       ((T0.cells.sum fun x => (x.im : Real)) / T0.cells.card) + 1 / 2) :=
           PrototileConstruction.hcentroid0 q r g T1 S hT0ne
  rw [hcentroid0]
  apply Prod.ext
  · have hh := congrArg Prod.fst ht0
    have hh' : (t0.re : Real) = 2 * p0.1 := by
      simpa [GaussianRealPoint] using hh
    have hp : p0.1 = (t0.re : Real) / 2 := by linarith
    have hcard : (T0.cells.card : Real) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hT0ne)
    rw [hp]
    field_simp [hcard]
    nlinarith [sRe]
  · have hh := congrArg Prod.snd ht0
    have hh' : (t0.im : Real) = 2 * p0.2 := by
      simpa [GaussianRealPoint] using hh
    have hp : p0.2 = (t0.im : Real) / 2 := by linarith
    have hcard : (T0.cells.card : Real) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hT0ne)
    rw [hp]
    field_simp [hcard]
    nlinarith [sIm]

end PrototileAssembly

namespace PositivePrototileProof

private theorem unitExists (C : BandCircle) (hcurvature : C.1.1.1 = 1) :
    ∃ T : ProtoTile, BandPrototile C.1.1 T := by
  obtain ⟨z, hz⟩ := CurvatureOneBandCircleClassification C hcurvature
  refine ⟨⟨{0}, 0⟩, ?_⟩
  rw [hz]
  exact BandPrototile.unit z 0 0

private theorem existence :
    (by
      classical
      exact
        (∀ (C : CircleCoordinates), ∀ (T : ProtoTile), (0 < C.1) → ((BandPrototile C T) →
            (T.cells.Nonempty))) → (∀ n : Nat, ∀ C : BandCircle, C.1.1.1.toNat = n → ∃ T :
            ProtoTile, BandPrototile C.1.1 T) ) := by
  classical
  intro positiveNonempty n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro C hc
    by_cases hone : n = 1
    · exact unitExists C (PrototileConstruction.hcurvAt165 n C hc hone)
    · have hgt := PrototileConstruction.hgt n C hc hone
      obtain hunit | ⟨q, hq, hchild, hless, _⟩ := BandGenealogy C
      · have hcurvature : n = 1 := by simpa only [hunit, Int.toNat_one] using hc.symm
        exact (hone hcurvature).elim
      · have hroot : q 0 = C.1.1 := by simpa using hchild
        have hproper : ProperBandQuadruple q := PrototileConstruction.hproper C q hq hless hroot
        obtain ⟨r, g, regime⟩ := BandRegimeClassification q hproper
        let q' : Fin 4 → CircleCoordinates :=
          BandPackingSymmetryQuadrupleAction g
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        have hqbase : ProperBandQuadruple
            ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] := PrototileConstruction.hqbase q
                hproper r g regime
        have hq' : ProperBandQuadruple q' :=
          BandPackingSymmetryProperCovariance g _ hqbase
        have normalized : ∃ T : ProtoTile, BandPrototile (q' 0) T := by
          rcases regime with hford | hrest
          · rcases hford with ⟨⟨P, hP, hEq⟩, _⟩
            have htile := (FordTileRecursiveIdentification P).1
            have hrootFord : q' 0 = FordCircleCoordinate P.p P.q :=
                PrototileConstruction.hrootFord q r g P hEq
            exact ⟨FordTile P.q, hrootFord ▸ htile⟩
          · rcases hrest with hdiamond | hgeneral
            · rcases hdiamond with ⟨⟨K, hK, hEq⟩, _⟩
              have htile := (DiamondTileRecursiveIdentification K).1
              refine ⟨DiamondTile K.1, ?_⟩
              simpa [q', hEq] using htile
            · rcases hgeneral with ⟨cfg⟩
              rcases cfg with ⟨cfg⟩
              have hnonneg := (SemiProperForestClassification q' hq'.1).1
              have hpos1 : 0 < (q' 1).1 := PrototileConstruction.hpos1 q r g cfg hnonneg
              have hlt1 : (q' 1).1.toNat < n := PrototileConstruction.hlt1 n C hc q hroot r g
                  hq' hnonneg
              let C1 : BandCircle := ⟨
                ⟨q' 1, ⟨Or.inl hpos1, ⟨q', hq'.1, ⟨1, rfl⟩⟩⟩⟩, hpos1⟩
              obtain ⟨T1, hT1⟩ := ih (Int.toNat (q' 1).1) hlt1 C1 (by rfl)
              have hT1' : BandPrototile (cfg.firstPredecessor 0) T1 :=
                  PrototileConstruction.hT1' q r g hq' cfg hpos1 T1 hT1
              have hT1ne : T1.cells.Nonempty := by
                apply positiveNonempty _ _ hpos1 hT1
              obtain ⟨S, hocc, hcells⟩ := BandPrototileReindexedDecomposition
                cfg.firstPredecessor cfg.firstProper T1 hT1'
              let a : GaussianInt := BandVectors.1 (q' 3) (q' 2)
              let U : Fin 3 → Bool → ProtoTile := fun i s =>
                if i = 0 then
                  if s then TileTranslation T1 (a - ⟨0, 1⟩ * a) else T1
                else if i = 1 then
                  if s then TileTranslation (S 1 s) a
                  else TileTranslation (S 1 s) (-⟨0, 1⟩ * a)
                else if s then TileTranslation (S 2 s) (-⟨0, 1⟩ * a)
                  else TileTranslation (S 2 s) a
              have hparents : ∀ i s, BandPrototile (q' i.succ) (U i s) :=
                  PrototileConstruction.hparents q r g hq' cfg hpos1 T1 hT1 S hocc
              let T0 : ProtoTile :=
                ⟨Finset.univ.biUnion (fun i : Fin 3 =>
                  Finset.univ.biUnion (fun s : Bool => (U i s).cells)), T1.anchor⟩
              have hcells0 (x : GaussianInt) :
                  x ∈ T0.cells ↔ ∃ i s, x ∈ (U i s).cells := PrototileConstruction.hcells0 q r
                      g T1 S x
              have hfoot : ∀ i s, FootprintVertices (U i s) ⊆ FootprintVertices T0 :=
                  PrototileConstruction.hfoot positiveNonempty q r g cfg hnonneg T1 hT1ne S
                  hparents hcells0
              let I : GaussianInt := ⟨0, 1⟩
              let d : GaussianInt → Real × Real := fun z =>
                (1 / 2 : Real) • (GaussianRealPoint z -
                  (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
              have pointNeg (z : GaussianInt) :
                  GaussianRealPoint (-z) = -GaussianRealPoint z :=
                      GaussianRealPointProperties.negation z
              have pointI (z : GaussianInt) :
                  GaussianRealPoint (I * z) =
                    (-(GaussianRealPoint z).2, (GaussianRealPoint z).1) :=
                        PrototileConstruction.pointI z
              let v : GaussianInt := BandVectors.1 (q' 2) (q' 1)
              have rRotateV :
                  BandVectors.1 (cfg.firstPredecessor 2)
                      (cfg.firstPredecessor 0) =
                    BandVectors.1 (cfg.firstPredecessor 2)
                        (cfg.firstPredecessor 1) -
                      I * BandVectors.1 (cfg.firstPredecessor 3)
                        (cfg.firstPredecessor 2) := PrototileConstruction.rRotateV q r g cfg
              have hv21 : BandVectors.1 (cfg.firstPredecessor 2)
                    (cfg.firstPredecessor 1) = v + I * a := PrototileConstruction.hv21 q r g
                        cfg rRotateV
              have hv13 : BandVectors.1 (cfg.firstPredecessor 1)
                    (cfg.firstPredecessor 3) = -v - (1 + I) * a := PrototileConstruction.hv13 q
                        r g cfg hv21
              have hq13 : BandVectors.1 (q' 1) (q' 3) = -a - v := PrototileConstruction.hq13 q
                  r g hq'
              have dIdent1 : d (BandVectors.1 (cfg.firstPredecessor 1)
                  (cfg.firstPredecessor 3)) + GaussianRealPoint a - d a =
                  d (BandVectors.1 (q' 1) (q' 3)) := PrototileConstruction.dIdent1 q r g cfg
                      hv13 hq13
              have dIdent2 : -d (BandVectors.1 (cfg.firstPredecessor 1)
                  (cfg.firstPredecessor 3)) - GaussianRealPoint (I * a) - d a =
                  -d (BandVectors.1 (q' 1) (q' 3)) := PrototileConstruction.dIdent2 q r g cfg
                      hv13 hq13
              have dIdent3 : d (BandVectors.1 (cfg.firstPredecessor 2)
                  (cfg.firstPredecessor 1)) - GaussianRealPoint (I * a) - d a =
                  d v := PrototileConstruction.dIdent3 q r g cfg hv21
              have dIdent4 : -d (BandVectors.1 (cfg.firstPredecessor 2)
                  (cfg.firstPredecessor 1)) + GaussianRealPoint a - d a =
                  -d v := PrototileConstruction.dIdent4 q r g cfg hv21
              let p0 : Real × Real := TileCentroid T1 + d a
              have hs1m : TileCentroid (S 1 false) - TileCentroid T1 =
                  -d (BandVectors.1 (cfg.firstPredecessor 1)
                    (cfg.firstPredecessor 3)) := PrototileConstruction.hs1m q r g cfg T1 S hocc
              have hs1p : TileCentroid (S 1 true) - TileCentroid T1 =
                  d (BandVectors.1 (cfg.firstPredecessor 1)
                    (cfg.firstPredecessor 3)) := PrototileConstruction.hs1p q r g cfg T1 S hocc
              have hs2m : TileCentroid (S 2 false) - TileCentroid T1 =
                  -d (BandVectors.1 (cfg.firstPredecessor 2)
                    (cfg.firstPredecessor 1)) := PrototileConstruction.hs2m q r g cfg T1 S hocc
              have hs2p : TileCentroid (S 2 true) - TileCentroid T1 =
                  d (BandVectors.1 (cfg.firstPredecessor 2)
                    (cfg.firstPredecessor 1)) := PrototileConstruction.hs2p q r g cfg T1 S hocc
              have transCent (V : ProtoTile) (z : GaussianInt) :
                  TileCentroid (TileTranslation V z) =
                    TileCentroid V + GaussianRealPoint z := PrototileConstruction.transCent V z
              have hcent' : ∀ i s,
                  TileCentroid (U i s) - p0 =
                    (if s = true then (1 : Real) else -1) •
                      d (BandVectors.1 (q' ((i + 2).succ))
                        (q' ((i + 1).succ))) := PrototileConstruction.hcent' q r g cfg T1 S
                            pointNeg pointI dIdent1 dIdent2 dIdent3 dIdent4 hs1m hs1p hs2m hs2p
                            transCent
              let c1 := TileCentroid T1
              let reCells : Finset Int := T1.cells.image (fun x => x.re)
              let imCells : Finset Int := T1.cells.image (fun x => x.im)
              have reNe : reCells.Nonempty := Finset.image_nonempty.mpr hT1ne
              have imNe : imCells.Nonempty := Finset.image_nonempty.mpr hT1ne
              have hcentral1 : CentrallyReflectedAt c1 T1 T1 :=
                BandPrototileCentralSymmetry (q' 1) T1 hT1
              have hboundRe : ∀ p ∈ TileRealization T1,
                  (↑(reCells.min' reNe) : Real) ≤ p.1 ∧
                    p.1 ≤ (↑(reCells.max' reNe) : Real) + 1 := PrototileConstruction.hboundRe
                        T1 reNe
              have reflect1 : ∀ p ∈ TileRealization T1,
                  (2 * c1.1 - p.1, 2 * c1.2 - p.2) ∈ TileRealization T1 :=
                      PrototileConstruction.reflect1 T1 hcentral1
              let mRe := reCells.min' reNe
              let MRe := reCells.max' reNe
              have minReCell : ∃ x ∈ T1.cells, x.re = mRe := PrototileConstruction.minReCell T1
                  reNe
              have maxReCell : ∃ x ∈ T1.cells, x.re = MRe := PrototileConstruction.maxReCell T1
                  reNe
              have centerRe : 2 * c1.1 = (mRe : Real) + MRe + 1 :=
                  PrototileConstruction.centerRe T1 reNe hboundRe reflect1 minReCell maxReCell
              have hboundIm : ∀ p ∈ TileRealization T1,
                  (↑(imCells.min' imNe) : Real) ≤ p.2 ∧
                    p.2 ≤ (↑(imCells.max' imNe) : Real) + 1 := PrototileConstruction.hboundIm
                        T1 imNe
              let mIm := imCells.min' imNe
              let MIm := imCells.max' imNe
              have minImCell : ∃ x ∈ T1.cells, x.im = mIm := PrototileConstruction.minImCell T1
                  imNe
              have maxImCell : ∃ x ∈ T1.cells, x.im = MIm := PrototileConstruction.maxImCell T1
                  imNe
              have centerIm : 2 * c1.2 = (mIm : Real) + MIm + 1 :=
                  PrototileConstruction.centerIm T1 imNe reflect1 hboundIm minImCell maxImCell
              let t1 : GaussianInt := ⟨mRe + MRe + 1, mIm + MIm + 1⟩
              have ht1 : GaussianRealPoint t1 = (2 * c1.1, 2 * c1.2) :=
                  PrototileConstruction.ht1 T1 reNe imNe centerRe centerIm
              have hrootCent : TileCentroid T0 = p0 := PrototileAssembly.hrootCent q r g T1
                  hT1ne S hparents hcells0 hcent' reNe imNe minReCell maxReCell minImCell
                  maxImCell ht1
              have hcent : ∀ i s,
                  TileCentroid (U i s) - TileCentroid T0 =
                    (if s = true then (1 : Real) else -1) •
                      ((1 / 2 : Real) •
                        (GaussianRealPoint
                            (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ))) -
                          (-((GaussianRealPoint
                              (BandVectors.1 (q' ((i + 2).succ))
                                (q' ((i + 1).succ)))).2),
                            (GaussianRealPoint
                              (BandVectors.1 (q' ((i + 2).succ))
                                (q' ((i + 1).succ)))).1))) := PrototileConstruction.hcent q r g
                                    T1 S hcent' hrootCent
              exact ⟨T0, BandPrototile.decompose hq' hparents hcells0 hfoot hcent⟩
        obtain ⟨inverse, hinvC, _, _, _, hinvT, _, _, _, _, _, _⟩ :=
          BandPackingSymmetryInversePhaseCancellation.2 g
        refine ⟨BandPackingSymmetryTileAction inverse normalized.choose, ?_⟩
        have hcov := (BandPackingSymmetryCovariance inverse).2.1
        have hresult := (hcov (q' 0) normalized.choose).mp normalized.choose_spec
        have hq0 : BandPackingSymmetryCircleAction inverse (q' 0) = C.1.1 :=
            PrototileConstruction.hq0 C q hroot r g inverse hinvC
        have hresult' : BandPrototile (C.1.1)
            (BandPackingSymmetryTileAction inverse normalized.choose) :=
                PrototileConstruction.hresult' C q r g normalized inverse hresult hq0
        exact hresult'

end PositivePrototileProof

theorem BandPrototileExists : ∀ C : BandGeneralCircle,
    ∃ T : ProtoTile, BandPrototile C.1 T := by
-- BODY
  classical
  have emptyCurv := PrototileConstruction.emptyCurv
  have positiveNonempty (C : CircleCoordinates) (T : ProtoTile)
      (hpos : 0 < C.1) (hT : BandPrototile C T) : T.cells.Nonempty :=
          PrototileConstruction.positiveNonempty emptyCurv C T hpos hT
  have existence : ∀ n : Nat, ∀ C : BandCircle,
      C.1.1.1.toNat = n → ∃ T : ProtoTile, BandPrototile C.1.1 T :=
          PositivePrototileProof.existence positiveNonempty
  intro C
  rcases C.2.1 with hpos | ⟨hz, hw⟩
  · let BC : BandCircle := ⟨C, hpos⟩
    obtain ⟨T, hT⟩ := existence BC.1.1.1.toNat BC (by rfl)
    exact ⟨T, hT⟩
  · rcases hw with hw | hw
    · have hcoord : C.1 = (0, 1) := Prod.ext hz hw
      refine ⟨⟨∅, 0⟩, ?_⟩
      rw [hcoord]
      exact BandPrototile.line 1 0 (Or.inl rfl)
    · have hcoord : C.1 = (0, -1) := Prod.ext hz hw
      refine ⟨⟨∅, 0⟩, ?_⟩
      rw [hcoord]
      exact BandPrototile.line (-1) 0 (Or.inr rfl)

end ApollonianSuperharmonic

end
