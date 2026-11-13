/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianRealPointProperties
public import LeanPool.ApollonianSuperharmonic.FordTileCellMembership
public import LeanPool.ApollonianSuperharmonic.ListEndpointFacts

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.OpposingStringInterfacePath
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain

-- [TABLET NODE: P4158T1SmallerStringEdges]

/-!
# P4158T1SmallerStringEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SmallerStringGeometry

private theorem hqone :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                (1 : ℤ) < Ci.1.1.1 →
                  i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                      i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁ →
                    ∀ (T : ProtoTile),
                      ∀ (T' : ProtoTile),
                        ∀ (u : GaussianInt),
                          T'.cells =
                              (TileTranslation (FordTile P.q)
                                (u +
                                if i = (0 : Fin (3 : ℕ)) then
                                (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt)
                              else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells →
                            (∀ (x : GaussianInt),
                                x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
                                ((x - u).re =
                                if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) ∧
                                (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ)
                              else (↑P.q₂ : ℤ)) ≤
                                (x - u).im ∧
                                (x - u).im ≤ (↑P.q : ℤ)) →
                              (P.q : Int) = P.q₁ + P.q₂ → 1 < P.q
    ) := by
  classical
  intro P Ci i hCi hlarge hsmall T T' u hc' hsegment hsum
  by_contra hn
  have he : P.q = 1 := by have := P.q_pos; omega
  have hunit := P.unit_case he
  rcases hsmall with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
  · simp only [FordRecursiveQuadruple, hunit.2.1, ↓reduceIte, Fin.isValue,
      Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hCi
    have := congrArg Prod.fst hCi
    omega
  · have hq2 : P.q₂ = 1 := hunit.2.2.2
    have := congrArg Prod.fst hCi
    simp [FordRecursiveQuadruple, FordCircleCoordinate, hq2] at this
    omega

private theorem hrpos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (P.q : Int) = P.q₁ + P.q₂ → 1 < P.q → 0 < P.q₁
    ) := by
  classical
  intro P hsum hqone
  by_contra hn
  have hz : P.q₁ = 0 := by omega
  have hd := P.det₁
  simp [hz] at hd
  have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
  have := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q : Int)) hdv
  omega

private theorem hC0pos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ)) = C0.1.1) → ((1 < P.q) → (0 < C0.1.1.1)) ) := by
  classical
  intro P C0 hC0 hqone
  rw [← hC0]
  simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      Fin.isValue, Matrix.cons_val_zero, mul_self_pos, ne_eq, Int.natCast_eq_zero]
  positivity

private theorem hCicurv :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter)
          (Ci : BandCircle) (i : Fin (3 : ℕ)),
          FordRecursiveQuadruple P i.succ =
              Ci.1.1 →
            i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨ i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁ →
              (0 : ℕ) < P.q₁ →
                let n := if i = (0 : Fin (3 : ℕ)) then P.q₁ else P.q₂;
                Ci.1.1.1 =
                  (↑n : ℤ) ^ (2 : ℕ)) := by
  classical
  intro P Ci i hCi hsmall hrpos n
  rw [← hCi]
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp [n, FordRecursiveQuadruple, FordCircleCoordinate, ne_of_gt hrpos, pow_two]
  · simp [n, FordRecursiveQuadruple, FordCircleCoordinate, pow_two]

private theorem hnlarge :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              (1 : ℤ) < Ci.1.1.1 →
                let n := if i = 0 then P.q₁ else P.q₂
                0 < n → Ci.1.1.1 = (n : Int) ^ 2 → 1 < n
    ) := by
  classical
  intro P Ci i hlarge n hnpos hCicurv
  rw [hCicurv] at hlarge
  by_contra hn
  have : n = 1 := by omega
  simp [this] at hlarge

private theorem determinantCoprime :
    (by
      classical
      exact
        ∀ (a : Int),
          ∀ (b : Nat),
            ∀ (d : Nat),
              ∀ (c : Int), a * (d : Int) - (b : Int) * c = 1 → Nat.Coprime b a.natAbs
    ) := by
  classical
  intro a b d c hd
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let g := Nat.gcd b a.natAbs
  have gb : g ∣ b := Nat.gcd_dvd_left _ _
  have ga : g ∣ a.natAbs := Nat.gcd_dvd_right _ _
  have gb' : (g : Int) ∣ (b : Int) := by exact_mod_cast gb
  have ga' : (g : Int) ∣ a := (Int.dvd_natAbs).mp (by exact_mod_cast ga)
  have gd := dvd_sub (dvd_mul_of_dvd_left ga' (d : Int))
    (dvd_mul_of_dvd_left gb' c)
  have gd1 : (g : Int) ∣ 1 := by simpa [hd] using gd
  have ge := Int.eq_one_of_dvd_one (by omega : 0 ≤ (g : Int)) gd1
  have gn : g = 1 := by exact_mod_cast ge
  simp [g, gn]

private theorem hFord :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              (FordRecursiveQuadruple P i.succ = Ci.1.1) →
                ((i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                    i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
                  ((0 < P.q₁) →
                    (((0 : ℕ) < P.q₂) →
                      (let n := if i = 0 then P.q₁ else P.q₂;
                      ((∀ (a : Int),
                          ∀ (b : Nat),
                            ∀ (d : Nat),
                              ∀ (c : Int),
                                (a * (d : Int) - (b : Int) * c = 1) →
                                  (Nat.Coprime b a.natAbs)) →
                        (BandPrototile Ci.1.1 (FordTile n)))))))) := by
  classical
  intro P Ci i hCi hsmall hrpos hspos n determinantCoprime
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · obtain ⟨Q, ⟨hpQ, hqQ⟩, _⟩ := FordFareyParentsExist P.p₁ P.q₁ hrpos
      (determinantCoprime P.p₁ P.q₁ P.q P.p P.det₁)
    have hF := (FordTileRecursiveIdentification Q).1
    rw [hpQ, hqQ] at hF
    simpa [n, ← hCi, FordRecursiveQuadruple, ne_of_gt hrpos] using hF
  · have hd : (-P.p₂) * (P.q : Int) - (P.q₂ : Int) * (-P.p) = 1 := by
      nlinarith [P.det₂]
    have hred : Nat.Coprime P.q₂ P.p₂.natAbs := by
      simpa using determinantCoprime (-P.p₂) P.q₂ P.q (-P.p) hd
    obtain ⟨Q, ⟨hpQ, hqQ⟩, _⟩ := FordFareyParentsExist P.p₂ P.q₂ hspos hred
    have hF := (FordTileRecursiveIdentification Q).1
    rw [hpQ, hqQ] at hF
    simpa [n, ← hCi, FordRecursiveQuadruple] using hF

private theorem fordcent :
    (by
      classical
      exact
        (∀ (m : Nat),
            ∀ (z : GaussianInt),
              z ∈ (FordTile m).cells ↔ 0 ≤ z.re ∧ z.re < m ∧ 0 ≤ z.im ∧ z.im < m) →
          (∀ (m : Nat), 0 < m → (FordTile m).cells.Nonempty) →
            ∀ (m : Nat),
              0 < m → TileCentroid (FordTile m) = ((m : Real) / 2, (m : Real) / 2)
    ) := by
  classical
  intro fordcell fordne m hm
  let R := TileTranslation (TileQuarterTurn (FordTile m)) ⟨m, 0⟩
  have hcR : R.cells = (FordTile m).cells := by
    ext z
    change z ∈ ((FordTile m).cells.image (fun x => GaussianQuarterTurn x - 1)).image
      (GaussianTranslation ⟨m, 0⟩) ↔ _
    rw [Finset.image_image, fordcell]
    constructor
    · rintro hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, hz⟩
      have hx := (fordcell m x).mp hx
      have hr := congrArg Zsqrtd.re hz
      have hi := congrArg Zsqrtd.im hz
      dsimp [GaussianTranslation, GaussianQuarterTurn, Function.comp_def] at hr hi
      omega
    · intro hz
      refine Finset.mem_image.mpr ⟨⟨z.im, (m : Int) - 1 - z.re⟩,
        (fordcell m _).mpr ?_, ?_⟩
      · dsimp; omega
      · ext <;> simp [GaussianTranslation, GaussianQuarterTurn]; omega
  have he : TileCentroid R = TileCentroid (FordTile m) :=
    (ProtoTileObservableExtensionality R (FordTile m) hcR
      (by intro he; rw [hcR] at he; exact ((fordne m hm).ne_empty he).elim)).2.2.2.2
  rw [(TileTranslationFormulas _ _).2.2.2.2.1,
    (TileQuarterTurnFormulas _).2.2.2.2.1] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  apply Prod.ext <;> norm_num at h1 h2 ⊢ <;> linarith

private theorem transne :
    (by
      classical
      exact
        (∀ (m : Nat), (0 < m) → ((FordTile m).cells.Nonempty)) → (∀ (m : Nat), (0 < m) → (∀ (v :
            GaussianInt), (TileTranslation (FordTile m) v).cells.Nonempty)) ) := by
  classical
  intro fordne m hm v
  exact (fordne m hm).image _

private theorem cellobs :
    (by
      classical
      exact
        (∀ (m : Nat), (0 < m) → (∀ (v : GaussianInt), (TileTranslation (FordTile m)
            v).cells.Nonempty)) → (∀ (A : ProtoTile), ∀ (m : Nat), (0 < m) → (∀ (v :
            GaussianInt), (A.cells = (TileTranslation (FordTile m) v).cells) → (FootprintVertices
            A = FootprintVertices (TileTranslation (FordTile m) v) ∧ TileCentroid A =
            TileCentroid (TileTranslation (FordTile m) v)))) ) := by
  classical
  intro transne A m hm v he
  have ha : A.cells = ∅ → A.anchor = (TileTranslation (FordTile m) v).anchor := by
    intro hempty
    exact ((transne m hm v).ne_empty (he.symm.trans hempty)).elim
  exact ⟨(ProtoTileObservableExtensionality _ _ he ha).1,
    (ProtoTileObservableExtensionality _ _ he ha).2.2.2.2⟩

private theorem hcentT :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → ((∀ (m : Nat), (0 < m) → (TileCentroid
            (FordTile m) = ((m : Real) / 2, (m : Real) / 2))) → ((∀ (A : ProtoTile), ∀ (m : Nat),
            (0 < m) → (∀ (v : GaussianInt), (A.cells = (TileTranslation (FordTile m) v).cells) →
            (FootprintVertices A = FootprintVertices (TileTranslation (FordTile m) v) ∧
            TileCentroid A = TileCentroid (TileTranslation (FordTile m) v)))) → (TileCentroid T =
            ((P.q : Real) / 2 + u.re, (P.q : Real) / 2 + u.im)))) ) := by
  classical
  intro P T u hc fordcent cellobs
  rw [(cellobs T P.q P.q_pos u hc).2,
    (TileTranslationFormulas _ _).2.2.2.2.1, fordcent P.q P.q_pos]

private theorem hcmcand :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ((i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
              (∀ (T : ProtoTile),
                ∀ (u : GaussianInt),
                  (∀ (Rminus : ProtoTile),
                    (TileCentroid Rminus - TileCentroid T =
                        (1 / 2 : ℝ) •
                          GaussianRealPoint
                            (BandVectors.1 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) -
                              BandVectors.1
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ))) →
                      (let n := if i = 0 then P.q₁ else P.q₂;
                      (0 < n) →
                        ((∀ (m : Nat),
                            (0 < m) →
                              (TileCentroid (FordTile m) =
                                ((m : Real) / 2, (m : Real) / 2))) →
                          ((TileCentroid T =
                              ((P.q : Real) / 2 + u.re, (P.q : Real) / 2 + u.im)) →
                            (let vm : GaussianInt :=
                              u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩;
                            (BandVectors.1
                                  (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                  (FordRecursiveQuadruple P i.succ) =
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
                                  BandVectors.1 (FordRecursiveQuadruple P i.succ)
                                    (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))) →
                              ((ProperBandQuadruple (FordRecursiveQuadruple P) ∧
                                  BandVectors.1
                                        (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
                                        (FordRecursiveQuadruple P
                                          (0 : Fin (4 : ℕ))) =
                                      (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) ∧
                                    BandVectors.1
                                          (FordRecursiveQuadruple P
                                            (2 : Fin (4 : ℕ)))
                                          (FordRecursiveQuadruple P
                                            (0 : Fin (4 : ℕ))) =
                                        (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt) ∧
                                      BandVectors.1
                                            (FordRecursiveQuadruple P
                                              (3 : Fin (4 : ℕ)))
                                            (FordRecursiveQuadruple P
                                              (0 : Fin (4 : ℕ))) =
                                          (⟨(0 : ℤ), -(↑P.q : ℤ)⟩ : GaussianInt) ∧
                                        BandVectors.2
                                              (FordRecursiveQuadruple P
                                                (1 : Fin (4 : ℕ)))
                                              (FordRecursiveQuadruple P
                                                (0 : Fin (4 : ℕ))) =
                                            (⟨P.p₁, P.p⟩ : GaussianInt) ∧
                                          BandVectors.2
                                                (FordRecursiveQuadruple P
                                                  (2 : Fin (4 : ℕ)))
                                                (FordRecursiveQuadruple P
                                                  (0 : Fin (4 : ℕ))) =
                                              (⟨P.p₂, -P.p⟩ : GaussianInt) ∧
                                            BandVectors.2
                                                  (FordRecursiveQuadruple P
                                                    (3 : Fin (4 : ℕ)))
                                                  (FordRecursiveQuadruple P
                                                    (0 : Fin (4 : ℕ))) =
                                                (⟨-P.p, (0 : ℤ)⟩ : GaussianInt) ∧
                                              BandVectors.2
                                                    (FordRecursiveQuadruple P
                                                      (3 : Fin (4 : ℕ)))
                                                    (FordRecursiveQuadruple P
                                                      (2 : Fin (4 : ℕ))) =
                                                  (⟨-P.p₂, (0 : ℤ)⟩ : GaussianInt) ∧
                                                BandVectors.2
                                                    (FordRecursiveQuadruple P
                                                      (1 : Fin (4 : ℕ)))
                                                    (FordRecursiveQuadruple P
                                                      (3 : Fin (4 : ℕ))) =
                                                  (⟨(0 : ℤ), P.p₁⟩ : GaussianInt)) →
                                (TileCentroid Rminus =
                                  TileCentroid
                                    (TileTranslation (FordTile n) vm))))))))))) := by
  classical
  intro P i hsmall T u Rminus hcm n hnpos fordcent hcentT vm hflip hvecs
  rw [(TileTranslationFormulas _ _).2.2.2.2.1, fordcent n hnpos]
  rw [hflip] at hcm
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl] at hcm
    rw [hvecs.2.1, hcentT] at hcm
    have h1 := congrArg Prod.fst hcm
    have h2 := congrArg Prod.snd hcm
    dsimp [n, vm, GaussianRealPoint] at *
    push_cast at h1 h2 ⊢
    ext <;> dsimp <;> linarith
  · simp only [show (1 : Fin 3).succ = (2 : Fin 4) from rfl] at hcm
    rw [hvecs.2.2.1, hcentT] at hcm
    have h1 := congrArg Prod.fst hcm
    have h2 := congrArg Prod.snd hcm
    dsimp [n, vm, GaussianRealPoint] at *
    push_cast at h1 h2 ⊢
    ext <;> dsimp <;> linarith

private theorem hcpcand :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ((i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
              (∀ (T : ProtoTile),
                ∀ (u : GaussianInt),
                  (∀ (Rplus : ProtoTile),
                    ((TileCentroid Rplus - TileCentroid T =
                        (1 / 2 : ℝ) •
                          GaussianRealPoint
                            (BandVectors.1 (FordRecursiveQuadruple P i.succ)
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) +
                              BandVectors.1
                                (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                (FordRecursiveQuadruple P i.succ))) →
                      (let n := if i = 0 then P.q₁ else P.q₂;
                      (0 < n) →
                        ((∀ (m : Nat),
                            (0 < m) →
                              (TileCentroid (FordTile m) =
                                ((m : Real) / 2, (m : Real) / 2))) →
                          ((TileCentroid T =
                              ((P.q : Real) / 2 + u.re, (P.q : Real) / 2 + u.im)) →
                            (let vp : GaussianInt :=
                              u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩;
                            (BandVectors.1
                                  (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
                                  (FordRecursiveQuadruple P i.succ) =
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
                                  BandVectors.1 (FordRecursiveQuadruple P i.succ)
                                    (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))) →
                              ((ProperBandQuadruple (FordRecursiveQuadruple P) ∧
                                  BandVectors.1
                                        (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
                                        (FordRecursiveQuadruple P
                                          (0 : Fin (4 : ℕ))) =
                                      (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) ∧
                                    BandVectors.1
                                          (FordRecursiveQuadruple P
                                            (2 : Fin (4 : ℕ)))
                                          (FordRecursiveQuadruple P
                                            (0 : Fin (4 : ℕ))) =
                                        (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt) ∧
                                      BandVectors.1
                                            (FordRecursiveQuadruple P
                                              (3 : Fin (4 : ℕ)))
                                            (FordRecursiveQuadruple P
                                              (0 : Fin (4 : ℕ))) =
                                          (⟨(0 : ℤ), -(↑P.q : ℤ)⟩ : GaussianInt) ∧
                                        BandVectors.2
                                              (FordRecursiveQuadruple P
                                                (1 : Fin (4 : ℕ)))
                                              (FordRecursiveQuadruple P
                                                (0 : Fin (4 : ℕ))) =
                                            (⟨P.p₁, P.p⟩ : GaussianInt) ∧
                                          BandVectors.2
                                                (FordRecursiveQuadruple P
                                                  (2 : Fin (4 : ℕ)))
                                                (FordRecursiveQuadruple P
                                                  (0 : Fin (4 : ℕ))) =
                                              (⟨P.p₂, -P.p⟩ : GaussianInt) ∧
                                            BandVectors.2
                                                  (FordRecursiveQuadruple P
                                                    (3 : Fin (4 : ℕ)))
                                                  (FordRecursiveQuadruple P
                                                    (0 : Fin (4 : ℕ))) =
                                                (⟨-P.p, (0 : ℤ)⟩ : GaussianInt) ∧
                                              BandVectors.2
                                                    (FordRecursiveQuadruple P
                                                      (3 : Fin (4 : ℕ)))
                                                    (FordRecursiveQuadruple P
                                                      (2 : Fin (4 : ℕ))) =
                                                  (⟨-P.p₂, (0 : ℤ)⟩ : GaussianInt) ∧
                                                BandVectors.2
                                                    (FordRecursiveQuadruple P
                                                      (1 : Fin (4 : ℕ)))
                                                    (FordRecursiveQuadruple P
                                                      (3 : Fin (4 : ℕ))) =
                                                  (⟨(0 : ℤ), P.p₁⟩ : GaussianInt)) →
                                (TileCentroid Rplus =
                                  TileCentroid
                                    (TileTranslation (FordTile n) vp)))))))))))) := by
  classical
  intro P i hsmall T u Rplus hcp n hnpos fordcent hcentT vp hflip hvecs
  rw [(TileTranslationFormulas _ _).2.2.2.2.1, fordcent n hnpos]
  rw [hflip] at hcp
  have hsumR : (P.q : Real) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl] at hcp
    rw [hvecs.2.1, hcentT] at hcp
    have h1 := congrArg Prod.fst hcp
    have h2 := congrArg Prod.snd hcp
    dsimp [n, vp, GaussianRealPoint] at *
    push_cast at h1 h2 ⊢
    ext <;> dsimp <;> linarith
  · simp only [show (1 : Fin 3).succ = (2 : Fin 4) from rfl] at hcp
    rw [hvecs.2.2.1, hcentT] at hcp
    have h1 := congrArg Prod.fst hcp
    have h2 := congrArg Prod.snd hcp
    dsimp [n, vp, GaussianRealPoint] at *
    push_cast at h1 h2 ⊢
    ext <;> dsimp <;> linarith

private theorem hdelta :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin 3), ∀ (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀
            (Rplus : ProtoTile),
        let n := if i = 0 then P.q₁ else P.q₂
        let vm : GaussianInt := u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩
        let vp : GaussianInt := u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩
        (TileCentroid Rminus = TileCentroid (TileTranslation (FordTile n) vm)) → ((TileCentroid
            Rplus = TileCentroid (TileTranslation (FordTile n) vp)) → (TileCentroid Rplus -
            TileCentroid Rminus = GaussianRealPoint (vp - vm))) ) := by
  classical
  intro P i u Rminus Rplus n vm vp hcmcand hcpcand
  rw [hcmcand, hcpcand, (TileTranslationFormulas _ _).2.2.2.2.1,
    (TileTranslationFormulas _ _).2.2.2.2.1]
  ext <;> simp [GaussianRealPoint]

private theorem hnormdelta :
    (by
      classical
        exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ((i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁) →
              (∀ (u : GaussianInt),
                (((P.q : Int) = P.q₁ + P.q₂) →
                  (let n := if i = 0 then P.q₁ else P.q₂;
                  (let vm : GaussianInt := u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩;
                  let vp : GaussianInt :=
                    u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩;
                  (Zsqrtd.norm (vp - vm) = (P.q : Int) ^ 2 + (n : Int) ^ 2))))))) := by
  classical
  intro P i hsmall u hsum n vm vp
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · simp [vm, vp, n, Zsqrtd.norm_def]
    nlinarith [hsum]
  · simp [vm, vp, n, Zsqrtd.norm_def]
    ring

private abbrev pointinj := ApollonianSuperharmonic.GaussianRealPointProperties.injective

private theorem hRS :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (i : Fin 3), ((1 : ℤ) < Ci.1.1.1) → (∀
            (u : GaussianInt), ∀ (Rminus : ProtoTile), ∀ (Rplus : ProtoTile),
        let n := if i = 0 then P.q₁ else P.q₂
        (Ci.1.1.1 = (n : Int) ^ 2) → (
        let vm : GaussianInt := u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩
        let vp : GaussianInt := u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩
        (TileCentroid Rplus - TileCentroid Rminus = GaussianRealPoint (vp - vm)) → ((Zsqrtd.norm
            (vp - vm) = (P.q : Int) ^ 2 + (n : Int) ^ 2) → ((Function.Injective
            GaussianRealPoint) → (Rminus ≠ Rplus))))) ) := by
  classical
  intro P Ci i hlarge u Rminus Rplus n hCicurv vm vp hdelta hnormdelta pointinj he
  have he0 : GaussianRealPoint (vp - vm) = GaussianRealPoint 0 := by
    rw [← hdelta, he]
    simp [GaussianRealPoint]
    rfl
  have he0 := pointinj he0
  rw [he0] at hnormdelta
  simp only [Zsqrtd.norm_zero] at hnormdelta
  have : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
  nlinarith

private theorem hincoming :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), (0 < Ci.1.1.1) → (∀ (Q : Fin (4 : ℕ) → CircleCoordinates),
            (SemiProperQuadruple Q) → ((Q (0 : Fin (4 : ℕ)) = Ci.1.1) → ((ProperBandQuadruple Q)
            → (∀ (j : Fin 3), Zsqrtd.norm (BandVectors.1 (Q j.succ) (Q 0)) = (Q j.succ).1 +
            Ci.1.1.1)))) ) := by
  classical
  intro Ci hCipos Q hQsemi hQ0 hQproper j
  have hj : j.succ ≠ (0 : Fin 4) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  have hv := (VectorSquareProduct Q hQsemi j.succ 0 hj).1
  have ht := TangencyCoordinateIdentity Q hQsemi j.succ 0 hj
  have hs : Zsqrtd.norm (BandVectors.1 (Q j.succ) (Q 0)) ^ 2 =
      ((Q j.succ).1 + (Q 0).1) ^ 2 := by
    calc
      _ = Zsqrtd.norm (BandVectors.1 (Q j.succ) (Q 0) ^ 2) := by
        simpa only [pow_two] using (Zsqrtd.norm_mul
          (BandVectors.1 (Q j.succ) (Q 0))
          (BandVectors.1 (Q j.succ) (Q 0))).symm
      _ = _ := by rw [hv]; exact ht
  have hn := GaussianInt.norm_nonneg (BandVectors.1 (Q j.succ) (Q 0))
  have hjpos := (ProperBandCurvatureStructure Q hQproper).2.1 j
  rw [← hQ0] at hCipos ⊢
  nlinarith

private theorem hRmem :
    (by
      classical
      exact
        ∀ (Rminus : ProtoTile), ∀ (tiles : List ProtoTile), (tiles.head? = some Rminus) → (Rminus
            ∈ tiles) ) := by
  classical
  intro Rminus tiles hhead
  have hopt : Rminus ∈ tiles.head? := by simp [hhead]
  rw [List.eq_cons_of_mem_head? hopt]
  simp

private abbrev hSmem :=
  @ListEndpointFacts.lastMembership ProtoTile

private theorem hnotouch :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              ∀ (u : GaussianInt),
                ∀ (base : ProtoTile),
                  ∀ (Rminus : ProtoTile),
                    ∀ (Rplus : ProtoTile),
                      ∀ (tiles : List ProtoTile),
                        let n := if i = 0 then P.q₁ else P.q₂
                        n < P.q →
                          Ci.1.1.1 = (n : Int) ^ 2 →
                            1 < n →
                              let vm : GaussianInt :=
                                u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩
                              let vp : GaussianInt :=
                                u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩
                              TileCentroid Rplus - TileCentroid Rminus =
                                GaussianRealPoint (vp - vm) →
                                Zsqrtd.norm (vp - vm) = (P.q : Int) ^ 2 + (n : Int) ^ 2 →
                                Function.Injective GaussianRealPoint →
                                ∀ (Q : Fin (4 : ℕ) → CircleCoordinates),
                                Q (0 : Fin (4 : ℕ)) = Ci.1.1 →
                                (∀ (j : Fin (3 : ℕ)), (Q j.succ).1 < Ci.1.1.1) →
                                ProperBandQuadruple Q →
                                (∀ (j : Fin 3),
                                Zsqrtd.norm (BandVectors.1 (Q j.succ) (Q 0)) =
                                (Q j.succ).1 + Ci.1.1.1) →
                                BandPrototile Ci.1.1 base →
                                (∀ T ∈ tiles,
                                T ∈ RegularTileFamily base (TilingLattice Ci)) →
                                Rminus ∈ tiles →
                                Rplus ∈ tiles → ¬TileTouching Rminus Rplus
    ) := by
  classical
  intro P Ci i u base Rminus Rplus tiles n hnq hCicurv hnlarge vm vp hdelta hnormdelta pointinj
      Q hQ0 hQless hQproper hincoming hbase hfamily hRmem hSmem htouch
  have hbaseQ : BandPrototile (Q 0) base := by simpa [hQ0] using hbase
  obtain ⟨j, hj⟩ := (BandRegularTileTouchingClassification Ci Q hQproper hQ0
    base hbaseQ Rminus Rplus (hfamily _ hRmem) (hfamily _ hSmem)).mp htouch
  have hnorm : Zsqrtd.norm (vp - vm) =
      Zsqrtd.norm (BandVectors.1 (Q j.succ) (Q 0)) := by
    rcases hj with hj | hj
    · rw [hdelta] at hj
      rw [pointinj hj]
    · have hj' : GaussianRealPoint (vp - vm) =
          GaussianRealPoint (-BandVectors.1 (Q j.succ) (Q 0)) := by
        rw [← hdelta, hj]
        ext <;> simp [GaussianRealPoint]
      rw [pointinj hj', Zsqrtd.norm_neg]
  rw [hnormdelta, hincoming] at hnorm
  have hless := hQless j
  rw [hCicurv] at hnorm hless
  have hnqZ : (n : Int) < P.q := by exact_mod_cast hnq
  have hnZ : 0 ≤ (n : Int) := by omega
  nlinarith

private theorem hnadj :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ((1 : ℤ) < Ci.1.1.1) → (∀ (orientation : Bool), ∀ (Rminus :
            ProtoTile), ∀ (Rplus : ProtoTile), (¬ TileTouching Rminus Rplus) → (¬ (if Ci.1.1.1 =
            1 then ∃ v : GaussianInt, UnitTriangularStep orientation v ∧ TileCentroid Rplus -
            TileCentroid Rminus = GaussianRealPoint v else TileTouching Rminus Rplus))) ) := by
  classical
  intro Ci hlarge orientation Rminus Rplus hnotouch
  simpa [ne_of_gt hlarge] using hnotouch

private theorem ancestorFoot :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), (0 < C0.1.1.1) → (∀ (A : ProtoTile), ∀ (root :
            ProtoTile), ∀ (g : PartialOdometer), ∀ (f : PartialOdometer), (AncestorOdometer
            Ci.1.1 C0.1.1 A root g f) → (FootprintVertices A ⊆ FootprintVertices root)) ) := by
  classical
  intro C0 Ci hC0pos A root g f ha x hx
  rw [← PositiveCurvatureTileOdometerDomain C0.1.1 root f hC0pos ha.1]
  apply ha.2.2.2.1
  change x ∈ (g.domain : Set GaussianInt)
  rw [ha.2.2.1]
  exact hx

private theorem hwroot :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (h' : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀ (reverseHs : List
            PartialOdometer), (∀ U ∈ (List.drop (1 : ℕ) tiles).dropLast, ∃ (g : PartialOdometer),
            (U, g) ∈ tiles.zip hs ∧ AncestorOdometer Ci.1.1 C0.1.1 U T g h) → ((∀ V ∈ (List.drop
            (1 : ℕ) reverseTiles).dropLast, ∃ (k : PartialOdometer), (V, k) ∈ reverseTiles.zip
            reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 V T' k h') → (∀ (walk : List GaussianInt),
            (∀ x ∈ walk, (∃ a ∈ (List.drop (1 : ℕ) tiles).dropLast, x ∈ FootprintVertices a) ∧ ∃
            b ∈ (List.drop (1 : ℕ) reverseTiles).dropLast, x ∈ FootprintVertices b) → ((∀ (A :
            ProtoTile), ∀ (root : ProtoTile), ∀ (g : PartialOdometer), ∀ (f : PartialOdometer),
            (AncestorOdometer Ci.1.1 C0.1.1 A root g f) → (FootprintVertices A ⊆
            FootprintVertices root)) → (∀ (x : GaussianInt), (x ∈ walk) → (x ∈ FootprintVertices
            T ∩ FootprintVertices T'))))) ) := by
  classical
  intro C0 Ci T T' h h' tiles reverseTiles hs reverseHs hanc hanc' walk hwvertices ancestorFoot x hx
  obtain ⟨⟨A, hA, hxA⟩, ⟨B, hB, hxB⟩⟩ := hwvertices x hx
  obtain ⟨g, _, hg⟩ := hanc A hA
  obtain ⟨k, _, hk⟩ := hanc' B hB
  exact ⟨ancestorFoot A T g h hg hxA, ancestorFoot B T' k h' hk hxB⟩

private theorem hwsegment :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin 3), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (u :
            GaussianInt), (∀ (x : GaussianInt), x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
            ((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) ∧ (if i = (0 :
            Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ (x - u).im ∧ (x - u).im ≤ (↑P.q :
            ℤ)) → (
        let n := if i = 0 then P.q₁ else P.q₂
        ∀ (walk : List GaussianInt), (∀ (x : GaussianInt), (x ∈ walk) → (x ∈ FootprintVertices T
            ∩ FootprintVertices T')) → (∀ (x : GaussianInt), (x ∈ walk) → ((x - u).re = (if i = 0
            then (P.q : Int) else 0) ∧ (n : Int) ≤ (x - u).im ∧ (x - u).im ≤ P.q))) ) := by
  classical
  intro P i T T' u hsegment n walk hwroot x hx
  simpa only [n, Nat.cast_ite] using (hsegment x).mp (hwroot x hx)

private theorem squarefoot :
    (by
      classical
      exact
        ∀ (m : Nat), (0 < m) → (∀ (v : GaussianInt), ∀ (x : GaussianInt), x ∈ FootprintVertices
            (TileTranslation (FordTile m) v) ↔ 0 ≤ (x - v).re ∧ (x - v).re ≤ m ∧ 0 ≤ (x - v).im ∧
            (x - v).im ≤ m) ) := by
  classical
  intro m hm v x
  rw [(TileTranslationFormulas _ _).2.2.2.2.2.1,
    (P4062T1CanonicalSupport m hm).1]
  simp only [Set.mem_image, FordVertexDomain, Set.mem_ofPred_eq, GaussianTranslation]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - v, hx, sub_add_cancel x v⟩

private theorem hminusheight :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                    i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁ →
                  ∀ (T : ProtoTile),
                    ∀ (T' : ProtoTile),
                      ∀ (u : GaussianInt),
                        T'.cells =
                            (TileTranslation (FordTile P.q)
                                (u +
                                if i = (0 : Fin (3 : ℕ)) then
                                (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt)
                              else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells →
                          (∀ (x : GaussianInt),
                              x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
                                ((x - u).re =
                                if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) ∧
                                (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ)
                              else (↑P.q₂ : ℤ)) ≤
                                (x - u).im ∧
                                (x - u).im ≤ (↑P.q : ℤ)) →
                            ∀ (Rminus : ProtoTile),
                              ∀ (Rplus : ProtoTile),
                                (P.q : Int) = P.q₁ + P.q₂ →
                                let n := if i = 0 then P.q₁ else P.q₂;
                              0 < n →
                                n < P.q →
                                Ci.1.1.1 = (n : Int) ^ 2 →
                                1 < n →
                                BandPrototile Ci.1.1 (FordTile n) →
                                (∀ (A : ProtoTile),
                                ∀ (m : Nat),
                                0 < m →
                                ∀ (v : GaussianInt),
                                A.cells = (TileTranslation (FordTile m) v).cells →
                                FootprintVertices A =
                                FootprintVertices (TileTranslation (FordTile m) v) ∧
                                TileCentroid A =
                                TileCentroid (TileTranslation (FordTile m) v)) →
                                let vm : GaussianInt :=
                                u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩;
                              let vp : GaussianInt :=
                                u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩;
                              TileCentroid Rminus =
                                TileCentroid (TileTranslation (FordTile n) vm) →
                                TileCentroid Rplus =
                                TileCentroid (TileTranslation (FordTile n) vp) →
                                Rminus.cells = (TileTranslation (FordTile n) vm).cells →
                                Rplus.cells = (TileTranslation (FordTile n) vp).cells →
                                TileCentroid Rplus - TileCentroid Rminus =
                                GaussianRealPoint (vp - vm) →
                                Zsqrtd.norm (vp - vm) = (P.q : Int) ^ 2 + (n : Int) ^ 2 →
                                ∀ (walk : List GaussianInt),
                                (∀ (x : GaussianInt),
                                x ∈ walk →
                                ((x - u).re = if i = 0 then (P.q : Int) else 0) ∧
                                (n : Int) ≤ (x - u).im ∧ (x - u).im ≤ P.q) →
                                (∀ (m : Nat),
                                0 < m →
                                ∀ (v : GaussianInt),
                                ∀ (x : GaussianInt),
                                x ∈ FootprintVertices (TileTranslation (FordTile m) v) ↔
                                0 ≤ (x - v).re ∧
                                (x - v).re ≤ m ∧ 0 ≤ (x - v).im ∧ (x - v).im ≤ m) →
                                ∀ (x : GaussianInt),
                                x ∈ walk →
                                x ∈ FootprintVertices Rminus →
                                (x - u).im = if i = 0 then (n : Int) else P.q
    ) := by
  classical
  intro P Ci i hCi hsmall T T' u hc' hsegment Rminus Rplus hsum n hnpos hnq hCicurv hnlarge
      hFord cellobs vm vp hcmcand hcpcand heqm heqp hdelta hnormdelta walk hwsegment squarefoot
      x hx hxm
  rw [(cellobs Rminus n hnpos vm heqm).1] at hxm
  have hxbox := (squarefoot n hnpos vm x).mp hxm
  have hxseg := hwsegment x hx
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  all_goals simp [n, vm] at hxbox hxseg ⊢; omega

private theorem hplusheight :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                i = (0 : Fin (3 : ℕ)) ∧ P.q₁ < P.q₂ ∨
                    i = (1 : Fin (3 : ℕ)) ∧ P.q₂ < P.q₁ →
                  ∀ (T : ProtoTile),
                    ∀ (T' : ProtoTile),
                      ∀ (u : GaussianInt),
                        T'.cells =
                            (TileTranslation (FordTile P.q)
                                (u +
                                if i = (0 : Fin (3 : ℕ)) then
                                (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt)
                              else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells →
                          (∀ (x : GaussianInt),
                              x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
                                ((x - u).re =
                                if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) ∧
                                (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ)
                              else (↑P.q₂ : ℤ)) ≤
                                (x - u).im ∧
                                (x - u).im ≤ (↑P.q : ℤ)) →
                            ∀ (Rminus : ProtoTile),
                              ∀ (Rplus : ProtoTile),
                                (P.q : Int) = P.q₁ + P.q₂ →
                                let n := if i = 0 then P.q₁ else P.q₂;
                              0 < n →
                                n < P.q →
                                Ci.1.1.1 = (n : Int) ^ 2 →
                                1 < n →
                                BandPrototile Ci.1.1 (FordTile n) →
                                (∀ (A : ProtoTile),
                                ∀ (m : Nat),
                                0 < m →
                                ∀ (v : GaussianInt),
                                A.cells = (TileTranslation (FordTile m) v).cells →
                                FootprintVertices A =
                                FootprintVertices (TileTranslation (FordTile m) v) ∧
                                TileCentroid A =
                                TileCentroid (TileTranslation (FordTile m) v)) →
                                let vm : GaussianInt :=
                                u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩;
                              let vp : GaussianInt :=
                                u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩;
                              TileCentroid Rminus =
                                TileCentroid (TileTranslation (FordTile n) vm) →
                                TileCentroid Rplus =
                                TileCentroid (TileTranslation (FordTile n) vp) →
                                Rminus.cells = (TileTranslation (FordTile n) vm).cells →
                                Rplus.cells = (TileTranslation (FordTile n) vp).cells →
                                TileCentroid Rplus - TileCentroid Rminus =
                                GaussianRealPoint (vp - vm) →
                                Zsqrtd.norm (vp - vm) = (P.q : Int) ^ 2 + (n : Int) ^ 2 →
                                ∀ (walk : List GaussianInt),
                                (∀ (x : GaussianInt),
                                x ∈ walk →
                                ((x - u).re = if i = 0 then (P.q : Int) else 0) ∧
                                (n : Int) ≤ (x - u).im ∧ (x - u).im ≤ P.q) →
                                (∀ (m : Nat),
                                0 < m →
                                ∀ (v : GaussianInt),
                                ∀ (x : GaussianInt),
                                x ∈ FootprintVertices (TileTranslation (FordTile m) v) ↔
                                0 ≤ (x - v).re ∧
                                (x - v).re ≤ m ∧ 0 ≤ (x - v).im ∧ (x - v).im ≤ m) →
                                (∀ (x : GaussianInt),
                                x ∈ walk →
                                x ∈ FootprintVertices Rminus →
                                (x - u).im = if i = 0 then (n : Int) else P.q) →
                                ∀ (x : GaussianInt),
                                x ∈ walk →
                                x ∈ FootprintVertices Rplus →
                                (x - u).im = if i = 0 then (P.q : Int) else n
    ) := by
  classical
  intro P Ci i hCi hsmall T T' u hc' hsegment Rminus Rplus hsum n hnpos hnq hCicurv hnlarge
      hFord cellobs vm vp hcmcand hcpcand heqm heqp hdelta hnormdelta walk hwsegment squarefoot
      hminusheight x hx hxp
  rw [(cellobs Rplus n hnpos vp heqp).1] at hxp
  have hxbox := (squarefoot n hnpos vp x).mp hxp
  have hxseg := hwsegment x hx
  rcases hsmall with ⟨rfl, _⟩ | ⟨rfl, _⟩
  all_goals simp [n, vp] at hxbox hxseg ⊢; omega

private theorem crossing :
    (by
      classical
      exact
        ∀ (test : GaussianInt → Prop), ∀ (p : List GaussianInt), (∃ a, p.head? = some a ∧ test a)
            → (∃ b, p.getLast? = some b ∧ ¬ test b) → ∃ x y : GaussianInt, ∃ l₁ l₂ : List
            GaussianInt, p = l₁ ++ x :: y :: l₂ ∧ test x ∧ ¬ test y ) := by
  classical
  intro test p
  induction p with
  | nil => simp
  | cons x xs ih =>
    rintro ⟨a, ha, hta⟩ hlast
    have hxa : x = a := Option.some.inj ha
    subst a
    cases xs with
    | nil =>
      obtain ⟨b, hb, htb⟩ := hlast
      have hxb : x = b := Option.some.inj hb
      exact (htb (hxb ▸ hta)).elim
    | cons y ys =>
      by_cases hy : test y
      · obtain ⟨a, b, l₁, l₂, he, hta', htb⟩ :=
          ih ⟨y, rfl, hy⟩ (by simpa using hlast)
        refine ⟨a, b, x :: l₁, l₂, ?_, hta', htb⟩
        simp only [List.cons_append, he]
      · exact ⟨x, y, [], ys, rfl, hta, hy⟩

private theorem stepPair :
    (by
      classical
      exact
        ∀ (u : GaussianInt),
          ∀ (x : GaussianInt),
            ∀ (y : GaussianInt),
              ∀ (z : GaussianInt),
                (x - u).re = (z - u).re →
                  (y - u).re = (z - u).re →
                    y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                      (x - u).im ≤ (z - u).im ∧ (z - u).im < (y - u).im ∨
                          (y - u).im ≤ (z - u).im ∧ (z - u).im < (x - u).im →
                        ({ x, y } : Finset GaussianInt) = {z, z + ⟨0, 1⟩}
    ) := by
  classical
  intro u x y z hx hy hstep hcross
  simp only [Zsqrtd.re_sub] at hx hy
  have hunit : y.im = x.im + 1 ∨ y.im = x.im - 1 := by
    rcases hstep with he | he | he | he
    · have hh := congrArg Zsqrtd.re he
      simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hh
      omega
    · have hh := congrArg Zsqrtd.re he
      simp only [Zsqrtd.re_sub, Zsqrtd.re_one] at hh
      omega
    · left
      have hh := congrArg Zsqrtd.im he
      simpa using hh
    · right
      have hh := congrArg Zsqrtd.im he
      simpa using hh
  simp only [Zsqrtd.im_sub] at hcross
  rcases hcross with hc | hc
  · have hxz : x = z := by ext <;> omega
    have hyz : y = z + ⟨0, 1⟩ := by ext <;> simp only [Zsqrtd.re_add,
      Zsqrtd.im_add] <;> omega
    rw [hxz, hyz]
  · have hyz : y = z := by ext <;> omega
    have hxz : x = z + ⟨0, 1⟩ := by ext <;> simp only [Zsqrtd.re_add,
      Zsqrtd.im_add] <;> omega
    rw [hxz, hyz, Finset.pair_comm]

private theorem hta :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (
        (∀ (i : Fin 3), ∀ (u :
            GaussianInt), ((P.q : Int) = P.q₁ + P.q₂) → (
        let n := if i = 0 then P.q₁ else P.q₂;
        ∀ (z : GaussianInt), ((z - u).im < (↑P.q : ℤ)) → (((n : Int) ≤ (z - u).im) → (∀ (a :
            GaussianInt),
        (((a - u).im = if i = (0 : Fin (3 : ℕ)) then (↑n : ℤ)
            else (↑P.q : ℤ)) → (
        let test := fun x : GaussianInt =>
          if i = 0 then (x - u).im ≤ (z - u).im else (z - u).im < (x - u).im;
        test a))))))) ) := by
  classical
  intro P i u hsum n z hzhi hzlo' a haheight test
  by_cases hi : i = 0
  · simp only [test, ite_eq_left hi] at *
    omega
  · simp only [test, ite_eq_right hi] at *
    omega

private theorem htb :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (
        (∀ (i : Fin 3), ∀ (u :
            GaussianInt), ((P.q : Int) = P.q₁ + P.q₂) → (
        let n := if i = 0 then P.q₁ else P.q₂;
        ∀ (z : GaussianInt), ((z - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ))
            → (((z - u).im < (↑P.q : ℤ)) → (((n : Int) ≤ (z - u).im) → (
        (∀ (b :
            GaussianInt), ((b - u).im = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (↑n : ℤ)) → (
        let test := fun x : GaussianInt =>
          if i = 0 then (x - u).im ≤ (z - u).im else (z - u).im < (x - u).im;
        ¬ test b)))))))) ) := by
  classical
  intro P i u hsum n z hzre hzhi hzlo' b hbheight test
  by_cases hi : i = 0
  · simp only [test, ite_eq_left hi] at *
    omega
  · simp only [test, ite_eq_right hi] at *
    omega

private theorem hcross :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (u : GaussianInt), ∀ (z : GaussianInt),
        let test := fun x : GaussianInt =>
          if i = 0 then (x - u).im ≤ (z - u).im else (z - u).im < (x - u).im
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), (test x) → ((¬test y) → (((x - u).im ≤ (z -
            u).im ∧ (z - u).im < (y - u).im) ∨ ((y - u).im ≤ (z - u).im ∧ (z - u).im < (x -
            u).im))) ) := by
  classical
  intro i u z test x y htx hty
  by_cases hi : i = 0
  · left
    simpa only [test, ite_eq_left hi, not_le] using And.intro htx hty
  · right
    simp only [test, ite_eq_right hi, not_lt] at htx hty
    exact ⟨hty, htx⟩

end SmallerStringGeometry

theorem P4158T1SmallerStringEdges
    (P : FordFareyParameter) (hq : ProperBandQuadruple (FordRecursiveQuadruple P))
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : FordRecursiveQuadruple P 0 = C0.1.1)
    (hCi : FordRecursiveQuadruple P i.succ = Ci.1.1)
    (hlarge : 1 < Ci.1.1.1)
    (hsmall : (i = 0 ∧ P.q₁ < P.q₂) ∨ (i = 1 ∧ P.q₂ < P.q₁))
    (T T' : ProtoTile) (h h' : PartialOdometer) (u : GaussianInt)
    (hc : T.cells = (TileTranslation (FordTile P.q) u).cells)
    (hc' : T'.cells = (TileTranslation (FordTile P.q)
      (u + if i = 0 then ⟨P.q, P.q₁⟩ else ⟨-(P.q : Int), P.q₂⟩)).cells)
    (hsegment : ∀ x, x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
      (x - u).re = (if i = 0 then (P.q : Int) else 0) ∧
      (if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (x - u).im ∧
      (x - u).im ≤ (P.q : Int))
    (orientation : Bool) (base Rminus Rplus : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : OdometerStringRespect Ci orientation base Rminus Rplus tiles hs)
    (hr : OdometerStringRespect Ci orientation base Rplus Rminus reverseTiles reverseHs)
    (hminus hplus : PartialOdometer)
    (hOm : TileOdometer Ci.1.1 Rminus hminus)
    (hOp : TileOdometer Ci.1.1 Rplus hplus)
    (hcm : TileCentroid Rminus - TileCentroid T = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0) - BandVectors.1 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)))
    (hcp : TileCentroid Rplus - TileCentroid T = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0) + BandVectors.1 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)))
    (hanc : ∀ U, U ∈ (tiles.drop 1).dropLast → ∃ g, (U, g) ∈ tiles.zip hs ∧
      AncestorOdometer Ci.1.1 C0.1.1 U T g h)
    (hanc' : ∀ V, V ∈ (reverseTiles.drop 1).dropLast → ∃ k,
      (V, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 V T' k h') :
    Rminus.cells = (TileTranslation (FordTile (if i = 0 then P.q₁ else P.q₂))
      (u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩)).cells ∧
    Rplus.cells = (TileTranslation (FordTile (if i = 0 then P.q₁ else P.q₂))
      (u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩)).cells ∧
    ∀ z : GaussianInt,
      (z - u).re = (if i = 0 then (P.q : Int) else 0) →
      (if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (z - u).im →
      (z - u).im < (P.q : Int) →
      ∃ (U V : ProtoTile) (g k : PartialOdometer),
        U ∈ (tiles.drop 1).dropLast ∧ V ∈ (reverseTiles.drop 1).dropLast ∧
        (U, g) ∈ tiles.zip hs ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧
        AncestorOdometer Ci.1.1 C0.1.1 U T g h ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges U ∧
        {z, z + ⟨0, 1⟩} ∈ FootprintEdges V := by
-- BODY
  classical
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have hqone := SmallerStringGeometry.hqone P Ci i hCi hlarge hsmall T T' u hc' hsegment hsum
  have hrpos := SmallerStringGeometry.hrpos P hsum hqone
  have hspos := P.q₂_pos
  let n := if i = 0 then P.q₁ else P.q₂
  have hnpos : 0 < n := by dsimp [n]; split_ifs <;> assumption
  have hnq : n < P.q := by dsimp [n]; split_ifs <;> omega
  have hCipos : 0 < Ci.1.1.1 := by omega
  have hC0pos := SmallerStringGeometry.hC0pos P C0 hC0 hqone
  have hCicurv := SmallerStringGeometry.hCicurv P Ci i hCi hsmall hrpos
  have hnlarge := SmallerStringGeometry.hnlarge P Ci i hlarge hnpos hCicurv
  have hFord := SmallerStringGeometry.hFord P Ci i hCi hsmall hrpos (P.q₂_pos)
      (SmallerStringGeometry.determinantCoprime)
  have fordcell (m : Nat) (z : GaussianInt) :
      z ∈ (FordTile m).cells ↔
        0 ≤ z.re ∧ z.re < m ∧ 0 ≤ z.im ∧ z.im < m := FordTileCellMembership m z
  have fordne (m : Nat) (hm : 0 < m) : (FordTile m).cells.Nonempty :=
    ⟨0, (fordcell m 0).mpr (by simp; omega)⟩
  have fordcent := SmallerStringGeometry.fordcent fordcell fordne
  have cellobs := SmallerStringGeometry.cellobs (SmallerStringGeometry.transne fordne)
  have hcentT := SmallerStringGeometry.hcentT P T u hc fordcent cellobs
  let vm : GaussianInt := u + if i = 0 then ⟨P.q, 0⟩ else ⟨0, P.q⟩
  let vp : GaussianInt := u + if i = 0 then ⟨P.q₂, P.q⟩ else ⟨-(P.q₂ : Int), 0⟩
  have hflip := ((VectorRecursionLaws (FordRecursiveQuadruple P) hq.1).2.2.2.2 hq i).1
  have hvecs := (FordCoordinateConfiguration P).2 hqone
  have hcmcand := SmallerStringGeometry.hcmcand P i hsmall T u Rminus hcm hnpos fordcent hcentT
      hflip hvecs
  have hcpcand := SmallerStringGeometry.hcpcand P i hsmall T u
      Rplus hcp hnpos fordcent hcentT hflip hvecs
  have heqm := (BandPrototileCentroidUnique Ci.1.1 Rminus _
    (TileOdometerBandPrototile _ _ _ hOm)
    (BandPrototileTranslation _ _ vm hFord) hcmcand).1
  have heqp := (BandPrototileCentroidUnique Ci.1.1 Rplus _
    (TileOdometerBandPrototile _ _ _ hOp)
    (BandPrototileTranslation _ _ vp hFord) hcpcand).1
  have hdelta := SmallerStringGeometry.hdelta P i u Rminus Rplus hcmcand hcpcand
  have hnormdelta := SmallerStringGeometry.hnormdelta P i hsmall u hsum
  have pointinj := SmallerStringGeometry.pointinj
  have hRS := SmallerStringGeometry.hRS P Ci i hlarge u Rminus Rplus hCicurv hdelta hnormdelta
      pointinj
  obtain ⟨Q, hQsemi, hQ0, hQless, _⟩ :
      ∃ Q : Fin 4 → CircleCoordinates, SemiProperQuadruple Q ∧ Q 0 = Ci.1.1 ∧
        (∀ j : Fin 3, (Q j.succ).1 < Ci.1.1.1) ∧
        ∀ Q' : Fin 4 → CircleCoordinates, SemiProperQuadruple Q' → Q' 0 = Ci.1.1 →
          (∀ j : Fin 3, (Q' j.succ).1 < Ci.1.1.1) →
          ∀ D : CircleCoordinates, (∃ j : Fin 3, Q j.succ = D) ↔
            ∃ j : Fin 3, Q' j.succ = D := by
    rcases BandGenealogy Ci with hu | hQ
    · omega
    · exact hQ
  have hQproper : ProperBandQuadruple Q := ⟨hQsemi, by simpa [hQ0] using hQless⟩
  have hincoming := SmallerStringGeometry.hincoming Ci hCipos Q hQsemi hQ0 hQproper
  have hft : TileString Ci orientation base Rminus Rplus tiles := hf.1
  obtain ⟨hbase, hhead, hlast, _, hfamily, _, _⟩ := hft
  have hnadj := SmallerStringGeometry.hnadj Ci hlarge orientation Rminus Rplus
      (SmallerStringGeometry.hnotouch P Ci i u base Rminus Rplus tiles hnq hCicurv hnlarge
      hdelta hnormdelta pointinj Q hQ0 hQless hQproper hincoming hbase hfamily
      (SmallerStringGeometry.hRmem Rminus tiles hhead) (SmallerStringGeometry.hSmem Rplus tiles
      hlast))
  obtain ⟨walk, hwhead, hwlast, hwchain, hwvertices, hwedges⟩ :=
    OpposingStringInterfacePath Ci orientation base Rminus Rplus hRS hnadj
      tiles reverseTiles hf.1 hr.1
  have hwsegment := SmallerStringGeometry.hwsegment P i T T' u hsegment walk
      (SmallerStringGeometry.hwroot C0 Ci T T' h h' tiles reverseTiles hs reverseHs hanc hanc'
      walk hwvertices (SmallerStringGeometry.ancestorFoot C0 Ci hC0pos))
  have squarefoot := SmallerStringGeometry.squarefoot
  have hminusheight := SmallerStringGeometry.hminusheight P Ci i hCi hsmall T T' u hc'
      hsegment Rminus Rplus hsum hnpos hnq hCicurv hnlarge hFord cellobs hcmcand
      hcpcand heqm heqp hdelta hnormdelta walk hwsegment squarefoot
  have hplusheight := SmallerStringGeometry.hplusheight P Ci i hCi hsmall T T' u hc' hsegment
      Rminus Rplus hsum hnpos hnq hCicurv hnlarge hFord cellobs hcmcand hcpcand
      heqm heqp hdelta hnormdelta walk hwsegment squarefoot hminusheight
  have crossing := SmallerStringGeometry.crossing
  have stepPair := SmallerStringGeometry.stepPair u
  refine ⟨heqm, heqp, ?_⟩
  intro z hzre hzlo hzhi
  have hzlo' : (n : Int) ≤ (z - u).im := by
    simpa only [n, Nat.cast_ite] using hzlo
  obtain ⟨a, ha, ham⟩ := hwhead
  obtain ⟨b, hb, hbp⟩ := hwlast
  have haheight := hminusheight a (List.mem_of_mem_head? (by simp [ha])) ham
  have hbheight := hplusheight b (List.mem_of_mem_getLast? (by simp [hb])) hbp
  let test := fun x : GaussianInt =>
    if i = 0 then (x - u).im ≤ (z - u).im else (z - u).im < (x - u).im
  have hta := SmallerStringGeometry.hta P i u hsum z hzhi hzlo' a haheight
  have htb := SmallerStringGeometry.htb P i u hsum z hzre hzhi hzlo' b hbheight
  obtain ⟨x, y, l₁, l₂, he, htx, hty⟩ :=
    crossing test walk ⟨a, ha, hta⟩ ⟨b, hb, htb⟩
  have hxmem : x ∈ walk := by rw [he]; simp
  have hymem : y ∈ walk := by rw [he]; simp
  have hxre := (hwsegment x hxmem).1
  have hyre := (hwsegment y hymem).1
  have hpair := stepPair x y z (hxre.trans hzre.symm) (hyre.trans hzre.symm)
    (List.isChain_iff_forall_rel_of_append_cons_cons.mp hwchain he) (SmallerStringGeometry.hcross
        i u z x y htx hty)
  obtain ⟨⟨U, hU, hEU⟩, ⟨V, hV, hEV⟩⟩ := hwedges x y l₁ l₂ he
  obtain ⟨g, hgzip, hg⟩ := hanc U hU
  obtain ⟨k, hkzip, hk⟩ := hanc' V hV
  rw [hpair] at hEU hEV
  exact ⟨U, V, g, k, hU, hV, hgzip, hkzip, hg, hk, hEU, hEV⟩

end ApollonianSuperharmonic

end
