/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification

-- [TABLET NODE: P4638T1EmptyFordLocalization]

/-!
# P4638T1EmptyFordLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EmptyFordGeometry

private theorem hρ :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ((r (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → (((0 : ℤ) < (r
            (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (r i.succ).1) ∧ ∀ (i : Fin (3
            : ℕ)), ∀ (j : Fin (3 : ℕ)), (r i.succ).1 = (0 : ℤ) → (r j.succ).1 = (0 : ℤ) → i = j)
            → (∀ (ρ : Fin (3 : ℕ)), ∀ (g₀ : BandPackingSymmetry), ∀ (P : FordFareyParameter), ((r
            (ρ + (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ)) → ((BandPackingSymmetryQuadrupleAction g₀
            ![r (0 : Fin (4 : ℕ)), r ρ.succ, r (ρ + (1 : Fin (3 : ℕ))).succ, r (ρ + (2 : Fin (3 :
            ℕ))).succ] = FordRecursiveQuadruple P) → (ρ = 1)))) ) := by
  classical
  intro r hline hcurve ρ g₀ P hz hrec
  have huni := hcurve.2.2
  fin_cases ρ
  · have hbad := huni 0 2 hline (by simpa using hz)
    exact False.elim ((by decide : (0 : Fin 3) ≠ 2) hbad)
  · rfl
  · have hbad := huni 0 1 hline (by simpa using hz)
    exact False.elim ((by decide : (0 : Fin 3) ≠ 1) hbad)

private theorem hp :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), (ProperBandQuadruple r) → (
        let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
        ProperBandQuadruple p) ) := by
  classical
  intro r hr p
  refine ⟨SemiProperQuadruple.rotate hr.1, ?_⟩
  intro j
  fin_cases j <;> simp only [Fin.isValue, Fin.mk_one, Fin.succ_one_eq_two, Matrix.cons_val,
      Matrix.cons_val_zero, p, Fin.reduceFinMk, Fin.reduceSucc, Fin.zero_eta,
      Fin.succ_zero_eq_one, Matrix.cons_val_one]
  · exact hr.2 1
  · exact hr.2 2
  · exact hr.2 0

private theorem hq1 :
    (by
      classical
      exact
        (Fin 4 → CircleCoordinates) → (∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (0 < P.q₁))
            ) := by
  classical
  intro r P hP
  by_contra hn
  have hzq : P.q₁ = 0 := by omega
  have hd := P.det₁
  simp [hzq, P.sum_q] at hd
  have hdiv : (P.q₂ : Int) ∣ 1 := ⟨P.p₁, by nlinarith⟩
  have hone : (P.q₂ : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le P.q₂)) hdiv
  have honeNat : P.q₂ = 1 := by exact_mod_cast hone
  have hqeq : P.q = 1 := by
    rw [P.sum_q, hzq, honeNat]
  rw [hqeq] at hP
  have hnot : ¬ 1 < 1 := by omega
  exact hnot hP

private theorem hrecg :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (g₀ : BandPackingSymmetry)
          (P : FordFareyParameter),
          let p :=
            ![r (0 : Fin (4 : ℕ)), r (2 : Fin (4 : ℕ)), r (3 : Fin (4 : ℕ)),
              r (1 : Fin (4 : ℕ))];
          BandPackingSymmetryQuadrupleAction g₀ p =
              FordRecursiveQuadruple P →
            ∀ (g : BandPackingSymmetry),
              g = g₀ ∨
                  g =
                    (BandPackingSymmetry.negate.comp
                          BandPackingSymmetry.negate).comp
                      g₀ →
                (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
                    BandPackingSymmetryQuadrupleAction g p =
                      BandPackingSymmetryQuadrupleAction g₀ p) →
                  BandPackingSymmetryQuadrupleAction g p =
                    FordRecursiveQuadruple P) := by
  classical
  intro r g₀ P p hrec' g hg hquadg
  rcases hg with rfl | rfl
  · exact hrec'
  · rw [hquadg p]
    exact hrec'

private theorem hcanonical :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : FordFareyParameter),
        let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryQuadrupleAction g p =
            FordRecursiveQuadruple P) → ((BandPackingSymmetryReversesOrientation g = false) →
            ((BandPackingSymmetryScopedPhase g p false) → (BandVectors.1 ((FordRecursiveQuadruple
            P) 2) ((FordRecursiveQuadruple P) 1) = BandPackingSymmetryVectorAction g
            (BandVectors.1 (p 2) (p 1))))) ) := by
  classical
  intro r P p g hrecg hgfalse hphase2
  have h := hphase2 2
  simpa [BandPackingSymmetryScopedPhase, hrecg, hgfalse] using h.2.2

private theorem hproperFord :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (ProperBandQuadruple
            (FordRecursiveQuadruple P)) ) := by
  classical
  intro P hP
  have h := (FordCoordinateConfiguration P).2 hP
  exact h.1

private theorem hvector :
    (by
      classical
      exact
        (Fin 4 → CircleCoordinates) → (∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → ((P.q = P.q₁
            + P.q₂) → ((ProperBandQuadruple (FordRecursiveQuadruple P)) → (BandVectors.1
            ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 1) = -((P.q₁ : Int) :
            GaussianInt) + ⟨0, (P.q₂ : Int)⟩)))) ) := by
  classical
  intro r P hP hsum hproperFord
  let F := FordRecursiveQuadruple P
  have hrot : SemiProperQuadruple ![F 0, F 2, F 3, F 1] :=
    SemiProperQuadruple.rotate hproperFord.1
  obtain ⟨hsumv, _, h10, _, _⟩ := VectorRecursionLaws F hproperFord.1
  obtain ⟨_, _, h20, _, _⟩ := VectorRecursionLaws ![F 0, F 2, F 3, F 1] hrot
  obtain ⟨_, hF10, hF20, _⟩ := (FordCoordinateConfiguration P).2 hP
  have h10' : BandVectors.1 (F 1) (F 0) = ⟨(P.q : Int), (P.q₁ : Int)⟩ := hF10
  have h20' : BandVectors.1 (F 2) (F 0) = ⟨-(P.q : Int), (P.q₂ : Int)⟩ := hF20
  have h20rot : BandVectors.1 (F 2) (F 0) =
      BandVectors.1 (F 2) (F 1) - ⟨0, 1⟩ * BandVectors.1 (F 3) (F 2) := by
    simpa using h20
  have h10eq : (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) =
      BandVectors.1 (F 1) (F 3) - ⟨0, 1⟩ * BandVectors.1 (F 2) (F 1) := by
    simpa [h10'] using h10
  let u := BandVectors.1 (F 3) (F 2)
  let v := BandVectors.1 (F 1) (F 3)
  let t := BandVectors.1 (F 2) (F 1)
  let ii : GaussianInt := ⟨0, 1⟩
  have hx : (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) = v - ii * t := by
    simpa [v, t, ii] using h10eq
  have hy : (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt) = t - ii * u := by
    simpa [t, u, ii, h20'] using h20rot
  have hcyc : u + v + t = 0 := by simpa [u, v, t] using hsumv
  have hv : v = (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) + ii * t := by
    calc
      v = (v - ii * t) + ii * t := by abel
      _ = _ := by rw [← hx]
  have hu : u = -ii * t + ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt) := by
    have hyre := congrArg Zsqrtd.re hy
    have hyim := congrArg Zsqrtd.im hy
    ext <;> simp [ii] at hyre hyim ⊢ <;> omega
  have hsumzero : (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) +
      ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt) + t = 0 := by
    calc
      _ = u + v + t := by rw [hu, hv]; ring
      _ = 0 := hcyc
  have ht : t = -((⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) +
      ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt)) := by
    have hsumzero' : (⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) +
        ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt) + t = 0 := hsumzero
    have hneg : -((⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) +
        ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt)) = t := by
      have h := congrArg Neg.neg (add_eq_zero_iff_eq_neg.mp hsumzero')
      simpa using h
    exact hneg.symm
  calc
    BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 1) = t := rfl
    _ = -((⟨(P.q : Int), (P.q₁ : Int)⟩ : GaussianInt) +
      ii * (⟨-(P.q : Int), (P.q₂ : Int)⟩ : GaussianInt)) := ht
    _ = -((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩ := by
      ext <;> simp [ii, hsum]

private theorem htargetvec :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : FordFareyParameter),
        let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
        ∀ (g : BandPackingSymmetry), (BandVectors.1 ((FordRecursiveQuadruple P) 2)
            ((FordRecursiveQuadruple P) 1) = BandPackingSymmetryVectorAction g (BandVectors.1 (p
            2) (p 1))) → ((BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple
            P) 1) = -((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩) →
            (BandPackingSymmetryVectorAction g (BandVectors.1 (r 3) (r 2)) = -((P.q₁ : Int) :
            GaussianInt) + ⟨0, (P.q₂ : Int)⟩)) ) := by
  classical
  intro r P p g hcanonical hvector
  simpa [p] using hcanonical.symm.trans hvector

private theorem cellTurn_bij :
    (by
      classical
      exact
        let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
        Function.Bijective cellTurn ) := by
  classical
  intro cellTurn
  constructor
  · intro a b hab
    have hre := congrArg Zsqrtd.re hab
    have him := congrArg Zsqrtd.im hab
    simp [cellTurn, GaussianQuarterTurn] at hre him
    ext <;> simp [cellTurn, GaussianQuarterTurn] at * <;> omega
  · intro z
    refine ⟨-GaussianQuarterTurn (z + 1), ?_⟩
    ext <;> simp [cellTurn, GaussianQuarterTurn]

private theorem hword :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (g₀ : BandPackingSymmetry), ∀ (P :
            FordFareyParameter), (∃ (w : GaussianInt), g₀ = BandPackingSymmetry.shift w ∨ g₀ =
            (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (
        let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
        ∀ (g : BandPackingSymmetry), (g = g₀ ∨ g = (BandPackingSymmetry.negate.comp
            BandPackingSymmetry.negate).comp g₀) → ((∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction g C = BandPackingSymmetryCircleAction g₀ C) →
            ((BandPackingSymmetryReversesOrientation g = BandPackingSymmetryReversesOrientation
            g₀) → ((∀ (p : Fin (4 : ℕ) → CircleCoordinates), BandPackingSymmetryQuadrupleAction g
            p = BandPackingSymmetryQuadrupleAction g₀ p) → ((BandPackingSymmetryScopedPhase g p
            false) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 :
            Fin (4 : ℕ)) = p (1 : Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ)) → r (3
            : Fin (4 : ℕ)) = p (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g r false) →
            ((BandPackingSymmetryQuadrupleAction g p = FordRecursiveQuadruple P) →
            ((BandPackingSymmetryReversesOrientation g = false) →
            ((BandPackingSymmetryScopedPhase g p false) → ((BandVectors.1
            ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 1) =
            BandPackingSymmetryVectorAction g (BandVectors.1 (p 2) (p 1))) →
            ((BandPackingSymmetryVectorAction g (BandVectors.1 (r 3) (r 2)) = -((P.q₁ : Int) :
            GaussianInt) + ⟨0, (P.q₂ : Int)⟩) → (
        let TP (k : Fin 4) (T : ProtoTile) : ProtoTile :=
          if k = 0 then T else if k = 1 then TileQuarterTurn T else
            if k = 2 then TileQuarterTurn (TileQuarterTurn T) else
              TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∃ k : Fin 4, (∀ T, BandPackingSymmetryTileAction g T = TP k T) ∧ (∀ z,
            BandPackingSymmetryVectorAction g z = VP k z))))))))))))) ) := by
  classical
  intro r g₀ P hw₀ p g hg hcirg horientg hquadg hfalse hfalsecyc hrecg hgfalse hphase2 hcanonical
      htargetvec TP VP
  rcases hw₀ with ⟨w, hw₀⟩
  rcases hg with hsame | hadapt
  · subst g
    rcases hw₀ with hw | hw
    · refine ⟨0, ?_, ?_⟩ <;> intro x <;> simp [TP, VP, hw, BandPackingSymmetryTileAction,
        BandPackingSymmetryVectorAction]
    · refine ⟨1, ?_, ?_⟩ <;> intro x <;> simp [TP, VP, hw, BandPackingSymmetryTileAction,
        BandPackingSymmetryVectorAction]
  · subst g
    rcases hw₀ with hw | hw
    · refine ⟨2, ?_, ?_⟩ <;> intro x <;> simp [TP, VP, hw, BandPackingSymmetryTileAction,
        BandPackingSymmetryVectorAction]
    · refine ⟨3, ?_, ?_⟩ <;> intro x <;> simp [TP, VP, hw, BandPackingSymmetryTileAction,
        BandPackingSymmetryVectorAction]

private theorem hcellpow :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
        ∀ (cellTurn_bij : Function.Bijective cellTurn),
        let E1 : GaussianInt ≃ GaussianInt := Equiv.ofBijective cellTurn cellTurn_bij
        let E2 : GaussianInt ≃ GaussianInt := E1.trans E1
        let E3 : GaussianInt ≃ GaussianInt := E2.trans E1
        let E : Fin 4 → GaussianInt ≃ GaussianInt := ![Equiv.refl _, E1, E2, E3]
        let TP (k : Fin 4) (T : ProtoTile) : ProtoTile :=
          if k = 0 then T else if k = 1 then TileQuarterTurn T else
            if k = 2 then TileQuarterTurn (TileQuarterTurn T) else
              TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), (∀ (T : ProtoTile), BandPackingSymmetryTileAction g T = TP k T) →
            ((∀ (z : GaussianInt), BandPackingSymmetryVectorAction g z = VP k z) → (∀ T,
            (BandPackingSymmetryTileAction g T).cells = T.cells.image (E k))) ) := by
  classical
  intro g cellTurn cellTurn_bij E1 E2 E3 E TP VP k htilepow hvecpow T
  rw [htilepow]
  fin_cases k <;>
    simp [TP, E, E1, E2, E3, cellTurn, TileQuarterTurnFormulas,
      Finset.image_image, Function.comp_def]

private theorem hanchorpow :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
        ∀ (cellTurn_bij : Function.Bijective cellTurn),
        let E1 : GaussianInt ≃ GaussianInt := Equiv.ofBijective cellTurn cellTurn_bij
        let E2 : GaussianInt ≃ GaussianInt := E1.trans E1
        let E3 : GaussianInt ≃ GaussianInt := E2.trans E1
        let E : Fin 4 → GaussianInt ≃ GaussianInt := ![Equiv.refl _, E1, E2, E3]
        let TP (k : Fin 4) (T : ProtoTile) : ProtoTile :=
          if k = 0 then T else if k = 1 then TileQuarterTurn T else
            if k = 2 then TileQuarterTurn (TileQuarterTurn T) else
              TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), (∀ (T : ProtoTile), BandPackingSymmetryTileAction g T = TP k T) →
            ((∀ (z : GaussianInt), BandPackingSymmetryVectorAction g z = VP k z) → ((∀ T,
            (BandPackingSymmetryTileAction g T).cells = T.cells.image (E k)) → (∀ T,
            (BandPackingSymmetryTileAction g T).anchor = VP k T.anchor))) ) := by
  classical
  intro g cellTurn cellTurn_bij E1 E2 E3 E TP VP k htilepow hvecpow hcellpow T
  rw [htilepow]
  fin_cases k <;> simp [TP, VP, TileQuarterTurnFormulas, GaussianQuarterTurn]

private theorem hcentpow :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry),
        let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
        ∀ (cellTurn_bij : Function.Bijective cellTurn),
        let E1 : GaussianInt ≃ GaussianInt := Equiv.ofBijective cellTurn cellTurn_bij
        let E2 : GaussianInt ≃ GaussianInt := E1.trans E1
        let E3 : GaussianInt ≃ GaussianInt := E2.trans E1
        let E : Fin 4 → GaussianInt ≃ GaussianInt := ![Equiv.refl _, E1, E2, E3]
        let TP (k : Fin 4) (T : ProtoTile) : ProtoTile :=
          if k = 0 then T else if k = 1 then TileQuarterTurn T else
            if k = 2 then TileQuarterTurn (TileQuarterTurn T) else
              TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))
        let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
          if k = 0 then x else if k = 1 then (-x.2, x.1) else
            if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), (∀ (T : ProtoTile), BandPackingSymmetryTileAction g T = TP k T) →
            ((∀ (z : GaussianInt), BandPackingSymmetryVectorAction g z = VP k z) → ((∀ T,
            (BandPackingSymmetryTileAction g T).cells = T.cells.image (E k)) → ((∀ T,
            (BandPackingSymmetryTileAction g T).anchor = VP k T.anchor) → (∀ T, TileCentroid
            (BandPackingSymmetryTileAction g T) = RP k (TileCentroid T))))) ) := by
  classical
  intro g cellTurn cellTurn_bij E1 E2 E3 E TP RP VP k htilepow hvecpow hcellpow hanchorpow T
  rw [htilepow]
  fin_cases k <;> simp [TP, RP, TileQuarterTurnFormulas]

private theorem hchild :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : FordFareyParameter),
        let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryQuadrupleAction g p =
            FordRecursiveQuadruple P) → ((BandPackingSymmetryReversesOrientation g = false) →
            (BandPackingSymmetryCircleAction g (r 0) = (FordRecursiveQuadruple P) 0)) ) := by
  classical
  intro r P p g hrecg hgfalse
  have h := congrFun hrecg 0
  simpa [p, BandPackingSymmetryQuadrupleAction, hgfalse] using h

private theorem hpointrot :
    (by
      classical
      exact
        let RP := fun (k : Fin (4 : ℕ)) (x : ℝ × ℝ) =>
          if k = (0 : Fin (4 : ℕ)) then x
          else
            if k = (1 : Fin (4 : ℕ)) then (-x.2, x.1)
            else if k = (2 : Fin (4 : ℕ)) then (-x.1, -x.2) else (x.2, -x.1);
        let VP := fun (k : Fin (4 : ℕ)) (z : GaussianInt) =>
          if k = (0 : Fin (4 : ℕ)) then z
          else
            if k = (1 : Fin (4 : ℕ)) then GaussianQuarterTurn z
            else
              if k = (2 : Fin (4 : ℕ)) then
                GaussianQuarterTurn
                  (GaussianQuarterTurn z)
              else
                GaussianQuarterTurn
                  (GaussianQuarterTurn
                    (GaussianQuarterTurn z));
        ∀ (k : Fin (4 : ℕ)) (z : GaussianInt),
          RP k (GaussianRealPoint z) =
            GaussianRealPoint (VP k z)) := by
  classical
  intro RP VP k z
  fin_cases k <;> ext <;> simp [RP, VP, GaussianRealPoint, GaussianQuarterTurn]

private theorem hDrot :
    (by
      classical
      exact
        let RP := fun (k : Fin (4 : ℕ)) (x : ℝ × ℝ) =>
          if k = (0 : Fin (4 : ℕ)) then x
          else
            if k = (1 : Fin (4 : ℕ)) then (-x.2, x.1)
            else if k = (2 : Fin (4 : ℕ)) then (-x.1, -x.2) else (x.2, -x.1);
        let VP := fun (k : Fin (4 : ℕ)) (z : GaussianInt) =>
          if k = (0 : Fin (4 : ℕ)) then z
          else
            if k = (1 : Fin (4 : ℕ)) then GaussianQuarterTurn z
            else
              if k = (2 : Fin (4 : ℕ)) then
                GaussianQuarterTurn
                  (GaussianQuarterTurn z)
              else
                GaussianQuarterTurn
                  (GaussianQuarterTurn
                    (GaussianQuarterTurn z));
        ∀ (k : Fin (4 : ℕ)),
          let D := fun (z : GaussianInt) =>
            (1 / 2 : ℝ) •
              (GaussianRealPoint z -
                (-(GaussianRealPoint z).2,
                  (GaussianRealPoint z).1));
          ∀ (z : GaussianInt), RP k (D z) = D (VP k z)) := by
  classical
  intro RP VP k D z
  fin_cases k <;> ext <;>
    simp [D, RP, VP, GaussianRealPoint, GaussianQuarterTurn] <;> ring

private theorem hDcanonical :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (P : FordFareyParameter), ∀ (g :
            BandPackingSymmetry), (BandPackingSymmetryVectorAction g (BandVectors.1 (r 3) (r 2))
            = -((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩) → (
        let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
          if k = 0 then x else if k = 1 then (-x.2, x.1) else
            if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), (∀ (z : GaussianInt), BandPackingSymmetryVectorAction g z = VP k z) → (
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        (∀ (z : GaussianInt), RP k (D z) = D (VP k z)) → (RP k (D (BandVectors.1 (r 3) (r 2))) =
            D (-((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩)))) ) := by
  classical
  intro r P g htargetvec RP VP k hvecpow D hDrot
  rw [hDrot, ← hvecpow, htargetvec]

private theorem hOempty :
    (by
      classical
      exact
        ∀ (O : ProtoTile), (O.cells = ∅) → (∀ (g : BandPackingSymmetry),
        let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
        ∀ (cellTurn_bij : Function.Bijective cellTurn),
        let E1 : GaussianInt ≃ GaussianInt := Equiv.ofBijective cellTurn cellTurn_bij
        let E2 : GaussianInt ≃ GaussianInt := E1.trans E1
        let E3 : GaussianInt ≃ GaussianInt := E2.trans E1
        let E : Fin 4 → GaussianInt ≃ GaussianInt := ![Equiv.refl _, E1, E2, E3]
        ∀ (k : Fin (4 : ℕ)), (∀ T, (BandPackingSymmetryTileAction g T).cells = T.cells.image (E
            k)) → ((BandPackingSymmetryTileAction g O).cells = ∅)) ) := by
  classical
  intro O hempty g cellTurn cellTurn_bij E1 E2 E3 E k hcellpow
  rw [hcellpow, hempty]
  simp

private theorem hw₀ :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (g : BandPackingSymmetry),
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), (∀ T, (BandPackingSymmetryTileAction g T).anchor = VP k T.anchor) → (
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        w₀ = VP k O.anchor) ) := by
  classical
  intro O g VP k hanchorpow w₀
  dsimp [w₀]
  exact hanchorpow O

private theorem hOcent :
    (by
      classical
      exact
        ∀ (O : ProtoTile),
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), ∀ (g : BandPackingSymmetry),
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        (w₀ = VP k O.anchor) → (
        let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
          if k = 0 then x else if k = 1 then (-x.2, x.1) else
            if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
        (∀ T, TileCentroid (BandPackingSymmetryTileAction g T) = RP k (TileCentroid T)) → ((∀ (z
            : GaussianInt), RP k (GaussianRealPoint z) = GaussianRealPoint (VP k z)) →
            ((TileCentroid O = GaussianRealPoint O.anchor) → (TileCentroid
            (BandPackingSymmetryTileAction g O) = GaussianRealPoint w₀)))) ) := by
  classical
  intro O VP k g w₀ hw₀ RP hcentpow hpointrot hObase
  rw [hcentpow, hObase, hpointrot O.anchor, ← hw₀]

private theorem hAcent' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (A : ProtoTile), ∀ (O : ProtoTile), (TileCentroid O
            - TileCentroid A = -((1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ)))) - (-(GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ))))).2, (GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ))))).1)))) → (
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        TileCentroid A = TileCentroid O + D (BandVectors.1 (r 3) (r 2))) ) := by
  classical
  intro r A O hAcent D
  ext
  · have h := congrArg Prod.fst hAcent
    dsimp [D, GaussianRealPoint] at h ⊢
    linarith
  · have h := congrArg Prod.snd hAcent
    dsimp [D, GaussianRealPoint] at h ⊢
    linarith

private theorem hBcent' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (B : ProtoTile), ∀ (O : ProtoTile), (TileCentroid O
            - TileCentroid B = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ)))) - (-(GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ))))).2, (GaussianRealPoint (BandVectors.1 (r (3 : Fin (4 :
            ℕ))) (r (2 : Fin (4 : ℕ))))).1))) → (
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        TileCentroid B = TileCentroid O - D (BandVectors.1 (r 3) (r 2))) ) := by
  classical
  intro r B O hBcent D
  ext
  · have h := congrArg Prod.fst hBcent
    dsimp [D, GaussianRealPoint] at h ⊢
    linarith
  · have h := congrArg Prod.snd hBcent
    dsimp [D, GaussianRealPoint] at h ⊢
    linarith

private theorem hAactual :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (A : ProtoTile), ∀ (O : ProtoTile), ∀ (P :
            FordFareyParameter),
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), ∀ (g : BandPackingSymmetry),
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        (w₀ = VP k O.anchor) → (
        let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
          if k = 0 then x else if k = 1 then (-x.2, x.1) else
            if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
        (∀ T, TileCentroid (BandPackingSymmetryTileAction g T) = RP k (TileCentroid T)) → (
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        (∀ (z : GaussianInt), RP k (GaussianRealPoint z) = GaussianRealPoint (VP k z)) → ((RP k
            (D (BandVectors.1 (r 3) (r 2))) = D (-((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ :
            Int)⟩)) → ((∀ (x : Real × Real), ∀ (y : Real × Real), RP k (x + y) = RP k x + RP k y)
            → ((TileCentroid O = GaussianRealPoint O.anchor) → ((TileCentroid A = TileCentroid O
            + D (BandVectors.1 (r 3) (r 2))) → (TileCentroid (BandPackingSymmetryTileAction g A)
            = GaussianRealPoint w₀ + D (-((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩))))))))
            ) := by
  classical
  intro r A O P VP k g w₀ hw₀ RP hcentpow D hpointrot hDcanonical hRPadd hObase hAcent'
  rw [hcentpow A, hAcent', hRPadd, hObase, hpointrot O.anchor, hw₀, hDcanonical]

private theorem hBactual :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (P :
            FordFareyParameter),
        let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
          if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
            if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
              GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
        ∀ (k : Fin (4 : ℕ)), ∀ (g : BandPackingSymmetry),
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        (w₀ = VP k O.anchor) → (
        let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
          if k = 0 then x else if k = 1 then (-x.2, x.1) else
            if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
        (∀ T, TileCentroid (BandPackingSymmetryTileAction g T) = RP k (TileCentroid T)) → (
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        (∀ (z : GaussianInt), RP k (GaussianRealPoint z) = GaussianRealPoint (VP k z)) → ((RP k
            (D (BandVectors.1 (r 3) (r 2))) = D (-((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ :
            Int)⟩)) → ((∀ (x : Real × Real), ∀ (y : Real × Real), RP k (x - y) = RP k x - RP k y)
            → ((TileCentroid O = GaussianRealPoint O.anchor) → ((TileCentroid B = TileCentroid O
            - D (BandVectors.1 (r 3) (r 2))) → (TileCentroid (BandPackingSymmetryTileAction g B)
            = GaussianRealPoint w₀ - D (-((P.q₁ : Int) : GaussianInt) + ⟨0, (P.q₂ : Int)⟩))))))))
            ) := by
  classical
  intro r B O P VP k g w₀ hw₀ RP hcentpow D hpointrot hDcanonical hRPsub hObase hBcent'
  rw [hcentpow B, hBcent', hRPsub, hObase, hpointrot O.anchor, hw₀, hDcanonical]

private theorem hAproto :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (A : ProtoTile), (BandPrototile (r (0 : Fin (4 :
            ℕ))) A) → (∀ (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryCircleAction g (r 0) = (FordRecursiveQuadruple P) 0) →
            (BandPrototile ((FordRecursiveQuadruple P) 0) (BandPackingSymmetryTileAction g A))) )
            := by
  classical
  intro r A hA P g hchild
  have h := (BandPackingSymmetryCovariance g).2.1 (r 0) A
  rw [hchild] at h
  exact h.mp hA

private theorem hBproto :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (B : ProtoTile), (BandPrototile (r (0 : Fin (4 :
            ℕ))) B) → (∀ (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
            (BandPackingSymmetryCircleAction g (r 0) = (FordRecursiveQuadruple P) 0) →
            (BandPrototile ((FordRecursiveQuadruple P) 0) (BandPackingSymmetryTileAction g B))) )
            := by
  classical
  intro r B hB P g hchild
  have h := (BandPackingSymmetryCovariance g).2.1 (r 0) B
  rw [hchild] at h
  exact h.mp hB

private theorem hmodel :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), BandPrototile ((FordRecursiveQuadruple P) 0) (FordTile P.q) )
            := by
  classical
  intro P
  simpa [FordRecursiveQuadruple, FordCircleCoordinate] using
    (FordTileRecursiveIdentification P).1

private theorem hMAcent :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (P : FordFareyParameter), (P.q = P.q₁ + P.q₂) → (∀ (g :
            BandPackingSymmetry),
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        let uA : GaussianInt := w₀ - ⟨(P.q₁ : Int), 0⟩
        let M_A := TileTranslation (FordTile P.q) uA
        (TileCentroid (FordTile P.q) = ((↑P.q : ℝ) / (2 : ℝ), (↑P.q : ℝ) / (2 : ℝ))) →
            (TileCentroid M_A = GaussianRealPoint w₀ + D (-((P.q₁ : Int) : GaussianInt) + ⟨0,
            (P.q₂ : Int)⟩))) ) := by
  classical
  intro O P hsum g D w₀ uA M_A hcentFord
  rw [(TileTranslationFormulas (FordTile P.q) uA).2.2.2.2.1, hcentFord]
  dsimp [uA, D, GaussianRealPoint]
  ext <;> simp [hsum] <;> ring

private theorem hMBcent :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (P : FordFareyParameter), (P.q = P.q₁ + P.q₂) → (∀ (g :
            BandPackingSymmetry),
        let D : GaussianInt → Real × Real := fun z =>
          (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint
              z).1))
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        let uB : GaussianInt := w₀ - ⟨(P.q₂ : Int), (P.q : Int)⟩
        let M_B := TileTranslation (FordTile P.q) uB
        (TileCentroid (FordTile P.q) = ((↑P.q : ℝ) / (2 : ℝ), (↑P.q : ℝ) / (2 : ℝ))) →
            (TileCentroid M_B = GaussianRealPoint w₀ - D (-((P.q₁ : Int) : GaussianInt) + ⟨0,
            (P.q₂ : Int)⟩))) ) := by
  classical
  intro O P hsum g D w₀ uB M_B hcentFord
  rw [(TileTranslationFormulas (FordTile P.q) uB).2.2.2.2.1, hcentFord]
  dsimp [uB, D, GaussianRealPoint]
  ext <;> simp [hsum] <;> ring

private theorem hvertices :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (a : GaussianInt), (O.anchor ∈ FootprintVertices (⟨{a}, a⟩ :
            ProtoTile)) → (O.anchor = a ∨ O.anchor = a + 1 ∨ O.anchor = a + ⟨0, 1⟩ ∨ O.anchor = a
            + 1 + ⟨0, 1⟩) ) := by
  classical
  intro O a ha
  simpa [FootprintVertices] using ha

private theorem ha'At433 :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (a : GaussianInt), (O.anchor = a + (1 : GaussianInt)) → (a =
            O.anchor - 1) ) := by
  classical
  intro O a h1
  calc a = (a + 1) - 1 := by simp
    _ = O.anchor - 1 := by rw [h1]

private theorem ha'At444 :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (a : GaussianInt), (O.anchor = a + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) → (a = O.anchor - ⟨0, 1⟩) ) := by
  classical
  intro O a h2
  calc a = (a + ⟨0, 1⟩) - ⟨0, 1⟩ := by simp
    _ = O.anchor - ⟨0, 1⟩ := by rw [h2]

private theorem ha'At455 :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (a : GaussianInt), (O.anchor = a + (1 : GaussianInt) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt)) → (a = O.anchor - 1 - ⟨0, 1⟩) ) := by
  classical
  intro O a h3
  calc a = (a + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ := by abel
    _ = O.anchor - 1 - ⟨0, 1⟩ := by rw [h3]

private theorem hmemAt468 :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        let uA : GaussianInt := w₀ - ⟨(P.q₁ : Int), 0⟩
        ∀ (a : GaussianInt), a ∈ (FordTile P.q).cells.image (GaussianTranslation uA) ↔ a - uA ∈
            (FordTile P.q).cells ) := by
  classical
  intro O P g w₀ uA a
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    simpa [GaussianTranslation] using hz
  · intro hz
    exact Finset.mem_image.mpr ⟨a - uA, hz, by simp [GaussianTranslation]⟩

private theorem hmemAt482 :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (P : FordFareyParameter), ∀ (g : BandPackingSymmetry),
        let w₀ := (BandPackingSymmetryTileAction g O).anchor
        let uB : GaussianInt := w₀ - ⟨(P.q₂ : Int), (P.q : Int)⟩
        ∀ (a : GaussianInt), a ∈ (FordTile P.q).cells.image (GaussianTranslation uB) ↔ a - uB ∈
            (FordTile P.q).cells ) := by
  classical
  intro O P g w₀ uB a
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    simpa [GaussianTranslation] using hz
  · intro hz
    exact Finset.mem_image.mpr ⟨a - uB, hz, by simp [GaussianTranslation]⟩

end EmptyFordGeometry

theorem P4638T1EmptyFordLocalization (r : Fin 4 → CircleCoordinates)
    (hr : ProperBandQuadruple r) (A B O : ProtoTile)
    (hA : BandPrototile (r 0) A) (hB : BandPrototile (r 0) B)
    (hempty : O.cells = ∅) (hline : (r 1).1 = 0)
    (hAcent : TileCentroid O - TileCentroid A =
      -((1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
          (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
            (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1))))
    (hBcent : TileCentroid O - TileCentroid B =
      (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
          (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
            (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1))) :
    ∃ (P : FordFareyParameter) (g : BandPackingSymmetry)
        (e : GaussianInt ≃ GaussianInt),
      0 < P.q₁ ∧ 0 < P.q₂ ∧
      (∀ T : ProtoTile, (BandPackingSymmetryTileAction g T).cells =
        T.cells.image e) ∧
      (∀ a : GaussianInt,
        O.anchor ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) →
        let z := e a - (BandPackingSymmetryTileAction g O).anchor;
        z = 0 ∨ z = -1 ∨ z = -⟨0, 1⟩ ∨ z = -1 - ⟨0, 1⟩) ∧
      (∀ a : GaussianInt,
        a ∈ (BandPackingSymmetryTileAction g A).cells ↔
        let z := a - (BandPackingSymmetryTileAction g O).anchor;
        -(P.q₁ : Int) ≤ z.re ∧ z.re < (P.q₂ : Int) ∧
          0 ≤ z.im ∧ z.im < ((P.q₁ + P.q₂ : Nat) : Int)) ∧
      (∀ a : GaussianInt,
        a ∈ (BandPackingSymmetryTileAction g B).cells ↔
        let z := a - (BandPackingSymmetryTileAction g O).anchor;
        -(P.q₂ : Int) ≤ z.re ∧ z.re < (P.q₁ : Int) ∧
          -((P.q₁ + P.q₂ : Nat) : Int) ≤ z.im ∧ z.im < 0) := by
-- BODY
  classical
  have hcurve := ProperBandCurvatureStructure r hr
  obtain ⟨ρ, g₀, P, hP, hg₀, hw₀, hz, hrec⟩ :=
    FordRegimeConverse r hr ⟨1, hline⟩
  have hρ := EmptyFordGeometry.hρ r hline hcurve ρ g₀ P hz hrec
  subst ρ
  let p : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
  have hp := EmptyFordGeometry.hp r hr
  have hrec' : BandPackingSymmetryQuadrupleAction g₀ p = FordRecursiveQuadruple P := by
    simpa [p] using hrec
  have hq1 := EmptyFordGeometry.hq1 r P hP
  have hq2 : 0 < P.q₂ := P.q₂_pos
  have hsum : P.q = P.q₁ + P.q₂ := P.sum_q
  obtain ⟨neg, hphase, _, hcyclic, hcirc, horient, hquad, hvec, g, hg, hcirg,
      horientg, hquadg, hfalse, hfalsecyc, _⟩ :=
    BandPackingSymmetryProjectiveVectorCovariance g₀ p hp
  have hrecg := EmptyFordGeometry.hrecg r g₀ P hrec' g hg hquadg
  have hgfalse : BandPackingSymmetryReversesOrientation g = false := by
    rw [horientg, hg₀]
  have hphase2 : BandPackingSymmetryScopedPhase g p false := hfalse
  have hcanonical := EmptyFordGeometry.hcanonical r P g hrecg hgfalse hphase2
  have hproperFord := EmptyFordGeometry.hproperFord P hP
  have hvector := EmptyFordGeometry.hvector r P hP hsum hproperFord
  have htargetvec := EmptyFordGeometry.htargetvec r P g hcanonical hvector
  let cellTurn : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1
  have cellTurn_bij := EmptyFordGeometry.cellTurn_bij
  let E1 : GaussianInt ≃ GaussianInt := Equiv.ofBijective cellTurn cellTurn_bij
  let E2 : GaussianInt ≃ GaussianInt := E1.trans E1
  let E3 : GaussianInt ≃ GaussianInt := E2.trans E1
  let E : Fin 4 → GaussianInt ≃ GaussianInt := ![Equiv.refl _, E1, E2, E3]
  let TP (k : Fin 4) (T : ProtoTile) : ProtoTile :=
    if k = 0 then T else if k = 1 then TileQuarterTurn T else
      if k = 2 then TileQuarterTurn (TileQuarterTurn T) else
        TileQuarterTurn (TileQuarterTurn (TileQuarterTurn T))
  let RP (k : Fin 4) (x : Real × Real) : Real × Real :=
    if k = 0 then x else if k = 1 then (-x.2, x.1) else
      if k = 2 then (-x.1, -x.2) else (x.2, -x.1)
  let VP (k : Fin 4) (z : GaussianInt) : GaussianInt :=
    if k = 0 then z else if k = 1 then GaussianQuarterTurn z else
      if k = 2 then GaussianQuarterTurn (GaussianQuarterTurn z) else
        GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z))
  have hword := EmptyFordGeometry.hword r g₀ P hw₀ g hg hcirg horientg hquadg hfalse hfalsecyc
      hrecg hgfalse hphase2 hcanonical htargetvec
  obtain ⟨k, htilepow, hvecpow⟩ := hword
  have hcellpow := EmptyFordGeometry.hcellpow g cellTurn_bij k htilepow hvecpow
  have hanchorpow := EmptyFordGeometry.hanchorpow g cellTurn_bij k htilepow hvecpow hcellpow
  have hcentpow := EmptyFordGeometry.hcentpow g cellTurn_bij k htilepow hvecpow hcellpow hanchorpow
  have hchild := EmptyFordGeometry.hchild r P g hrecg hgfalse
  let D : GaussianInt → Real × Real := fun z =>
    (1 / 2 : Real) • (GaussianRealPoint z - (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
  have hpointrot (z : GaussianInt) := EmptyFordGeometry.hpointrot k z
  have hDrot (z : GaussianInt) := EmptyFordGeometry.hDrot k z
  have hDcanonical := EmptyFordGeometry.hDcanonical r P g htargetvec k hvecpow hDrot
  have hRPadd (x y : Real × Real) : RP k (x + y) = RP k x + RP k y := by
    fin_cases k <;> ext <;> simp [RP] <;> ring
  have hRPsub (x y : Real × Real) : RP k (x - y) = RP k x - RP k y := by
    fin_cases k <;> ext <;> simp [RP] <;> ring
  have hOempty := EmptyFordGeometry.hOempty O hempty g cellTurn_bij k hcellpow
  let w₀ := (BandPackingSymmetryTileAction g O).anchor
  have hw₀ : w₀ = VP k O.anchor := EmptyFordGeometry.hw₀ O g k hanchorpow
  have hObase : TileCentroid O = GaussianRealPoint O.anchor := by
    simp [TileCentroid, hempty, GaussianRealPoint]
  have hOcent := EmptyFordGeometry.hOcent O k g hw₀ hcentpow hpointrot hObase
  have hAcent' := EmptyFordGeometry.hAcent' r A O hAcent
  have hBcent' := EmptyFordGeometry.hBcent' r B O hBcent
  have hAactual := EmptyFordGeometry.hAactual r A O P k g hw₀ hcentpow hpointrot hDcanonical
      hRPadd hObase hAcent'
  have hBactual := EmptyFordGeometry.hBactual r B O P k g hw₀ hcentpow hpointrot hDcanonical
      hRPsub hObase hBcent'
  have hfordC : (FordRecursiveQuadruple P) 0 = FordCircleCoordinate P.p P.q := by rfl
  have hAproto := EmptyFordGeometry.hAproto r A hA P g hchild
  have hBproto := EmptyFordGeometry.hBproto r B hB P g hchild
  let uA : GaussianInt := w₀ - ⟨(P.q₁ : Int), 0⟩
  let uB : GaussianInt := w₀ - ⟨(P.q₂ : Int), (P.q : Int)⟩
  let M_A := TileTranslation (FordTile P.q) uA
  let M_B := TileTranslation (FordTile P.q) uB
  have hmodel := EmptyFordGeometry.hmodel P
  have hMA : BandPrototile ((FordRecursiveQuadruple P) 0) M_A :=
    BandPrototileTranslation _ _ _ hmodel
  have hMB : BandPrototile ((FordRecursiveQuadruple P) 0) M_B :=
    BandPrototileTranslation _ _ _ hmodel
  have hcentFord := P4210T1FordSquareCentroid P.q (by omega)
  have hMAcent := EmptyFordGeometry.hMAcent O P hsum g hcentFord
  have hMBcent := EmptyFordGeometry.hMBcent O P hsum g hcentFord
  have hcellA : (BandPackingSymmetryTileAction g A).cells = M_A.cells :=
    (BandPrototileCentroidUnique _ _ _ hAproto hMA (hAactual.trans hMAcent.symm)).1
  have hcellB : (BandPackingSymmetryTileAction g B).cells = M_B.cells :=
    (BandPrototileCentroidUnique _ _ _ hBproto hMB (hBactual.trans hMBcent.symm)).1
  refine ⟨P, g, E k, hq1, hq2, hcellpow, ?_, ?_, ?_⟩
  · intro a ha
    have hvertices := EmptyFordGeometry.hvertices O a ha
    have hE1 (z : GaussianInt) : E1 z = cellTurn z := rfl
    have hE2 (z : GaussianInt) : E2 z = cellTurn (cellTurn z) := rfl
    have hE3 (z : GaussianInt) : E3 z = cellTurn (cellTurn (cellTurn z)) := rfl
    change E k a - w₀ = 0 ∨ E k a - w₀ = -1 ∨
      E k a - w₀ = -⟨0, 1⟩ ∨ E k a - w₀ = -1 - ⟨0, 1⟩
    rw [hw₀]
    rcases hvertices with h0 | h1 | h2 | h3
    · rw [h0]
      fin_cases k
      · exact Or.inl (by
          ext <;> simp [E, VP])
      · exact Or.inr (Or.inl (by
          ext <;> simp [E, hE1, VP, cellTurn, GaussianQuarterTurn]
          ))
      · exact Or.inr (Or.inr (Or.inr (by
          ext <;> simp [E, hE2, VP, cellTurn, GaussianQuarterTurn] <;> omega)))
      · exact Or.inr (Or.inr (Or.inl (by
          ext <;> simp [E, hE3, VP, cellTurn, GaussianQuarterTurn]; omega)))
    · have ha' : a = O.anchor - 1 := EmptyFordGeometry.ha'At433 O a h1
      rw [ha']
      fin_cases k
      · exact Or.inr (Or.inl (by
          ext <;> simp [E, VP]))
      · exact Or.inr (Or.inr (Or.inr (by
          ext <;> simp [E, hE1, VP, cellTurn, GaussianQuarterTurn]; omega)))
      · exact Or.inr (Or.inr (Or.inl (by
          ext <;> simp [E, hE2, VP, cellTurn, GaussianQuarterTurn]; omega)))
      · exact Or.inl (by
          ext <;> simp [E, hE3, VP, cellTurn, GaussianQuarterTurn] )
    · have ha' : a = O.anchor - ⟨0, 1⟩ := EmptyFordGeometry.ha'At444 O a h2
      rw [ha']
      fin_cases k
      · exact Or.inr (Or.inr (Or.inl (by
          ext <;> simp [E, VP])))
      · exact Or.inl (by
          ext <;> simp [E, hE1, VP, cellTurn, GaussianQuarterTurn] )
      · exact Or.inr (Or.inl (by
          ext <;> simp [E, hE2, VP, cellTurn, GaussianQuarterTurn]
          ))
      · exact Or.inr (Or.inr (Or.inr (by
          ext <;> simp [E, hE3, VP, cellTurn, GaussianQuarterTurn]; omega)))
    · have ha' : a = O.anchor - 1 - ⟨0, 1⟩ := EmptyFordGeometry.ha'At455 O a h3
      rw [ha']
      fin_cases k
      · exact Or.inr (Or.inr (Or.inr (by
          ext <;> simp [E, VP])))
      · exact Or.inr (Or.inr (Or.inl (by
          ext <;> simp [E, hE1, VP, cellTurn, GaussianQuarterTurn]
          )))
      · exact Or.inl (by
          ext <;> simp [E, hE2, VP, cellTurn, GaussianQuarterTurn] )
      · exact Or.inr (Or.inl (by
          ext <;> simp [E, hE3, VP, cellTurn, GaussianQuarterTurn]
          ))
  · intro a
    rw [hcellA, (TileTranslationFormulas (FordTile P.q) uA).1]
    have hmem : a ∈ (FordTile P.q).cells.image (GaussianTranslation uA) ↔
        a - uA ∈ (FordTile P.q).cells := EmptyFordGeometry.hmemAt468 O P g a
    rw [hmem, (P4210T1FordCellRectangles P.q (a - uA)).1]
    dsimp [uA, w₀]
    omega
  · intro a
    rw [hcellB, (TileTranslationFormulas (FordTile P.q) uB).1]
    have hmem : a ∈ (FordTile P.q).cells.image (GaussianTranslation uB) ↔
        a - uB ∈ (FordTile P.q).cells := EmptyFordGeometry.hmemAt482 O P g a
    rw [hmem, (P4210T1FordCellRectangles P.q (a - uB)).1]
    dsimp [uB, w₀]
    omega

end ApollonianSuperharmonic

end
