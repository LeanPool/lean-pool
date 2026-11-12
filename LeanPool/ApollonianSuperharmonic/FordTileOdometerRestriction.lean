/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordOdometerFamilyExistsUnique
public import LeanPool.ApollonianSuperharmonic.FordCircleCoordinate
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist
public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.OdometerTranslation
public import LeanPool.ApollonianSuperharmonic.PartialOdometer
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.P4217T2SquareGeometry
public import LeanPool.ApollonianSuperharmonic.P4217T2RectangularBoundarySlope
public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport

-- [TABLET NODE: FordTileOdometerRestriction]

/-!
# FordTileOdometerRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordOdometerRestriction

private theorem mem :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        (∀ (R : FordFareyParameter), (↑(P4217T2SquareRestriction R.q (FordOdometer R)).domain :
            Set GaussianInt) = FordVertexDomain R.q ∧ (∀ x ∈ (P4217T2SquareRestriction R.q
            (FordOdometer R)).domain, (P4217T2SquareRestriction R.q (FordOdometer R)).value x =
            FordOdometer R x) ∧ PartialOdometerSquares (P4217T2SquareRestriction R.q
            (FordOdometer R)) = (FordTile R.q).cells ∧ (PartialOdometerSquares
            (P4217T2SquareRestriction R.q (FordOdometer R))).card = R.q * R.q ∧
            (PartialOdometerSquares (P4217T2SquareRestriction R.q (FordOdometer R))).Nonempty)
            → (∀ (R : FordFareyParameter), ∀ (x : GaussianInt), x ∈ (H R).domain ↔ x ∈
            FordVertexDomain R.q) ) := by
  classical
  intro H geom R x
  exact Set.ext_iff.mp (geom R).1 x

private theorem slope :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        (∀ (R : FordFareyParameter), (↑(P4217T2SquareRestriction R.q (FordOdometer R)).domain :
            Set GaussianInt) = FordVertexDomain R.q ∧ (∀ x ∈ (P4217T2SquareRestriction R.q
            (FordOdometer R)).domain, (P4217T2SquareRestriction R.q (FordOdometer R)).value x =
            FordOdometer R x) ∧ PartialOdometerSquares (P4217T2SquareRestriction R.q
            (FordOdometer R)) = (FordTile R.q).cells ∧ (PartialOdometerSquares
            (P4217T2SquareRestriction R.q (FordOdometer R))).card = R.q * R.q ∧
            (PartialOdometerSquares (P4217T2SquareRestriction R.q (FordOdometer R))).Nonempty)
            → ((∀ (R : FordFareyParameter), ∀ (x : GaussianInt), x ∈ (H R).domain ↔ x ∈
            FordVertexDomain R.q) → ((∀ (R : FordFareyParameter), ∀ (x : GaussianInt), (x ∈ (H
            R).domain) → ((H R).value x = FordOdometer R x)) → (((∀ (R : FordFareyParameter), ∀
            (x : GaussianInt), R.q = (1 : ℕ) → FordOdometer R x = x.re * (x.re - (1 : ℤ)) / (2 :
            ℤ) + R.p * x.re * x.im) ∧ (∀ (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q,
            Classical.choose FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re *
            x.im) (↑P.q : ℤ) (by exact_mod_cast P.q_pos.ne')) ∧ (∀ (P : FordFareyParameter), ∀ (x
                : GaussianInt),
            Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) =
            Classical.choose FordOdometerFamilyExistsUnique P x - P.p * x.re) ∧ (∀ (P :
            FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique P (x + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) = Classical.choose
            FordOdometerFamilyExistsUnique P x + P.p₁ * x.re + P.p * x.im + (↑P.q₁ : ℤ) * P.p) ∧
            (∀ (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique P (x + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) = Classical.choose
            FordOdometerFamilyExistsUnique P x + P.p₂ * x.re - P.p * x.im - (↑P.q : ℤ) * P.p₂) ∧
            ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), ∀ (P₂ : FordFareyParameter),
            (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q = P.q₁ → P₂.p = P.p₂ → P₂.q = P.q₂ → (∀ x ∈
            FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ)
            + (1 : ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈ FordRecursiveVertexDomains P
            (3 : Fin (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x =
            Classical.choose FordOdometerFamilyExistsUnique P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
            P.p₁ * x.re) → (∀ (R : FordFareyParameter), PartialOdometerSlope (H R) = some ((↑R.p
            : ℝ) / (2 : ℝ), (↑R.p : ℝ) / (2 : ℝ)))))) ) := by
  classical
  intro H geom mem val laws R
  have boundary (x : GaussianInt) (hx : x ∈ FordVertexDomain R.q)
      (hs : x.re = 0 ∨ x.re = R.q ∨ x.im = 0 ∨ x.im = R.q) :
      (H R).value x = IntegerCeilDiv (R.p * x.re * x.im) R.q
        (by exact_mod_cast R.q_pos.ne') := by
    rw [val R x ((mem R x).mpr hx)]
    apply laws.2.1
    refine ⟨hx, ?_⟩
    rcases hs with hs | hs | hs | hs <;> simp only [hs] <;> omega
  have left (y : Int) (hy : 0 ≤ y) (hyq : y ≤ R.q) :
      (H R).value ⟨0, y⟩ = 0 := by
    rw [boundary _ (by exact ⟨le_rfl, by dsimp; omega, hy, hyq⟩) (Or.inl rfl)]
    simp [IntegerCeilDiv]
  have right (y : Int) (hy : 0 ≤ y) (hyq : y ≤ R.q) :
      (H R).value ⟨(R.q : Int), y⟩ = R.p * y := by
    rw [boundary _ (by exact ⟨by dsimp; omega, le_rfl, hy, hyq⟩) (Or.inr (Or.inl rfl))]
    simp only [IntegerCeilDiv]
    have he : -(R.p * (R.q : Int) * y) = -(R.p * y) * (R.q : Int) := by ring
    rw [he, Int.mul_ediv_cancel _ (by exact_mod_cast R.q_pos.ne')]
    simp
  have bottom (x : Int) (hx : 0 ≤ x) (hxq : x ≤ R.q) :
      (H R).value ⟨x, 0⟩ = 0 := by
    rw [boundary _ (by exact ⟨hx, hxq, le_rfl, by dsimp; omega⟩) (Or.inr (Or.inr (Or.inl rfl)))]
    simp [IntegerCeilDiv]
  have top (x : Int) (hx : 0 ≤ x) (hxq : x ≤ R.q) :
      (H R).value ⟨x, (R.q : Int)⟩ = R.p * x := by
    rw [boundary _ (by exact ⟨hx, hxq, by dsimp; omega, le_rfl⟩) (Or.inr (Or.inr (Or.inr rfl)))]
    change -(-(R.p * x * (R.q : Int)) / (R.q : Int)) = R.p * x
    rw [← neg_mul]
    rw [Int.mul_ediv_cancel _ (by exact_mod_cast R.q_pos.ne')]
    simp
  have hs := P4217T2RectangularBoundarySlope (H R) R.q R.q
    R.q_pos R.q_pos R.p R.p (geom R).1 left right bottom top
  have hn : (R.q : Real) ≠ 0 := by exact_mod_cast R.q_pos.ne'
  convert hs using 1; congr 2 <;> field_simp

private theorem hdomain :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (R : FordFareyParameter), (R.q = (1 : ℕ)) → ((H R).domain = (CurvatureOneOdometer ⟨0,
            R.p⟩).domain) ) := by
  classical
  intro H R hu
  dsimp [H, P4217T2SquareRestriction, CurvatureOneOdometer]
  rw [hu]
  decide +kernel

private theorem ht :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        (∀ (R : FordFareyParameter), ∀ (x : GaussianInt), (x ∈ (H R).domain) → ((H R).value x =
            FordOdometer R x)) → (((∀ (R : FordFareyParameter), ∀ (x : GaussianInt), R.q = (1 :
            ℕ) → FordOdometer R x = x.re * (x.re - (1 : ℤ)) / (2 : ℤ) + R.p * x.re * x.im) ∧ (∀
            (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q, Classical.choose
            FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ)
                (by exact_mod_cast P.q_pos.ne'))
            ∧ (∀ (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique P (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) = Classical.choose
            FordOdometerFamilyExistsUnique P x - P.p * x.re) ∧ (∀ (P : FordFareyParameter), ∀ (x
            : GaussianInt), Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨(↑P.q : ℤ),
            (↑P.q₁ : ℤ)⟩) = Classical.choose FordOdometerFamilyExistsUnique P x + P.p₁ * x.re +
            P.p * x.im + (↑P.q₁ : ℤ) * P.p) ∧ (∀ (P : FordFareyParameter), ∀ (x : GaussianInt),
            Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) =
            Classical.choose FordOdometerFamilyExistsUnique P x + P.p₂ * x.re - P.p * x.im -
            (↑P.q : ℤ) * P.p₂) ∧ ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), ∀ (P₂ :
            FordFareyParameter), (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q = P.q₁ → P₂.p = P.p₂ → P₂.q =
            P.q₂ → (∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ)
            + (1 : ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈ FordRecursiveVertexDomains P
            (3 : Fin (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x =
            Classical.choose FordOdometerFamilyExistsUnique P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
            P.p₁ * x.re) → (∀ (R : FordFareyParameter), (R.q = (1 : ℕ)) → (((H R).domain =
            (CurvatureOneOdometer ⟨0, R.p⟩).domain) → (OdometerTranslation (H R)
            (CurvatureOneOdometer ⟨0, R.p⟩))))) ) := by
  classical
  intro H val laws R hu hdomain
  refine ⟨0, 0, 0, ?_, ?_⟩
  · intro x
    simp [hdomain]
  · intro x hx
    rw [val R x hx, laws.1 R x hu]
    rw [hdomain] at hx
    simp only [CurvatureOneOdometer, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      norm_num [CurvatureOneOdometer, Zsqrtd.ext_iff]

private theorem q1pos :
    (by
      classical
      exact
        ∀ (R : FordFareyParameter), (1 < R.q) → (0 < R.q₁) ) := by
  classical
  intro R hgt
  by_contra h
  have hz : R.q₁ = 0 := by omega
  have hd := R.det₁
  simp [hz] at hd
  have hdv : (R.q : Int) ∣ 1 := ⟨R.p₁, by simpa [mul_comm] using hd.symm⟩
  have := Int.eq_one_of_dvd_one (by omega : 0 ≤ (R.q : Int)) hdv
  omega

private theorem cross :
    (by
      classical
      exact
        ∀ (R : FordFareyParameter), R.p₁ * (R.q₂ : Int) - (R.q₁ : Int) * R.p₂ = 1 ) := by
  classical
  intro R
  have hd := R.det₁
  rw [R.sum_q, R.sum_p, Nat.cast_add] at hd
  nlinarith [hd]

private theorem red :
    (by
      classical
      exact
        (FordFareyParameter) → (∀ (a : ℤ), ∀ (b : ℕ), ∀ (d : ℕ), ∀ (c : ℤ), a * (↑d : ℤ) - (↑b :
            ℤ) * c = (1 : ℤ) → b.Coprime a.natAbs) ) := by
  classical
  intro R a b d c hd
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let g := Nat.gcd b a.natAbs
  have gb : (g : Int) ∣ (b : Int) := by exact_mod_cast Nat.gcd_dvd_left b a.natAbs
  have ga : (g : Int) ∣ a := (Int.dvd_natAbs).mp (by
    exact_mod_cast Nat.gcd_dvd_right b a.natAbs)
  have gd := dvd_sub (dvd_mul_of_dvd_left ga (d : Int)) (dvd_mul_of_dvd_left gb c)
  rw [hd] at gd
  have he := Int.eq_one_of_dvd_one (by omega : 0 ≤ (g : Int)) gd
  have : g = 1 := by exact_mod_cast he
  simp? [g] at this ⊢
  exact this

private theorem kcert :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (R : FordFareyParameter), ∀ (q1pos : 0 < R.q₁), ∀ (R1 : FordFareyParameter), ∀ (R2 :
            FordFareyParameter), ∀ (ho1 : TileOdometer (FordCircleCoordinate R.p₁ R.q₁) (FordTile
            R.q₁) (H R1)), ∀ (ho2 : TileOdometer (FordCircleCoordinate R.p₂ R.q₂) (FordTile R.q₂)
            (H R2)), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hS : ∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence (FordRecursiveQuadruple R) (FordTile R.q) i s (S i s)),
            ∀ (c0t : (S (0 : Fin (3 : ℕ)) true).cells = (FordTile R.q₁).cells), ∀ (c0f : (S (0 :
            Fin (3 : ℕ)) false).cells = (TileTranslation (FordTile R.q₁) ⟨(↑R.q₂ : ℤ), (↑R.q₂ :
            ℤ)⟩).cells), ∀ (c1t : (S (1 : Fin (3 : ℕ)) true).cells = (TileTranslation (FordTile
            R.q₂) ⟨(↑R.q₁ : ℤ), (0 : ℤ)⟩).cells), ∀ (c1f : (S (1 : Fin (3 : ℕ)) false).cells =
            (TileTranslation (FordTile R.q₂) ⟨(0 : ℤ), (↑R.q₁ : ℤ)⟩).cells), ∀ (c2t : (S (2 : Fin
            (3 : ℕ)) true).cells = ∅), ∀ (a2t : (S (2 : Fin (3 : ℕ)) true).anchor = ⟨(↑R.q₂ : ℤ),
            (↑R.q : ℤ)⟩), ∀ (c2f : (S (2 : Fin (3 : ℕ)) false).cells = ∅), ∀ (a2f : (S (2 : Fin
            (3 : ℕ)) false).anchor = ⟨(↑R.q₁ : ℤ), (0 : ℤ)⟩),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer (FordRecursiveQuadruple R i.succ) (S i s)
            (K i s) ) := by
  classical
  intro H R q1pos R1 R2 ho1 ho2 S hS c0t c0f c1t c1f c2t a2t c2f a2f line K i s
  have pos (p : Int) (q : Nat) (h : 0 < q) : 0 < (FordCircleCoordinate p q).1 := by
    change (0 : Int) < ((q * q : Nat) : Int)
    exact_mod_cast Nat.mul_pos h h
  fin_cases i <;> cases s <;>
    simp only [Fin.succ, Fin.reduceFinMk, FordRecursiveQuadruple,
      ite_eq_right q1pos.ne']
  · apply PositiveCurvatureTileOdometerSupportTransport
      (FordCircleCoordinate R.p₁ R.q₁)
      (TileTranslation (FordTile R.q₁) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩)
      _ _ (pos _ _ q1pos)
    · exact TileOdometerAffineTranslation _ _ _ _ _ _ ho1
    · simpa [FordRecursiveQuadruple, q1pos.ne'] using (hS 0 false).1
    · exact c0f.symm
  · apply PositiveCurvatureTileOdometerSupportTransport
      (FordCircleCoordinate R.p₁ R.q₁) (FordTile R.q₁) _ _ (pos _ _ q1pos) ho1
    · simpa [FordRecursiveQuadruple, q1pos.ne'] using (hS 0 true).1
    · exact c0t.symm
  · apply PositiveCurvatureTileOdometerSupportTransport
      (FordCircleCoordinate R.p₂ R.q₂)
      (TileTranslation (FordTile R.q₂) ⟨0, (R.q₁ : Int)⟩)
      _ _ (pos _ _ R.q₂_pos)
    · exact TileOdometerAffineTranslation _ _ _ _ _ _ ho2
    · simpa [FordRecursiveQuadruple] using (hS 1 false).1
    · exact c1f.symm
  · apply PositiveCurvatureTileOdometerSupportTransport
      (FordCircleCoordinate R.p₂ R.q₂)
      (TileTranslation (FordTile R.q₂) ⟨(R.q₁ : Int), 0⟩)
      _ _ (pos _ _ R.q₂_pos)
    · exact TileOdometerAffineTranslation _ _ _ _ _ _ ho2
    · simpa [FordRecursiveQuadruple] using (hS 1 true).1
    · exact c1t.symm
  · have he : S 2 false = ⟨∅, ⟨(R.q₁ : Int), 0⟩⟩ := by
      cases ht : S 2 false
      simpa only [ht, ProtoTile.mk.injEq] using And.intro c2f a2f
    rw [he]
    exact TileOdometer.line (-1) _ (Or.inr rfl) _ rfl
  · have he : S 2 true = ⟨∅, ⟨(R.q₂ : Int), (R.q : Int)⟩⟩ := by
      cases ht : S 2 true
      simpa only [ht, ProtoTile.mk.injEq] using And.intro c2t a2t
    rw [he]
    exact TileOdometer.line (-1) _ (Or.inr rfl) _ rfl

private theorem kd :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (mem : ∀ (R : FordFareyParameter), ∀ (x : GaussianInt), x ∈ (H R).domain ↔ x ∈
            FordVertexDomain R.q), ∀ (R : FordFareyParameter), ∀ (R1 : FordFareyParameter), ∀
            (hq1 : R1.q = R.q₁), ∀ (R2 : FordFareyParameter), ∀ (hq2 : R2.q = R.q₂),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (x : GaussianInt), x ∈ (K i s).domain ↔ if i = (0 :
            Fin (3 : ℕ)) then x ∈ FordRecursiveVertexDomains R (if s = true then (0 : Fin (4 :
            ℕ)) else (1 : Fin (4 : ℕ))) else if i = (1 : Fin (3 : ℕ)) then x ∈
            FordRecursiveVertexDomains R (if s = true then (2 : Fin (4 : ℕ)) else (3 : Fin (4 :
            ℕ))) else x = if s = true then ⟨(↑R.q₂ : ℤ), (↑R.q : ℤ)⟩ else ⟨(↑R.q₁ : ℤ), (0 : ℤ)⟩
            ) := by
  classical
  intro H mem R R1 hq1 R2 hq2 line K i s x
  have hsum : (R.q : Int) = (R.q₁ : Int) + (R.q₂ : Int) := by exact_mod_cast R.sum_q
  fin_cases i <;> cases s <;>
    simp [K, line, (PartialOdometerAffineTranslateFormulas _ _ _ _).2.1,
      mem, FordRecursiveVertexDomains, FordVertexDomain, hq1, hq2] <;> omega

private theorem dom :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (mem : ∀ (R : FordFareyParameter), ∀ (x : GaussianInt), x ∈ (H R).domain ↔ x ∈
            FordVertexDomain R.q), ∀ (R : FordFareyParameter), ∀ (hgt : 1 < R.q), ∀ (q1pos : 0 <
            R.q₁), ∀ (q2lt : R.q₂ < R.q), ∀ (R1 : FordFareyParameter), ∀ (hq1 : R1.q = R.q₁), ∀
            (R2 : FordFareyParameter), ∀ (hq2 : R2.q = R.q₂),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), x ∈ (K i s).domain ↔ if i = 0 then x ∈
            FordRecursiveVertexDomains R (if s then 0 else 1) else if i = 1 then x ∈
            FordRecursiveVertexDomains R (if s then 2 else 3) else x = if s then ⟨(R.q₂ : Int),
            (R.q : Int)⟩ else ⟨(R.q₁ : Int), 0⟩) → (∀ (x : GaussianInt), x ∈ (H R).domain ↔ ∃ (i
            : Fin (3 : ℕ)) (s : Bool), x ∈ (K i s).domain) ) := by
  classical
  intro H mem R hgt q1pos q2lt R1 hq1 R2 hq2 line K kd x
  rw [mem]
  constructor
  · intro hx
    have he : x ∈ FordRecursiveVertexDomains R 0 ∨
        x ∈ FordRecursiveVertexDomains R 1 ∨
        x ∈ FordRecursiveVertexDomains R 2 ∨
        x ∈ FordRecursiveVertexDomains R 3 := by
      have hs := R.sum_q
      simp [FordRecursiveVertexDomains, FordVertexDomain] at hx ⊢
      omega
    rcases he with he | he | he | he
    · exact ⟨0, true, (kd 0 true x).mpr he⟩
    · exact ⟨0, false, (kd 0 false x).mpr he⟩
    · exact ⟨1, true, (kd 1 true x).mpr he⟩
    · exact ⟨1, false, (kd 1 false x).mpr he⟩
  · rintro ⟨i, s, hx⟩
    have hx := (kd i s x).mp hx
    have hs := R.sum_q
    fin_cases i <;> cases s <;>
      simp? [FordRecursiveVertexDomains, FordVertexDomain] at hx ⊢ <;>
      (try subst x) <;> dsimp at * <;> omega

private theorem values :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (val : ∀ (R : FordFareyParameter), ∀ (x : GaussianInt), (x ∈ (H R).domain) → ((H
            R).value x = FordOdometer R x)), ∀ (laws : (∀ (R : FordFareyParameter), ∀ (x :
            GaussianInt), R.q = (1 : ℕ) → FordOdometer R x = x.re * (x.re - (1 : ℤ)) / (2 : ℤ) +
            R.p * x.re * x.im) ∧ (∀ (P : FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q,
            Classical.choose FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re *
            x.im) (↑P.q : ℤ) (by exact_mod_cast P.q_pos.ne')) ∧ (∀ (P : FordFareyParameter), ∀ (x
                : GaussianInt),
            Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) =
            Classical.choose FordOdometerFamilyExistsUnique P x - P.p * x.re) ∧ (∀ (P :
            FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique P (x + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) = Classical.choose
            FordOdometerFamilyExistsUnique P x + P.p₁ * x.re + P.p * x.im + (↑P.q₁ : ℤ) * P.p) ∧
            (∀ (P : FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique P (x + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) = Classical.choose
            FordOdometerFamilyExistsUnique P x + P.p₂ * x.re - P.p * x.im - (↑P.q : ℤ) * P.p₂) ∧
            ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), ∀ (P₂ : FordFareyParameter),
            (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q = P.q₁ → P₂.p = P.p₂ → P₂.q = P.q₂ → (∀ x ∈
            FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₁ (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ)
            + (1 : ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
            FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique
            P₂ (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈ FordRecursiveVertexDomains P
            (3 : Fin (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x =
            Classical.choose FordOdometerFamilyExistsUnique P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
            P.p₁ * x.re), ∀ (R : FordFareyParameter), ∀ (hgt : 1 < R.q), ∀ (R1 :
            FordFareyParameter), ∀ (hp1 : R1.p = R.p₁), ∀ (hq1 : R1.q = R.q₁), ∀ (R2 :
            FordFareyParameter), ∀ (hp2 : R2.p = R.p₂), ∀ (hq2 : R2.q = R.q₂),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), x ∈ (K i s).domain ↔ if i = 0 then x ∈
            FordRecursiveVertexDomains R (if s then 0 else 1) else if i = 1 then x ∈
            FordRecursiveVertexDomains R (if s then 2 else 3) else x = if s then ⟨(R.q₂ : Int),
            (R.q : Int)⟩ else ⟨(R.q₁ : Int), 0⟩) → ((∀ (x : GaussianInt), x ∈ (H R).domain ↔ ∃ i
            s, x ∈ (K i s).domain) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ x ∈ (K i s).domain, (H
            R).value x = (K i s).value x)) ) := by
  classical
  intro H val laws R hgt R1 hp1 hq1 R2 hp2 hq2 line K kd dom i s x hx
  rw [val R x ((dom x).mpr ⟨i, s, hx⟩)]
  have recs := laws.2.2.2.2.2 R R1 R2 hgt hp1 hq1 hp2 hq2
  change
    (∀ x, x ∈ FordRecursiveVertexDomains R 0 → FordOdometer R x = FordOdometer R1 x) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains R 1 →
      FordOdometer R x = FordOdometer R1 (x - ⟨(R.q₂ : Int), (R.q₂ : Int)⟩) +
        R.p₂ * x.re + R.p₂ * x.im - R.p₂ * (R.q₂ : Int) + 1) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains R 2 →
      FordOdometer R x = FordOdometer R2 (x - ⟨(R.q₁ : Int), 0⟩) + R.p₁ * x.im) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains R 3 →
      FordOdometer R x = FordOdometer R2 (x - ⟨0, (R.q₁ : Int)⟩) + R.p₁ * x.re) at recs
  have he := (kd i s x).mp hx
  fin_cases i <;> cases s <;> norm_num at he
  · rw [recs.2.1 x he]
    change _ = (PartialOdometerAffineTranslate (H R1)
      ⟨(R.q₂ : Int), (R.q₂ : Int)⟩ ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1)).value x
    have hf := (PartialOdometerAffineTranslateFormulas (H R1) _ _ _).2.2.1 x hx
    rw [hf, val R1 _ ((PartialOdometerAffineTranslateFormulas (H R1) _ _ _).2.1 x |>.mp hx)]
    dsimp
    ring
  · exact (recs.1 x he).trans (val R1 x hx).symm
  · rw [recs.2.2.2 x he]
    change _ = (PartialOdometerAffineTranslate (H R2)
      ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0).value x
    have hf := (PartialOdometerAffineTranslateFormulas (H R2) _ _ _).2.2.1 x hx
    rw [hf, val R2 _ ((PartialOdometerAffineTranslateFormulas (H R2) _ _ _).2.1 x |>.mp hx)]
    dsimp
    ring
  · rw [recs.2.2.1 x he]
    change _ = (PartialOdometerAffineTranslate (H R2)
      ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0).value x
    have hf := (PartialOdometerAffineTranslateFormulas (H R2) _ _ _).2.2.1 x hx
    rw [hf, val R2 _ ((PartialOdometerAffineTranslateFormulas (H R2) _ _ _).2.1 x |>.mp hx)]
    dsimp
    ring
  · simp [K, line, he]
  · simp [K, line, he]

private theorem compat :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (R : FordFareyParameter), ∀ (R1 : FordFareyParameter), ∀ (R2 : FordFareyParameter),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        (∀ (i : Fin 3), ∀ (s : Bool), ∀ (x : GaussianInt), (x ∈ (K i s).domain) → ((H R).value x
            = (K i s).value x)) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)), ∀ (t :
            Bool), OdometerCompatibility (K i s) (K j t)) ) := by
  classical
  intro H R R1 R2 line K values i s j t
  right
  refine ⟨0, ?_⟩
  intro x hx hy
  rw [← values i s x hx, ← values j t x hy, sub_self]

private theorem slopes :
    (by
      classical
      exact
        let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
        ∀ (slope : ∀ (R : FordFareyParameter), PartialOdometerSlope (H R) = some ((R.p : Real) /
            2, (R.p : Real) / 2)), ∀ (R : FordFareyParameter), ∀ (hgt : 1 < R.q), ∀ (R1 :
            FordFareyParameter), ∀ (hp1 : R1.p = R.p₁), ∀ (R2 : FordFareyParameter), ∀ (hp2 :
            R2.p = R.p₂),
        let line (x : GaussianInt) : PartialOdometer :=
          { domain := {x}
            value := fun y => if y = x then FordOdometer R y else 0
            value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
        let K : Fin 3 → Bool → PartialOdometer :=
          ![fun s => if s then H R1 else
              PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
                ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
            fun s => if s then
              PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
              PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
            fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (FordRecursiveQuadruple R i.succ).1 = (0 : ℤ) ∨ ∃ (p :
            ℝ × ℝ) (pi : ℝ × ℝ), PartialOdometerSlope (H R) = some p ∧ PartialOdometerSlope (K i
            s) = some pi ∧ pi.1 - p.1 = (if s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (FordRecursiveQuadruple R (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple R (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2
            (FordRecursiveQuadruple R (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple R (i
            + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ pi.2 - p.2 = (if s = true then (1 : ℝ) else
            (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (FordRecursiveQuadruple R (i + (2 : Fin
            (3 : ℕ))).succ) (FordRecursiveQuadruple R (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ) +
            (↑(BandVectors.2 (FordRecursiveQuadruple R (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple R (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ)) ) := by
  classical
  intro H slope R hgt R1 hp1 R2 hp2 line K i s
  have cfg := (FordCoordinateConfiguration R).2 hgt
  have a32 := cfg.2.2.2.2.2.2.2.1
  have a13 := cfg.2.2.2.2.2.2.2.2
  have sp : (R.p : Real) = (R.p₁ : Real) + (R.p₂ : Real) := by exact_mod_cast R.sum_p
  have sl1 := slope R1
  have sl2 := slope R2
  rw [hp1] at sl1
  rw [hp2] at sl2
  fin_cases i
  · right
    cases s
    · refine ⟨_, ((R.p₁ : Real) / 2 + R.p₂, (R.p₁ : Real) / 2 + R.p₂),
        slope R, ?_, ?_, ?_⟩
      · simpa [K, sl1] using (PartialOdometerAffineTranslateFormulas (H R1)
          ⟨(R.q₂ : Int), (R.q₂ : Int)⟩ ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1)).2.2.2.2.2
      · simp [a32]; linarith only [sp]
      · simp [a32]; linarith only [sp]
    · exact ⟨_, _, slope R, sl1, by simp [a32]; linarith only [sp],
        by simp [a32]; linarith only [sp]⟩
  · right
    cases s
    · refine ⟨_, ((R.p₂ : Real) / 2 + R.p₁, (R.p₂ : Real) / 2),
        slope R, ?_, ?_, ?_⟩
      · simpa [K, sl2] using (PartialOdometerAffineTranslateFormulas (H R2)
          ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0).2.2.2.2.2
      · simp [a13]; linarith only [sp]
      · simp [a13]; linarith only [sp]
    · refine ⟨_, ((R.p₂ : Real) / 2, (R.p₂ : Real) / 2 + R.p₁),
        slope R, ?_, ?_, ?_⟩
      · simpa [K, sl2] using (PartialOdometerAffineTranslateFormulas (H R2)
          ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0).2.2.2.2.2
      · simp [a13]; linarith only [sp]
      · simp [a13]; linarith only [sp]
  · left
    rfl

end FordOdometerRestriction

theorem FordTileOdometerRestriction (P : FordFareyParameter) :
    exists h : PartialOdometer,
      TileOdometer (FordCircleCoordinate P.p P.q) (FordTile P.q) h /\
      (h.domain : Set GaussianInt) = FordVertexDomain P.q /\
      forall x, x ∈ h.domain -> h.value x = FordOdometer P x := by
-- BODY
  classical
  let H (R : FordFareyParameter) := P4217T2SquareRestriction R.q (FordOdometer R)
  have geom (R : FordFareyParameter) :=
    P4217T2SquareGeometry R.q (FordOdometer R) R.q_pos
  have mem (R : FordFareyParameter) (x : GaussianInt) := FordOdometerRestriction.mem geom R x
  have val (R : FordFareyParameter) (x : GaussianInt) (hx : x ∈ (H R).domain) :
      (H R).value x = FordOdometer R x := (geom R).2.1 x hx
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ R x, R.q = 1 → FordOdometer R x = _) ∧ _ at laws
  have slope (R : FordFareyParameter) := FordOdometerRestriction.slope geom mem val laws R
  have main (n : Nat) : ∀ R : FordFareyParameter, R.q = n →
      TileOdometer (FordCircleCoordinate R.p R.q) (FordTile R.q) (H R) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R hn
      subst n
      by_cases hu : R.q = 1
      · have htile := (FordTileRecursiveIdentification R).2.1 hu
        have hdomain := FordOdometerRestriction.hdomain R hu
        have ht := FordOdometerRestriction.ht val laws R hu hdomain
        have hc : FordCircleCoordinate R.p R.q = (1, 1 + 2 * (⟨0, R.p⟩ : GaussianInt)) := by
          ext <;> simp [FordCircleCoordinate, hu]
        rw [hc]
        apply TileOdometer.unit ⟨0, R.p⟩ 0 _ _
        · rw [htile]
        · exact (geom R).1.trans (by
            simpa [hu] using (P4062T1CanonicalSupport R.q R.q_pos).1.symm)
        · exact ht
      have hgt : 1 < R.q := by have := R.q_pos; omega
      have q1pos := FordOdometerRestriction.q1pos R hgt
      have q2lt : R.q₂ < R.q := by have := R.sum_q; omega
      have cross : R.p₁ * (R.q₂ : Int) - (R.q₁ : Int) * R.p₂ = 1 := FordOdometerRestriction.cross R
      have red (a : Int) (b d : Nat) (c : Int)
          (hd : a * (d : Int) - (b : Int) * c = 1) : Nat.Coprime b a.natAbs :=
              FordOdometerRestriction.red R a b d c hd
      obtain ⟨R1, ⟨hp1, hq1⟩, _⟩ := FordFareyParentsExist R.p₁ R.q₁ q1pos
        (red R.p₁ R.q₁ R.q₂ R.p₂ cross)
      obtain ⟨R2, ⟨hp2, hq2⟩, _⟩ := FordFareyParentsExist R.p₂ R.q₂ R.q₂_pos
        (by simpa using red (-R.p₂) R.q₂ R.q₁ (-R.p₁) (by nlinarith [cross]))
      have ho1 : TileOdometer (FordCircleCoordinate R.p₁ R.q₁) (FordTile R.q₁) (H R1) := by
        simpa [hp1, hq1] using ih R.q₁ R.q₁_lt R1 hq1
      have ho2 : TileOdometer (FordCircleCoordinate R.p₂ R.q₂) (FordTile R.q₂) (H R2) := by
        simpa [hp2, hq2] using ih R.q₂ q2lt R2 hq2
      obtain ⟨hq, S, hS, hcells, c0t, c0f, c1t, c1f, c2t, a2t, c2f, a2f⟩ :=
        (FordTileRecursiveIdentification R).2.2 hgt
      let line (x : GaussianInt) : PartialOdometer :=
        { domain := {x}
          value := fun y => if y = x then FordOdometer R y else 0
          value_outside := by intro y hy; exact ite_eq_right (by simpa using hy) }
      let K : Fin 3 → Bool → PartialOdometer :=
        ![fun s => if s then H R1 else
            PartialOdometerAffineTranslate (H R1) ⟨(R.q₂ : Int), (R.q₂ : Int)⟩
              ⟨R.p₂, R.p₂⟩ (-R.p₂ * R.q₂ + 1),
          fun s => if s then
            PartialOdometerAffineTranslate (H R2) ⟨(R.q₁ : Int), 0⟩ ⟨0, R.p₁⟩ 0 else
            PartialOdometerAffineTranslate (H R2) ⟨0, (R.q₁ : Int)⟩ ⟨R.p₁, 0⟩ 0,
          fun s => if s then line ⟨(R.q₂ : Int), (R.q : Int)⟩ else line ⟨(R.q₁ : Int), 0⟩]
      have kcert (i : Fin 3) (s : Bool) := FordOdometerRestriction.kcert R q1pos R1 R2 ho1 ho2 S
          hS c0t c0f c1t c1f c2t a2t c2f a2f i s
      have kd (i : Fin 3) (s : Bool) (x : GaussianInt) := FordOdometerRestriction.kd mem R R1 hq1
          R2 hq2 i s x
      have dom (x : GaussianInt) := FordOdometerRestriction.dom mem R hgt q1pos q2lt R1 hq1 R2
          hq2 kd x
      have values (i : Fin 3) (s : Bool) (x : GaussianInt) (hx : x ∈ (K i s).domain) :=
          FordOdometerRestriction.values val laws R hgt R1 hp1 hq1 R2 hp2 hq2 kd dom i s x hx
      have compat (i : Fin 3) (s : Bool) (j : Fin 3) (t : Bool) := FordOdometerRestriction.compat
          R R1 R2 values i s j t
      have slopes (i : Fin 3) (s : Bool) := FordOdometerRestriction.slopes slope R hgt R1 hp1 R2
          hp2 i s
      exact TileOdometer.decompose hq (FordTileRecursiveIdentification R).1 kcert
        hcells (fun i s => (hS i s).2.1) (fun i s => (hS i s).2.2)
        dom values compat slopes
  exact ⟨H P, main P.q P rfl, (geom P).1, val P⟩

end ApollonianSuperharmonic

end
