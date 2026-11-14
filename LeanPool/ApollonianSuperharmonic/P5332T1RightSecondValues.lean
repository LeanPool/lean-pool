/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1RightRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles

-- [TABLET NODE: P5332T1RightSecondValues]

/-!
# P5332T1RightSecondValues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightSecondValuesProof

private theorem hB :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (f : IntegerLatticeFunction), ∀ (B : Int),
        (∀ y ∈ FordVertexDomain P.q, f y = FordOdometer P y) → ((∀ (y : GaussianInt), y -
        (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).displacement ∈ FordVertexDomain P.q → f
        y = FordOdometer P (y - (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).displacement) +
        (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.re * y.re + (P5332T1RightRows P
        (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.im * y.im + B) → ((∀ (u : Int), (0 ≤ u) → ((u ≤ P.q) →
        (FordOdometer P ⟨u,0⟩ = 0))) → ((∀ (u : Int), (0 ≤ u) → ((u ≤ P.q) → (FordOdometer P
        ⟨u,(P.q : Int)⟩ = P.p*u))) → (∀ (X : ℤ), ((P.q : Int) = (P.q₁ : Int) + P.q₂) → (((0 : ℤ)
        ≤ X ∧ X ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ)) → (((0 : ℤ) ≤ X -
        -(↑P.q₂ : ℤ) ∧ X - -(↑P.q₂ : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) - -(↑P.q : ℤ) ∧ (0 : ℤ)
        - -(↑P.q : ℤ) ≤ (↑P.q : ℤ)) → (
    let t : Int := X
    (0 ≤ t) → (B = -P.p * (P.q₂ : Int)))))))))) := by
  classical
  intro P hq f B hbase hother bottom top X hsum hx hx' t ht
  have hxt : (⟨t,0⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
    change 0 ≤ t ∧ t ≤ P.q ∧ 0 ≤ (0 : Int) ∧ (0 : Int) ≤ P.q
    exact ⟨ht, by omega, by omega, by omega⟩
  have hc0 := hbase ⟨t,0⟩ hxt
  have hc1 := hother ⟨t,0⟩ (by
    dsimp [P5332T1RightRows]
    change 0 ≤ t - (-(P.q₂ : Int)) ∧ t - (-(P.q₂ : Int)) ≤ P.q ∧
      0 ≤ (0 : Int) - (-(P.q : Int)) ∧ (0 : Int) - (-(P.q : Int)) ≤ P.q
    omega)
  dsimp [P5332T1RightRows] at hc1
  have arg : (⟨t,0⟩ : GaussianInt) - (⟨-(P.q₂ : Int),-(P.q : Int)⟩ : GaussianInt) = ⟨t+P.q₂,P.q⟩
      := by ext <;> simp
  rw [arg, top (t+P.q₂) (by omega) (by omega)] at hc1
  simp only [Int.mul_zero, add_zero] at hc1
  rw [bottom t ht (by omega)] at hc0
  rw [hc0] at hc1
  nlinarith [hc1]

private theorem hWest :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (f : IntegerLatticeFunction), ∀ (hqn : (P.q
        : Int) ≠ 0), (∀ (u : Int), (0 ≤ u) → ((u ≤ P.q) → (FordOdometer P ⟨u,(P.q : Int)⟩ =
        P.p*u))) → (∀ (X : ℤ), ((P.q : Int) = (P.q₁ : Int) + P.q₂) → ((0 < (P.q₂ : Int)) → (((0 :
        ℤ) ≤ X ∧ X ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ)) → (((0 : ℤ) ≤ X -
        -(↑P.q₂ : ℤ) ∧ X - -(↑P.q₂ : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) - -(↑P.q : ℤ) ∧ (0 : ℤ)
        - -(↑P.q : ℤ) ≤ (↑P.q : ℤ)) → (
    let t : Int := X
    (∀ (y : GaussianInt), y - (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).displacement ∈
        FordVertexDomain P.q → f y = FordOdometer P (y - (P5332T1RightRows P (1 : Fin (3 : ℕ))
        (0 : ℤ)).displacement) + (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.re *
        y.re + (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.im * y.im + -P.p * (↑P.q₂
        : ℤ)) → ((∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ P.q) → ((0 ≤ v) → ((v ≤ P.q) → ((u ≤
        1 ∨ P.q - 1 ≤ u ∨ v ≤ 1 ∨ P.q - 1 ≤ v) → (f ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q
        hqn)))))) → (f ((⟨t,0⟩ : GaussianInt)-1) = 0)))))))) := by
  classical
  intro P hq f hqn top X hsum hq₂pos hx hx' t hother hbaseval
  by_cases htz : t = 0
  · have hmem : (⟨-1,0⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
        FordVertexDomain P.q := by
      dsimp [P5332T1RightRows]
      change 0 ≤ -1 - (-(P.q₂ : Int)) ∧ -1 - (-(P.q₂ : Int)) ≤ P.q ∧
        0 ≤ (0 : Int) - (-(P.q : Int)) ∧ (0 : Int) - (-(P.q : Int)) ≤ P.q
      omega
    have hw := hother ⟨-1,0⟩ hmem
    dsimp [P5332T1RightRows] at hw
    have ha : (⟨-1,0⟩ : GaussianInt) - (⟨-(P.q₂ : Int),-(P.q : Int)⟩ : GaussianInt) =
        ⟨P.q₂-1,P.q⟩ := by
      ext <;> simp; ring
    rw [ha, top (P.q₂-1) (by omega) (by omega)] at hw
    have hval : f (⟨-1,0⟩ : GaussianInt) = 0 := by rw [hw]; ring
    have hp : ((⟨t,0⟩ : GaussianInt)-1) = ⟨-1,0⟩ := by rw [htz]; ext <;> simp
    rw [hp, hval]
  · have htpos : 0 < t := by omega
    have hp : (⟨t,0⟩ : GaussianInt)-1 = ⟨t-1,0⟩ := by ext <;> simp
    rw [hp, hbaseval (t-1) 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]

private theorem hSouth :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (f : IntegerLatticeFunction), ∀ (hqn : (P.q
        : Int) ≠ 0), (∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ P.q) → ((0 ≤ v) → ((v ≤ P.q) →
        ((u ≤ 1 ∨ (P.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q : Int)-1 ≤ v) → (FordOdometer P ⟨u,v⟩ =
        IntegerCeilDiv (P.p*u*v) P.q hqn)))))) → (∀ (X : ℤ), ((P.q : Int) = (P.q₁ : Int) + P.q₂)
        → ((((0 : ℤ) ≤ X - -(↑P.q₂ : ℤ) ∧ X - -(↑P.q₂ : ℤ) ≤ (↑P.q : ℤ) ∧ (0
        : ℤ) ≤ (0 : ℤ) - -(↑P.q : ℤ) ∧ (0 : ℤ) - -(↑P.q : ℤ) ≤ (↑P.q : ℤ)) → (
    let t : Int := X
    (∀ (y : GaussianInt), y - (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).displacement ∈
        FordVertexDomain P.q → f y = FordOdometer P (y - (P5332T1RightRows P (1 : Fin (3 : ℕ))
        (0 : ℤ)).displacement) + (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.re *
        y.re + (P5332T1RightRows P (1 : Fin (3 : ℕ)) (0 : ℤ)).linear.im * y.im + -P.p * (↑P.q₂
        : ℤ)) → (f ((⟨t,0⟩ : GaussianInt)+(-⟨0,1⟩)) = -((P.p*t+1)/P.q))))))) := by
  classical
  intro P hq f hqn boundary X hsum hx' t hother
  have hdom : (⟨t,-1⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈ FordVertexDomain
      P.q := by
    dsimp [P5332T1RightRows]
    change 0 ≤ t - (-(P.q₂ : Int)) ∧ t - (-(P.q₂ : Int)) ≤ P.q ∧
      0 ≤ -1 - (-(P.q : Int)) ∧ -1 - (-(P.q : Int)) ≤ P.q
    omega
  have hsarg : (⟨t,-1⟩ : GaussianInt) - (⟨-(P.q₂ : Int),-(P.q : Int)⟩ : GaussianInt) =
      ⟨t+P.q₂,P.q-1⟩ := by
    ext <;> simp; ring
  have hsbd : FordOdometer P ⟨t+P.q₂,P.q-1⟩ =
      IntegerCeilDiv (P.p*(t+P.q₂)*(P.q-1)) P.q hqn :=
    boundary _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have hs := hother ⟨t,-1⟩ hdom
  dsimp [P5332T1RightRows] at hs
  rw [hsarg, hsbd] at hs
  have hdet := P.det₂
  have hshift : IntegerCeilDiv (P.p*(t+P.q₂)*(P.q-1)) P.q hqn =
      IntegerCeilDiv (-(P.p*t+1)) P.q hqn + P.p*(t+P.q₂) - P.p₂ := by
    have hn : P.p*(t+P.q₂)*(P.q-1) = -(P.p*t+1) + (P.p*(t+P.q₂)-P.p₂)*P.q := by
      nlinarith [hdet]
    rw [hn, P5188T1CeilingShift]
    ring
  rw [hshift] at hs
  have hpt : ((⟨t,0⟩ : GaussianInt)+(-⟨0,1⟩)) = ⟨t,-1⟩ := by ext <;> simp
  rw [hpt]
  ring_nf at hs
  simpa [IntegerCeilDiv] using hs

private theorem westUnion :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (
        (
        (∀ (X : ℤ), ((P.q : Int) = (P.q₁ : Int) + P.q₂) → (((0 : ℤ) ≤ X ∧ X ≤ (↑P.q : ℤ) ∧ (0 :
        ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ)) → (
    let t : Int := X;
    (∀ (u : Int), ∀ (v : Int), (⟨u,v⟩ : GaussianInt) ∈ (FordTile P.q).cells ↔ 0 ≤ u ∧ u < P.q ∧ 0
        ≤ v ∧ v < P.q) → ((∀ (u : Int), ∀ (v : Int), ((⟨u,v⟩ : GaussianInt) - (P5332T1RightRows
        P 1 0).displacement) ∈ (FordTile P.q).cells ↔ 0 ≤ u + P.q₂ ∧ u + P.q₂ < P.q ∧ 0 ≤ v + P.q
        ∧ v + P.q < P.q) → ((⟨t-1,0⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨
        (⟨t-1,0⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
          (FordTile P.q).cells ↔ 0 < t))))))) := by
  classical
  intro P hq X hsum hx t rect transRect
  rw [rect, transRect]
  constructor
  · rintro (⟨hlo,_,_,_⟩ | ⟨_,hhi,_,_⟩) <;> omega
  · intro htpos
    left
    exact ⟨by omega, by omega, by omega, by omega⟩

private theorem lowerUnion :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (
        (
        (∀ (X : ℤ), ((P.q : Int) = (P.q₁ : Int) + P.q₂) → (((0 : ℤ) ≤ X - -(↑P.q₂ : ℤ) ∧ X -
        -(↑P.q₂ : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ (0 : ℤ) - -(↑P.q : ℤ) ∧ (0 : ℤ) - -(↑P.q : ℤ) ≤
        (↑P.q : ℤ)) → (
    let t : Int := X;
    (∀ (u : Int), ∀ (v : Int), (⟨u,v⟩ : GaussianInt) ∈ (FordTile P.q).cells ↔ 0 ≤ u ∧ u < P.q ∧ 0
        ≤ v ∧ v < P.q) → ((∀ (u : Int), ∀ (v : Int), ((⟨u,v⟩ : GaussianInt) - (P5332T1RightRows
        P 1 0).displacement) ∈ (FordTile P.q).cells ↔ 0 ≤ u + P.q₂ ∧ u + P.q₂ < P.q ∧ 0 ≤ v + P.q
        ∧ v + P.q < P.q) → ((⟨t,-1⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨
        (⟨t,-1⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
          (FordTile P.q).cells ↔ t < P.q₁))))))) := by
  classical
  intro P hq X hsum hx' t rect transRect
  rw [rect, transRect]
  constructor
  · rintro (⟨_,_,hlo,_⟩ | ⟨hlo,hhi,_,_⟩) <;> omega
  · intro hlt
    right
    exact ⟨by omega, by omega, by omega, by omega⟩

private theorem hcriterion :
    ∀ (P : FordFareyParameter), ∀ (X : ℤ),
    let t : Int := X
    (((⟨t,0⟩ : GaussianInt)-1) = ⟨t-1,0⟩) → ((((⟨t,0⟩ : GaussianInt)-⟨0,1⟩) = ⟨t,-1⟩) → ((((⟨t,0⟩
        : GaussianInt)-1-⟨0,1⟩) = ⟨t-1,-1⟩) → (((⟨t-1,0⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨
        (⟨t-1,0⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈ (FordTile P.q).cells
        ↔ 0 < t) → (((⟨t,-1⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨ (⟨t,-1⟩ : GaussianInt) -
        (P5332T1RightRows P 1 0).displacement ∈ (FordTile P.q).cells ↔ t < P.q₁) → (((⟨t,0⟩ :
        GaussianInt) ∈ (FordTile P.q).cells) → (((⟨t-1,-1⟩ : GaussianInt) - (P5332T1RightRows P
        1 0).displacement ∈ (FordTile P.q).cells) → ((∀ z : GaussianInt,
        z = (⟨t,0⟩ : GaussianInt) ∨ z = (⟨t,0⟩ : GaussianInt)-1 ∨
          z = (⟨t,0⟩ : GaussianInt)-⟨0,1⟩ ∨
          z = (⟨t,0⟩ : GaussianInt)-1-⟨0,1⟩ →
        z ∈ (FordTile P.q).cells ∨
          z - (P5332T1RightRows P 1 0).displacement ∈ (FordTile P.q).cells) ↔
        0 < t ∧ t < P.q₁))))))) := by
  classical
  intro P X t westPt lowerPt cornerPt westUnion lowerUnion centerCell cornerCell
  constructor
  · intro hall
    have hw := hall (⟨t,0⟩-1) (by simp)
    have hl := hall (⟨t,0⟩-⟨0,1⟩) (by simp)
    constructor
    · exact westUnion.mp (by simpa [westPt] using hw)
    · exact lowerUnion.mp (by simpa [lowerPt] using hl)
  · rintro ⟨htpos, htlt⟩ z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inl centerCell
    · exact (westUnion.mpr htpos).imp_left (by intro hm; exact hm)
    · simpa [lowerPt] using lowerUnion.mpr htlt
    · exact Or.inr (by simpa [cornerPt] using cornerCell)

end RightSecondValuesProof

theorem P5332T1RightSecondValues (P : FordFareyParameter) (hq : 1 < P.q)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1RightRows P 1 0).displacement ∈ FordVertexDomain P.q →
      f y = FordOdometer P (y - (P5332T1RightRows P 1 0).displacement) +
        (P5332T1RightRows P 1 0).linear.re * y.re +
        (P5332T1RightRows P 1 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1RightRows P 1 0).displacement ∈ FordVertexDomain P.q)
    (hstar : ∀ k : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) - (P5332T1RightRows P 1
          0).displacement ∈ FordVertexDomain P.q) :
    ∃ t : Int, 0 ≤ t ∧ t ≤ (P.q₁ : Int) ∧
      x = (P5332T1RightRows P 1 t).center ∧ B = -P.p * (P.q₂ : Int) ∧
      (∀ k : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) =
        (P5332T1RightRows P 1 t).values k) ∧
      ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ →
        z ∈ (FordTile P.q).cells ∨
        z - (P5332T1RightRows P 1 0).displacement ∈ (FordTile P.q).cells) ↔
        0 < t ∧ t < (P.q₁ : Int)) := by
-- BODY
  classical
  have hqn : (P.q : Int) ≠ 0 := by omega
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hs : u ≤ 1 ∨ (P.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q : Int)-1 ≤ v) :
      FordOdometer P ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q hqn := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ v ∧ v ≤ (P.q : Int)) ∧
      ¬ (2 ≤ u ∧ u ≤ (P.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (P.q : Int)-2)
    omega
  have bottom (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      FordOdometer P ⟨u,0⟩ = 0 := by
    rw [boundary u 0 hu huq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have top (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      FordOdometer P ⟨u,(P.q : Int)⟩ = P.p*u := by
    rw [boundary u P.q hu huq (by omega) (by omega) (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*u*(P.q : Int)) = (-P.p*u)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  let x₀ := x
  rcases x with ⟨X,Y⟩
  change ⟨X,Y⟩ ∈ FordVertexDomain P.q at hx
  change ⟨X,Y⟩- (P5332T1RightRows P 1 0).displacement ∈ FordVertexDomain P.q at hx'
  simp only [FordVertexDomain, Set.mem_ofPred_eq] at hx
  dsimp [P5332T1RightRows] at hx'
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
    Zsqrtd.im_sub] at hx'
  have hsum : (P.q : Int) = (P.q₁ : Int) + P.q₂ := by exact_mod_cast P.sum_q
  have hq₂pos : 0 < (P.q₂ : Int) := by exact_mod_cast P.q₂_pos
  have hgeom : Y = 0 ∧ 0 ≤ X ∧ X ≤ P.q₁ := by omega
  rcases hgeom with ⟨rfl, hX, hXr⟩
  let t : Int := X
  have ht : 0 ≤ t := hX
  have htr : t ≤ P.q₁ := hXr
  have hB : B = -P.p * (P.q₂ : Int) := RightSecondValuesProof.hB P hq f B hbase hother bottom top
      X hsum hx hx' ht
  subst B
  have hbaseval (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hs : u ≤ 1 ∨ P.q - 1 ≤ u ∨ v ≤ 1 ∨ P.q - 1 ≤ v) :
      f ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q hqn := by
    have hdom : (⟨u,v⟩ : GaussianInt) ∈ FordVertexDomain P.q := ⟨hu,huq,hv,hvq⟩
    rw [hbase ⟨u,v⟩ hdom, boundary u v hu huq hv hvq hs]
  have hcenterVal : f ⟨t,0⟩ = 0 := by
    rw [hbaseval t 0 ht (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have hEast : f ((⟨t,0⟩ : GaussianInt)+1) = 0 := by
    have hp : (⟨t,0⟩ : GaussianInt)+1 = ⟨t+1,0⟩ := by ext <;> simp
    rw [hp, hbaseval (t+1) 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have hWest : f ((⟨t,0⟩ : GaussianInt)-1) = 0 := RightSecondValuesProof.hWest P hq f hqn top X
      hsum hq₂pos hx hx' hother hbaseval
  have hNorth : f ((⟨t,0⟩ : GaussianInt)+⟨0,1⟩) = IntegerCeilDiv (P.p*t) P.q hqn := by
    have hp : (⟨t,0⟩ : GaussianInt)+⟨0,1⟩ = ⟨t,1⟩ := by ext <;> simp
    rw [hp, hbaseval t 1 ht (by omega) (by omega) (by omega) (by omega)]
    norm_num [IntegerCeilDiv]
  have hSouth : f ((⟨t,0⟩ : GaussianInt)+(-⟨0,1⟩)) = -((P.p*t+1)/P.q) :=
      RightSecondValuesProof.hSouth P hq f hqn boundary X hsum hx' hother
  refine ⟨t, ht, htr, ?_, ?_, ?_, ?_⟩
  · simp [t, P5332T1RightRows]
  · rfl
  · intro k
    fin_cases k
    · simpa [P5332T1RightRows, t] using hcenterVal
    · simpa [P5332T1RightRows, t] using hEast
    · simpa [P5332T1RightRows, t, sub_eq_add_neg] using hWest
    · simpa [P5332T1RightRows, t, IntegerCeilDiv] using hNorth
    · simpa [P5332T1RightRows, t] using hSouth
  · have dval : (P5332T1RightRows P 1 0).displacement =
        (⟨-(P.q₂ : Int),-(P.q : Int)⟩ : GaussianInt) := by
      simp [P5332T1RightRows]
    have rect (u v : Int) :
        (⟨u,v⟩ : GaussianInt) ∈ (FordTile P.q).cells ↔
          0 ≤ u ∧ u < P.q ∧ 0 ≤ v ∧ v < P.q := by
      simpa using (P4210T1FordCellRectangles P.q ⟨u,v⟩).1
    have transRect (u v : Int) :
        ((⟨u,v⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement) ∈
          (FordTile P.q).cells ↔
          0 ≤ u + P.q₂ ∧ u + P.q₂ < P.q ∧
            0 ≤ v + P.q ∧ v + P.q < P.q := by
      have hp : (⟨u,v⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement =
          ⟨u+P.q₂,v+P.q⟩ := by rw [dval]; ext <;> simp
      rw [hp, rect]
    have westPt : ((⟨t,0⟩ : GaussianInt)-1) = ⟨t-1,0⟩ := by ext <;> simp
    have lowerPt : ((⟨t,0⟩ : GaussianInt)-⟨0,1⟩) = ⟨t,-1⟩ := by ext <;> simp
    have cornerPt : ((⟨t,0⟩ : GaussianInt)-1-⟨0,1⟩) = ⟨t-1,-1⟩ := by ext <;> simp
    have westUnion :
        (⟨t-1,0⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨
          (⟨t-1,0⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
            (FordTile P.q).cells ↔ 0 < t := RightSecondValuesProof.westUnion P hq X hsum hx
                rect transRect
    have lowerUnion :
        (⟨t,-1⟩ : GaussianInt) ∈ (FordTile P.q).cells ∨
          (⟨t,-1⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
            (FordTile P.q).cells ↔ t < P.q₁ := RightSecondValuesProof.lowerUnion P hq X
                hsum hx' rect transRect
    have centerCell : (⟨t,0⟩ : GaussianInt) ∈ (FordTile P.q).cells := by
      rw [rect]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have cornerCell :
        (⟨t-1,-1⟩ : GaussianInt) - (P5332T1RightRows P 1 0).displacement ∈
          (FordTile P.q).cells := by
      rw [transRect]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hcriterion :
        (∀ z : GaussianInt,
          z = (⟨t,0⟩ : GaussianInt) ∨ z = (⟨t,0⟩ : GaussianInt)-1 ∨
            z = (⟨t,0⟩ : GaussianInt)-⟨0,1⟩ ∨
            z = (⟨t,0⟩ : GaussianInt)-1-⟨0,1⟩ →
          z ∈ (FordTile P.q).cells ∨
            z - (P5332T1RightRows P 1 0).displacement ∈ (FordTile P.q).cells) ↔
          0 < t ∧ t < P.q₁ := RightSecondValuesProof.hcriterion P X westPt lowerPt cornerPt
              westUnion lowerUnion centerCell cornerCell
    simpa [x₀, t, P5332T1RightRows, sub_eq_add_neg] using hcriterion

end ApollonianSuperharmonic

end
