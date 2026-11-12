/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1RightRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingShift

-- [TABLET NODE: P5332T1RightFirstValues]

/-!
# P5332T1RightFirstValues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1RightFirstValues (P : FordFareyParameter) (hq : 1 < P.q)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1RightRows P 0 0).displacement ∈ FordVertexDomain P.q →
      f y = FordOdometer P (y - (P5332T1RightRows P 0 0).displacement) +
        (P5332T1RightRows P 0 0).linear.re * y.re +
        (P5332T1RightRows P 0 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1RightRows P 0 0).displacement ∈ FordVertexDomain P.q)
    (hstar : ∀ k : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) - (P5332T1RightRows P 0
          0).displacement ∈ FordVertexDomain P.q) :
    ∃ t : Int, 0 ≤ t ∧ t ≤ (P.q₂ : Int) ∧
      x = (P5332T1RightRows P 0 t).center ∧ B = P.p₁ * (P.q : Int) ∧
      (∀ k : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) =
        (P5332T1RightRows P 0 t).values k) ∧
      ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ →
        z ∈ (FordTile P.q).cells ∨
        z - (P5332T1RightRows P 0 0).displacement ∈ (FordTile P.q).cells) ↔
        0 < t ∧ t < (P.q₂ : Int)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqn : (P.q : Int) ≠ 0 := by omega
  have hr : 0 < P.q₁ := by
    by_contra h
    have hz : P.q₁ = 0 := by omega
    have hd := P.det₁
    rw [hz] at hd
    norm_num at hd
    have hqpos : 0 < (P.q : Int) := by exact_mod_cast P.q_pos
    have hpone : P.p₁ * (P.q : Int) = 1 := hd
    have hqdiv : (P.q : Int) ∣ 1 := ⟨P.p₁, by nlinarith [mul_comm P.p₁ (P.q : Int)]⟩
    have hqle : (P.q : Int) ≤ 1 := Int.le_of_dvd (by norm_num) hqdiv
    omega
  have hs : 0 < P.q₂ := P.q₂_pos
  have hsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
    exact_mod_cast P.sum_q
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hb : u ≤ 1 ∨ (P.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q : Int)-1 ≤ v) :
      FordOdometer P ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q hqn := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ v ∧ v ≤ (P.q : Int)) ∧
      ¬ (2 ≤ u ∧ u ≤ (P.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (P.q : Int)-2)
    omega
  have top (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      FordOdometer P ⟨u,(P.q : Int)⟩ = P.p*u := by
    rw [boundary _ _ hu (by omega) (by omega) (by omega) (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*u*(P.q : Int)) = -(P.p*u)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  have bottom (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      FordOdometer P ⟨u,0⟩ = 0 := by
    rw [boundary _ _ hu huq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have domain (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q) : (⟨u,v⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
    exact ⟨hu, huq, hv, hvq⟩
  rcases x with ⟨X,Y⟩
  change ⟨X,Y⟩ ∈ FordVertexDomain P.q at hx
  change ⟨X,Y⟩ - (P5332T1RightRows P 0 0).displacement ∈ FordVertexDomain P.q at hx'
  simp only [FordVertexDomain, Set.mem_ofPred_eq, P5332T1RightRows,
    Matrix.cons_val_zero, Zsqrtd.re_sub, Zsqrtd.im_sub] at hx hx'
  have hY : Y = (P.q : Int) := by omega
  subst Y
  have ht0 : 0 ≤ X := hx.1
  have htq : X ≤ P.q₂ := by rw [hsum] at *; omega
  have hstarE := hstar 1
  have hstarW := hstar 2
  dsimp [P5332T1RightRows] at hstarE hstarW
  norm_num [FordVertexDomain] at hstarE hstarW
  have hcenter0 := hbase ⟨X,(P.q : Int)⟩ hx
  have hcenter1 := hother ⟨X,(P.q : Int)⟩ (by
    dsimp [P5332T1RightRows]
    change 0 ≤ X - (-(P.q₁ : Int)) ∧ X - (-(P.q₁ : Int)) ≤ P.q ∧
      0 ≤ (P.q : Int)-(P.q : Int) ∧ (P.q : Int)-(P.q : Int) ≤ P.q
    omega)
  have argCenter : (⟨X,(P.q : Int)⟩ : GaussianInt) - ⟨-(P.q₁ : Int),P.q⟩ =
      ⟨X+(P.q₁ : Int),0⟩ := by ext <;> simp
  rw [show (⟨X,(P.q : Int)⟩ : GaussianInt) - (P5332T1RightRows P 0 0).displacement =
      ⟨X+(P.q₁ : Int),0⟩ by simpa [P5332T1RightRows] using argCenter,
    bottom (X+(P.q₁ : Int)) (by omega) (by omega)] at hcenter1
  simp only [P5332T1RightRows, Matrix.cons_val_zero,
    zero_add,
    ] at hcenter1
  rw [top X ht0 (by omega)] at hcenter0
  have hB : B = P.p₁ * (P.q : Int) := by
    have hdet : P.p * (P.q₁ : Int) = P.p₁ * (P.q : Int) - 1 := by
      have := P.det₁
      nlinarith
    nlinarith
  subst B
  have valueTop (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      f ⟨u,(P.q : Int)⟩ = P.p*u := by
    exact (hbase ⟨u,(P.q : Int)⟩ ⟨by dsimp; omega, by dsimp; omega,
      by dsimp; omega, by dsimp; omega⟩).trans (top u hu huq)
  have hNorth : f (⟨X,(P.q : Int)⟩ + ⟨0,1⟩) =
      P.p*X + IntegerCeilDiv (P.p*X-1) P.q hqn := by
    have arg : (⟨X,(P.q : Int)⟩ : GaussianInt)+⟨0,1⟩-⟨-(P.q₁ : Int),P.q⟩ =
        ⟨X+(P.q₁ : Int),1⟩ := by ext <;> simp
    have he := hother (⟨X,(P.q : Int)⟩+⟨0,1⟩) (by
      dsimp [P5332T1RightRows]
      change 0 ≤ (X+0) - (-(P.q₁ : Int)) ∧ (X+0) - (-(P.q₁ : Int)) ≤ P.q ∧
        0 ≤ ((P.q : Int)+1)-(P.q : Int) ∧ ((P.q : Int)+1)-(P.q : Int) ≤ P.q
      omega)
    rw [show (⟨X,(P.q : Int)⟩ + ⟨0,1⟩ : GaussianInt) -
        (P5332T1RightRows P 0 0).displacement = ⟨X+(P.q₁ : Int),1⟩ by
        simpa [P5332T1RightRows] using arg,
      boundary _ _ (by omega) (by omega) (by omega) (by omega) (by omega)] at he
    have hdet : P.p * (P.q₁ : Int) = P.p₁ * (P.q : Int) - 1 := by
      have := P.det₁
      nlinarith
    have hp : P.p*(X+(P.q₁ : Int)) = (P.p*X-1) + P.p₁*(P.q : Int) := by
      rw [mul_add, hdet]
      ring
    simp only [mul_one] at he
    rw [hp, P5188T1CeilingShift (P.p*X-1) P.p₁ P.q hqn] at he
    simp only [P5332T1RightRows, Matrix.cons_val_zero,
      Zsqrtd.re_add, Zsqrtd.im_add,
      zero_add, add_zero] at he
    nlinarith
  have hSouth : f (⟨X,(P.q : Int)⟩ - ⟨0,1⟩) =
      P.p*X - P.p*X/(P.q : Int) := by
    have arg : (⟨X,(P.q : Int)⟩ : GaussianInt)-⟨0,1⟩ = ⟨X,(P.q : Int)-1⟩ := by
      ext <;> simp
    rw [arg, hbase ⟨X,(P.q : Int)-1⟩ (domain X ((P.q : Int)-1)
      (by omega) (by omega) (by omega) (by omega)),
      boundary _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    have hnum : P.p*X*((P.q : Int)-1) = (-P.p*X) + (P.p*X)*(P.q : Int) := by ring
    rw [hnum, P5188T1CeilingShift (-P.p*X) (P.p*X) P.q hqn]
    simp [IntegerCeilDiv]
    ring
  have hWest : f (⟨X,(P.q : Int)⟩-1) = P.p*(X-1) := by
    by_cases hXpos : X = 0
    · subst X
      have arg : (⟨0,(P.q : Int)⟩ : GaussianInt)-1-⟨-(P.q₁ : Int),P.q⟩ =
          ⟨(P.q₁ : Int)-1,0⟩ := by ext <;> simp; ring
      have hw := hother (⟨0,(P.q : Int)⟩-1) (by
        simp [FordVertexDomain, P5332T1RightRows]
        omega)
      rw [show (⟨0,(P.q : Int)⟩ - 1 : GaussianInt) -
          (P5332T1RightRows P 0 0).displacement = ⟨(P.q₁ : Int)-1,0⟩ by
          simpa [P5332T1RightRows] using arg,
        bottom _ (by omega) (by omega)] at hw
      norm_num [P5332T1RightRows] at hw
      nlinarith
    · have arg : (⟨X,(P.q : Int)⟩ : GaussianInt)-1 = ⟨X-1,(P.q : Int)⟩ := by
        ext <;> simp
      rw [arg, hbase ⟨X-1,(P.q : Int)⟩ (domain (X-1) (P.q : Int)
        (by omega) (by omega) (by omega) (by omega)), top (X-1) (by omega) (by omega)]
  refine ⟨X, ht0, htq, ?_, rfl, ?_, ?_⟩
  · ext <;> simp [P5332T1RightRows]
  · intro k
    fin_cases k
    · simpa [P5332T1RightRows] using valueTop X ht0 (by omega)
    · have heast : f (⟨X,(P.q : Int)⟩+1) = P.p*(X+1) := by
        have arg : (⟨X,(P.q : Int)⟩ : GaussianInt)+1 = ⟨X+1,(P.q : Int)⟩ := by
          ext <;> simp
        simpa [arg] using valueTop (X+1) (by omega) (by omega)
      simpa [P5332T1RightRows] using heast
    · simpa [P5332T1RightRows, sub_eq_add_neg] using hWest
    · simpa [P5332T1RightRows, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, IntegerCeilDiv] using hNorth
    · simpa [P5332T1RightRows, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, ← sub_eq_add_neg] using hSouth
  · constructor
    · intro hc
      have hc0 := hc ⟨X,(P.q : Int)⟩ (Or.inl rfl)
      have hc1 := hc (⟨X,(P.q : Int)⟩-1-⟨0,1⟩) (Or.inr (Or.inr (Or.inr rfl)))
      simp only [(P4210T1FordCellRectangles P.q _).1] at hc0 hc1
      simp [P5332T1RightRows] at hc0 hc1
      omega
    · intro ht z hz
      rcases hz with rfl | rfl | rfl | rfl
      · right
        simp only [(P4210T1FordCellRectangles P.q _).1]
        simp [P5332T1RightRows]
        omega
      · right
        simp only [(P4210T1FordCellRectangles P.q _).1]
        simp [P5332T1RightRows]
        omega
      · left
        simp only [(P4210T1FordCellRectangles P.q _).1]
        simp []
        omega
      · left
        simp only [(P4210T1FordCellRectangles P.q _).1]
        simp []
        omega

end ApollonianSuperharmonic

end
