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

-- [TABLET NODE: P5332T1RightHorizontalValues]

/-!
# P5332T1RightHorizontalValues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1RightHorizontalValues (P : FordFareyParameter) (hq : 1 < P.q)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1RightRows P 2 0).displacement ∈ FordVertexDomain P.q →
      f y = FordOdometer P (y - (P5332T1RightRows P 2 0).displacement) +
        (P5332T1RightRows P 2 0).linear.re * y.re +
        (P5332T1RightRows P 2 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1RightRows P 2 0).displacement ∈ FordVertexDomain P.q)
    (hstar : ∀ k : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k) - (P5332T1RightRows P 2
          0).displacement ∈ FordVertexDomain P.q) :
    ∃ t : Int, 0 ≤ t ∧ t ≤ (P.q : Int) ∧
      x = (P5332T1RightRows P 2 t).center ∧ B = 0 ∧
      (∀ k : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] k)) =
        (P5332T1RightRows P 2 t).values k) ∧
      ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ →
        z ∈ (FordTile P.q).cells ∨
        z - (P5332T1RightRows P 2 0).displacement ∈ (FordTile P.q).cells) ↔
        0 < t ∧ t < (P.q : Int)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqn : (P.q : Int) ≠ 0 := by omega
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (r t : Int) (hr : 0 ≤ r) (hrq : r ≤ P.q)
      (ht : 0 ≤ t) (htq : t ≤ P.q)
      (hs : r ≤ 1 ∨ (P.q : Int)-1 ≤ r ∨ t ≤ 1 ∨ (P.q : Int)-1 ≤ t) :
      FordOdometer P ⟨r,t⟩ = IntegerCeilDiv (P.p*r*t) P.q hqn := by
    apply laws.2.1
    change (0 ≤ r ∧ r ≤ (P.q : Int) ∧ 0 ≤ t ∧ t ≤ (P.q : Int)) ∧
      ¬ (2 ≤ r ∧ r ≤ (P.q : Int)-2 ∧ 2 ≤ t ∧ t ≤ (P.q : Int)-2)
    omega
  have right (t : Int) (ht : 0 ≤ t) (htq : t ≤ P.q) :
      FordOdometer P ⟨(P.q : Int),t⟩ = P.p*t := by
    rw [boundary _ _ (by omega) (by omega) ht htq (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*(P.q : Int)*t) = -(P.p*t)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  have left (t : Int) (ht : 0 ≤ t) (htq : t ≤ P.q) :
      FordOdometer P ⟨0,t⟩ = 0 := by
    rw [boundary _ _ (by omega) (by omega) ht htq (by omega)]
    simp [IntegerCeilDiv]
  rcases x with ⟨X,t⟩
  change ⟨X,t⟩-⟨(P.q : Int),0⟩ ∈ FordVertexDomain P.q at hx'
  have hx0 := hx
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
    sub_zero] at hx0 hx'
  have hX : X = (P.q : Int) := by omega
  subst X
  have hlow := hstar 4
  have hhigh := hstar 3
  dsimp [P5332T1RightRows] at hlow hhigh
  norm_num [FordVertexDomain] at hlow hhigh
  have ht : 0 < t ∧ t < (P.q : Int) := by omega
  have hcenter0 := hbase ⟨(P.q : Int),t⟩ hx
  have hcenter1 := hother ⟨(P.q : Int),t⟩ (by
    change 0 ≤ (P.q : Int)-P.q ∧ (P.q : Int)-P.q ≤ P.q ∧ 0 ≤ t-0 ∧ t-0 ≤ P.q
    omega)
  simp only [P5332T1RightRows, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hcenter1
  have B0 : B = 0 := by
    have centerarg : (⟨(P.q : Int),t⟩ : GaussianInt)-⟨(P.q : Int),0⟩ = ⟨0,t⟩ := by
      ext <;> simp
    rw [centerarg, left t (by omega) (by omega)] at hcenter1
    rw [right t (by omega) (by omega)] at hcenter0
    norm_num only [zero_mul, zero_add, add_zero] at hcenter1
    omega
  subst B
  have valueR : ∀ z : Int, 0 ≤ z → z ≤ P.q →
      f ⟨(P.q : Int),z⟩ = P.p*z := by
    intro z hz hzq
    exact (hbase ⟨(P.q : Int),z⟩ ⟨by dsimp; omega, le_rfl, hz, hzq⟩).trans (right z hz hzq)
  have valueE : f (⟨(P.q : Int),t⟩+1) = P.p*t - (-(P.p*t))/(P.q : Int) := by
    have arg : (⟨(P.q : Int),t⟩ : GaussianInt)+1-⟨(P.q : Int),0⟩ = ⟨1,t⟩ := by
      ext <;> simp
    have he := hother (⟨(P.q : Int),t⟩+1) (by
      change (⟨(P.q : Int),t⟩ : GaussianInt)+1-⟨(P.q : Int),0⟩ ∈ FordVertexDomain P.q
      rw [arg]
      change 0 ≤ (1 : Int) ∧ (1 : Int) ≤ P.q ∧ 0 ≤ t ∧ t ≤ P.q
      omega)
    dsimp [P5332T1RightRows] at he
    rw [arg, boundary 1 t (by omega) (by omega) (by omega) (by omega) (by omega)] at he
    simp only [IntegerCeilDiv, mul_one, zero_mul, add_zero,
      ] at he
    simpa only [sub_eq_add_neg, add_comm] using he
  have valueW : f (⟨(P.q : Int),t⟩-1) = P.p*t - P.p*t/(P.q : Int) := by
    have arg : (⟨(P.q : Int),t⟩ : GaussianInt)-1 = ⟨(P.q : Int)-1,t⟩ := by
      ext <;> simp
    rw [arg, hbase (⟨(P.q : Int)-1,t⟩ : GaussianInt)
        ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩,
      boundary _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    have num : P.p*((P.q : Int)-1)*t = -P.p*t+(P.p*t)*(P.q : Int) := by ring
    rw [num, P5188T1CeilingShift (-P.p*t) (P.p*t) P.q hqn]
    simp only [IntegerCeilDiv, neg_mul, neg_neg]
    ring
  refine ⟨t, by omega, by omega, rfl, rfl, ?_, ?_⟩
  · intro l
    fin_cases l
    · simpa [P5332T1RightRows] using valueR t (by omega) (by omega)
    · simpa [P5332T1RightRows, sub_eq_add_neg] using valueE
    · simpa [P5332T1RightRows, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        sub_eq_add_neg] using valueW
    · have arg : (⟨(P.q : Int),t⟩ : GaussianInt)+⟨0,1⟩ = ⟨(P.q : Int),t+1⟩ := by ext <;> simp
      simpa [P5332T1RightRows, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, arg]
        using valueR (t+1) (by omega) (by omega)
    · have arg : (⟨(P.q : Int),t⟩ : GaussianInt)-⟨0,1⟩ = ⟨(P.q : Int),t-1⟩ := by ext <;> simp
      simpa [P5332T1RightRows, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        ← sub_eq_add_neg, arg] using valueR (t-1) (by omega) (by omega)
  · constructor
    · intro _
      exact ht
    · intro _ z hz
      rcases hz with rfl | rfl | rfl | rfl
      · right
        rw [(P4210T1FordCellRectangles P.q _).1]
        change 0 ≤ (P.q : Int)-P.q ∧ (P.q : Int)-P.q < P.q ∧ 0 ≤ t-0 ∧ t-0 < P.q
        omega
      · left
        rw [(P4210T1FordCellRectangles P.q _).1]
        change 0 ≤ (P.q : Int)-1 ∧ (P.q : Int)-1 < P.q ∧ 0 ≤ t-0 ∧ t-0 < P.q
        omega
      · right
        rw [(P4210T1FordCellRectangles P.q _).1]
        change 0 ≤ (P.q : Int)-0-P.q ∧ (P.q : Int)-0-P.q < P.q ∧ 0 ≤ t-1-0 ∧ t-1-0 < P.q
        omega
      · left
        rw [(P4210T1FordCellRectangles P.q _).1]
        change 0 ≤ (P.q : Int)-1-0 ∧ (P.q : Int)-1-0 < P.q ∧ 0 ≤ t-0-1 ∧ t-0-1 < P.q
        omega

end ApollonianSuperharmonic

end
