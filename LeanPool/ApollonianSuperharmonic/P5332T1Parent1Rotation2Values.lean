/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent1Rotation2Values]

/-!
# P5332T1Parent1Rotation2Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1Parent1Rotation2Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₁) (hAq : A.q = P.q₁)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 0 2 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 0 2 0).displacement) +
        (P5332T1ParentRows P 0 2 0).linear.re * y.re +
        (P5332T1ParentRows P 0 2 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 0 2 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 0 2 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₁ : Int) ∧
      x = (P5332T1ParentRows P 0 2 t).center ∧ B = 0 ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 0 2 t).values l) ∧
      (x - (P5332T1ParentRows P 0 2 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (2+0 : Nat)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqtwo : 2 ≤ (P.q : Int) := by omega
  have hqn : (P.q : Int) ≠ 0 := by omega
  have hrpos : 0 < P.q₁ := by
    by_contra h
    have : P.q₁ = 0 := by omega
    have hd := P.det₁
    rw [this] at hd
    norm_num at hd
    by_cases hp : P.p₁ ≤ 0
    · have hprod : P.p₁ * (P.q : Int) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hp (by omega)
      linarith
    · have hp' : 1 ≤ P.p₁ := by omega
      have hq0 : 0 ≤ (P.q : Int) := by omega
      have hmul := mul_le_mul_of_nonneg_right hp' hq0
      have hmul' : (P.q : Int) ≤ P.p₁ * (P.q : Int) := by simpa using hmul
      have hprod : 2 ≤ P.p₁ * (P.q : Int) := by
        exact hqtwo.trans hmul'
      nlinarith [hd, hprod]
  have hrLtqInt : (P.q₁ : Int) < (P.q : Int) := by exact_mod_cast P.q₁_lt
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundaryP (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hs : u ≤ 1 ∨ (P.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q : Int)-1 ≤ v) :
      FordOdometer P ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q hqn := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ v ∧ v ≤ (P.q : Int)) ∧
      ¬(2 ≤ u ∧ u ≤ (P.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (P.q : Int)-2)
    rcases hs with h | h | h | h <;> omega
  have hra : (P.q₁ : Int) ≠ 0 := by omega
  have boundaryA (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q₁)
      (hv : 0 ≤ v) (hvq : v ≤ P.q₁)
      (hs : u ≤ 1 ∨ (P.q₁ : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q₁ : Int)-1 ≤ v) :
      FordOdometer A ⟨u,v⟩ = IntegerCeilDiv (A.p*u*v) P.q₁ hra := by
    have hn : (A.q : Int) ≠ 0 := by rw [hAq]; exact hra
    have hb := laws.2.1 A ⟨u,v⟩
    have hmem : (⟨u,v⟩ : GaussianInt) ∈ FordDoubledBoundary A.q := by
      change (0 ≤ u ∧ u ≤ (A.q : Int) ∧ 0 ≤ v ∧ v ≤ (A.q : Int)) ∧
        ¬(2 ≤ u ∧ u ≤ (A.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (A.q : Int)-2)
      rw [hAq]
      omega
    have hb' := hb hmem
    change FordOdometer A ⟨u,v⟩ =
      IntegerCeilDiv (A.p*u*v) A.q (by exact_mod_cast A.q_pos.ne') at hb'
    convert hb' using 1; simp [hAp, hAq]
  rcases x with ⟨X,Y⟩
  have hx0 := hx
  have hx'0 := hx'
  change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int) at hx0
  simp only [FordVertexDomain, Int.reduceNeg, P5332T1ParentRows, Nat.succ_eq_add_one,
      Nat.reduceAdd, add_zero, mul_zero, neg_zero, EuclideanDomain.zero_div, zero_add,
      sub_zero, zero_sub, neg_neg, Fin.isValue, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Set.mem_ofPred_eq, Zsqrtd.re_sub,
      Zsqrtd.im_sub, sub_neg_eq_add] at hx'0
  have hY : Y = 0 := by omega
  subst Y
  have hXr : X ≤ (P.q₁ : Int) := by simpa [hAq] using hx'0.2.1
  have hXpos : 0 < X := by
    by_contra h
    have : X = 0 := by omega
    subst X
    have hstarLeft := hstar 2
    dsimp [P5332T1ParentRows] at hstarLeft
    simp [FordVertexDomain] at hstarLeft
  let t : Int := (P.q₁ : Int) - X
  let x0 : GaussianInt := ⟨X,0⟩
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have htlt : t < (P.q₁ : Int) := by dsimp [t]; omega
  have hX : X = (P.q₁ : Int) - t := by dsimp [t]; omega
  have hcenter : x0 = (P5332T1ParentRows P 0 2 t).center := by
    change (⟨X,0⟩ : GaussianInt) = _
    simp [P5332T1ParentRows, hX]
  have hparentCenter := hother x0 (by
    simp [x0, P5332T1ParentRows, FordVertexDomain]
    omega)
  have hbaseCenter := hbase x0 (by simpa [x0] using hx)
  have leftA (z : Int) (hz : 0 ≤ z) (hzr : z ≤ P.q₁) :
      FordOdometer A ⟨z,(P.q₁ : Int)⟩ = A.p*z := by
    rw [boundaryA z (P.q₁ : Int) hz hzr (by omega) le_rfl (by omega)]
    unfold IntegerCeilDiv
    rw [show -(A.p*z*(P.q₁ : Int)) = -(A.p*z)*(P.q₁ : Int) by ring,
      Int.mul_ediv_cancel _ hra]
    ring
  have bottomP (z : Int) (hz : 0 ≤ z) (hzq : z ≤ P.q) :
      FordOdometer P ⟨z,0⟩ = 0 := by
    rw [boundaryP z 0 hz hzq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have centerarg : x0 -
      (P5332T1ParentRows P 0 2 0).displacement =
      ⟨X,(P.q₁ : Int)⟩ := by
    change (⟨X,0⟩ : GaussianInt) - ⟨0,-(P.q₁ : Int)⟩ = _
    ext <;> simp
  rw [centerarg] at hparentCenter
  rw [leftA X (by omega) hXr] at hparentCenter
  change f x0 = A.p*X + (-P.p₁)*X + 0*0 + B at hparentCenter
  rw [bottomP X (by omega) (by omega)] at hbaseCenter
  have B0 : B = 0 := by
    rw [hAp] at hparentCenter
    ring_nf at hparentCenter
    linarith [hbaseCenter]
  subst B
  have valueBottom (z : Int) (hz : 0 ≤ z) (hzq : z ≤ P.q) :
      f ⟨z,0⟩ = 0 := by
    have hm : (⟨z,0⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
      simp [FordVertexDomain]
      omega
    exact (hbase ⟨z,0⟩ hm).trans
      (bottomP z hz hzq)
  have valueUp : f (x0 + ⟨0,1⟩) = IntegerCeilDiv (P.p*X) P.q hqn := by
    have arg : x0 + ⟨0,1⟩ -
        (P5332T1ParentRows P 0 2 0).displacement =
        ⟨X,1+(P.q₁ : Int)⟩ := by
      change (⟨X,0⟩ : GaussianInt) + ⟨0,1⟩ - ⟨0,-(P.q₁ : Int)⟩ = _
      ext <;> simp
    have hdom : x0 + ⟨0,1⟩ ∈ FordVertexDomain P.q := by
      simp [FordVertexDomain, x0]
      omega
    have hu := hbase (x0 + ⟨0,1⟩) hdom
    have sourceEq : x0 + ⟨0,1⟩ = (⟨X,1⟩ : GaussianInt) := by
      change (⟨X,0⟩ : GaussianInt) + ⟨0,1⟩ = _
      ext <;> simp
    rw [sourceEq, boundaryP X 1 (by omega) (by omega) (by omega)
      (by omega) (by omega)] at hu
    rw [← sourceEq] at hu
    have heq : P.p*X*1 = P.p*X := by ring
    rw [heq] at hu
    simpa [P5332T1ParentRows] using hu
  have valueDown : f (x0 - ⟨0,1⟩) = -(P.p₁*X/(P.q₁ : Int)) := by
    have arg : x0 - ⟨0,1⟩ -
        (P5332T1ParentRows P 0 2 0).displacement =
        ⟨X,(P.q₁ : Int)-1⟩ := by
      ext <;> simp [x0, P5332T1ParentRows]; ring
    have hd := hother (x0 - ⟨0,1⟩) (by
      rw [arg]
      simp only [FordVertexDomain, Set.mem_ofPred_eq]
      rw [hAq]
      omega)
    rw [arg, boundaryA X ((P.q₁ : Int)-1) (by omega) (by omega) (by omega)
      (by omega) (by omega)] at hd
    dsimp [P5332T1ParentRows] at hd
    rw [hAp] at hd
    have hshift := P5188T1CeilingShift (-(P.p₁*X)) (P.p₁*X) P.q₁ hra
    have harg : P.p₁*X*((P.q₁ : Int)-1) =
        -(P.p₁*X)+(P.p₁*X)*(P.q₁ : Int) := by ring
    rw [harg, hshift] at hd
    dsimp [IntegerCeilDiv] at hd
    have hval : -((- (-(P.p₁*X)))/(P.q₁ : Int)) =
        -(P.p₁*X/(P.q₁ : Int)) := by norm_num
    rw [hval] at hd
    have hxcoord : x0.re = X := rfl
    rw [hxcoord] at hd
    ring_nf at hd
    exact hd
  refine ⟨t, ht0, htlt, ?_, rfl, ?_, ?_⟩
  · simpa [x0] using hcenter
  · intro l
    fin_cases l
    · simpa [P5332T1ParentRows, x0] using valueBottom X (by omega) (by omega)
    · have harg : x0 + 1 = ⟨X+1,0⟩ := by
        change (⟨X,0⟩ : GaussianInt) + 1 = _
        ext <;> simp
      have hv : f (x0+1) = 0 := by rw [harg]; exact valueBottom (X+1) (by omega) (by omega)
      simpa [P5332T1ParentRows, x0] using hv
    · have harg : x0 + (-1) = ⟨X-1,0⟩ := by
        change (⟨X,0⟩ : GaussianInt) + (-1) = _
        ext <;> simp; ring
      have hv : f (x0+(-1)) = 0 := by rw [harg]; exact valueBottom (X-1) (by omega) (by omega)
      simpa [P5332T1ParentRows, x0] using hv
    · simpa [P5332T1ParentRows, x0, ← hX, IntegerCeilDiv, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] using valueUp
    · simpa [P5332T1ParentRows, x0, hX, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, sub_eq_add_neg] using valueDown
  · constructor
    · intro hmem
      simp [P5332T1ParentRows, FordVertexDomain] at hmem
      have htzero : t = 0 := by omega
      exact ⟨htzero, by decide⟩
    · intro h
      rcases h with ⟨htzero, _⟩
      simp [P5332T1ParentRows, FordVertexDomain]
      omega

end ApollonianSuperharmonic

end
