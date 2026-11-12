/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent1Rotation1Values]

/-!
# P5332T1Parent1Rotation1Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParentRotationValuesProof

private theorem hB :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), (A.p = P.p₁) → (((A.q : Int) = P.q₁)
        → (∀ (f : IntegerLatticeFunction), ∀ (B : Int), ((0 : ℕ) < P.q₁) → ((∀ (Q :
        FordFareyParameter), ∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ Q.q) → ((0 ≤ v) → ((v ≤
        Q.q) → ((u ≤ 1 ∨ (Q.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (Q.q : Int)-1 ≤ v) → (FordOdometer Q ⟨u,v⟩ =
        IntegerCeilDiv (Q.p*u*v) Q.q (by exact_mod_cast Q.q_pos.ne'))))))) → (∀ (Y : ℤ), (A.q =
        P.q₁) → (
    let t : Int := Y-P.q₂
    (0 ≤ t) → ((t ≤ (P.q₁ : Int)) → ((f ⟨0,Y⟩ = 0) → ((f ⟨(0 : ℤ), Y⟩ = FordOdometer A ⟨(↑P.q₁ :
        ℤ), t⟩ + P.p₂ * (0 : ℤ) + -P.p₁ * Y + B) → (B = P.p₁ * P.q₂))))))))) := by
  classical
  intro P A hAp hAq f B rposN boundary Y hAqNat t ht0 htr hcenterbase hcenterother
  have htrA : t ≤ (A.q : Int) := by rw [hAq]; exact htr
  have hbnd := boundary A (P.q₁ : Int) t (by omega) (by rw [hAq])
    ht0 htrA (by omega)
  rw [hbnd] at hcenterother
  simp only [hAp, hAqNat] at hcenterother
  simp only [IntegerCeilDiv] at hcenterother
  have hceil : -(-(P.p₁*(P.q₁ : Int)*t) / (P.q₁ : Int)) = P.p₁*t := by
    rw [show -(P.p₁*(P.q₁ : Int)*t) = (-P.p₁*t)*(P.q₁ : Int) by ring,
      Int.mul_ediv_cancel _ (by omega)]
    ring
  rw [hceil] at hcenterother
  rw [hcenterbase] at hcenterother
  simp only [mul_zero, add_zero] at hcenterother
  have hY : Y = (P.q₂ : Int) + t := by dsimp [t]; ring
  nlinarith [hY]

end ParentRotationValuesProof

theorem P5332T1Parent1Rotation1Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₁) (hAq : A.q = P.q₁)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 0 1 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 0 1 0).displacement) +
        (P5332T1ParentRows P 0 1 0).linear.re * y.re +
        (P5332T1ParentRows P 0 1 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 0 1 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 0 1 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₁ : Int) ∧
      x = (P5332T1ParentRows P 0 1 t).center ∧ B = P.p₁ * (P.q₂ : Int) ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 0 1 t).values l) ∧
      (x - (P5332T1ParentRows P 0 1 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (1+0 : Nat)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqn : (P.q : Int) ≠ 0 := by omega
  have rposN := (P5130T5ParentArithmetic P hq).1
  have rpos : 0 < (P.q₁ : Int) := by exact_mod_cast rposN
  have spos : 0 < (P.q₂ : Int) := by exact_mod_cast P.q₂_pos
  have rq : (P.q₁ : Int) + P.q₂ = P.q := by
    have := P.sum_q
    exact_mod_cast this.symm
  have pp : P.p = P.p₁ + P.p₂ := P.sum_p
  have d1 : P.p₁ * (P.q : Int) - (P.q₁ : Int) * P.p = 1 := P.det₁
  have d2 : P.p₂ * (P.q : Int) - P.q₂ * P.p = -1 := P.det₂
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (Q : FordFareyParameter) (u v : Int)
      (hu : 0 ≤ u) (huq : u ≤ Q.q) (hv : 0 ≤ v) (hvq : v ≤ Q.q)
      (hs : u ≤ 1 ∨ (Q.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (Q.q : Int)-1 ≤ v) :
      FordOdometer Q ⟨u,v⟩ = IntegerCeilDiv (Q.p*u*v) Q.q
        (by exact_mod_cast Q.q_pos.ne') := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (Q.q : Int) ∧ 0 ≤ v ∧ v ≤ (Q.q : Int)) ∧
      ¬(2 ≤ u ∧ u ≤ (Q.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (Q.q : Int)-2)
    omega
  rcases x with ⟨X,Y⟩
  have hx0 := hx
  have hx'0 := hx'
  change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int) at hx0
  dsimp [P5332T1ParentRows] at hx'0
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub] at hx'0
  have hAqNat : A.q = P.q₁ := hAq
  have hAq : (A.q : Int) = P.q₁ := by exact_mod_cast hAqNat
  have hAp' : A.p = P.p₁ := hAp
  have hX : X = 0 := by omega
  subst X
  let t : Int := Y-P.q₂
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have htr : t ≤ (P.q₁ : Int) := by dsimp [t]; omega
  have htrlt : t < (P.q₁ : Int) := by
    have hs := hstar 3
    dsimp [P5332T1ParentRows] at hs
    norm_num [FordVertexDomain] at hs
    dsimp [t]
    omega
  have hY : Y = P.q₂+t := by dsimp [t]; omega
  have hcenter : (⟨0,Y⟩ : GaussianInt) =
      (P5332T1ParentRows P 0 1 t).center := by
    simp [P5332T1ParentRows, hY]
  have hcenterbase : f ⟨0,Y⟩ = 0 := by
    rw [hbase _ hx]
    rw [boundary P 0 Y (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have hcenterother := hother ⟨0,Y⟩ hx'
  have harg : (⟨0,Y⟩ : GaussianInt) - (P5332T1ParentRows P 0 1 0).displacement =
      ⟨(P.q₁ : Int),t⟩ := by
    dsimp [P5332T1ParentRows]
    ext <;> simp [t]
  rw [harg] at hcenterother
  dsimp [P5332T1ParentRows] at hcenterother
  have hB : B = P.p₁ * P.q₂ := ParentRotationValuesProof.hB P A hAp hAq f B rposN boundary Y
      hAqNat ht0 htr hcenterbase hcenterother
  have hps : P.p * P.q₂ = 1 + P.p₂ * (P.q : Int) := by
    nlinarith [d1, pp, rq]
  have hplusbase : f ⟨1,Y⟩ = FordOdometer P ⟨1,Y⟩ := by
    apply hbase
    change 0 ≤ (1 : Int) ∧ 1 ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int)
    omega
  have hplusbnd := boundary P 1 Y (by norm_num) (by omega) (by omega) (by omega)
    (Or.inl (by norm_num))
  have hplus : f (⟨0,Y⟩ + 1) =
      IntegerCeilDiv (P.p * Y) P.q hqn := by
    have hcoord : (⟨0,Y⟩ : GaussianInt) + 1 = ⟨1,Y⟩ := by ext <;> simp
    rw [hcoord, hplusbase, hplusbnd]
    simp only [mul_one]
  have hnum : P.p * Y = P.p * t + 1 + P.p₂ * (P.q : Int) := by
    rw [hY]
    nlinarith [hps]
  have hplusShift : IntegerCeilDiv (P.p * Y) P.q hqn =
      IntegerCeilDiv (P.p * t + 1) P.q hqn + P.p₂ := by
    rw [hnum]
    exact P5188T1CeilingShift (P.p*t+1) P.p₂ (P.q : Int) hqn
  have hminusArg : (⟨0,Y⟩ : GaussianInt) - 1 -
      (P5332T1ParentRows P 0 1 0).displacement =
      ⟨(P.q₁ : Int)-1,t⟩ := by
    dsimp [P5332T1ParentRows]
    ext <;> simp [t]; ring
  have hminusMem : (⟨0,Y⟩ : GaussianInt) - 1 -
      (P5332T1ParentRows P 0 1 0).displacement ∈ FordVertexDomain A.q := by
    rw [hminusArg]
    change 0 ≤ (P.q₁ : Int)-1 ∧ (P.q₁ : Int)-1 ≤ (A.q : Int) ∧
      0 ≤ t ∧ t ≤ (A.q : Int)
    rw [hAq]
    omega
  have hminus := hother (⟨0,Y⟩ - 1) hminusMem
  rw [hminusArg] at hminus
  dsimp [P5332T1ParentRows] at hminus
  have hminusBnd := boundary A ((P.q₁ : Int)-1) t (by omega)
    (by rw [hAq]; omega) ht0 (by rw [hAq]; omega) (by
      right
      left
      simp [hAq])
  rw [hminusBnd] at hminus
  simp only [hAp, hAqNat] at hminus
  have hceilMinus : IntegerCeilDiv
      (P.p₁*((P.q₁ : Int)-1)*t) (P.q₁ : Int) (by omega) =
      P.p₁*t - (P.p₁*t)/(P.q₁ : Int) := by
    have hnum' : P.p₁*((P.q₁ : Int)-1)*t =
        -(P.p₁*t) + (P.p₁*t)*(P.q₁ : Int) := by ring
    rw [hnum']
    rw [P5188T1CeilingShift (-(P.p₁*t)) (P.p₁*t) (P.q₁ : Int) (by omega)]
    simp only [IntegerCeilDiv, neg_neg]
    ring
  rw [hceilMinus] at hminus
  have hminusValue : f (⟨0,Y⟩ - 1) =
      -P.p₂ - (P.p₁*t)/(P.q₁ : Int) := by
    rw [hB] at hminus
    simp only [
      Int.sub_zero, mul_neg_one] at hminus
    nlinarith only [hminus, hB]
  have outerLeft (z : Int) (hz : 0 ≤ z) (hzq : z ≤ (P.q : Int)) :
      f ⟨0,z⟩ = 0 := by
    rw [hbase _ (by change 0 ≤ (0:Int) ∧ 0 ≤ (P.q:Int) ∧ 0 ≤ z ∧ z ≤ (P.q:Int); omega)]
    rw [boundary P 0 z (by norm_num) (by omega) hz hzq (Or.inl (by norm_num))]
    simp [IntegerCeilDiv]
  have rowValue0 : (P5332T1ParentRows P 0 1 t).values 0 = 0 := rfl
  have rowValue1 : (P5332T1ParentRows P 0 1 t).values 1 =
      P.p₂ + IntegerCeilDiv (P.p*t+1) P.q (by exact_mod_cast P.q_pos.ne') := rfl
  have rowValue2 : (P5332T1ParentRows P 0 1 t).values 2 =
      -P.p₂ - (P.p₁*t)/(P.q₁ : Int) := rfl
  have rowValue3 : (P5332T1ParentRows P 0 1 t).values 3 = 0 := rfl
  have rowValue4 : (P5332T1ParentRows P 0 1 t).values 4 = 0 := rfl
  have rowCompanion : (P5332T1ParentRows P 0 1 0).companion =
      ⟨-(P.q₁ : Int),(P.q : Int)⟩ := rfl
  refine ⟨t, ht0, htrlt, ?_, hB, ?_, ?_⟩
  · simp [P5332T1ParentRows, hY]
  · intro l
    fin_cases l
    · have hs : (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
          (0 : Fin 5) : GaussianInt) = 0 := rfl
      simp only []
      change f (⟨0,Y⟩ + (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
        (0 : Fin 5))) = (P5332T1ParentRows P 0 1 t).values (0 : Fin 5)
      rw [hs, rowValue0]
      simpa using hcenterbase
    · have hs : (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
          (1 : Fin 5) : GaussianInt) = 1 := rfl
      simp only []
      change f (⟨0,Y⟩ + (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
        (1 : Fin 5))) = (P5332T1ParentRows P 0 1 t).values (1 : Fin 5)
      rw [hs, rowValue1]
      change f (⟨0,Y⟩ + 1) =
        P.p₂ + IntegerCeilDiv (P.p*t+1) P.q (by exact_mod_cast P.q_pos.ne')
      simpa [add_comm] using hplus.trans hplusShift
    · have hs : (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
          (2 : Fin 5) : GaussianInt) = -1 := rfl
      simp only []
      change f (⟨0,Y⟩ + (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
        (2 : Fin 5))) = (P5332T1ParentRows P 0 1 t).values (2 : Fin 5)
      rw [hs, rowValue2]
      simpa [sub_eq_add_neg] using hminusValue
    · have hu := outerLeft (Y+1) (by omega) (by omega)
      have hs : (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
          (3 : Fin 5) : GaussianInt) = ⟨0,1⟩ := rfl
      simp only []
      change f (⟨0,Y⟩ + (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
        (3 : Fin 5))) = (P5332T1ParentRows P 0 1 t).values (3 : Fin 5)
      rw [hs, rowValue3]
      change f (⟨0,Y⟩ + ⟨0,1⟩) = 0
      have hcoord : (⟨0,Y⟩ : GaussianInt) + ⟨0,1⟩ = ⟨0,Y+1⟩ := by ext <;> simp
      rw [hcoord]
      exact hu
    · have hu := outerLeft (Y-1) (by omega) (by omega)
      have hs : (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
          (4 : Fin 5) : GaussianInt) = -⟨0,1⟩ := rfl
      simp only []
      change f (⟨0,Y⟩ + (![0, 1, -1, (⟨0,1⟩ : GaussianInt), -⟨0,1⟩]
        (4 : Fin 5))) = (P5332T1ParentRows P 0 1 t).values (4 : Fin 5)
      rw [hs, rowValue4]
      change f (⟨0,Y⟩ + -⟨0,1⟩) = 0
      have hcoord : (⟨0,Y⟩ : GaussianInt) + -⟨0,1⟩ = ⟨0,Y-1⟩ := by
        ext <;> simp; ring
      rw [hcoord]
      exact hu
  · have hnot : (⟨0,Y⟩ : GaussianInt) -
        (P5332T1ParentRows P 0 1 0).companion ∉ FordVertexDomain P.q :=
      by
      rw [rowCompanion]
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub]
      have hbelow : Y < (P.q : Int) := by rw [hY]; omega
      intro h
      omega
    constructor
    · intro hm
      exact False.elim (hnot hm)
    · intro hh
      norm_num at hh

end ApollonianSuperharmonic

end
