/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.P5188T1CeilingShift

-- [TABLET NODE: P5332T1Parent2Rotation3Values]

/-!
# P5332T1Parent2Rotation3Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1Parent2Rotation3Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₂) (hAq : A.q = P.q₂)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 1 3 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 1 3 0).displacement) +
        (P5332T1ParentRows P 1 3 0).linear.re * y.re +
        (P5332T1ParentRows P 1 3 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 1 3 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 1 3 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₂ : Int) ∧
      x = (P5332T1ParentRows P 1 3 t).center ∧ B = 0 ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 3 t).values l) ∧
      (x - (P5332T1ParentRows P 1 3 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (3+1 : Nat)) := by
-- BODY
  classical
  have hqI : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqn : (P.q : Int) ≠ 0 := by omega
  have hrpos : 0 < P.q₁ := by
    by_contra hn
    have hz : P.q₁ = 0 := by omega
    have hd := P.det₁
    simp [hz] at hd
    have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
    have hqone : (P.q : Int) = 1 := Int.eq_one_of_dvd_one (by omega) hdv
    omega
  have hspos : 0 < P.q₂ := P.q₂_pos
  have hsum : (P.q₁ : Int) + (P.q₂ : Int) = (P.q : Int) := by
    exact_mod_cast P.sum_q.symm
  have hq2le : (P.q₂ : Int) ≤ P.q := by omega
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  -- The parameter record for the child is P itself; use its principal boundary law.
  have pboundary (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hb : u ≤ 1 ∨ (P.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q : Int)-1 ≤ v) :
      FordOdometer P ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q (by exact_mod_cast P.q_pos.ne') := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ v ∧ v ≤ (P.q : Int)) ∧
      ¬ (2 ≤ u ∧ u ≤ (P.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (P.q : Int)-2)
    omega
  have top (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) :
      FordOdometer P ⟨u,(P.q : Int)⟩ = P.p*u := by
    rw [pboundary u P.q hu huq (by omega) le_rfl (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*u*(P.q : Int)) = -(P.p*u)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ hqn]
    simp
  rcases x with ⟨X,Y⟩
  let x' : GaussianInt := ⟨X,Y⟩
  change 0 ≤ X ∧ X ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q at hx
  have hx'0 := hx'
  simp only [P5332T1ParentRows, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, FordVertexDomain, Set.mem_ofPred_eq,
    Zsqrtd.re_sub, Zsqrtd.im_sub, sub_zero] at hx'0
  change 0 ≤ X ∧ X ≤ (A.q : Int) ∧ 0 ≤ Y - P.q ∧ Y - P.q ≤ (A.q : Int) at hx'0
  have hXle : X ≤ (P.q₂ : Int) := by omega
  have hY : Y = P.q := by omega
  have htdef : 0 ≤ (P.q₂ : Int) - X := by omega
  let t : Int := (P.q₂ : Int) - X
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have htle : t ≤ P.q₂ := by dsimp [t]; omega
  have hstrict : t < P.q₂ := by
    have hbad := hstar (⟨2, by omega⟩ : Fin 5)
    dsimp at hbad
    have hdisp : (P5332T1ParentRows P 1 3 0).displacement = ⟨0,(P.q : Int)⟩ := by rfl
    have hAqI : (A.q : Int) = P.q₂ := by exact_mod_cast hAq
    by_contra hlt
    have heq : t = P.q₂ := by omega
    have hXzero : X = 0 := by dsimp [t] at heq; omega
    rcases hbad with h | h
    · simp [FordVertexDomain, hXzero] at h
    · simp [FordVertexDomain, hdisp, hXzero, hY] at h
  have hX : X = (P.q₂ : Int) - t := by dsimp [t]; omega
  have hcenter : x' = (P5332T1ParentRows P 1 3 t).center := by
    change x' = ⟨(P.q₂ : Int)-t,(P.q : Int)⟩
    apply Zsqrtd.ext
    · change X = (P.q₂ : Int)-t
      exact hX
    · change Y = (P.q : Int)
      exact hY
  have hcenterbase : f x' = P.p * X := by
    rw [hbase x' hx]
    change FordOdometer P ⟨X,Y⟩ = P.p * X
    rw [hY]
    exact top X (by omega) (by omega)
  have hcenterother : f x' = P.p * X + B := by
    have hxA : x' - (P5332T1ParentRows P 1 3 0).displacement ∈ FordVertexDomain A.q := hx'
    have hh := hother x' hxA
    dsimp [P5332T1ParentRows] at hh
    have harg : x' - ⟨0,(P.q : Int)⟩ = ⟨X,0⟩ := by
      ext <;> simp [x', hY]
    rw [harg] at hh
    have hz : FordOdometer A ⟨X,0⟩ = 0 := by
      have hab := (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1 A ⟨X,0⟩
      have hAqI : (A.q : Int) = P.q₂ := by exact_mod_cast hAq
      have hmem : ⟨X,0⟩ ∈ FordDoubledBoundary A.q := by
        change (0 ≤ X ∧ X ≤ (A.q : Int) ∧ 0 ≤ (0:Int) ∧ 0 ≤ (A.q : Int)) ∧ _
        have hn : ¬ (2 ≤ X ∧ X ≤ (A.q : Int)-2 ∧ 2 ≤ (0:Int) ∧ 0 ≤ (A.q : Int)-2) := by omega
        exact ⟨by omega, hn⟩
      have hzbd := hab hmem
      simp? [IntegerCeilDiv] at hzbd
      exact hzbd
    rw [hz] at hh
    norm_num at hh ⊢
    omega
  have hB : B = 0 := by omega
  have htopfun (u : Int) (hu : 0 ≤ u) (huq : u ≤ P.q) : f ⟨u,(P.q : Int)⟩ = P.p*u := by
    apply (hbase _ ⟨hu, huq, (show 0 ≤ (P.q : Int) by exact_mod_cast P.q_pos.le), le_rfl⟩).trans
    exact top u hu huq
  have vals : ∀ l : Fin 5,
      f (x' + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 3 t).values l := by
    intro l
    fin_cases l
    all_goals dsimp
    · rw [add_zero]
      change f x' = P.p*((P.q₂ : Int)-t)
      simpa [hX] using hcenterbase
    · change f (x'+1) = P.p*((P.q₂ : Int)-t+1)
      have heq : x'+1 = ⟨X+1,(P.q : Int)⟩ := by ext <;> simp [x', hY]
      rw [heq, htopfun (X+1) (by omega) (by omega), hX]
    · change f (x'-1) = P.p*((P.q₂ : Int)-t-1)
      have heq : x'-1 = ⟨X-1,(P.q : Int)⟩ := by ext <;> simp [x', hY]
      rw [heq, htopfun (X-1) (by omega) (by omega), hX]
    · change f (x'+⟨0,1⟩) = P.p*((P.q₂ : Int)-t) + IntegerCeilDiv
        (P.p₂*((P.q₂ : Int)-t)) P.q₂ (by exact_mod_cast P.q₂_pos.ne')
      have heq : x'+⟨0,1⟩ = (⟨X,Y+1⟩ : GaussianInt) := by ext <;> simp [x']
      rw [heq]
      have ha : (⟨X,Y+1⟩ : GaussianInt) - ⟨0,(P.q : Int)⟩ = ⟨X,1⟩ := by ext <;> simp [hY]
      have hAqI : (A.q : Int) = P.q₂ := by exact_mod_cast hAq
      have hpdom : ⟨X,1⟩ ∈ FordVertexDomain A.q := by
        change 0 ≤ X ∧ X ≤ (A.q : Int) ∧ 0 ≤ (1:Int) ∧ 1 ≤ (A.q : Int)
        omega
      have hd : (P5332T1ParentRows P 1 3 0).displacement = ⟨0,(P.q : Int)⟩ := by rfl
      have hv := hother ⟨X,Y+1⟩ (by simpa [hd, ha] using hpdom)
      dsimp [P5332T1ParentRows] at hv
      rw [ha, hB] at hv
      have hbnd := (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1 A ⟨X,1⟩
      have hbmem : ⟨X,1⟩ ∈ FordDoubledBoundary A.q := by
        change (0 ≤ X ∧ X ≤ (A.q : Int) ∧ 0 ≤ (1:Int) ∧ 1 ≤ (A.q : Int)) ∧ _
        have hn : ¬ (2 ≤ X ∧ X ≤ (A.q : Int)-2 ∧ 2 ≤ (1:Int) ∧ 1 ≤ (A.q : Int)-2) := by omega
        exact ⟨by omega, hn⟩
      have hceil := hbnd hbmem
      change FordOdometer A ⟨X,1⟩ = IntegerCeilDiv
        (A.p*X*1) (A.q : Int) (by exact_mod_cast A.q_pos.ne') at hceil
      have hceil' : FordOdometer A ⟨X,1⟩ = IntegerCeilDiv
          (P.p₂*X*1) (P.q₂ : Int) (by exact_mod_cast P.q₂_pos.ne') := by
        simpa only [hAp, hAq] using hceil
      rw [hceil'] at hv
      rw [← hX]
      simpa [IntegerCeilDiv, add_comm] using hv
    · change f (x'-⟨0,1⟩) = P.p*((P.q₂ : Int)-t) -
        P.p*((P.q₂ : Int)-t)/P.q
      have heq : x'-⟨0,1⟩ = (⟨X,Y-1⟩ : GaussianInt) := by ext <;> simp [x']
      rw [heq, hY]
      have hu : 0 ≤ X := by omega
      have huq : X ≤ P.q := by omega
      have hdom : (⟨X,(P.q : Int)-1⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
        change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ (P.q : Int)-1 ∧ (P.q : Int)-1 ≤ (P.q : Int)
        omega
      rw [hbase _ hdom]
      rw [pboundary X ((P.q : Int)-1) hu (by omega) (by omega) (by omega) (by omega)]
      rw [hX]
      have hceil := P5188T1CeilingShift (-(P.p*((P.q₂ : Int)-t)))
        (P.p*((P.q₂ : Int)-t)) (P.q : Int) hqn
      calc
        IntegerCeilDiv (P.p*((P.q₂ : Int)-t)*((P.q : Int)-1)) (P.q : Int) (by exact_mod_cast
            P.q_pos.ne') =
            IntegerCeilDiv (-(P.p*((P.q₂ : Int)-t)) + P.p*((P.q₂ : Int)-t)*(P.q : Int))
              (P.q : Int) (by exact_mod_cast P.q_pos.ne') := by congr 1; ring
        _ = IntegerCeilDiv (-(P.p*((P.q₂ : Int)-t))) (P.q : Int) (by exact_mod_cast P.q_pos.ne') +
            P.p*((P.q₂ : Int)-t) := hceil
        _ = P.p*((P.q₂ : Int)-t) - P.p*((P.q₂ : Int)-t)/(P.q : Int) := by
          simp [IntegerCeilDiv]
          ring
  refine ⟨t, ht0, hstrict, hcenter, hB, vals, ?_⟩
  constructor
  · intro hmem
    simp only [P5332T1ParentRows, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, FordVertexDomain, Set.mem_ofPred_eq,
      Zsqrtd.re_sub, Zsqrtd.im_sub, sub_zero] at hmem
    have htzero : t = 0 := by rw [hX] at hmem; omega
    exact ⟨htzero, ⟨2, by norm_num⟩⟩
  · rintro ⟨ht, _⟩
    have hw : (P5332T1ParentRows P 1 3 0).companion = ⟨(P.q₂ : Int),(P.q : Int)⟩ := by rfl
    rw [hw]
    change 0 ≤ X-P.q₂ ∧ X-P.q₂ ≤ P.q ∧ 0 ≤ Y-P.q ∧ Y-P.q ≤ P.q
    have hXzero : X = P.q₂ := by rw [hX, ht]; ring
    rw [hXzero, hY]
    norm_num

end ApollonianSuperharmonic

end
