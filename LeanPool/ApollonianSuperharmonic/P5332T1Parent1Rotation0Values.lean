/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent1Rotation0Values]

/-!
# P5332T1Parent1Rotation0Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1Parent1Rotation0Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₁) (hAq : A.q = P.q₁)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 0 0 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 0 0 0).displacement) +
        (P5332T1ParentRows P 0 0 0).linear.re * y.re +
        (P5332T1ParentRows P 0 0 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 0 0 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 0 0 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₁ : Int) ∧
      x = (P5332T1ParentRows P 0 0 t).center ∧ B = -P.p₂ * (P.q : Int) ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 0 0 t).values l) ∧
      (x - (P5332T1ParentRows P 0 0 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (0+0 : Nat)) := by
-- BODY
  classical
  have hqn : (P.q : Int) ≠ 0 := by omega
  have par := P5130T5ParentArithmetic P hq
  have hr : 0 < (P.q₁ : Int) := by exact_mod_cast par.1
  have hrs : (P.q₁ : Int) + P.q₂ = P.q := by exact_mod_cast P.sum_q.symm
  have hpb : P.p₂ * P.q - (P.q₂ : Int) * P.p = -1 := P.det₂
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (N : FordFareyParameter) (r t : Int)
      (hr0 : 0 ≤ r) (hrq : r ≤ (N.q : Int))
      (ht0 : 0 ≤ t) (htq : t ≤ (N.q : Int))
      (hsb : r ≤ 1 ∨ (N.q : Int)-1 ≤ r ∨ t ≤ 1 ∨ (N.q : Int)-1 ≤ t) :
      FordOdometer N ⟨r,t⟩ = IntegerCeilDiv (N.p*r*t) N.q (by exact_mod_cast N.q_pos.ne') := by
    apply laws.2.1
    change (0 ≤ r ∧ r ≤ (N.q : Int) ∧ 0 ≤ t ∧ t ≤ (N.q : Int)) ∧
      ¬(2 ≤ r ∧ r ≤ (N.q : Int)-2 ∧ 2 ≤ t ∧ t ≤ (N.q : Int)-2)
    omega
  rcases x with ⟨X,Y⟩
  have hx0 := hx
  change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int) at hx0
  have hchild := hx'
  change 0 ≤ X-(P.q₂ : Int) ∧ X-(P.q₂ : Int) ≤ (A.q : Int) ∧
    0 ≤ Y-(P.q : Int) ∧ Y-(P.q : Int) ≤ (A.q : Int) at hchild
  have hAq : (A.q : Int) = P.q₁ := by exact_mod_cast hAq
  have hAp : A.p = P.p₁ := hAp
  have hY : Y = (P.q : Int) := by
    have := hx0.2.2.2
    have := hchild.2.2.2
    omega
  let t : Int := X - (P.q₂ : Int)
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have hstarTop := hstar 3
  have hstarRight := hstar 1
  dsimp [P5332T1ParentRows] at hstarTop hstarRight
  norm_num [FordVertexDomain] at hstarTop hstarRight
  have htlt : t < (P.q₁ : Int) := by
    rcases hstarTop with h | h
    · have := h.2.2.2
      dsimp [t] at *
      omega
    · have := h.2.2.2
      dsimp [t] at *
      omega
  have hcenter : (⟨X,Y⟩ : GaussianInt) = (P5332T1ParentRows P 0 0 t).center := by
    ext <;> simp [P5332T1ParentRows, t, hY]
  have hcenter1 := hother (⟨X,Y⟩ : GaussianInt) (by
    change 0 ≤ X-(P.q₂ : Int) ∧ X-(P.q₂ : Int) ≤ (A.q : Int) ∧
      0 ≤ Y-(P.q : Int) ∧ Y-(P.q : Int) ≤ (A.q : Int)
    omega)
  have top (N : FordFareyParameter) (u : Int)
      (hu : 0 ≤ u) (huq : u ≤ (N.q : Int)) :
      FordOdometer N ⟨u,(N.q : Int)⟩ = N.p*u := by
    rw [boundary N u (N.q : Int) hu huq (by omega) (by omega) (by omega)]
    dsimp [IntegerCeilDiv]
    have he : -(N.p*u*(N.q : Int)) = (-N.p*u)*(N.q : Int) := by ring
    rw [he, Int.mul_ediv_cancel _ (by exact_mod_cast N.q_pos.ne')]
    ring
  have bottom (N : FordFareyParameter) (u : Int)
      (hu : 0 ≤ u) (huq : u ≤ (N.q : Int)) :
      FordOdometer N ⟨u,0⟩ = 0 := by
    rw [boundary N u 0 hu huq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have centerarg : (⟨X,Y⟩ : GaussianInt) -
      (P5332T1ParentRows P 0 0 0).displacement = ⟨t,0⟩ := by
    ext <;> simp [P5332T1ParentRows, t, hY]
  have hcenter0' : f (⟨X,Y⟩ : GaussianInt) = P.p*(P.q₂ + t) := by
    rw [hbase _ hx]
    have hc : (⟨X,Y⟩ : GaussianInt) = ⟨P.q₂+t,(P.q : Int)⟩ := by
      ext <;> simp [t, hY]
    rw [hc]
    exact top P _ (by omega) (by omega)
  have hcenter1' : f (⟨X,Y⟩ : GaussianInt) =
      0 + P.p*(P.q₂+t) + P.p₂*(P.q : Int) + B := by
    rw [hother _ (by
      change 0 ≤ X-(P.q₂ : Int) ∧ X-(P.q₂ : Int) ≤ (A.q : Int) ∧
        0 ≤ Y-(P.q : Int) ∧ Y-(P.q : Int) ≤ (A.q : Int)
      omega)]
    rw [centerarg]
    rw [bottom A t (by omega) (by omega)]
    simp [P5332T1ParentRows, hY, t]
  have hB : B = -P.p₂*(P.q : Int) := by
    rw [hcenter0'] at hcenter1'
    nlinarith [hcenter1']
  subst B
  let u : Int := P.q₂ + t
  have hu0 : 0 ≤ u := by dsimp [u]; omega
  have huq : u + 1 ≤ (P.q : Int) := by dsimp [u]; omega
  have huq' : u - 1 ≥ 0 := by dsimp [u]; omega
  have hxcoord : (⟨X,Y⟩ : GaussianInt) = ⟨u,(P.q : Int)⟩ := by
    ext <;> simp [u, t, hY]
  have topValue (v : Int) (hv : 0 ≤ v) (hvq : v ≤ (P.q : Int)) :
      f ⟨v,(P.q : Int)⟩ = P.p*v := by
    apply (hbase _ ?_).trans
    · exact top P v hv hvq
    · change 0 ≤ v ∧ v ≤ (P.q : Int) ∧ 0 ≤ (P.q : Int) ∧
        (P.q : Int) ≤ (P.q : Int)
      omega
  have hval0 : f (⟨X,Y⟩ : GaussianInt) = P.p*u := by
    rw [hxcoord]
    exact topValue u hu0 (by omega)
  have hval1 : f ((⟨X,Y⟩ : GaussianInt) + 1) = P.p*(u+1) := by
    have he : (⟨X,Y⟩ : GaussianInt)+1 = ⟨u+1,(P.q : Int)⟩ := by
      ext <;> simp [hxcoord]
    rw [he]
    exact topValue (u+1) (by omega) huq
  have hval2 : f ((⟨X,Y⟩ : GaussianInt) - 1) = P.p*(u-1) := by
    have he : (⟨X,Y⟩ : GaussianInt)-1 = ⟨u-1,(P.q : Int)⟩ := by
      ext <;> simp [hxcoord]
    rw [he]
    exact topValue (u-1) huq' (by omega)
  have argN : (⟨X,Y⟩ : GaussianInt) + ⟨0,1⟩ -
      (P5332T1ParentRows P 0 0 0).displacement = ⟨t,1⟩ := by
    ext <;> simp [P5332T1ParentRows, t, hY]
  have hq1n : (P.q₁ : Int) ≠ 0 := ne_of_gt hr
  have hval3 : f ((⟨X,Y⟩ : GaussianInt) + ⟨0,1⟩) =
      P.p*u + P.p₂ + IntegerCeilDiv (P.p₁*t) (P.q₁ : Int) hq1n := by
    rw [hother _ (by
      rw [argN]
      change 0 ≤ t ∧ t ≤ (A.q : Int) ∧ 0 ≤ (1 : Int) ∧ 1 ≤ (A.q : Int)
      rw [hAq]
      omega)]
    rw [argN, boundary A t 1 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [P5332T1ParentRows, u, t, hY, hAp, hAq, IntegerCeilDiv]
    ring
  have hpu : P.p*u = P.p₂*(P.q : Int) + (P.p*t+1) := by
    have hps : P.p*(P.q₂ : Int) = P.p₂*(P.q : Int)+1 := by
      linear_combination -hpb
    calc
      P.p*u = P.p*((P.q₂ : Int)+t) := rfl
      _ = P.p*(P.q₂ : Int)+P.p*t := by ring
      _ = P.p₂*(P.q : Int)+(P.p*t+1) := by rw [hps]; ring
  have hceilNeg : IntegerCeilDiv (-(P.p*u)) P.q hqn =
      -P.p₂ - ((P.p*t+1)/(P.q : Int)) := by
    have hn : -(P.p*u) = -(P.p*t+1) + (-P.p₂)*(P.q : Int) := by
      linear_combination -hpu
    rw [hn, P5188T1CeilingShift _ _ _ hqn]
    simp [IntegerCeilDiv]
    ring
  have hval4 : f ((⟨X,Y⟩ : GaussianInt) - ⟨0,1⟩) =
      P.p*u - P.p₂ - ((P.p*t+1)/(P.q : Int)) := by
    have he : (⟨X,Y⟩ : GaussianInt)-⟨0,1⟩ = ⟨u,(P.q : Int)-1⟩ := by
      ext <;> simp [hxcoord]
    rw [he]
    have hbnd := boundary P u ((P.q : Int)-1) hu0 (by omega) (by omega) (by omega) (by omega)
    rw [hbase _ (by
      change 0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ (P.q : Int)-1 ∧
        (P.q : Int)-1 ≤ (P.q : Int)
      omega), hbnd]
    have hnum : P.p*u*((P.q : Int)-1) = -(P.p*u) + (P.p*u)*(P.q : Int) := by ring
    rw [hnum, P5188T1CeilingShift _ _ _ hqn, hceilNeg]
    ring
  refine ⟨t, ht0, htlt, hcenter, rfl, ?_, ?_⟩
  · intro l
    fin_cases l
    · simpa [P5332T1ParentRows, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.tail_cons, u] using hval0
    · simpa [P5332T1ParentRows, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, u] using hval1
    · simpa [P5332T1ParentRows, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, u, sub_eq_add_neg] using hval2
    · simpa [P5332T1ParentRows, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, u, IntegerCeilDiv] using hval3
    · simpa [P5332T1ParentRows, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, u, sub_eq_add_neg] using hval4
  · constructor
    · intro hm
      have hcomp : (⟨X,Y⟩ : GaussianInt) -
          (P5332T1ParentRows P 0 0 0).companion = ⟨(P.q : Int)+t,0⟩ := by
        ext <;> simp [P5332T1ParentRows, t, hY]; omega
      rw [hcomp] at hm
      change 0 ≤ (P.q : Int)+t ∧ (P.q : Int)+t ≤ (P.q : Int) ∧
        0 ≤ (0 : Int) ∧ (0 : Int) ≤ (P.q : Int) at hm
      have htzero : t = 0 := by omega
      exact ⟨htzero, by norm_num⟩
    · rintro ⟨htzero, _⟩
      have hcomp : (⟨X,Y⟩ : GaussianInt) -
          (P5332T1ParentRows P 0 0 0).companion = ⟨(P.q : Int),0⟩ := by
        ext <;> simp [P5332T1ParentRows, hY]; omega
      rw [hcomp]
      change 0 ≤ (P.q : Int) ∧ (P.q : Int) ≤ (P.q : Int) ∧
        0 ≤ (0 : Int) ∧ (0 : Int) ≤ (P.q : Int)
      exact ⟨by omega, le_rfl, le_rfl, by omega⟩

end ApollonianSuperharmonic

end
