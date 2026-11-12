/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent1Rotation3Values]

/-!
# P5332T1Parent1Rotation3Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1Parent1Rotation3Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₁) (hAq : A.q = P.q₁)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 0 3 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 0 3 0).displacement) +
        (P5332T1ParentRows P 0 3 0).linear.re * y.re +
        (P5332T1ParentRows P 0 3 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 0 3 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 0 3 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₁ : Int) ∧
      x = (P5332T1ParentRows P 0 3 t).center ∧ B = 0 ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 0 3 t).values l) ∧
      (x - (P5332T1ParentRows P 0 3 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (3+0 : Nat)) := by
-- BODY
  classical
  have hq1_lt : P.q₁ < P.q := P.q₁_lt
  have hq1_pos : 0 < P.q₁ := by
    by_contra h
    have hz : P.q₁ = 0 := by omega
    have : P.p₁ * (P.q : Int) = 1 := by
      simpa [hz] using P.det₁
    have hqpos : 1 < (P.q : Int) := by exact_mod_cast hq
    by_cases hp : P.p₁ ≤ 0
    · nlinarith
    · have hp1 : 1 ≤ P.p₁ := by omega
      have hprod : 0 ≤ (P.p₁ - 1) * ((P.q : Int) - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  have hA : (A.q : Int) = (P.q₁ : Int) := by exact_mod_cast hAq
  rcases x with ⟨X,Y⟩
  change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int) at hx
  have hx'0 := hx'
  dsimp [P5332T1ParentRows] at hx'0
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
    sub_zero] at hx'0
  change 0 ≤ X - P.q ∧ X - P.q ≤ (A.q : Int) ∧
    0 ≤ Y ∧ Y ≤ (A.q : Int) at hx'0
  have hX : X = P.q := by omega
  subst X
  have hYlow : 0 ≤ Y := hx.2.2.1
  have hYhigh : Y ≤ P.q₁ := by simpa [hA] using hx'0.2.2.2
  have hsouth := hstar 4
  dsimp [P5332T1ParentRows] at hsouth
  have hYpos : 1 ≤ Y := by
    by_contra hy
    have hy0 : Y = 0 := by omega
    subst Y
    norm_num [FordVertexDomain, P5332T1ParentRows] at hsouth
  let t : Int := P.q₁ - Y
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have htr : t < (P.q₁ : Int) := by dsimp [t]; omega
  have hY : Y = P.q₁ - t := by dsimp [t]; omega
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundary (R : FordFareyParameter) (u v : Int)
      (hu : 0 ≤ u) (huq : u ≤ R.q) (hv : 0 ≤ v) (hvq : v ≤ R.q)
      (hs : u ≤ 1 ∨ (R.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (R.q : Int)-1 ≤ v) :
      FordOdometer R ⟨u,v⟩ = IntegerCeilDiv (R.p*u*v) R.q (by
        have hR : 0 < (R.q : Int) := by exact_mod_cast R.q_pos
        omega) := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (R.q : Int) ∧ 0 ≤ v ∧ v ≤ (R.q : Int)) ∧
      ¬(2 ≤ u ∧ u ≤ (R.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (R.q : Int)-2)
    omega
  have rightChild (v : Int) (hv : 0 ≤ v) (hvq : v ≤ P.q) :
      FordOdometer P ⟨(P.q : Int),v⟩ = P.p*v := by
    rw [boundary P _ _ (by omega) (by omega) hv hvq (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*(P.q : Int)*v) = -(P.p*v)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ (by omega)]
    ring
  have leftParent (v : Int) (hv : 0 ≤ v) (hvq : v ≤ P.q₁) :
      FordOdometer A ⟨0,v⟩ = 0 := by
    have hvqA : v ≤ A.q := by simpa [hA] using hvq
    rw [boundary A _ _ (by omega) (by omega) hv hvqA (Or.inl (by omega))]
    simp [IntegerCeilDiv]
  have hcenterBase := hbase ⟨(P.q : Int),Y⟩ (by
    change 0 ≤ (P.q : Int) ∧ (P.q : Int) ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q
    omega)
  have harg : (⟨(P.q : Int),Y⟩ : GaussianInt) - ⟨(P.q : Int),0⟩ = ⟨0,Y⟩ := by
    ext <;> simp
  have hcenterOther := hother ⟨(P.q : Int),Y⟩ (by
    dsimp [P5332T1ParentRows]
    rw [harg]
    change 0 ≤ (0 : Int) ∧ (0 : Int) ≤ (A.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (A.q : Int)
    exact ⟨by omega, by omega, hYlow, by simpa [hA] using hYhigh⟩)
  dsimp [P5332T1ParentRows] at hcenterOther
  rw [harg, leftParent Y hYlow hYhigh] at hcenterOther
  rw [rightChild Y hYlow (by omega)] at hcenterBase
  simp only [zero_mul, zero_add, add_zero] at hcenterOther
  have hB : B = 0 := by omega
  have hB0 := hB
  subst B
  have valueR (z : Int) (hz : 0 ≤ z) (hzq : z ≤ P.q) :
      f ⟨(P.q : Int),z⟩ = P.p*z := by
    exact (hbase ⟨(P.q : Int),z⟩ (by
      change 0 ≤ (P.q : Int) ∧ (P.q : Int) ≤ P.q ∧ 0 ≤ z ∧ z ≤ P.q
      omega)).trans (rightChild z hz hzq)
  have valueE : f ((⟨(P.q : Int),Y⟩ : GaussianInt)+1) =
      P.p*Y + IntegerCeilDiv (P.p₁*Y) P.q₁ (by omega) := by
    have arg : (⟨(P.q : Int),Y⟩ : GaussianInt)+1-⟨(P.q : Int),0⟩ = ⟨1,Y⟩ := by
      ext <;> simp
    have he := hother (⟨(P.q : Int),Y⟩+1) (by
      dsimp [P5332T1ParentRows]
      rw [arg]
      change 0 ≤ (1 : Int) ∧ (1 : Int) ≤ (A.q : Int) ∧
        0 ≤ Y ∧ Y ≤ (A.q : Int)
      have hrA : 0 < (A.q : Int) := by rw [hA]; exact_mod_cast hq1_pos
      exact ⟨by omega, by omega, hYlow, by simpa [hA] using hYhigh⟩)
    dsimp [P5332T1ParentRows] at he
    rw [arg, boundary A 1 Y (by omega) (by omega) hYlow
      (by simpa [hA] using hYhigh) (Or.inl (by omega))] at he
    simp only [zero_mul, add_zero] at he
    have he' : f ((⟨(P.q : Int),Y⟩ : GaussianInt)+1) =
        P.p*Y + IntegerCeilDiv (P.p₁*Y) P.q₁ (by omega) := by
      simpa [hAp, hAq, one_mul, mul_one, add_comm] using he
    exact he'
  have valueW : f ((⟨(P.q : Int),Y⟩ : GaussianInt)-1) =
      P.p*Y - P.p*Y/(P.q : Int) := by
    have arg : (⟨(P.q : Int),Y⟩ : GaussianInt)-1 = ⟨(P.q : Int)-1,Y⟩ := by
      ext <;> simp
    rw [arg, hbase (⟨(P.q : Int)-1,Y⟩ : GaussianInt) (by
      change 0 ≤ (P.q : Int)-1 ∧ (P.q : Int)-1 ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q
      omega)]
    rw [boundary P ((P.q : Int)-1) Y (by omega) (by omega) hYlow (by omega)
      (Or.inr (Or.inl (by omega)))]
    have hnum : P.p*((P.q : Int)-1)*Y = -(P.p*Y)+(P.p*Y)*(P.q : Int) := by ring
    rw [hnum, P5188T1CeilingShift (-(P.p*Y)) (P.p*Y) P.q (by omega)]
    simp [IntegerCeilDiv]
    ring
  refine ⟨t, ht0, htr, ?_, hB0, ?_, ?_⟩
  · dsimp [P5332T1ParentRows]
    ext <;> simp [hY]
  · intro l
    fin_cases l
    · simpa [P5332T1ParentRows, hY] using valueR Y hYlow (by omega)
    · simpa [P5332T1ParentRows, hY, IntegerCeilDiv] using valueE
    · norm_num
      change f ((⟨(P.q : Int),Y⟩ : GaussianInt)-1) = _
      simpa [P5332T1ParentRows, hY] using valueW
    · norm_num
      simpa [P5332T1ParentRows, hY] using valueR (Y+1) (by omega) (by omega)
    · have hs : (⟨(P.q : Int),Y⟩ : GaussianInt)-⟨0,1⟩ = ⟨(P.q : Int),Y-1⟩ := by
        ext <;> simp
      norm_num
      change f ((⟨(P.q : Int),Y⟩ : GaussianInt)-⟨0,1⟩) = _
      rw [hs]
      simpa [P5332T1ParentRows, hY] using valueR (Y-1) (by omega) (by omega)
  · constructor
    · intro hmem
      dsimp [P5332T1ParentRows] at hmem
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hmem
      omega
    · intro h
      rcases h with ⟨_, hEven⟩
      rcases hEven with ⟨n, hn⟩
      have : False := by omega
      exact this.elim

end ApollonianSuperharmonic

end
