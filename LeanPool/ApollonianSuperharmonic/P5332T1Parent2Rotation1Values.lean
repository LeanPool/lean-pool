/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent2Rotation1Values]

/-!
# P5332T1Parent2Rotation1Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParentTwoRotationOneProof

private theorem hrpos :
    ∀ (P : FordFareyParameter), (1 : ℕ) < P.q → 0 < P.q₁ := by
  classical
  intro P hq
  by_contra h; have hr0 : P.q₁ = 0 := by omega
  have := P.det₁
  rw [hr0] at this
  have hpq : P.p₁ * (P.q : Int) = 1 := by omega
  have hp1 : P.q = 1 := by
    have hdvd : (P.q : Int) ∣ 1 := ⟨P.p₁, by nlinarith⟩
    have hle : (P.q : Int) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    have : P.q ≤ 1 := by exact_mod_cast hle
    omega
  omega

private theorem hcenterA :
    ∀ (P : FordFareyParameter),
      ∀ (A : FordFareyParameter),
        A.p = P.p₂ →
          A.q = P.q₂ →
            0 < P.q₂ →
              (∀ (r : Int),
                  ∀ (z : Int),
                    0 ≤ r →
                      r ≤ A.q →
                        0 ≤ z →
                          z ≤ A.q →
                            r ≤ 1 ∨ (A.q : Int) - 1 ≤ r ∨ z ≤ 1 ∨ (A.q : Int) - 1 ≤ z →
                            FordOdometer A ⟨r, z⟩ =
                            IntegerCeilDiv (A.p * r * z) A.q
                            (by exact_mod_cast A.q_pos.ne')) →
                ∀ (X : ℤ),
                  (A.q : Int) = P.q₂ →
                    let t : Int := X - (P.q₁ : Int)
                    0 ≤ t → t < P.q₂ → FordOdometer A ⟨t, P.q₂⟩ = P.p₂ * t := by
  classical
  intro P A hAp hAq hspos boundaryA X hAqInt t ht0 hstrict
  have hbA := boundaryA t P.q₂ ht0 (by omega) (by omega) (by omega) (by omega)
  have hbA' : FordOdometer A ⟨t,P.q₂⟩ =
      IntegerCeilDiv (P.p₂*t*P.q₂) P.q₂ (by omega) := by
    simpa [hAp, hAqInt] using hbA
  rw [hbA']
  simp only [IntegerCeilDiv]
  rw [show -(P.p₂*t*P.q₂) = (-(P.p₂*t))*P.q₂ by ring,
    Int.mul_ediv_cancel _ (by omega)]
  ring

private theorem southVal :
    ∀ (P : FordFareyParameter),
      ∀ (A : FordFareyParameter),
        A.p = P.p₂ →
          A.q = P.q₂ →
            ∀ (f : IntegerLatticeFunction),
              0 < P.q₂ →
                (∀ (r : Int),
                    ∀ (z : Int),
                      0 ≤ r →
                        r ≤ A.q →
                          0 ≤ z →
                            z ≤ A.q →
                            r ≤ 1 ∨ (A.q : Int) - 1 ≤ r ∨ z ≤ 1 ∨ (A.q : Int) - 1 ≤ z →
                            FordOdometer A ⟨r, z⟩ =
                            IntegerCeilDiv (A.p * r * z) A.q
                            (by exact_mod_cast A.q_pos.ne')) →
                  ∀ (X : ℤ),
                    ∀ (Y : ℤ),
                      (0 : ℤ) ≤ X - (↑P.q₁ : ℤ) ∧
                          X - (↑P.q₁ : ℤ) ≤ (↑A.q : ℤ) ∧
                            (0 : ℤ) ≤ Y - -(↑P.q₂ : ℤ) ∧ Y - -(↑P.q₂ : ℤ) ≤ (↑A.q : ℤ) →
                        (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (1 : Fin (4 : ℕ))
                            (0 : ℤ)).displacement =
                            ⟨(↑P.q₁ : ℤ), -(↑P.q₂ : ℤ)⟩ →
                          (A.q : Int) = P.q₂ →
                            Y = 0 →
                            let t : Int := X - (P.q₁ : Int)
                          0 ≤ t →
                            X = P.q₁ + t →
                            t < P.q₂ →
                            (P5332T1ParentRows P 1 1 0).linear = ⟨-P.p₂, P.p₁⟩ →
                            (∀ (y : GaussianInt),
                            y -
                            (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (1 : Fin (4 : ℕ))
                            (0 : ℤ)).displacement ∈
                            FordVertexDomain A.q →
                            f y =
                            FordOdometer A
                            (y -
                            (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (1 : Fin (4 : ℕ))
                            (0 : ℤ)).displacement) +
                            (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (1 : Fin (4 : ℕ))
                            (0 : ℤ)).linear.re *
                            y.re +
                            (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (1 : Fin (4 : ℕ))
                            (0 : ℤ)).linear.im *
                            y.im +
                            P.p₂ * (↑P.q₁ : ℤ)) →
                            (⟨X, Y⟩ : GaussianInt) - ⟨0, 1⟩ = ⟨X, Y - 1⟩ →
                            f (⟨X, Y⟩ - ⟨0, 1⟩) = -P.p₁ - P.p₂ * t / P.q₂ := by
  classical
  intro P A hAp hAq f hspos boundaryA X Y hx' hdis hAqInt hy t ht0 hX hstrict hrow0 hother
      southArg
  have hsource : (⟨X,Y⟩-⟨0,1⟩ : GaussianInt) = ⟨P.q₁+t,-1⟩ := by
    rw [southArg, hX, hy]
    ext <;> simp
  have yarg : (⟨X,Y⟩-⟨0,1⟩ : GaussianInt) -
      (P5332T1ParentRows P 1 1 0).displacement = ⟨t,P.q₂-1⟩ := by
    rw [hsource, hdis]
    ext <;> simp [t]; omega
  have hychild : (⟨t,P.q₂-1⟩ : GaussianInt) ∈ FordVertexDomain A.q := by
    simp only [FordVertexDomain, Set.mem_ofPred_eq]
    omega
  have yarg2 : (⟨P.q₁+t,-1⟩ : GaussianInt) -
      (P5332T1ParentRows P 1 1 0).displacement = ⟨t,P.q₂-1⟩ := by
    rw [hdis]
    ext <;> simp [t]; omega
  have hsouth := hother ⟨P.q₁+t,-1⟩ (by rw [yarg2]; exact hychild)
  rw [yarg2] at hsouth
  simp only [hrow0] at hsouth
  have hbS : FordOdometer A ⟨t,P.q₂-1⟩ =
      IntegerCeilDiv (P.p₂*t*(P.q₂-1)) P.q₂ (by omega) := by
    have htmp := boundaryA t (P.q₂-1) ht0 (by omega) (by omega) (by omega) (by omega)
    simpa [hAp, hAqInt] using htmp
  rw [hbS] at hsouth
  have hceil : IntegerCeilDiv (P.p₂*t*(P.q₂-1)) P.q₂ (by omega) =
      P.p₂*t - P.p₂*t / P.q₂ := by
    dsimp [IntegerCeilDiv]
    have hh : -(P.p₂*t*(P.q₂-1)) = P.p₂*t + P.q₂ * (-(P.p₂*t)) := by ring
    rw [hh, Int.add_mul_ediv_left _ _ (by omega)]
    ring
  rw [hceil] at hsouth
  norm_num at hsouth
  rw [← hsource] at hsouth
  nlinarith

private theorem hnorth :
    ∀ (P : FordFareyParameter), ∀ (f : IntegerLatticeFunction), ∀ (hqn : (P.q : Int) ≠ 0), (P.p₁
        * (P.q : Int) - (P.q₁ : Int) * P.p = 1) → (∀ (X : ℤ), ∀ (Y : ℤ), (Y = 0) → (
    let t : Int := X-(P.q₁ : Int)
    (X = P.q₁ + t) → (((⟨X,Y⟩ : GaussianInt)+⟨0,1⟩ = ⟨X,Y+1⟩) → ((f (⟨X,Y⟩+⟨0,1⟩) =
        IntegerCeilDiv (P.p*X) P.q hqn) → (f (⟨X,Y⟩+⟨0,1⟩) = P.p₁ + IntegerCeilDiv (P.p*t-1) P.q
        hqn))))) := by
  classical
  intro P f hqn hdet1 X Y hy t hX northArg northVal
  have hraw := northVal
  rw [hX, hy] at hraw
  have hpq1 : P.p * (P.q₁ : Int) = P.p₁ * P.q - 1 := by
    linear_combination -hdet1
  have hshift : P.p*(P.q₁+t) = P.p₁*P.q + (P.p*t-1) := by
    rw [Int.mul_add, hpq1]
    ring
  rw [hshift] at hraw
  rw [show P.p₁*P.q + (P.p*t-1) = (P.p*t-1) + P.p₁*P.q by ring] at hraw
  rw [P5188T1CeilingShift (P.p*t-1) P.p₁ P.q hqn] at hraw
  rw [northArg, hX, hy]
  simpa [add_comm] using hraw

end ParentTwoRotationOneProof

theorem P5332T1Parent2Rotation1Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₂) (hAq : A.q = P.q₂)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 1 1 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 1 1 0).displacement) +
        (P5332T1ParentRows P 1 1 0).linear.re * y.re +
        (P5332T1ParentRows P 1 1 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 1 1 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 1 1 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₂ : Int) ∧
      x = (P5332T1ParentRows P 1 1 t).center ∧ B = P.p₂ * (P.q₁ : Int) ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 1 t).values l) ∧
      (x - (P5332T1ParentRows P 1 1 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (1+1 : Nat)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hqn : (P.q : Int) ≠ 0 := by omega
  have hrpos : 0 < P.q₁ := ParentTwoRotationOneProof.hrpos P hq
  have hspos : 0 < P.q₂ := P.q₂_pos
  have hsumq : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by exact_mod_cast P.sum_q
  have hpairs : P.p = P.p₁ + P.p₂ := P.sum_p
  have hdet1 : P.p₁ * (P.q : Int) - (P.q₁ : Int) * P.p = 1 := P.det₁
  have hdet2 : P.p₂ * (P.q : Int) - (P.q₂ : Int) * P.p = -1 := P.det₂
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have boundaryP (r z : Int) (hr : 0 ≤ r) (hrq : r ≤ P.q)
      (hz : 0 ≤ z) (hzq : z ≤ P.q)
      (hs : r ≤ 1 ∨ (P.q : Int)-1 ≤ r ∨ z ≤ 1 ∨ (P.q : Int)-1 ≤ z) :
      FordOdometer P ⟨r,z⟩ = IntegerCeilDiv (P.p*r*z) P.q hqn := by
    apply laws.2.1
    change (0 ≤ r ∧ r ≤ (P.q : Int) ∧ 0 ≤ z ∧ z ≤ (P.q : Int)) ∧
      ¬ (2 ≤ r ∧ r ≤ (P.q : Int)-2 ∧ 2 ≤ z ∧ z ≤ (P.q : Int)-2)
    omega
  have boundaryA (r z : Int) (hr : 0 ≤ r) (hrq : r ≤ A.q)
      (hz : 0 ≤ z) (hzq : z ≤ A.q)
      (hs : r ≤ 1 ∨ (A.q : Int)-1 ≤ r ∨ z ≤ 1 ∨ (A.q : Int)-1 ≤ z) :
      FordOdometer A ⟨r,z⟩ = IntegerCeilDiv (A.p*r*z) A.q (by exact_mod_cast A.q_pos.ne') := by
    apply laws.2.1
    change (0 ≤ r ∧ r ≤ (A.q : Int) ∧ 0 ≤ z ∧ z ≤ (A.q : Int)) ∧
      ¬ (2 ≤ r ∧ r ≤ (A.q : Int)-2 ∧ 2 ≤ z ∧ z ≤ (A.q : Int)-2)
    omega
  have hr : 0 < (P.q₁ : Int) := by omega
  have hs : 0 < (P.q₂ : Int) := by exact_mod_cast hspos
  have hqsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := hsumq
  rcases x with ⟨X,Y⟩
  have hxcoord := hx
  change 0 ≤ X ∧ X ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ (P.q : Int) at hxcoord
  have hdis : (P5332T1ParentRows P 1 1 0).displacement = ⟨(P.q₁ : Int), -(P.q₂ : Int)⟩ := by
    rfl
  rw [hdis] at hx'
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
    ] at hx'
  have hAqInt : (A.q : Int) = P.q₂ := by exact_mod_cast hAq
  have hy : Y = 0 := by omega
  have hXlo : (P.q₁ : Int) ≤ X := by omega
  have hXhi : X ≤ (P.q : Int) := hxcoord.2.1
  have htdef : 0 ≤ X-(P.q₁ : Int) ∧ X-(P.q₁ : Int) ≤ P.q₂ := by omega
  let t : Int := X-(P.q₁ : Int)
  have ht0 : 0 ≤ t := htdef.1
  have htle : t ≤ P.q₂ := htdef.2
  have hX : X = P.q₁ + t := by dsimp [t]; omega
  have hxrow : (⟨X,Y⟩ : GaussianInt) = (P5332T1ParentRows P 1 1 t).center := by
    rw [hX, hy]
    rfl
  have hstrict : t < P.q₂ := by
    by_contra hn
    have hteq : t = P.q₂ := by omega
    have hsstar := hstar 1
    dsimp [P5332T1ParentRows, FordVertexDomain] at hsstar
    rw [hX, hteq, hy, hqsum, hAqInt] at hsstar
    norm_num at hsstar
    omega
  have hxcenter : f ⟨X,Y⟩ = FordOdometer P ⟨X,Y⟩ := hbase _ hx
  have hcenterarg : (⟨X,Y⟩ : GaussianInt) - (P5332T1ParentRows P 1 1 0).displacement = ⟨t,P.q₂⟩
      := by
    rw [hdis, hX, hy]
    ext <;> simp [t]
  have hxother := hother ⟨X,Y⟩ hx'
  rw [hcenterarg] at hxother
  have hrow0 : (P5332T1ParentRows P 1 1 0).linear = ⟨-P.p₂,P.p₁⟩ := by rfl
  simp only [hrow0] at hxother
  rw [hX, hy] at hxother
  have hpnum : P.p₂ * (P.q : Int) - P.q₂ * P.p = -1 := hdet2
  have hcenterP : FordOdometer P ⟨X,Y⟩ = 0 := by
    rw [hX, hy, boundaryP (P.q₁+t) 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have hcenterA : FordOdometer A ⟨t,P.q₂⟩ = P.p₂*t := ParentTwoRotationOneProof.hcenterA P A hAp
      hAq hspos boundaryA X hAqInt ht0 hstrict
  have hB : B = P.p₂ * (P.q₁ : Int) := by
    rw [hcenterP] at hxcenter
    rw [hcenterA] at hxother
    rw [hX, hy] at hxcenter
    linear_combination hxcenter - hxother
  subst B
  have valueChild (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q)
      (hv : 0 ≤ v) (hvq : v ≤ P.q)
      (hb : u ≤ 1 ∨ P.q-1 ≤ u ∨ v ≤ 1 ∨ P.q-1 ≤ v) :
      f ⟨u,v⟩ = IntegerCeilDiv (P.p*u*v) P.q hqn := by
    exact (hbase ⟨u,v⟩ ⟨hu,huq,hv,hvq⟩).trans (boundaryP u v hu huq hv hvq hb)
  have centerVal : f ⟨X,Y⟩ = 0 := by rw [hbase _ hx, hcenterP]
  have eastArg : (⟨X,Y⟩ : GaussianInt)+1 = ⟨X+1,Y⟩ := by ext <;> simp
  have westArg : (⟨X,Y⟩ : GaussianInt)-1 = ⟨X-1,Y⟩ := by ext <;> simp
  have northArg : (⟨X,Y⟩ : GaussianInt)+⟨0,1⟩ = ⟨X,Y+1⟩ := by ext <;> simp
  have southArg : (⟨X,Y⟩ : GaussianInt)-⟨0,1⟩ = ⟨X,Y-1⟩ := by ext <;> simp
  have eastVal : f (⟨X,Y⟩+1) = 0 := by
    have mem : (⟨X+1,Y⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
      change 0 ≤ X+1 ∧ X+1 ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q
      omega
    rw [eastArg, hbase _ mem, hy]
    rw [boundaryP (X+1) 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have westVal : f (⟨X,Y⟩-1) = 0 := by
    have mem : (⟨X-1,Y⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
      change 0 ≤ X-1 ∧ X-1 ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q
      omega
    rw [westArg, hbase _ mem, hy]
    rw [boundaryP (X-1) 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have northVal : f (⟨X,Y⟩+⟨0,1⟩) = IntegerCeilDiv (P.p*X) P.q hqn := by
    have mem : (⟨X,Y+1⟩ : GaussianInt) ∈ FordVertexDomain P.q := by
      change 0 ≤ X ∧ X ≤ P.q ∧ 0 ≤ Y+1 ∧ Y+1 ≤ P.q
      omega
    rw [northArg, hbase _ mem, hy]
    norm_num
    rw [boundaryP X 1 (by omega) (by omega) (by norm_num) (by omega) (by omega)]
    simp
  have southVal : f (⟨X,Y⟩-⟨0,1⟩) =
      -P.p₁ - (P.p₂*t / P.q₂) := ParentTwoRotationOneProof.southVal P A hAp hAq f hspos
          boundaryA X Y hx' hdis hAqInt hy ht0 hX hstrict hrow0 hother southArg
  have hnorth : f (⟨X,Y⟩+⟨0,1⟩) = P.p₁ + IntegerCeilDiv (P.p*t-1) P.q hqn :=
      ParentTwoRotationOneProof.hnorth P f hqn hdet1 X Y hy hX northArg northVal
  refine ⟨t, ht0, hstrict, hxrow, rfl, ?_, ?_⟩
  · intro l
    fin_cases l
    · simp [centerVal, P5332T1ParentRows]
    · simpa [P5332T1ParentRows, IntegerCeilDiv] using eastVal
    · simpa [P5332T1ParentRows, IntegerCeilDiv, sub_eq_add_neg] using westVal
    · simpa [P5332T1ParentRows, IntegerCeilDiv] using hnorth
    · simpa [P5332T1ParentRows, sub_eq_add_neg] using southVal
  · constructor
    · intro hmem
      have hcoord := hmem
      have hcomp : (P5332T1ParentRows P 1 1 0).companion = ⟨-(P.q₂ : Int),-(P.q : Int)⟩ := by rfl
      rw [hcomp] at hcoord
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub] at hcoord
      rw [hX, hy] at hcoord
      constructor
      · omega
      · exact ⟨1, by norm_num⟩
    · rintro ⟨htzero, _⟩
      have hcomp : (P5332T1ParentRows P 1 1 0).companion = ⟨-(P.q₂ : Int),-(P.q : Int)⟩ := by rfl
      rw [hcomp, hX, hy, htzero]
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub]
      omega

end ApollonianSuperharmonic

end
