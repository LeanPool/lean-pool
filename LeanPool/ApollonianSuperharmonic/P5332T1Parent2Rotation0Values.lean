/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent2Rotation0Values]

/-!
# P5332T1Parent2Rotation0Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace Parent2Rotation0Proof

private theorem rpos :
    ∀ (P : FordFareyParameter), (1 : ℕ) < P.q → 1 < (P.q : Int) → 0 < (P.q₁ : Int) := by
  classical
  intro P hq hq'
  by_contra hn
  have hz : (P.q₁ : Int) = 0 := by omega
  have : P.p₁ * (P.q : Int) = 1 := by rw [← P.det₁]; simp [hz]
  by_cases hp : P.p₁ ≤ 0
  · have hq2 : 2 ≤ (P.q : Int) := hq'
    nlinarith
  · have hp' : 1 ≤ P.p₁ := by omega
    have hq2 : 2 ≤ (P.q : Int) := hq'
    nlinarith

private theorem hcenterB :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), ∀ (f : IntegerLatticeFunction), ∀ (B
        : Int), (∀ y ∈ FordVertexDomain P.q, f y = FordOdometer P y) → ((∀ (y : GaussianInt), y -
        (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).displacement ∈
        FordVertexDomain A.q → f y = FordOdometer A (y - (P5332T1ParentRows P (1 : Fin (2 : ℕ))
        (0 : Fin (4 : ℕ)) (0 : ℤ)).displacement) + (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (0 :
        Fin (4 : ℕ)) (0 : ℤ)).linear.re * y.re + (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (0 :
        Fin (4 : ℕ)) (0 : ℤ)).linear.im * y.im + B) → (((P.q : Int) = (P.q₁ : Int) + (P.q₂ :
        Int)) → ((0 < (P.q₂ : Int)) → (((P.q₂ : Int) ≠ 0) → (∀ (Y : ℤ), ((↑A.q : ℤ) = (↑P.q₂ :
        ℤ)) → (((P5332T1ParentRows P (1 : Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).displacement
        = ⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩) → (((0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ Y ∧ Y
        ≤ (↑P.q : ℤ)) → (((0 : ℤ) ≤ (0 : ℤ) + (↑P.q₂ : ℤ) ∧ (0 : ℤ) + (↑P.q₂ : ℤ) ≤ (↑P.q₂ : ℤ) ∧
        (0 : ℤ) ≤ Y ∧ Y ≤ (↑P.q₂ : ℤ)) → ((Y ≤ (P.q₂ : Int)) → ((1 ≤ Y) → ((∀ (v : Int), (0 ≤ v)
        → ((v ≤ P.q) → (FordOdometer P ⟨0,v⟩ = 0))) → ((∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤
        P.q₂) → ((0 ≤ v) → ((v ≤ P.q₂) → ((u ≤ 1 ∨ (P.q₂ : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q₂ : Int)-1 ≤
        v) → (FordOdometer A ⟨u,v⟩ = IntegerCeilDiv (P.p₂*u*v) P.q₂ (by exact_mod_cast
        P.q₂_pos.ne'))))))) → (B = 0))))))))))))) := by
  classical
  intro P A f B hbase hother qsum spos hsn Y hAqInt hdisp hx0 hx'0 hY hlow valLeft valA
  have hc := hbase ⟨0,Y⟩ ⟨by simp, by simp, by exact hx0.2.2.1, by exact hx0.2.2.2⟩
  have ho := hother ⟨0,Y⟩ (by
    rw [hdisp]
    simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
      sub_zero]
    rw [hAqInt]
    omega)
  rw [hdisp] at ho
  have arg : (⟨0,Y⟩ : GaussianInt) - ⟨-(P.q₂ : Int),0⟩ = ⟨(P.q₂ : Int),Y⟩ := by
    ext <;> simp
  rw [arg] at ho
  have hlinR : (P5332T1ParentRows P 1 0 0).linear.re = 0 := by rfl
  have hlinI : (P5332T1ParentRows P 1 0 0).linear.im = -P.p₂ := by rfl
  rw [hlinR, hlinI] at ho
  simp only [zero_mul, neg_mul, add_zero] at ho
  rw [valLeft Y (by omega) (by omega)] at hc
  have hvA := valA (P.q₂ : Int) Y (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hvA] at ho
  have hceil : IntegerCeilDiv (P.p₂*(P.q₂ : Int)*Y) P.q₂
      (by exact_mod_cast P.q₂_pos.ne') = P.p₂*Y := by
    unfold IntegerCeilDiv
    rw [show -(P.p₂*(P.q₂ : Int)*Y) = -(P.p₂*Y)*(P.q₂ : Int) by ring,
      Int.mul_ediv_cancel _ hsn]
    ring
  rw [hceil] at ho
  linarith [ho, hc]

private theorem values :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (f :
        IntegerLatticeFunction), (∀ y ∈ FordVertexDomain P.q, f y = FordOdometer P y) → (((P.q :
        Int) = (P.q₁ : Int) + (P.q₂ : Int)) → ((0 < (P.q₁ : Int)) → ((0 < (P.q₂ : Int)) → (((P.q₂
        : Int) ≠ 0) → (∀ (Y : ℤ), ((↑A.q : ℤ) = (↑P.q₂ : ℤ)) → (((P5332T1ParentRows P (1 : Fin
        (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).displacement = ⟨-(↑P.q₂ : ℤ), (0 : ℤ)⟩) → (((0 : ℤ) ≤
        (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ Y ∧ Y ≤ (↑P.q : ℤ)) → (((0 : ℤ) ≤ (0 : ℤ) +
        (↑P.q₂ : ℤ) ∧ (0 : ℤ) + (↑P.q₂ : ℤ) ≤ (↑P.q₂ : ℤ) ∧ (0 : ℤ) ≤ Y ∧ Y ≤ (↑P.q₂ : ℤ)) → ((Y
        ≤ (P.q₂ : Int)) → ((1 ≤ Y) → (
    let t : Int := (P.q₂ : Int) - Y
    (∀ (v : Int), (0 ≤ v) → ((v ≤ P.q) → (FordOdometer P ⟨0,v⟩ = 0))) → ((∀ (v : Int), (0 ≤ v) →
        ((v ≤ P.q) → (FordOdometer P ⟨1,v⟩ = IntegerCeilDiv (P.p*v) P.q (by exact_mod_cast
        P.q_pos.ne')))) → ((∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ P.q₂) → ((0 ≤ v) → ((v ≤
        P.q₂) → ((u ≤ 1 ∨ (P.q₂ : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q₂ : Int)-1 ≤ v) → (FordOdometer A
        ⟨u,v⟩ = IntegerCeilDiv (P.p₂*u*v) P.q₂ (by exact_mod_cast P.q₂_pos.ne'))))))) → ((∀ (y :
            GaussianInt), y - (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 :
        ℤ)).displacement ∈ FordVertexDomain A.q → f y = FordOdometer A (y - (P5332T1ParentRows
        P (1 : Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).displacement) + (P5332T1ParentRows P (1
        : Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).linear.re * y.re + (P5332T1ParentRows P (1 :
        Fin (2 : ℕ)) (0 : Fin (4 : ℕ)) (0 : ℤ)).linear.im * y.im + (0 : ℤ)) → (∀ l : Fin 5, f
        ((⟨0,Y⟩ : GaussianInt) + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l)) =
        (P5332T1ParentRows P 1 0 t).values l)))))))))))))))) := by
  classical
  intro P A hq f hbase qsum rpos spos hsn Y hAqInt hdisp hx0 hx'0 hY hlow t valLeft valChildEast
      valA hother l
  fin_cases l
  · simp only [Int.reduceNeg, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, add_zero]
    have hh := hbase ⟨0,Y⟩ hx0
    rw [hh, valLeft Y (by omega) (by omega)]
    simp [P5332T1ParentRows]
  · simp only [Int.reduceNeg, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    have eastArg : (⟨0,Y⟩ : GaussianInt) + 1 = ⟨1,Y⟩ := by ext <;> simp
    rw [eastArg]
    have hh := hbase ⟨1,Y⟩ (by
      change 0 ≤ (1 : Int) ∧ 1 ≤ (P.q : Int) ∧ 0 ≤ Y ∧ Y ≤ P.q
      omega)
    rw [hh, valChildEast Y (by omega) (by omega)]
    simp only [IntegerCeilDiv, P5332T1ParentRows, Nat.succ_eq_add_one, Nat.reduceAdd,
        Int.reduceNeg, neg_add_rev, neg_sub, Fin.isValue, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, neg_inj]
    have hy : Y = (P.q₂ : Int)-t := by dsimp [t]; omega
    rw [hy]
  · simp only [Int.reduceNeg, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val, Fin.isValue]
    have arg : (⟨0,Y⟩ : GaussianInt)-1 = ⟨-1,Y⟩ := by ext <;> simp
    have hp := hother (⟨0,Y⟩-1) (by
      rw [arg]
      rw [hdisp]
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
        sub_zero]
      rw [hAqInt]
      omega)
    rw [hdisp] at hp
    have parg : (⟨-1,Y⟩ : GaussianInt)-⟨-(P.q₂ : Int),0⟩ = ⟨(P.q₂ : Int)-1,Y⟩ := by
      ext <;> simp; omega
    rw [arg, parg] at hp
    have hlinI : (P5332T1ParentRows P 1 0 0).linear.im = -P.p₂ := by rfl
    have hlinR : (P5332T1ParentRows P 1 0 0).linear.re = 0 := by rfl
    rw [hlinI, hlinR] at hp
    simp only [zero_mul, neg_mul, add_zero] at hp
    have hbnd := valA ((P.q₂ : Int)-1) Y (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [hbnd] at hp
    have hnum : P.p₂*((P.q₂ : Int)-1)*Y = -P.p₂*Y+(P.p₂*Y)*(P.q₂ : Int) := by ring
    rw [hnum, P5188T1CeilingShift (-P.p₂*Y) (P.p₂*Y) P.q₂ hsn] at hp
    simp only [IntegerCeilDiv, neg_mul, neg_neg] at hp
    ring_nf at hp
    have hy : Y = (P.q₂ : Int)-t := by dsimp [t]; omega
    have westPlus : (⟨0,Y⟩ : GaussianInt) + (-1) = ⟨-1,Y⟩ := by ext <;> simp
    rw [westPlus, hy]
    have hrowval : (P5332T1ParentRows P 1 0 t).values 2 =
        -(P.p₂*((P.q₂ : Int)-t)/(P.q₂ : Int)) := by rfl
    rw [hrowval]
    simpa only [hy] using hp
  · simp only [Int.reduceNeg, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val, Zsqrtd.add_def, add_zero, Fin.isValue]
    have northArg : (⟨0,Y⟩ : GaussianInt) + ⟨0,1⟩ = ⟨0,Y+1⟩ := by ext <;> simp
    have hh := hbase ⟨0,Y+1⟩ (by
      change (0 : Int) ≤ 0 ∧ 0 ≤ (P.q : Int) ∧ 0 ≤ Y+1 ∧ Y+1 ≤ (P.q : Int)
      omega)
    rw [hh, valLeft (Y+1) (by omega) (by omega)]
    simp [P5332T1ParentRows]
  · simp only [Int.reduceNeg, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val, Fin.isValue]
    have southArg : (⟨0,Y⟩ : GaussianInt) - ⟨0,1⟩ = ⟨0,Y-1⟩ := by ext <;> simp
    have southPlus : (⟨0,Y⟩ : GaussianInt) + (-⟨0,1⟩) = ⟨0,Y-1⟩ := by
      ext <;> simp; ring
    rw [southPlus]
    have hh := hbase ⟨0,Y-1⟩ (by
      change (0 : Int) ≤ 0 ∧ 0 ≤ (P.q : Int) ∧ 0 ≤ Y-1 ∧ Y-1 ≤ (P.q : Int)
      omega)
    rw [hh, valLeft (Y-1) (by omega) (by omega)]
    simp [P5332T1ParentRows]

private theorem companion :
    ∀ (P : FordFareyParameter),
      (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) →
        ∀ (Y : ℤ),
          (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (↑P.q : ℤ) ∧ (0 : ℤ) ≤ Y ∧ Y ≤ (↑P.q : ℤ) →
            1 ≤ Y →
              let t : Int := (P.q₂ : Int) - Y
              (⟨0, Y⟩ : GaussianInt) - (P5332T1ParentRows P 1 0 0).companion ∈
                  FordVertexDomain P.q ↔
                t = 0 ∧ Even (0 + 1 : Nat) := by
  classical
  intro P qsum Y hx0 hlow t
  have hn : ¬ Even (0+1 : Nat) := by norm_num
  have hcomp : (P5332T1ParentRows P 1 0 0).companion =
      ⟨-(P.q₂ : Int),-(P.q : Int)⟩ := by rfl
  constructor
  · intro h
    rw [hcomp] at h
    simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
      Zsqrtd.im_sub] at h
    have hy : Y ≥ 0 := hx0.2.2.1
    have hqnat : (P.q : Int) = (P.q₁ : Int)+(P.q₂ : Int) := qsum
    omega
  · rintro ⟨_, he⟩
    exact (hn he).elim

end Parent2Rotation0Proof

theorem P5332T1Parent2Rotation0Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₂) (hAq : A.q = P.q₂)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 1 0 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 1 0 0).displacement) +
        (P5332T1ParentRows P 1 0 0).linear.re * y.re +
        (P5332T1ParentRows P 1 0 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 1 0 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 1 0 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₂ : Int) ∧
      x = (P5332T1ParentRows P 1 0 t).center ∧ B = 0 ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 0 t).values l) ∧
      (x - (P5332T1ParentRows P 1 0 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (0+1 : Nat)) := by
-- BODY
  classical
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have qsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by exact_mod_cast P.sum_q
  have rpos : 0 < (P.q₁ : Int) := Parent2Rotation0Proof.rpos P hq hq'
  have spos : 0 < (P.q₂ : Int) := by exact_mod_cast P.q₂_pos
  have rlt : (P.q₁ : Int) < P.q := by exact_mod_cast P.q₁_lt
  have slt : (P.q₂ : Int) < P.q := by omega
  have hqn : (P.q : Int) ≠ 0 := by omega
  have hsn : (P.q₂ : Int) ≠ 0 := by omega
  have hdet : P.p₂ * (P.q : Int) - (P.q₂ : Int) * P.p = -1 := P.det₂
  have hsumP : P.p = P.p₁ + P.p₂ := P.sum_p
  have hcross : P.p₁ * (P.q₂ : Int) - P.p₂ * (P.q₁ : Int) = 1 := by
    nlinarith [P.det₁, P.det₂, P.sum_q, P.sum_p]
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧
    (∀ P x, x ∈ FordDoubledBoundary P.q → FordOdometer P x = _) ∧ _ at laws
  have boundary (R : FordFareyParameter) (u v : Int)
      (hu : 0 ≤ u) (huq : u ≤ R.q) (hv : 0 ≤ v) (hvq : v ≤ R.q)
      (hs : u ≤ 1 ∨ (R.q : Int)-1 ≤ u ∨ v ≤ 1 ∨ (R.q : Int)-1 ≤ v) :
      FordOdometer R ⟨u,v⟩ = IntegerCeilDiv (R.p*u*v) R.q
        (by exact_mod_cast R.q_pos.ne') := by
    apply laws.2.1
    change (0 ≤ u ∧ u ≤ (R.q : Int) ∧ 0 ≤ v ∧ v ≤ (R.q : Int)) ∧
      ¬ (2 ≤ u ∧ u ≤ (R.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (R.q : Int)-2)
    omega
  rcases x with ⟨X,Y⟩
  have hx0 := hx
  have hx'0 := hx'
  change 0 ≤ X ∧ X ≤ P.q ∧ 0 ≤ Y ∧ Y ≤ P.q at hx0
  have hAqInt : (A.q : Int) = (P.q₂ : Int) := by exact_mod_cast hAq
  have hdisp : (P5332T1ParentRows P 1 0 0).displacement = ⟨-(P.q₂ : Int),0⟩ := by rfl
  rw [hdisp] at hx'0
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
    Zsqrtd.im_sub] at hx'0
  rw [hAqInt] at hx'0
  simp only [sub_neg_eq_add, sub_zero] at hx'0
  have hX : X = 0 := by
    omega
  subst X
  have hY : Y ≤ (P.q₂ : Int) := by
    omega
  have hlow : 1 ≤ Y := by
    have hsouth := hstar (4 : Fin 5)
    have hstencil : (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] (4 : Fin 5)) = -⟨0,1⟩ := by rfl
    rw [hstencil] at hsouth
    rw [hdisp] at hsouth
    norm_num [FordVertexDomain] at hsouth
    rw [hAqInt] at hsouth
    omega
  let t : Int := (P.q₂ : Int) - Y
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have hts : t < (P.q₂ : Int) := by dsimp [t]; omega
  have hxcenter : (⟨0,Y⟩ : GaussianInt) = (P5332T1ParentRows P 1 0 t).center := by
    dsimp [P5332T1ParentRows, t]
    ext <;> simp
  have valLeft (v : Int) (hv : 0 ≤ v) (hvq : v ≤ P.q) :
      FordOdometer P ⟨0,v⟩ = 0 := by
    rw [boundary P 0 v (by omega) (by omega) hv hvq (by omega)]
    simp [IntegerCeilDiv]
  have valRight (v : Int) (hv : 0 ≤ v) (hvq : v ≤ P.q) :
      FordOdometer P ⟨(P.q : Int),v⟩ = P.p*v := by
    rw [boundary P P.q v (by omega) (by omega) hv hvq (by omega)]
    unfold IntegerCeilDiv
    rw [show -(P.p*(P.q : Int)*v) = -(P.p*v)*(P.q : Int) by ring,
      Int.mul_ediv_cancel _ hqn]
    ring
  have valChildEast (v : Int) (hv : 0 ≤ v) (hvq : v ≤ P.q) :
      FordOdometer P ⟨1,v⟩ = IntegerCeilDiv (P.p*v) P.q (by exact_mod_cast P.q_pos.ne') := by
    rw [boundary P 1 v (by omega) (by omega) hv hvq (by omega)]
    congr 1
    ring
  have valA (u v : Int) (hu : 0 ≤ u) (huq : u ≤ P.q₂)
      (hv : 0 ≤ v) (hvq : v ≤ P.q₂)
      (hs : u ≤ 1 ∨ (P.q₂ : Int)-1 ≤ u ∨ v ≤ 1 ∨ (P.q₂ : Int)-1 ≤ v) :
      FordOdometer A ⟨u,v⟩ = IntegerCeilDiv (P.p₂*u*v) P.q₂ (by exact_mod_cast P.q₂_pos.ne') := by
    have hb := boundary A u v hu (by simpa only [hAqInt] using huq)
      hv (by simpa only [hAqInt] using hvq) (by simpa only [hAqInt] using hs)
    simpa only [hAp, hAq] using hb
  have hcenterB : B = 0 := Parent2Rotation0Proof.hcenterB P A f B hbase hother qsum spos hsn Y
      hAqInt hdisp hx0 hx'0 hY hlow valLeft valA
  subst B
  have values : ∀ l : Fin 5,
      f ((⟨0,Y⟩ : GaussianInt) + (![0,1,-1,(⟨0,1⟩ : GaussianInt),-⟨0,1⟩] l)) =
        (P5332T1ParentRows P 1 0 t).values l := Parent2Rotation0Proof.values P A hq f hbase
            qsum rpos spos hsn Y hAqInt hdisp hx0 hx'0 hY hlow valLeft valChildEast valA hother
  have companion : (⟨0,Y⟩ : GaussianInt) -
      (P5332T1ParentRows P 1 0 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (0+1 : Nat) := Parent2Rotation0Proof.companion P qsum Y hx0 hlow
  refine ⟨t, ht0, hts, hxcenter, rfl, ?_, companion⟩
  intro l
  exact values l

end ApollonianSuperharmonic

end
