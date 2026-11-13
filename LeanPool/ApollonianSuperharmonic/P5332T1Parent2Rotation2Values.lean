/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer

-- [TABLET NODE: P5332T1Parent2Rotation2Values]

/-!
# P5332T1Parent2Rotation2Values

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace Parent2Rotation2Proof

private theorem baseBd :
    ∀ (P : FordFareyParameter),
      let q : Int := P.q
      let r : Int := P.q₁
      let s : Int := P.q₂
      let p : Int := P.p
      q = r + s →
        ∀ (hqn : q ≠ 0),
          ((∀ (P : FordFareyParameter),
                ∀ (x : GaussianInt),
                  P.q = (1 : ℕ) →
                    FordOdometer P x =
                      x.re * (x.re - (1 : ℤ)) / (2 : ℤ) + P.p * x.re * x.im) ∧
              (∀ (P : FordFareyParameter),
                  ∀ x ∈ FordDoubledBoundary P.q,
                    Classical.choose FordOdometerFamilyExistsUnique P x =
                      IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ)
                        (by exact_mod_cast P.q_pos.ne')) ∧
                (∀ (P : FordFareyParameter),
                    ∀ (x : GaussianInt),
                      Classical.choose FordOdometerFamilyExistsUnique P
                          (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) =
                        Classical.choose FordOdometerFamilyExistsUnique P x - P.p * x.re) ∧
                  (∀ (P : FordFareyParameter),
                      ∀ (x : GaussianInt),
                        Classical.choose FordOdometerFamilyExistsUnique P
                            (x + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) =
                          Classical.choose FordOdometerFamilyExistsUnique P x +
                            P.p₁ * x.re +
                            P.p * x.im +
                            (↑P.q₁ : ℤ) * P.p) ∧
                    (∀ (P : FordFareyParameter),
                        ∀ (x : GaussianInt),
                          Classical.choose FordOdometerFamilyExistsUnique P
                            (x + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) =
                            Classical.choose FordOdometerFamilyExistsUnique P x +
                            P.p₂ * x.re -
                            P.p * x.im -
                            (↑P.q : ℤ) * P.p₂) ∧
                      ∀ (P : FordFareyParameter),
                        ∀ (P₁ : FordFareyParameter),
                          ∀ (P₂ : FordFareyParameter),
                            (1 : ℕ) < P.q →
                            P₁.p = P.p₁ →
                            P₁.q = P.q₁ →
                            P₂.p = P.p₂ →
                            P₂.q = P.q₂ →
                            (∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)),
                            Classical.choose FordOdometerFamilyExistsUnique P x =
                            Classical.choose FordOdometerFamilyExistsUnique P₁ x) ∧
                            (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)),
                            Classical.choose FordOdometerFamilyExistsUnique P x =
                            Classical.choose FordOdometerFamilyExistsUnique P₁
                            (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) +
                            P.p₂ * x.re +
                            P.p₂ * x.im -
                            P.p₂ * (↑P.q₂ : ℤ) +
                            (1 : ℤ)) ∧
                            (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)),
                            Classical.choose FordOdometerFamilyExistsUnique P x =
                            Classical.choose FordOdometerFamilyExistsUnique P₂
                            (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) +
                            P.p₁ * x.im) ∧
                            ∀ x ∈ FordRecursiveVertexDomains P (3 : Fin (4 : ℕ)),
                            Classical.choose FordOdometerFamilyExistsUnique P x =
                            Classical.choose FordOdometerFamilyExistsUnique P₂
                            (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) +
                            P.p₁ * x.re) →
            ∀ (u : ℤ),
              ∀ (v : ℤ),
                (0 : ℤ) ≤ u →
                  u ≤ q →
                    (0 : ℤ) ≤ v →
                      v ≤ q →
                        u ≤ (1 : ℤ) ∨ q - (1 : ℤ) ≤ u ∨ v ≤ (1 : ℤ) ∨ q - (1 : ℤ) ≤ v →
                          FordOdometer P ⟨u, v⟩ = IntegerCeilDiv (p * u * v) q hqn := by
  classical
  intro P q r s p hsum hqn laws u v hu huq hv hvq hedge
  apply laws.2.1
  change (0 ≤ u ∧ u ≤ (P.q : Int) ∧ 0 ≤ v ∧ v ≤ (P.q : Int)) ∧
    ¬ (2 ≤ u ∧ u ≤ (P.q : Int)-2 ∧ 2 ≤ v ∧ v ≤ (P.q : Int)-2)
  constructor
  · exact ⟨hu,huq,hv,hvq⟩
  · intro h
    change 2 ≤ u ∧ u ≤ q-2 ∧ 2 ≤ v ∧ v ≤ q-2 at h
    rcases h with ⟨hu2,hu2q,hv2,hv2q⟩
    rcases hedge with h1 | h2 | h3 | h4 <;> omega

private theorem parentBd :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), (A.p = P.p₂) → ((A.q = P.q₂) → (
    let s : Int := P.q₂
    let b : Int := P.p₂
    ∀ (hsn : s ≠ 0), ((∀ (P : FordFareyParameter), ∀ (x : GaussianInt), P.q = (1 : ℕ) →
        FordOdometer P x = x.re * (x.re - (1 : ℤ)) / (2 : ℤ) + P.p * x.re * x.im) ∧ (∀ (P :
            FordFareyParameter), ∀ x ∈ FordDoubledBoundary P.q, Classical.choose
        FordOdometerFamilyExistsUnique P x = IntegerCeilDiv (P.p * x.re * x.im) (↑P.q : ℤ) (by
        exact_mod_cast P.q_pos.ne')) ∧ (∀ (P : FordFareyParameter), ∀ (x : GaussianInt),
            Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨(0 : ℤ), -(↑P.q : ℤ)⟩) =
        Classical.choose FordOdometerFamilyExistsUnique P x - P.p * x.re) ∧ (∀ (P :
            FordFareyParameter), ∀ (x : GaussianInt), Classical.choose
            FordOdometerFamilyExistsUnique
        P (x + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) = Classical.choose FordOdometerFamilyExistsUnique P x +
        P.p₁ * x.re + P.p * x.im + (↑P.q₁ : ℤ) * P.p) ∧ (∀ (P : FordFareyParameter), ∀ (x :
            GaussianInt), Classical.choose FordOdometerFamilyExistsUnique P (x + ⟨-(↑P.q : ℤ),
            (↑P.q₂
        : ℤ)⟩) = Classical.choose FordOdometerFamilyExistsUnique P x + P.p₂ * x.re - P.p * x.im -
        (↑P.q : ℤ) * P.p₂) ∧ ∀ (P : FordFareyParameter), ∀ (P₁ : FordFareyParameter), ∀ (P₂ :
            FordFareyParameter), (1 : ℕ) < P.q → P₁.p = P.p₁ → P₁.q = P.q₁ → P₂.p = P.p₂ → P₂.q =
        P.q₂ → (∀ x ∈ FordRecursiveVertexDomains P (0 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₁
        x) ∧ (∀ x ∈ FordRecursiveVertexDomains P (1 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₁
        (x - ⟨(↑P.q₂ : ℤ), (↑P.q₂ : ℤ)⟩) + P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (↑P.q₂ : ℤ) + (1 :
        ℤ)) ∧ (∀ x ∈ FordRecursiveVertexDomains P (2 : Fin (4 : ℕ)), Classical.choose
        FordOdometerFamilyExistsUnique P x = Classical.choose FordOdometerFamilyExistsUnique P₂
        (x - ⟨(↑P.q₁ : ℤ), (0 : ℤ)⟩) + P.p₁ * x.im) ∧ ∀ x ∈ FordRecursiveVertexDomains P (3 : Fin
        (4 : ℕ)), Classical.choose FordOdometerFamilyExistsUnique P x = Classical.choose
        FordOdometerFamilyExistsUnique P₂ (x - ⟨(0 : ℤ), (↑P.q₁ : ℤ)⟩) + P.p₁ * x.re) → (∀ (u :
            ℤ), ∀ (v : ℤ), (0 : ℤ) ≤ u → u ≤ s → (0 : ℤ) ≤ v → v ≤ s → u ≤ (1 : ℤ) ∨ s - (1 : ℤ) ≤ u
        ∨ v ≤ (1 : ℤ) ∨ s - (1 : ℤ) ≤ v → FordOdometer A ⟨u, v⟩ = IntegerCeilDiv (b * u * v) s
        hsn))) := by
  classical
  intro P A hAp hAq s b hsn laws u v hu hus hv hvs hedge
  have hAn : (A.q : Int) = s := by dsimp [s]; exact_mod_cast hAq
  have hAp' : A.p = b := by dsimp [b]; exact hAp
  have hAnz : (A.q : Int) ≠ 0 := by rw [hAn]; exact hsn
  have hbdy : (⟨u,v⟩ : GaussianInt) ∈ FordDoubledBoundary A.q := by
    change (0 ≤ u ∧ u ≤ (A.q : Int) ∧ 0 ≤ v ∧ v ≤ (A.q : Int)) ∧ ¬ _
    rw [hAn]
    constructor
    · exact ⟨hu,hus,hv,hvs⟩
    · intro h
      change 2 ≤ u ∧ u ≤ s-2 ∧ 2 ≤ v ∧ v ≤ s-2 at h
      rcases h with ⟨hu2,hus2,hv2,hvs2⟩
      rcases hedge with h1 | h2 | h3 | h4 <;> omega
  have hb := laws.2.1 A ⟨u,v⟩ hbdy
  change FordOdometer A ⟨u,v⟩ = IntegerCeilDiv (A.p*u*v) (A.q : Int) (by omega) at hb
  simpa [hAp', hAn] using hb

private theorem htStrict :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter),
    let q : Int := P.q
    let r : Int := P.q₁
    let s : Int := P.q₂
    (q = r + s) → (∀ (Y : ℤ), ((P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 : ℕ)) (0 :
        ℤ)).displacement = ⟨q, r⟩) → (((↑A.q : ℤ) = s) → (
    let t : Int := Y-r
    (Y = r+t) → ((∀ (l : Fin (5 : ℕ)), ⟨q, Y⟩ + ![(0 : ℤ√(-1 : ℤ)), (1 : ℤ√(-1 : ℤ)), (-1 : ℤ√(-1
        : ℤ)), ⟨(0 : ℤ), (1 : ℤ)⟩, -⟨(0 : ℤ), (1 : ℤ)⟩] l ∈ FordVertexDomain P.q ∨ ⟨q, Y⟩ + ![(0
        : ℤ√(-1 : ℤ)), (1 : ℤ√(-1 : ℤ)), (-1 : ℤ√(-1 : ℤ)), ⟨(0 : ℤ), (1 : ℤ)⟩, -⟨(0 : ℤ), (1 :
        ℤ)⟩] l - (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 : ℕ)) (0 : ℤ)).displacement
        ∈ FordVertexDomain A.q) → (t < s))))) := by
  classical
  intro P A q r s hsum Y hdisp hAn t hY hstar
  have htop := hstar 3
  rw [hY] at htop
  rw [hdisp] at htop
  change (⟨q,r+t⟩ : GaussianInt)+⟨0,1⟩ ∈ FordVertexDomain P.q ∨
    (⟨q,r+t⟩ : GaussianInt)+⟨0,1⟩-⟨q,r⟩ ∈ FordVertexDomain A.q at htop
  simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_add, Zsqrtd.im_add,
    Zsqrtd.re_sub, Zsqrtd.im_sub] at htop
  rcases htop with htop | htop
  · change 0 ≤ q ∧ q ≤ (P.q : Int) ∧ 0 ≤ r+t+1 ∧ r+t+1 ≤ (P.q : Int) at htop
    dsimp [q] at htop
    omega
  · change 0 ≤ q-q ∧ q-q ≤ (A.q : Int) ∧ 0 ≤ r+t+1-r ∧ r+t+1-r ≤ (A.q : Int) at htop
    rw [hAn] at htop
    omega

private theorem valueEast :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), ∀ (f : IntegerLatticeFunction), ∀ (B
        : Int), (∀ (y : GaussianInt), y - (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 :
        ℕ)) (0 : ℤ)).displacement ∈ FordVertexDomain A.q → f y = FordOdometer A (y -
        (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 : ℕ)) (0 : ℤ)).displacement) +
        (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 : ℕ)) (0 : ℤ)).linear.re * y.re +
        (P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 : ℕ)) (0 : ℤ)).linear.im * y.im + B)
        → (
    let q : Int := P.q
    let r : Int := P.q₁
    let s : Int := P.q₂
    let p : Int := P.p
    let a : Int := P.p₁
    let b : Int := P.p₂
    (0 < s) → (∀ (hsn : s ≠ 0), (∀ (u : Int), ∀ (v : Int), (0 ≤ u) → ((u ≤ s) → ((0 ≤ v) → ((v ≤
        s) → ((u ≤ 1 ∨ s-1 ≤ u ∨ v ≤ 1 ∨ s-1 ≤ v) → (FordOdometer A ⟨u,v⟩ = IntegerCeilDiv
        (b*u*v) s hsn)))))) → (∀ (Y : ℤ), ((P5332T1ParentRows P (1 : Fin (2 : ℕ)) (2 : Fin (4 :
        ℕ)) (0 : ℤ)).displacement = ⟨q, r⟩) → (((↑A.q : ℤ) = s) → (
    let t : Int := Y-r
    (0 ≤ t) → ((t ≤ s) → ((B = -a*q) → (f ⟨q+1,r+t⟩ = p*(r+t)+a+IntegerCeilDiv (b*t) s
        hsn)))))))) := by
  classical
  intro P A f B hother q r s p a b hs hsn parentBd Y hdisp hAn t ht0 htS hB
  have arg : (⟨q+1,r+t⟩ : GaussianInt) -
      (P5332T1ParentRows P 1 2 0).displacement = ⟨1,t⟩ := by
    rw [hdisp]
    ext <;> simp
  have hdom : (⟨q+1,r+t⟩ : GaussianInt)-
      (P5332T1ParentRows P 1 2 0).displacement ∈ FordVertexDomain A.q := by
    rw [arg]
    change 0 ≤ 1 ∧ 1 ≤ (A.q : Int) ∧ 0 ≤ t ∧ t ≤ (A.q : Int)
    rw [hAn]
    exact ⟨by omega, by omega, ht0, by omega⟩
  have hv := hother ⟨q+1,r+t⟩ hdom
  rw [arg] at hv
  change f ⟨q+1,r+t⟩ = FordOdometer A ⟨1,t⟩ + a*(q+1) + p*(r+t) + B at hv
  rw [parentBd 1 t (by omega) (by omega) ht0 (by omega) (by omega), hB] at hv
  convert hv using 1; ring

private theorem valueWest :
    ∀ (P : FordFareyParameter),
      (1 : ℕ) < P.q →
        ∀ (f : IntegerLatticeFunction),
          (∀ y ∈ FordVertexDomain P.q, f y = FordOdometer P y) →
            let q : Int := P.q;
            let r : Int := P.q₁;
            let s : Int := P.q₂;
            let p : Int := P.p;
            q = r + s →
              ∀ (hqn : q ≠ 0),
                (∀ (u : Int),
                    ∀ (v : Int),
                      0 ≤ u →
                        u ≤ q →
                          0 ≤ v →
                            v ≤ q →
                            u ≤ 1 ∨ q - 1 ≤ u ∨ v ≤ 1 ∨ q - 1 ≤ v →
                            FordOdometer P ⟨u, v⟩ = IntegerCeilDiv (p * u * v) q hqn) →
                  ∀ (Y : ℤ),
                    let t : Int := Y - r
                    (0 : ℤ) ≤ q ∧ q ≤ q ∧ (0 : ℤ) ≤ Y ∧ Y ≤ q →
                      t < s → f ⟨q - 1, r + t⟩ = p * (r + t) - p * (r + t) / q := by
  classical
  intro P hq f hbase q r s p hsum hqn baseBd Y t hx0 htStrict
  have hv := hbase ⟨q-1,r+t⟩ (by change 0 ≤ q-1 ∧ q-1 ≤ q ∧ 0 ≤ r+t ∧ r+t ≤ q; omega)
  rw [baseBd (q-1) (r+t) (by omega) (by omega) (by omega) (by omega) (by omega)] at hv
  have hcdiv : IntegerCeilDiv (p*(q-1)*(r+t)) q hqn =
      p*(r+t) - (p*(r+t))/q := by
    rw [show p*(q-1)*(r+t) = (-p*(r+t)) + (p*(r+t))*q by ring,
      P5188T1CeilingShift (-p*(r+t)) (p*(r+t)) q hqn]
    simp [IntegerCeilDiv]
    ring
  exact hv.trans hcdiv

private theorem rowValues :
    ∀ (P : FordFareyParameter), ∀ (f : IntegerLatticeFunction),
    let q : Int := P.q
    let r : Int := P.q₁
    let s : Int := P.q₂
    let p : Int := P.p
    let a : Int := P.p₁
    let b : Int := P.p₂
    ∀ (hsn : s ≠ 0), ∀ (Y : ℤ),
    let t : Int := Y-r
    (f ⟨q,r+t⟩ = p*(r+t)) → ((f ⟨q+1,r+t⟩ = p*(r+t)+a+IntegerCeilDiv (b*t) s hsn) → ((f ⟨q-1,r+t⟩
        = p*(r+t) - a - ((p*t-1)/q)) → ((f ⟨q,r+t+1⟩ = p*(r+t+1)) → ((f ⟨q,r+t-1⟩ = p*(r+t-1)) →
        (∀ l : Fin 5, f (⟨q,r+t⟩ + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 2 t).values l))))) := by
  classical
  intro P f q r s p a b hsn Y t valueCenter valueEast valueWestRow valueNorth valueSouth l
  fin_cases l
  · simpa [P5332T1ParentRows,q,r,p] using valueCenter
  · have arg : (⟨q,r+t⟩ : GaussianInt) + 1 = ⟨q+1,r+t⟩ := by ext <;> simp
    simpa [P5332T1ParentRows,q,r,p,a,b,s, IntegerCeilDiv,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, arg] using valueEast
  · have arg : (⟨q,r+t⟩ : GaussianInt) + (-1) = ⟨q-1,r+t⟩ := by
      ext <;> simp; ring
    simpa [P5332T1ParentRows,q,r,p,a,b,s,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, arg] using valueWestRow
  · have arg : (⟨q,r+t⟩ : GaussianInt) + ⟨0,1⟩ = ⟨q,r+t+1⟩ := by ext <;> simp
    simpa [P5332T1ParentRows,q,r,p,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, arg] using valueNorth
  · have arg : (⟨q,r+t⟩ : GaussianInt) - ⟨0,1⟩ = ⟨q,r+t-1⟩ := by ext <;> simp
    simpa [P5332T1ParentRows,q,r,p,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, arg,
      ← sub_eq_add_neg] using valueSouth

end Parent2Rotation2Proof

theorem P5332T1Parent2Rotation2Values (P A : FordFareyParameter) (hq : 1 < P.q)
    (hAp : A.p = P.p₂) (hAq : A.q = P.q₂)
    (f : IntegerLatticeFunction) (B : Int) (x : GaussianInt)
    (hbase : ∀ y, y ∈ FordVertexDomain P.q → f y = FordOdometer P y)
    (hother : ∀ y,
      y - (P5332T1ParentRows P 1 2 0).displacement ∈ FordVertexDomain A.q →
      f y = FordOdometer A (y - (P5332T1ParentRows P 1 2 0).displacement) +
        (P5332T1ParentRows P 1 2 0).linear.re * y.re +
        (P5332T1ParentRows P 1 2 0).linear.im * y.im + B)
    (hx : x ∈ FordVertexDomain P.q)
    (hx' : x - (P5332T1ParentRows P 1 2 0).displacement ∈ FordVertexDomain A.q)
    (hstar : ∀ l : Fin 5,
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) ∈ FordVertexDomain P.q ∨
      x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l) -
        (P5332T1ParentRows P 1 2 0).displacement ∈ FordVertexDomain A.q) :
    ∃ t : Int, 0 ≤ t ∧ t < (P.q₂ : Int) ∧
      x = (P5332T1ParentRows P 1 2 t).center ∧ B = -P.p₁ * (P.q : Int) ∧
      (∀ l : Fin 5, f (x + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 2 t).values l) ∧
      (x - (P5332T1ParentRows P 1 2 0).companion ∈ FordVertexDomain P.q ↔
        t = 0 ∧ Even (2+1 : Nat)) := by
-- BODY
  classical
  let q : Int := P.q
  let r : Int := P.q₁
  let s : Int := P.q₂
  let p : Int := P.p
  let a : Int := P.p₁
  let b : Int := P.p₂
  have hsum : q = r + s := by
    dsimp [q, r, s]
    exact_mod_cast P.sum_q
  have hr : 0 < r := by
    have hpos := (P5130T5ParentArithmetic P hq).1
    dsimp [r]
    exact_mod_cast hpos
  have hs : 0 < s := by dsimp [s]; exact_mod_cast P.q₂_pos
  have hdet₁ : a*q - r*p = 1 := by
    exact P.det₁
  have hqn : q ≠ 0 := by omega
  have hsn : s ≠ 0 := by omega
  have laws := (Classical.choose_spec FordOdometerFamilyExistsUnique).1
  change (∀ P x, P.q = 1 → FordOdometer P x = _) ∧ _ at laws
  have baseBd (u v : Int) (hu : 0 ≤ u) (huq : u ≤ q)
      (hv : 0 ≤ v) (hvq : v ≤ q)
      (hedge : u ≤ 1 ∨ q-1 ≤ u ∨ v ≤ 1 ∨ q-1 ≤ v) :
      FordOdometer P ⟨u,v⟩ = IntegerCeilDiv (p*u*v) q hqn := Parent2Rotation2Proof.baseBd P
          hsum hqn laws u v hu huq hv hvq hedge
  have parentBd (u v : Int) (hu : 0 ≤ u) (hus : u ≤ s)
      (hv : 0 ≤ v) (hvs : v ≤ s)
      (hedge : u ≤ 1 ∨ s-1 ≤ u ∨ v ≤ 1 ∨ s-1 ≤ v) :
      FordOdometer A ⟨u,v⟩ = IntegerCeilDiv (b*u*v) s hsn := Parent2Rotation2Proof.parentBd P A
          hAp hAq hsn laws u v hu hus hv hvs hedge
  have sideRight (u : Int) (hu : 0 ≤ u) (huq : u ≤ q) :
      FordOdometer P ⟨q,u⟩ = p*u := by
    rw [baseBd q u (by omega) (by omega) hu huq (by omega)]
    dsimp [IntegerCeilDiv]
    rw [show -(p*q*u) = (-p*u)*q by ring, Int.mul_ediv_cancel _ hqn]
    ring
  rcases x with ⟨X,Y⟩
  have hx0 := hx
  change 0 ≤ X ∧ X ≤ q ∧ 0 ≤ Y ∧ Y ≤ q at hx0
  have hdisp : (P5332T1ParentRows P 1 2 0).displacement = ⟨q,r⟩ := by
    simp [P5332T1ParentRows,q,r]
  rw [hdisp] at hx'
  change 0 ≤ X-q ∧ X-q ≤ (A.q : Int) ∧ 0 ≤ Y-r ∧ Y-r ≤ (A.q : Int) at hx'
  have hAn : (A.q : Int) = s := by dsimp [s]; exact_mod_cast hAq
  rw [hAn] at hx'
  have hX : X = q := by omega
  let t : Int := Y-r
  have ht0 : 0 ≤ t := by dsimp [t]; omega
  have htS : t ≤ s := by dsimp [t]; omega
  have hY : Y = r+t := by dsimp [t]; omega
  subst X
  have htStrict : t < s := Parent2Rotation2Proof.htStrict P A hsum Y hdisp hAn hY hstar
  have centerArg : (⟨q,r+t⟩ : GaussianInt)-⟨q,r⟩ = ⟨0,t⟩ := by ext <;> simp
  have hc := hbase ⟨q,r+t⟩ (by change 0 ≤ q ∧ q ≤ q ∧ 0 ≤ r+t ∧ r+t ≤ q; omega)
  have hp := hother ⟨q,r+t⟩ (by
    change (⟨q,r+t⟩ : GaussianInt)-⟨q,r⟩ ∈ FordVertexDomain A.q
    rw [centerArg]
    change 0 ≤ (0 : Int) ∧ (0 : Int) ≤ (A.q : Int) ∧ 0 ≤ t ∧ t ≤ (A.q : Int)
    rw [hAn]
    exact ⟨by omega, by omega, ht0, by omega⟩)
  have centerChild : FordOdometer P ⟨q,r+t⟩ = p*(r+t) := sideRight (r+t) (by omega) (by omega)
  have centerParent : FordOdometer A ⟨0,t⟩ = 0 := by
    rw [parentBd 0 t (by omega) (by omega) ht0 (by omega) (by omega)]
    simp [IntegerCeilDiv]
  rw [centerChild] at hc
  change f ⟨q,r+t⟩ = FordOdometer A ((⟨q,r+t⟩ : GaussianInt)-⟨q,r⟩) +
    a*q + p*(r+t) + B at hp
  rw [centerArg, centerParent] at hp
  have hcentEq := hc.symm.trans hp
  change p*(r+t) = 0 + a*q + p*(r+t) + B at hcentEq
  have hB : B = -a*q := by
    linarith [hcentEq]
  have rowCenter : (P5332T1ParentRows P 1 2 t).center = ⟨q,r+t⟩ := by
    simp [P5332T1ParentRows,q,r,t]
  have valueCenter : f ⟨q,r+t⟩ = p*(r+t) := hc
  have valueEast : f ⟨q+1,r+t⟩ = p*(r+t)+a+IntegerCeilDiv (b*t) s hsn :=
      Parent2Rotation2Proof.valueEast P A f B hother hs hsn parentBd Y hdisp hAn ht0 htS hB
  have valueWest : f ⟨q-1,r+t⟩ = p*(r+t) - (p*(r+t))/q := Parent2Rotation2Proof.valueWest P hq
      f hbase hsum hqn baseBd Y hx0 htStrict
  have hdiv : (p*(r+t))/q = (p*t-1)/q + a := by
    have hnum : p*(r+t) = (p*t-1) + a*q := by nlinarith [hdet₁]
    rw [hnum, show (p*t-1) + a*q = (p*t-1) + q*a by ring,
      Int.add_mul_ediv_left _ _ hqn]
  have valueWestRow : f ⟨q-1,r+t⟩ = p*(r+t) - a - ((p*t-1)/q) := by
    rw [valueWest, hdiv]
    omega
  have valueNorth : f ⟨q,r+t+1⟩ = p*(r+t+1) := by
    have hv := hbase ⟨q,r+t+1⟩ (by change 0 ≤ q ∧ q ≤ q ∧ 0 ≤ r+t+1 ∧ r+t+1 ≤ q; omega)
    exact hv.trans (sideRight (r+t+1) (by omega) (by omega))
  have valueSouth : f ⟨q,r+t-1⟩ = p*(r+t-1) := by
    have hv := hbase ⟨q,r+t-1⟩ (by change 0 ≤ q ∧ q ≤ q ∧ 0 ≤ r+t-1 ∧ r+t-1 ≤ q; omega)
    exact hv.trans (sideRight (r+t-1) (by omega) (by omega))
  have rowValues : ∀ l : Fin 5,
      f (⟨q,r+t⟩ + (![0, 1, -1, (⟨0, 1⟩ : GaussianInt), -⟨0, 1⟩] l)) =
        (P5332T1ParentRows P 1 2 t).values l := Parent2Rotation2Proof.rowValues P f hsn Y
            valueCenter valueEast valueWestRow valueNorth valueSouth
  refine ⟨t, ht0, htStrict, ?_, hB, ?_, ?_⟩
  · simpa [rowCenter]
  · intro l
    rw [hY]
    exact rowValues l
  · constructor
    · intro h
      rw [hY] at h
      have hcomp : (⟨q,r+t⟩ : GaussianInt) - (P5332T1ParentRows P 1 2 0).companion ∈
          FordVertexDomain P.q := h
      have hw : (P5332T1ParentRows P 1 2 0).companion = ⟨s,q⟩ := by
        simp [P5332T1ParentRows,q,s]
      rw [hw] at hcomp
      change 0 ≤ q-s ∧ q-s ≤ q ∧ 0 ≤ r+t-q ∧ r+t-q ≤ q at hcomp
      omega
    · rintro ⟨htzero, heven⟩
      have hn : ¬ Even (2+1 : Nat) := by decide
      exact (hn heven).elim

end ApollonianSuperharmonic

end
