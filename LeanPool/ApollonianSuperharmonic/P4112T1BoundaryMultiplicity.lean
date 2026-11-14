/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeRectangleBoundary

public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderPaths
public import LeanPool.ApollonianSuperharmonic.FordBoundaryMultiplicity
public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.BigOperators.Fin

/-!
# P4112T1BoundaryMultiplicity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic


-- [TABLET NODE: P4112T1BoundaryMultiplicity]
theorem P4112T1BoundaryMultiplicity (P : FordFareyParameter) (hP : 2 < P.q) :
    let B := P4062T1RemainderPaths P
    ∀ j, ∀ x ∈ (B j).1,
      FordBoundaryMultiplicity P x = (if x = (B j).2 then 3 else 2) := by
-- BODY
  classical
  intro B j x hx
  change x ∈ (P4062T1RemainderPaths P j).1 at hx
  change FordBoundaryMultiplicity P x =
    (if x = (P4062T1RemainderPaths P j).2 then 3 else 2)
  have hrpos : 0 < P.q₁ := by
    by_contra h
    have hzero : P.q₁ = 0 := by omega
    have hq : (P.q : Int) = (P.q₂ : Int) := by
      rw [P.sum_q, hzero]
      simp
    have hqNat := P.sum_q
    rw [hzero] at hqNat
    have hdet := P.det₁
    rw [hq] at hdet
    rw [hzero] at hdet
    have hprod : P.p₁ * (P.q₂ : Int) = 1 := by simpa using hdet
    have hdiv : (P.q₂ : Int) ∣ 1 := ⟨P.p₁, by
      rw [Int.mul_comm]
      exact hprod.symm⟩
    have hunit := Int.eq_one_of_dvd_one (by omega) hdiv
    have : P.q₂ = 1 := by exact_mod_cast hunit
    omega
  have hq : (P.q : Int) = (P.q₁ : Int) + P.q₂ := by
    exact_mod_cast P.sum_q
  have hcross : P.p₁ * (P.q₂ : Int) - P.p₂ * P.q₁ = 1 := by
    calc
      P.p₁ * (P.q₂ : Int) - P.p₂ * P.q₁ =
          P.p₁ * (P.q : Int) - P.q₁ * P.p := by
            rw [P.sum_q, P.sum_p]
            push_cast
            ring
      _ = 1 := P.det₁
  have hneq : P.q₁ ≠ P.q₂ := by
    intro heq
    have hq1 : P.q₁ = 1 := by
      have hd : (P.p₁ - P.p₂) * (P.q₁ : Int) = 1 := by
        rw [heq] at hcross
        nlinarith [hcross]
      have hdiv : (P.q₁ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, by
        rw [Int.mul_comm]
        exact hd.symm⟩
      have hunit := Int.eq_one_of_dvd_one (by omega) hdiv
      exact_mod_cast hunit
    have hqNat := P.sum_q
    omega
  have b0 : x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) ↔
      (0 : Int) ≤ x.re ∧ x.re ≤ P.q₁ ∧ (0 : Int) ≤ x.im ∧ x.im ≤ P.q₁ ∧
        (x.re = 0 ∨ x.re = P.q₁ ∨ x.im = 0 ∨ x.im = P.q₁) := by
    change x ∈ LatticeVertexBoundary {z : GaussianInt |
      0 ≤ z.re ∧ z.re ≤ P.q₁ ∧ 0 ≤ z.im ∧ z.im ≤ P.q₁} ↔ _
    rw [LatticeVertexBoundary.rectangle]
    simp only [and_assoc]
  have b1 : x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) ↔
      (P.q₂ : Int) ≤ x.re ∧ x.re ≤ P.q ∧ P.q₂ ≤ x.im ∧ x.im ≤ P.q ∧
        (x.re = P.q₂ ∨ x.re = P.q ∨ x.im = P.q₂ ∨ x.im = P.q) := by
    change x ∈ LatticeVertexBoundary {z : GaussianInt |
      P.q₂ ≤ z.re ∧ z.re ≤ P.q ∧ P.q₂ ≤ z.im ∧ z.im ≤ P.q} ↔ _
    rw [LatticeVertexBoundary.rectangle]
    simp only [and_assoc]
  have b2 : x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) ↔
      (P.q₁ : Int) ≤ x.re ∧ x.re ≤ P.q ∧ (0 : Int) ≤ x.im ∧ x.im ≤ P.q₂ ∧
        (x.re = P.q₁ ∨ x.re = P.q ∨ x.im = 0 ∨ x.im = P.q₂) := by
    change x ∈ LatticeVertexBoundary {z : GaussianInt |
      P.q₁ ≤ z.re ∧ z.re ≤ P.q ∧ 0 ≤ z.im ∧ z.im ≤ P.q₂} ↔ _
    rw [LatticeVertexBoundary.rectangle]
    simp only [and_assoc]
  have b3 : x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) ↔
      (0 : Int) ≤ x.re ∧ x.re ≤ P.q₂ ∧ P.q₁ ≤ x.im ∧ x.im ≤ P.q ∧
        (x.re = 0 ∨ x.re = P.q₂ ∨ x.im = P.q₁ ∨ x.im = P.q) := by
    change x ∈ LatticeVertexBoundary {z : GaussianInt |
      0 ≤ z.re ∧ z.re ≤ P.q₂ ∧ P.q₁ ≤ z.im ∧ z.im ≤ P.q} ↔ _
    rw [LatticeVertexBoundary.rectangle]
    simp only [and_assoc]
  have count : FordBoundaryMultiplicity P x =
      (if (0 : Int) ≤ x.re ∧ x.re ≤ P.q₁ ∧ 0 ≤ x.im ∧ x.im ≤ P.q₁ ∧
          (x.re = 0 ∨ x.re = P.q₁ ∨ x.im = 0 ∨ x.im = P.q₁) then 1 else 0) +
      (if (P.q₂ : Int) ≤ x.re ∧ x.re ≤ P.q ∧ P.q₂ ≤ x.im ∧ x.im ≤ P.q ∧
          (x.re = P.q₂ ∨ x.re = P.q ∨ x.im = P.q₂ ∨ x.im = P.q) then 1 else 0) +
      (if (P.q₁ : Int) ≤ x.re ∧ x.re ≤ P.q ∧ 0 ≤ x.im ∧ x.im ≤ P.q₂ ∧
          (x.re = P.q₁ ∨ x.re = P.q ∨ x.im = 0 ∨ x.im = P.q₂) then 1 else 0) +
    (if 0 ≤ x.re ∧ x.re ≤ P.q₂ ∧ P.q₁ ≤ x.im ∧ x.im ≤ P.q ∧
          (x.re = 0 ∨ x.re = P.q₂ ∨ x.im = P.q₁ ∨ x.im = P.q) then 1 else 0) := by
    simp only [FordBoundaryMultiplicity, Finset.card_filter,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 0) then 1 else 0) +
      ((if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 1) then 1 else 0) +
      ((if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 2) then 1 else 0) +
      (if x ∈ LatticeVertexBoundary (FordRecursiveVertexDomains P 3) then 1 else 0))) = _
    simp only [b0, b1, b2, b3]
    omega
  rw [count]
  by_cases hlt : P.q₂ < P.q₁
  · fin_cases j
    · simp only [P4062T1RemainderPaths, hlt] at ⊢
      have hle : P.q₂ ≤ P.q₁ := Nat.le_of_lt hlt
      simp only [P4062T1RemainderPaths, hlt, ↓reduceIte, Int.reduceNeg, P4062T1InteriorSquare,
          Finset.product_eq_sprod, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
          Prod.exists] at hx
      rcases hx with ⟨⟨a, b, hmem, heq⟩, hp⟩
      rcases hmem with ⟨⟨ha1, ha2⟩, hb1, hb2⟩
      subst x
      simp only at hp
      by_cases hroot : (⟨a, b⟩ : GaussianInt) = ⟨(P.q₁ : Int), (P.q₂ : Int)⟩
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq] at hroot
        rcases hroot with ⟨rfl, rfl⟩
        simp_all []
      · rcases hp with hp | hp <;> rcases hp with ⟨h1, h2⟩ <;>
          simp_all [] <;>
            split_ifs <;> omega
    · simp only [P4062T1RemainderPaths, hlt] at ⊢
      have hle : P.q₂ ≤ P.q₁ := Nat.le_of_lt hlt
      simp only [P4062T1RemainderPaths, hlt, ↓reduceIte, Int.reduceNeg, P4062T1InteriorSquare,
          Finset.product_eq_sprod, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
          Finset.mem_Icc, Prod.exists] at hx
      rcases hx with ⟨⟨a, b, hmem, heq⟩, hp⟩
      rcases hmem with ⟨⟨ha1, ha2⟩, hb1, hb2⟩
      subst x
      simp only at hp
      by_cases hroot : (⟨a, b⟩ : GaussianInt) = ⟨(P.q₂ : Int), (P.q₁ : Int)⟩
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq] at hroot
        rcases hroot with ⟨rfl, rfl⟩
        simp_all []
      · rcases hp with hp | hp <;> rcases hp with ⟨h1, h2⟩ <;>
          simp_all [] <;>
            split_ifs <;> omega
  · fin_cases j
    · simp only [P4062T1RemainderPaths, hlt] at ⊢
      have hleNat : P.q₁ ≤ P.q₂ := Nat.le_of_not_gt hlt
      have hlt' : P.q₁ < P.q₂ := Nat.lt_of_le_of_ne hleNat hneq
      have hle : P.q₁ ≤ P.q₂ := Nat.le_of_lt hlt'
      simp only [P4062T1RemainderPaths, hlt, ↓reduceIte, Int.reduceNeg, P4062T1InteriorSquare,
          Finset.product_eq_sprod, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
          Prod.exists] at hx
      rcases hx with ⟨⟨a, b, hmem, heq⟩, hp⟩
      rcases hmem with ⟨⟨ha1, ha2⟩, hb1, hb2⟩
      subst x
      simp only at hp
      by_cases hroot : (⟨a, b⟩ : GaussianInt) = ⟨(P.q₁ : Int), (P.q₁ : Int)⟩
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq] at hroot
        rcases hroot with ⟨rfl, rfl⟩
        simp_all []
      · rcases hp with hp | hp <;> rcases hp with ⟨h1, h2⟩ <;>
          simp_all [] <;>
            split_ifs <;> omega
    · simp only [P4062T1RemainderPaths, hlt] at ⊢
      have hleNat : P.q₁ ≤ P.q₂ := Nat.le_of_not_gt hlt
      have hlt' : P.q₁ < P.q₂ := Nat.lt_of_le_of_ne hleNat hneq
      have hle : P.q₁ ≤ P.q₂ := Nat.le_of_lt hlt'
      simp only [P4062T1RemainderPaths, hlt, ↓reduceIte, Int.reduceNeg, P4062T1InteriorSquare,
          Finset.product_eq_sprod, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
          Finset.mem_Icc, Prod.exists] at hx
      rcases hx with ⟨⟨a, b, hmem, heq⟩, hp⟩
      rcases hmem with ⟨⟨ha1, ha2⟩, hb1, hb2⟩
      subst x
      simp only at hp
      by_cases hroot : (⟨a, b⟩ : GaussianInt) = ⟨(P.q₂ : Int), (P.q₂ : Int)⟩
      · simp only [Int.reduceNeg, Zsqrtd.mk.injEq] at hroot
        rcases hroot with ⟨rfl, rfl⟩
        simp_all []
      · rcases hp with hp | hp <;> rcases hp with ⟨h1, h2⟩ <;>
          simp_all [] <;>
            split_ifs <;> omega

end ApollonianSuperharmonic

end
