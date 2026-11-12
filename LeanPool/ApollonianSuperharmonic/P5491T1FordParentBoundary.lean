/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1ParentRows
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary

-- [TABLET NODE: P5491T1FordParentBoundary]

/-!
# P5491T1FordParentBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5491T1FordParentBoundary :
    ∀ (P : FordFareyParameter), ∀ (A : FordFareyParameter), (1 < P.q) → (∀ (j : Fin 2), ∀ (s :
        Fin 4), (A.p = ![P.p₁, P.p₂] j) → ((A.q = ![P.q₁, P.q₂] j) → (
    let R := P5332T1ParentRows P j s 0;
    ∃ b : ℤ, ∀ x : GaussianInt,
      x ∈ FordVertexDomain P.q → x - R.displacement ∈ FordVertexDomain A.q →
      FordOdometer A (x-R.displacement) + R.linear.re*x.re +
        R.linear.im*x.im - FordOdometer P x = b))) := by
  intro P A hq j s hp hd
-- BODY
  have hnP : (P.q : ℤ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
  have boundary (N : FordFareyParameter) (x y : ℤ)
      (hx : 0 ≤ x) (hxq : x ≤ N.q) (hy : 0 ≤ y) (hyq : y ≤ N.q)
      (hb : x = 0 ∨ x = N.q ∨ y = 0 ∨ y = N.q) :
      FordOdometer N ⟨x,y⟩ = IntegerCeilDiv (N.p*x*y) N.q
        (by exact_mod_cast N.q_pos.ne') := by
    apply (Classical.choose_spec FordOdometerFamilyExistsUnique).1.2.1
    change (0 ≤ x ∧ x ≤ (N.q : ℤ) ∧ 0 ≤ y ∧ y ≤ (N.q : ℤ)) ∧
      ¬ (2 ≤ x ∧ x ≤ (N.q : ℤ)-2 ∧ 2 ≤ y ∧ y ≤ (N.q : ℤ)-2)
    exact ⟨⟨hx,hxq,hy,hyq⟩, by
      rcases hb with h | h | h | h <;> simp [h]⟩
  have bottom (N : FordFareyParameter) (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ N.q) :
      FordOdometer N ⟨x,0⟩ = 0 := by
    rw [boundary N x 0 hx hxq (by omega) (by omega) (by omega)]
    simp [IntegerCeilDiv]
  have leftEdge (N : FordFareyParameter) (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ N.q) :
      FordOdometer N ⟨0,y⟩ = 0 := by
    rw [boundary N 0 y (by omega) (by omega) hy hyq (by omega)]
    simp [IntegerCeilDiv]
  have top (N : FordFareyParameter) (x : ℤ) (hx : 0 ≤ x) (hxq : x ≤ N.q) :
      FordOdometer N ⟨x,N.q⟩ = N.p*x := by
    rw [boundary N x N.q hx hxq (by omega) (by omega) (by omega)]
    unfold IntegerCeilDiv
    have hq : (N.q : ℤ) ≠ 0 := by exact_mod_cast N.q_pos.ne'
    rw [show -(N.p*x*(N.q : ℤ)) = (-(N.p*x))*(N.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hq]
    ring
  have rightEdge (N : FordFareyParameter) (y : ℤ) (hy : 0 ≤ y) (hyq : y ≤ N.q) :
      FordOdometer N ⟨N.q,y⟩ = N.p*y := by
    rw [boundary N N.q y (by omega) (by omega) hy hyq (by omega)]
    unfold IntegerCeilDiv
    have hq : (N.q : ℤ) ≠ 0 := by exact_mod_cast N.q_pos.ne'
    rw [show -(N.p*(N.q : ℤ)*y) = (-(N.p*y))*(N.q : ℤ) by ring,
      Int.mul_ediv_cancel _ hq]
    ring
  have parent (j' : Fin 2) (s' : Fin 4)
      (hpj : A.p = ![P.p₁, P.p₂] j') (hqj : A.q = ![P.q₁, P.q₂] j') :
      let R := P5332T1ParentRows P j' s' 0
      ∃ b : ℤ, ∀ x : GaussianInt,
        x ∈ FordVertexDomain P.q → x-R.displacement ∈ FordVertexDomain A.q →
        FordOdometer A (x-R.displacement) + R.linear.re*x.re +
          R.linear.im*x.im - FordOdometer P x = b := by
    fin_cases j' <;> fin_cases s'
    all_goals
      simp only [P5332T1ParentRows, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, Fin.isValue]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] at hpj hqj
    · refine ⟨P.p₂ * (P.q : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [] at hx hy ⊢
      have hqParent : A.q = P.q₁ := by simpa using hqj
      change FordOdometer A (⟨x,y⟩-⟨P.q₂,P.q⟩) + P.p*x + P.p₂*y -
        FordOdometer P ⟨x,y⟩ = _
      have he : y = P.q := by omega
      subst y
      rw [show (⟨x,P.q⟩-⟨P.q₂,P.q⟩ : GaussianInt) = ⟨x-P.q₂,0⟩ by ext <;> simp]
      have he' : 0 ≤ x-P.q₂ ∧ x-P.q₂ ≤ A.q := by omega
      rw [bottom A _ he'.1 he'.2, top P _ hx.1 hx.2.1]
      ring
    · refine ⟨-P.p₁ * (P.q₂ : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [] at hx hy ⊢
      have hqParent : A.q = P.q₁ := by simpa using hqj
      have he : x = 0 := by omega
      subst x
      rw [show (⟨0,y⟩-⟨-P.q₁,P.q₂⟩ : GaussianInt) = ⟨P.q₁,y-P.q₂⟩ by ext <;> simp]
      rw [leftEdge P _ hx.2.2.1 hx.2.2.2]
      -- The parent point is on its right edge by the determinant identity.
      have hpq : A.q = P.q₁ := by simpa using hqj
      have hpa : A.p = P.p₁ := by simpa using hpj
      rw [show (⟨P.q₁,y-P.q₂⟩ : GaussianInt) = ⟨A.q,y-P.q₂⟩ by simp [hpq]]
      rw [rightEdge A _ (by omega) (by omega)]
      rw [hpa]
      ring
    · refine ⟨0, ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [sub_zero] at hx hy ⊢
      have he : y = 0 := by omega
      subst y
      have hpa : A.p = P.p₁ := by simpa using hpj
      have hpq : A.q = P.q₁ := by simpa using hqj
      rw [show (⟨x,0⟩-⟨0,-P.q₁⟩ : GaussianInt) = ⟨x,P.q₁⟩ by ext <;> simp]
      rw [show (⟨x,P.q₁⟩ : GaussianInt) = ⟨x,A.q⟩ by simp [hpq],
        top A _ (by omega) (by omega), bottom P _ hx.1 hx.2.1]
      rw [hpa]
      ring
    · refine ⟨0, ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [sub_zero] at hx hy ⊢
      change 0 ≤ x-P.q ∧ x-P.q ≤ A.q ∧ 0 ≤ y ∧ y ≤ A.q at hy
      have he : x = P.q := by omega
      subst x
      rw [show (⟨P.q,y⟩-⟨P.q,0⟩ : GaussianInt) = ⟨0,y⟩ by ext <;> simp,
        leftEdge A _ (by omega) (by omega), rightEdge P _ hx.2.2.1 hx.2.2.2]
      ring
    · refine ⟨0, ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [sub_zero] at hx hy ⊢
      have hqParent : A.q = P.q₂ := by simpa using hqj
      have he : x = 0 := by omega
      subst x
      have hpa : A.p = P.p₂ := by simpa using hpj
      rw [show (⟨0,y⟩-⟨-P.q₂,0⟩ : GaussianInt) = ⟨P.q₂,y⟩ by ext <;> simp,
        show (⟨P.q₂,y⟩ : GaussianInt) = ⟨A.q,y⟩ by simp [hqParent],
        rightEdge A _ (by omega) (by omega), leftEdge P _ hx.2.2.1 hx.2.2.2,
        hpa]
      ring
    · refine ⟨-P.p₂ * (P.q₁ : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [] at hx hy ⊢
      have hqParent : A.q = P.q₂ := by simpa using hqj
      have he : y = 0 := by omega
      subst y
      have hpa : A.p = P.p₂ := by simpa using hpj
      rw [show (⟨x,0⟩-⟨P.q₁,-P.q₂⟩ : GaussianInt) = ⟨x-P.q₁,P.q₂⟩ by
        ext <;> simp,
        show (⟨x-P.q₁,P.q₂⟩ : GaussianInt) = ⟨x-P.q₁,A.q⟩ by simp [hqParent],
        top A _ (by omega) (by omega), bottom P _ hx.1 hx.2.1, hpa]
      ring
    · refine ⟨P.p₁ * (P.q : ℤ), ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [] at hx hy ⊢
      have hqParent : A.q = P.q₂ := by simpa using hqj
      have he : x = P.q := by omega
      subst x
      rw [show (⟨P.q,y⟩-⟨P.q,P.q₁⟩ : GaussianInt) = ⟨0,y-P.q₁⟩ by
        ext <;> simp,
        leftEdge A _ (by omega) (by omega), rightEdge P _ hx.2.2.1 hx.2.2.2]
      ring
    · refine ⟨0, ?_⟩
      rintro ⟨x,y⟩ hx hy
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub,
        Zsqrtd.im_sub] at hx hy
      simp only [sub_zero] at hx hy ⊢
      have hqParent : A.q = P.q₂ := by simpa using hqj
      have he : y = P.q := by omega
      subst y
      rw [show (⟨x,P.q⟩-⟨0,P.q⟩ : GaussianInt) = ⟨x,0⟩ by ext <;> simp,
        bottom A _ (by omega) (by omega), top P _ hx.1 hx.2.1]
      ring
  dsimp only
  exact parent j s hp hd

end ApollonianSuperharmonic

end
