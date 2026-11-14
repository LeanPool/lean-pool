/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5130T5Prescription
public import LeanPool.ApollonianSuperharmonic.P5130T5ParentArithmetic
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains

-- [TABLET NODE: P5130T5MixedOverlaps]

/-!
# P5130T5MixedOverlaps

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5130T5MixedOverlaps (P P₁ P₂ : FordFareyParameter)
    (hq : 1 < P.q) (hp₁ : P₁.p = P.p₁) (hq₁ : P₁.q = P.q₁)
    (hp₂ : P₂.p = P.p₂) (hq₂ : P₂.q = P.q₂)
    (g₁ g₂ : IntegerLatticeFunction)
    (h₁ : ∀ x ∈ FordDoubledBoundary P₁.q,
      g₁ x = IntegerCeilDiv (P₁.p * x.re * x.im) P₁.q (by exact_mod_cast P₁.q_pos.ne'))
    (h₂ : ∀ x ∈ FordDoubledBoundary P₂.q,
      g₂ x = IntegerCeilDiv (P₂.p * x.re * x.im) P₂.q (by exact_mod_cast P₂.q_pos.ne')) :
    let F := P5130T5Prescription P g₁ g₂
    (∀ x, x ∈ FordRecursiveVertexDomains P 0 → x ∈ FordRecursiveVertexDomains P 2 → F 0 x = F 2 x) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains P 0 → x ∈ FordRecursiveVertexDomains P 3 → F 0 x = F 3 x) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains P 1 → x ∈ FordRecursiveVertexDomains P 2 → F 1 x = F 2 x) ∧
    (∀ x, x ∈ FordRecursiveVertexDomains P 1 → x ∈ FordRecursiveVertexDomains P 3 → F 1 x = F 3
        x) := by
-- BODY
  have edges (R : FordFareyParameter) (g : IntegerLatticeFunction)
      (h : ∀ x ∈ FordDoubledBoundary R.q,
        g x = IntegerCeilDiv (R.p * x.re * x.im) R.q (by exact_mod_cast R.q_pos.ne'))
      (t : Int) (ht : 0 ≤ t) (htq : t ≤ (R.q : Int)) :
      g ⟨R.q, t⟩ = R.p * t ∧ g ⟨t, R.q⟩ = R.p * t ∧
        g ⟨0, t⟩ = 0 ∧ g ⟨t, 0⟩ = 0 := by
    have hq : 0 < (R.q : Int) := by exact_mod_cast R.q_pos
    have bound (u v : Int) (hu : 0 ≤ u) (huq : u ≤ (R.q : Int))
        (hv : 0 ≤ v) (hvq : v ≤ (R.q : Int))
        (he : u = 0 ∨ u = (R.q : Int) ∨ v = 0 ∨ v = (R.q : Int)) :
        (⟨u, v⟩ : GaussianInt) ∈ FordDoubledBoundary R.q := by
      change (0 ≤ u ∧ u ≤ (R.q : Int) ∧ 0 ≤ v ∧ v ≤ (R.q : Int)) ∧
        ¬(2 ≤ u ∧ u ≤ (R.q : Int) - 2 ∧ 2 ≤ v ∧ v ≤ (R.q : Int) - 2)
      exact ⟨⟨hu, huq, hv, hvq⟩, by omega⟩
    have e₁ := h ⟨R.q, t⟩ (bound _ _ hq.le le_rfl ht htq (Or.inr (Or.inl rfl)))
    have e₂ := h ⟨t, R.q⟩ (bound _ _ ht htq hq.le le_rfl (Or.inr (Or.inr (Or.inr rfl))))
    have e₃ := h ⟨0, t⟩ (bound _ _ le_rfl hq.le ht htq (Or.inl rfl))
    have e₄ := h ⟨t, 0⟩ (bound _ _ ht htq le_rfl hq.le (Or.inr (Or.inr (Or.inl rfl))))
    have div₁ : IntegerCeilDiv (R.p * (R.q : Int) * t) R.q (by omega) = R.p * t := by
      dsimp only [IntegerCeilDiv]
      have he : -(R.p * (R.q : Int) * t) = (R.q : Int) * (-R.p * t) := by ring
      rw [he, Int.mul_ediv_cancel_left _ hq.ne']
      ring
    have div₂ : IntegerCeilDiv (R.p * t * (R.q : Int)) R.q (by omega) = R.p * t := by
      rw [show R.p * t * (R.q : Int) = R.p * (R.q : Int) * t by ring]
      exact div₁
    exact ⟨e₁.trans div₁, e₂.trans div₂, by simpa [IntegerCeilDiv] using e₃,
      by simpa [IntegerCeilDiv] using e₄⟩
  have ea (t : Int) (ht : 0 ≤ t) (htq : t ≤ (P.q₁ : Int)) :
      g₁ ⟨P.q₁, t⟩ = P.p₁ * t ∧ g₁ ⟨t, P.q₁⟩ = P.p₁ * t ∧
        g₁ ⟨0, t⟩ = 0 ∧ g₁ ⟨t, 0⟩ = 0 := by
    simpa only [hp₁, hq₁] using edges P₁ g₁ h₁ t ht (by simpa only [hq₁] using htq)
  have eb (t : Int) (ht : 0 ≤ t) (htq : t ≤ (P.q₂ : Int)) :
      g₂ ⟨P.q₂, t⟩ = P.p₂ * t ∧ g₂ ⟨t, P.q₂⟩ = P.p₂ * t ∧
        g₂ ⟨0, t⟩ = 0 ∧ g₂ ⟨t, 0⟩ = 0 := by
    simpa only [hp₂, hq₂] using edges P₂ g₂ h₂ t ht (by simpa only [hq₂] using htq)
  have hsum : (P.q : Int) = P.q₁ + P.q₂ := by exact_mod_cast P.sum_q
  have hcross := (P5130T5ParentArithmetic P hq).2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hy
    simp only [FordRecursiveVertexDomains, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero,
        Set.mem_ofPred_eq, Matrix.cons_val] at hx hy
    have hr : x.re = (P.q₁ : Int) := by omega
    have ex : x = ⟨P.q₁, x.im⟩ := by ext <;> simp [hr]
    have ey : x - ⟨(P.q₁ : Int), 0⟩ = (⟨0, x.im⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hr]
    change g₁ x = g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im
    calc
      g₁ x = g₁ ⟨P.q₁, x.im⟩ := congrArg g₁ ex
      _ = P.p₁ * x.im := (ea x.im (by omega) (by omega)).1
      _ = g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im := by
        rw [ey, (eb x.im (by omega) (by omega)).2.2.1, zero_add]
  · intro x hx hy
    simp only [FordRecursiveVertexDomains, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero,
        Set.mem_ofPred_eq, Matrix.cons_val] at hx hy
    have hi : x.im = (P.q₁ : Int) := by omega
    have ex : x = ⟨x.re, P.q₁⟩ := by ext <;> simp [hi]
    have ey : x - ⟨0, (P.q₁ : Int)⟩ = (⟨x.re, 0⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hi]
    change g₁ x = g₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re
    calc
      g₁ x = g₁ ⟨x.re, P.q₁⟩ := congrArg g₁ ex
      _ = P.p₁ * x.re := (ea x.re (by omega) (by omega)).2.1
      _ = g₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re := by
        rw [ey, (eb x.re (by omega) (by omega)).2.2.2, zero_add]
  · intro x hx hy
    simp only [FordRecursiveVertexDomains, Int.reduceNeg, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, Set.mem_ofPred_eq, Matrix.cons_val] at hx hy
    have hi : x.im = (P.q₂ : Int) := by omega
    have ex : x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ = (⟨x.re - P.q₂, 0⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hi]
    have ey : x - ⟨(P.q₁ : Int), 0⟩ = (⟨x.re - P.q₁, P.q₂⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hi]
    change g₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
      P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1 =
      g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im
    rw [ex, ey, (ea (x.re - P.q₂) (by omega) (by omega)).2.2.2,
      (eb (x.re - P.q₁) (by omega) (by omega)).2.1, hi]
    nlinarith [hcross]
  · intro x hx hy
    simp only [FordRecursiveVertexDomains, Int.reduceNeg, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, Set.mem_ofPred_eq, Matrix.cons_val] at hx hy
    have hr : x.re = (P.q₂ : Int) := by omega
    have ex : x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ = (⟨0, x.im - P.q₂⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hr]
    have ey : x - ⟨0, (P.q₁ : Int)⟩ = (⟨P.q₂, x.im - P.q₁⟩ : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hr]
    change g₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
      P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1 =
      g₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re
    rw [ex, ey, (ea (x.im - P.q₂) (by omega) (by omega)).2.2.1,
      (eb (x.im - P.q₁) (by omega) (by omega)).1, hr]
    nlinarith [hcross]

end ApollonianSuperharmonic

end
