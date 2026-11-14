/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P5130T5UnitCase]

/-!
# P5130T5UnitCase

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5130T5UnitCase (P : FordFareyParameter) (hq : P.q = 1) :
    let g : IntegerLatticeFunction := fun x => x.re * (x.re - 1) / 2 + P.p * x.re * x.im
    (∀ x ∈ FordDoubledBoundary P.q,
      g x = IntegerCeilDiv (P.p * x.re * x.im) P.q (by exact_mod_cast P.q_pos.ne')) ∧
    (∀ x, g (x + ⟨0, -(P.q : Int)⟩) = g x - P.p * x.re) ∧
    (∀ x, g (x + ⟨(P.q : Int), (P.q₁ : Int)⟩) =
      g x + P.p₁ * x.re + P.p * x.im + (P.q₁ : Int) * P.p) ∧
    (∀ x, g (x + ⟨-(P.q : Int), (P.q₂ : Int)⟩) =
      g x + P.p₂ * x.re - P.p * x.im - (P.q : Int) * P.p₂) := by
-- BODY
  rcases P.unit_case hq with ⟨hp₁, hq₁, hp₂, hq₂⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [FordDoubledBoundary, FordVertexDomain, Set.mem_ofPred_eq, hq,
      Nat.cast_one] at hx
    have hre : x.re = 0 ∨ x.re = 1 := by omega
    have him : x.im = 0 ∨ x.im = 1 := by omega
    rcases hre with hr | hr <;> rcases him with hi | hi <;>
      simp [hr, hi, IntegerCeilDiv, hq]
  · intro x
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, hq, Nat.cast_one, add_zero]
    ring
  · intro x
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, hq, hp₁, hq₁, Nat.cast_one,
      Nat.cast_zero, add_zero, one_mul, zero_mul]
    have hnum : (x.re + 1) * (x.re + 1 - 1) = x.re * (x.re - 1) + 2 * x.re := by ring
    rw [hnum, Int.add_mul_ediv_left _ _ (by norm_num : (2 : Int) ≠ 0)]
    ring
  · intro x
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, hq, hp₂, hq₂, Nat.cast_one]
    have hnum : (x.re + -1) * (x.re + -1 - 1) = x.re * (x.re - 1) + 2 * (1 - x.re) := by ring
    rw [hnum, Int.add_mul_ediv_left _ _ (by norm_num : (2 : Int) ≠ 0)]
    ring

end ApollonianSuperharmonic

end
