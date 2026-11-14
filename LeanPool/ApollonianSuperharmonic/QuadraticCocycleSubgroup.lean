/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.LinearCombination

/-!
# Subgroup of quadratic cocycle translations

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Translations with an integral matrix slope and its associated quadratic cocycle. -/
def quadraticCocycleSubgroup (M : Matrix (Fin 2) (Fin 2) ℝ)
    (g : IntegerLatticeFunction) (hzero : g 0 = 0) : AddSubgroup GaussianInt := by
  classical
  exact
    { carrier := {v | ∃ a : GaussianInt,
        M.mulVec ![(v.re : ℝ), (v.im : ℝ)] = ![(a.re : ℝ), (a.im : ℝ)] ∧
        ∀ x, g (x+v) = g x + x.re*a.re + x.im*a.im + g v}
      zero_mem' := by
        refine ⟨0, ?_, ?_⟩
        · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
        · intro x; simp [hzero]
      add_mem' := by
        rintro u v ⟨a, hMa, hua⟩ ⟨b, hMb, hvb⟩
        refine ⟨a+b, ?_, ?_⟩
        · have he : ![((u+v).re : Real), ((u+v).im : Real)] =
              ![(u.re : Real), (u.im : Real)] + ![(v.re : Real), (v.im : Real)] := by
            ext i; fin_cases i <;> simp
          rw [he, Matrix.mulVec_add, hMa, hMb]
          ext i; fin_cases i <;> simp
        · intro x
          have h1 := hvb (x+u)
          have h2 := hua x
          have h3 := hvb u
          simp only [Zsqrtd.re_add, Zsqrtd.im_add] at h1 ⊢
          rw [add_assoc] at h1
          linear_combination h1 + h2 - h3
      neg_mem' := by
        rintro v ⟨a, hMa, hva⟩
        refine ⟨-a, ?_, ?_⟩
        · have he : ![((-v).re : Real), ((-v).im : Real)] =
              - ![(v.re : Real), (v.im : Real)] := by
            ext i; fin_cases i <;> simp
          rw [he, Matrix.mulVec_neg, hMa]
          ext i; fin_cases i <;> simp
        · intro x
          have h1 := hva (x-v)
          have h2 := hva (-v)
          simp only [sub_add_cancel, neg_add_cancel, Zsqrtd.re_sub,
            Zsqrtd.im_sub, Zsqrtd.re_neg, Zsqrtd.im_neg, hzero] at h1 h2
          simp only [Zsqrtd.re_neg, Zsqrtd.im_neg]
          rw [show x + -v = x-v by abel]
          linear_combination -h1 + h2 }

end ApollonianSuperharmonic

end
