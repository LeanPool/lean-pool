/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Interval

-- [TABLET NODE: P4849T1PeriodResidues]

/-!
# P4849T1PeriodResidues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1PeriodResidues (p : IntegerLatticeFunction)
    (u v : GaussianInt) (hdet : u.re * v.im - u.im * v.re ≠ 0)
    (hu : ∀ x, p (x + u) = p x) (hv : ∀ x, p (x + v) = p x) :
    ∃ R : Finset GaussianInt,
      (∀ z, ∃ r ∈ R, ∃ a b : ℤ, z = r + a • u + b • v) ∧
      (∀ a b : ℤ, ∀ x, p (x + a • u + b • v) = p x) := by
-- BODY
  classical
  let D : ℤ := u.re * v.im - u.im * v.re
  have hD : D ≠ 0 := hdet
  let R : Finset GaussianInt :=
    ((Finset.Ico (0 : ℤ) |D|).product (Finset.Ico (0 : ℤ) |D|)).image
      (fun z : ℤ × ℤ => (⟨z.1, z.2⟩ : GaussianInt))
  refine ⟨R, ?_, ?_⟩
  · intro z
    let r : GaussianInt := ⟨z.re % D, z.im % D⟩
    have hr : r ∈ R := by
      dsimp only [R]
      apply Finset.mem_image.mpr
      refine ⟨(z.re % D, z.im % D), ?_, rfl⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hD, Int.emod_lt_abs _ hD⟩,
          Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hD, Int.emod_lt_abs _ hD⟩⟩
    refine ⟨r, hr, (z.re / D) * v.im - (z.im / D) * v.re,
      -(z.re / D) * u.im + (z.im / D) * u.re, ?_⟩
    have hre := Int.emod_add_mul_ediv z.re D
    have him := Int.emod_add_mul_ediv z.im D
    ext <;> simp [r, zsmul_eq_mul] <;> dsimp [D] at hre him ⊢ <;> nlinarith
  · intro a b x
    have hup : Function.Periodic p u := hu
    have hvp : Function.Periodic p v := hv
    rw [hvp.zsmul b, hup.zsmul a]

end ApollonianSuperharmonic

end
