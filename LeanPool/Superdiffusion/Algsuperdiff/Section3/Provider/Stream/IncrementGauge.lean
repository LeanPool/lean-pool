/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellSum

/-!
# IncrementGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Subadditivity of the local cube derivative gauges

The two derivative gauges of
`Algsuperdiff.Section3.Provider.Stream.ShellDerivativeControl` are raw suprema
over an open origin cube, so they obey the triangle inequality along the
additive layer of `Algsuperdiff.Section3.Provider.Stream.ShellSum`.

## Main results

* `localCubeDerivNorm_add_le`, `localCubeSecondDerivNorm_add_le`: the binary
  triangle inequality for the two open-cube gauges.
* `localCubeDerivNorm_sum_le`, `localCubeSecondDerivNorm_sum_le`: the finite
  triangle inequality along `ShellField.sum`.
* `localCubeDerivNorm_translate_shellIncrement_le`,
  `localCubeSecondDerivNorm_translate_shellIncrement_le`: the same for the
  literal stream increment `k_m - k_n` on a translated cube.

## References

* ABK26, `e.Bosc.def`, `e.Bosc.decomp`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Set
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The two induced matrix-derivative norms vanish at zero -/

theorem matrixDerivativeNorm_zero_le :
    ShellField.matrixDerivativeNorm (0 : ShellField.MatrixDerivative d) ≤ 0 := by
  rw [matrixDerivativeNorm_le_iff]
  refine ⟨le_refl 0, fun v _ => le_of_eq ?_⟩
  show matrixOperatorNorm ((0 : ShellField.MatrixDerivative d) v) = 0
  rw [zero_apply, matrixOperatorNorm_zero]

theorem matrixSecondDerivativeNorm_zero_le :
    ShellField.matrixSecondDerivativeNorm
      (0 : ShellField.MatrixSecondDerivative d) ≤ 0 := by
  rw [ShellField.matrixSecondDerivativeNorm_le_iff]
  refine ⟨le_refl 0, fun u _ => ?_⟩
  show ShellField.matrixDerivativeNorm
    ((0 : ShellField.MatrixSecondDerivative d) u) ≤ 0
  rw [zero_apply]
  exact matrixDerivativeNorm_zero_le

/-! ## The gauges of the zero shell field -/

@[simp]
theorem localCubeDerivNorm_zero_field (ell : ℤ) :
    localCubeDerivNorm ell (ShellField.zero d) = 0 := by
  refine le_antisymm ?_ (localCubeDerivNorm_nonneg ell _)
  refine localCubeDerivNorm_le_of_forall ell _ (le_refl 0) fun x _ => ?_
  rw [ShellField.zero_deriv]
  exact matrixDerivativeNorm_zero_le

@[simp]
theorem localCubeSecondDerivNorm_zero_field (ell : ℤ) :
    localCubeSecondDerivNorm ell (ShellField.zero d) = 0 := by
  refine le_antisymm ?_ (localCubeSecondDerivNorm_nonneg ell _)
  refine localCubeSecondDerivNorm_le_of_forall ell _ (le_refl 0) fun x _ => ?_
  rw [ShellField.zero_secondDeriv]
  exact matrixSecondDerivativeNorm_zero_le

/-! ## Binary triangle inequalities -/

/-- `||grad (j + k)||_{L∞(cu_ell)} <= ||grad j|| + ||grad k||`. -/
theorem localCubeDerivNorm_add_le (ell : ℤ) (j k : ShellField d) :
    localCubeDerivNorm ell (ShellField.add j k) ≤
      localCubeDerivNorm ell j + localCubeDerivNorm ell k := by
  refine localCubeDerivNorm_le_of_forall ell _
    (add_nonneg (localCubeDerivNorm_nonneg ell j)
      (localCubeDerivNorm_nonneg ell k)) ?_
  intro x hx
  rw [ShellField.add_deriv]
  exact (ShellField.matrixDerivativeNorm_add_le _ _).trans
    (add_le_add (matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell j hx)
      (matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell k hx))

/-- `||grad² (j + k)||_{L∞(cu_ell)} <= ||grad² j|| + ||grad² k||`. -/
theorem localCubeSecondDerivNorm_add_le (ell : ℤ) (j k : ShellField d) :
    localCubeSecondDerivNorm ell (ShellField.add j k) ≤
      localCubeSecondDerivNorm ell j + localCubeSecondDerivNorm ell k := by
  refine localCubeSecondDerivNorm_le_of_forall ell _
    (add_nonneg (localCubeSecondDerivNorm_nonneg ell j)
      (localCubeSecondDerivNorm_nonneg ell k)) ?_
  intro x hx
  rw [ShellField.add_secondDeriv]
  exact (ShellField.matrixSecondDerivativeNorm_add_le _ _).trans
    (add_le_add
      (matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm ell j hx)
      (matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm ell k hx))

/-! ## Finite triangle inequalities -/

/-- `||grad (sum_i j_i)||_{L∞(cu_ell)} <= sum_i ||grad j_i||_{L∞(cu_ell)}`. -/
theorem localCubeDerivNorm_sum_le (ell : ℤ) {ι : Type*} (s : Finset ι)
    (f : ι → ShellField d) :
    localCubeDerivNorm ell (ShellField.sum s f) ≤
      ∑ i ∈ s, localCubeDerivNorm ell (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [ShellField.sum_empty, Finset.sum_empty, localCubeDerivNorm_zero_field]
  | cons a s ha ih =>
      rw [ShellField.sum_cons, Finset.sum_cons]
      have hadd := localCubeDerivNorm_add_le ell (f a) (ShellField.sum s f)
      linarith

/-- `||grad² (sum_i j_i)||_{L∞(cu_ell)} <= sum_i ||grad² j_i||_{L∞(cu_ell)}`. -/
theorem localCubeSecondDerivNorm_sum_le (ell : ℤ) {ι : Type*} (s : Finset ι)
    (f : ι → ShellField d) :
    localCubeSecondDerivNorm ell (ShellField.sum s f) ≤
      ∑ i ∈ s, localCubeSecondDerivNorm ell (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [ShellField.sum_empty, Finset.sum_empty,
        localCubeSecondDerivNorm_zero_field]
  | cons a s ha ih =>
      rw [ShellField.sum_cons, Finset.sum_cons]
      have hadd := localCubeSecondDerivNorm_add_le ell (f a) (ShellField.sum s f)
      linarith

/-! ## The literal stream increment -/

/-- The literal-increment first-derivative triangle inequality
`||grad (k_m - k_n)||_{L∞(z + cu_ell)} <= sum_{k in (n,m]} ||grad j_k||`. -/
theorem localCubeDerivNorm_translate_shellIncrement_le (ell : ℤ) (z : Vec d)
    (omega : Algsuperdiff.Section3.Cutoff.ShellSeq d) (n m : ℤ) :
    localCubeDerivNorm ell
        (ShellField.translate z (shellIncrement omega n m)) ≤
      ∑ k ∈ Finset.Ioc n m,
        localCubeDerivNorm ell (ShellField.translate z (omega k)) := by
  rw [shellIncrement, ShellField.translate_sum]
  exact localCubeDerivNorm_sum_le ell (Finset.Ioc n m)
    fun k => ShellField.translate z (omega k)

/-- The literal-increment second-derivative triangle inequality. -/
theorem localCubeSecondDerivNorm_translate_shellIncrement_le (ell : ℤ) (z : Vec d)
    (omega : Algsuperdiff.Section3.Cutoff.ShellSeq d) (n m : ℤ) :
    localCubeSecondDerivNorm ell
        (ShellField.translate z (shellIncrement omega n m)) ≤
      ∑ k ∈ Finset.Ioc n m,
        localCubeSecondDerivNorm ell (ShellField.translate z (omega k)) := by
  rw [shellIncrement, ShellField.translate_sum]
  exact localCubeSecondDerivNorm_sum_le ell (Finset.Ioc n m)
    fun k => ShellField.translate z (omega k)

end

end Algsuperdiff.Section3.Provider.Stream
