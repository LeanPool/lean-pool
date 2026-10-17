/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of alternating trilinear forms

This file constructs the scalar extension of an alternating trilinear form. The construction is
written for three variables, which is the case used by vector products on oriented rank-three
modules. It first extends the curried trilinear map one variable at a time and then verifies that
the resulting form remains alternating, without any assumption that two is invertible.

## Main definitions

* `AlternatingMap.baseChangeAlternatingFinThree` : scalar extension of an alternating trilinear
  form.

## Main results

* `AlternatingMap.baseChangeAlternatingFinThree_tmul` : evaluation on pure tensors.
* `AlternatingMap.baseChangeFinThree_mul_eq_det` : scalar extension preserves the determinant
  identity coupling a form on a module to one on its dual.
-/

@[expose] public section

universe u v w

open Matrix TensorProduct

namespace AlternatingMap

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {S : Type w} [CommRing S] [Algebra R S]

/-- An alternating trilinear form, curried as two linear maps followed by a dual vector. -/
noncomputable def curryFinThree (a : M [⋀^Fin 3]→ₗ[R] R) :
    M →ₗ[R] M →ₗ[R] Module.Dual R M :=
  let z : M [⋀^Fin 0]→ₗ[R] R ≃ₗ[R] R := constLinearEquivOfIsEmpty.symm
  let y₁ : M [⋀^Fin 1]→ₗ[R] R →ₗ[R] Module.Dual R M :=
    LinearMap.llcomp R M (M [⋀^Fin 0]→ₗ[R] R) R z ∘ₗ curryLeftLinearMap
  let y₂ : M [⋀^Fin 2]→ₗ[R] R →ₗ[R] M →ₗ[R] Module.Dual R M :=
    LinearMap.llcomp R M (M [⋀^Fin 1]→ₗ[R] R) (Module.Dual R M) y₁ ∘ₗ
      curryLeftLinearMap
  LinearMap.llcomp R M (M [⋀^Fin 2]→ₗ[R] R) (M →ₗ[R] Module.Dual R M) y₂
    a.curryLeft

@[simp] theorem curryFinThree_apply (a : M [⋀^Fin 3]→ₗ[R] R) (x y z : M) :
    curryFinThree a x y z = a ![x, y, z] := by
  simp [curryFinThree, Matrix.vecCons, Matrix.vecEmpty]

/-- The scalar extension of the curried trilinear map underlying an alternating trilinear
form. -/
noncomputable def baseChangeFinThree (a : M [⋀^Fin 3]→ₗ[R] R) :
    (S ⊗[R] M) →ₗ[S] (S ⊗[R] M) →ₗ[S] Module.Dual S (S ⊗[R] M) :=
  let middleR : M →ₗ[R] M →ₗ[R] Module.Dual S (S ⊗[R] M) :=
    (curryFinThree a).compr₂ (Module.Dual.baseChange (R := R) (V := M) S)
  let outerR : M →ₗ[R] (S ⊗[R] M) →ₗ[S] Module.Dual S (S ⊗[R] M) :=
    { toFun := fun x ↦ (middleR x).liftBaseChange S
      map_add' := by intro x y; ext z; simp [middleR]
      map_smul' := by intro r x; ext z; simp [middleR] }
  outerR.liftBaseChange S

@[simp] theorem baseChangeFinThree_tmul (a : M [⋀^Fin 3]→ₗ[R] R)
    (r s t : S) (x y z : M) :
    baseChangeFinThree (S := S) a (r ⊗ₜ[R] x) (s ⊗ₜ[R] y) (t ⊗ₜ[R] z) =
      r * s * t * algebraMap R S (a ![x, y, z]) := by
  simp [baseChangeFinThree, Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  ring

private theorem fin_three_swap_zero_one (a : M [⋀^Fin 3]→ₗ[R] R) (x y z : M) :
    a ![x, y, z] = -a ![y, x, z] := by
  have h := a.map_swap ![x, y, z] (show (0 : Fin 3) ≠ 1 by decide)
  have heq : ![x, y, z] ∘ Equiv.swap (0 : Fin 3) 1 = ![y, x, z] := by
    ext i
    fin_cases i <;> rfl
  rw [heq] at h
  rw [h, neg_neg]

private theorem fin_three_swap_one_two (a : M [⋀^Fin 3]→ₗ[R] R) (x y z : M) :
    a ![x, y, z] = -a ![x, z, y] := by
  have h := a.map_swap ![x, y, z] (show (1 : Fin 3) ≠ 2 by decide)
  have heq : ![x, y, z] ∘ Equiv.swap (1 : Fin 3) 2 = ![x, z, y] := by
    ext i
    fin_cases i <;> rfl
  rw [heq] at h
  rw [h, neg_neg]

theorem baseChangeFinThree_swap_zero_one (a : M [⋀^Fin 3]→ₗ[R] R)
    (x y z : S ⊗[R] M) :
    baseChangeFinThree (S := S) a x y z = -baseChangeFinThree (S := S) a y x z := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx']; abel
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [hy, hy']; abel
    | tmul s y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp [hz, hz']; abel
      | tmul t z =>
        rw [baseChangeFinThree_tmul, baseChangeFinThree_tmul, fin_three_swap_zero_one]
        simp only [map_neg]
        ring

theorem baseChangeFinThree_swap_one_two (a : M [⋀^Fin 3]→ₗ[R] R)
    (x y z : S ⊗[R] M) :
    baseChangeFinThree (S := S) a x y z = -baseChangeFinThree (S := S) a x z y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx']; abel
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [hy, hy']; abel
    | tmul s y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp [hz, hz']; abel
      | tmul t z =>
        rw [baseChangeFinThree_tmul, baseChangeFinThree_tmul, fin_three_swap_one_two]
        simp only [map_neg]
        ring

theorem baseChangeFinThree_self_zero_one (a : M [⋀^Fin 3]→ₗ[R] R)
    (x z : S ⊗[R] M) : baseChangeFinThree (S := S) a x x z = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy, baseChangeFinThree_swap_zero_one a y x z]
    abel
  | tmul r x =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp [hz, hz']
    | tmul t z =>
      rw [baseChangeFinThree_tmul]
      rw [a.map_eq_zero_of_eq ![x, x, z] (by rfl) (show (0 : Fin 3) ≠ 1 by decide)]
      simp

theorem baseChangeFinThree_self_one_two (a : M [⋀^Fin 3]→ₗ[R] R)
    (x y : S ⊗[R] M) : baseChangeFinThree (S := S) a x y y = 0 := by
  rw [baseChangeFinThree_swap_zero_one a x y y,
    baseChangeFinThree_swap_one_two a y x y,
    baseChangeFinThree_self_zero_one, neg_neg]

theorem baseChangeFinThree_self_zero_two (a : M [⋀^Fin 3]→ₗ[R] R)
    (x y : S ⊗[R] M) : baseChangeFinThree (S := S) a x y x = 0 := by
  rw [baseChangeFinThree_swap_zero_one a x y x,
    baseChangeFinThree_self_one_two, neg_zero]

/-- Scalar extension of an alternating trilinear form. The diagonal-vanishing proof is valid in
all characteristics; in particular it does not infer alternation from skew-symmetry. -/
noncomputable def baseChangeAlternatingFinThree (a : M [⋀^Fin 3]→ₗ[R] R) :
    (S ⊗[R] M) [⋀^Fin 3]→ₗ[S] S where
  toMultilinearMap := MultilinearMap.mk' (fun x ↦
      baseChangeFinThree (S := S) a (x 0) (x 1) (x 2))
    (by intro x i y z; fin_cases i <;> simp [Function.update, Fin.ext_iff])
    (by intro x i r y; fin_cases i <;> simp [Function.update, Fin.ext_iff])
  map_eq_zero_of_eq' x i j hij hne := by
    change baseChangeFinThree (S := S) a (x 0) (x 1) (x 2) = 0
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h : x 0 = x 1 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_zero_one]
    · have h : x 0 = x 2 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_zero_two]
    · have h : x 1 = x 0 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_zero_one]
    · exact (hne rfl).elim
    · have h : x 1 = x 2 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_one_two]
    · have h : x 2 = x 0 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_zero_two]
    · have h : x 2 = x 1 := by
        convert hij using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h, baseChangeFinThree_self_one_two]
    · exact (hne rfl).elim

@[simp] theorem baseChangeAlternatingFinThree_tmul
    (a : M [⋀^Fin 3]→ₗ[R] R) (r s t : S) (x y z : M) :
    baseChangeAlternatingFinThree (S := S) a ![r ⊗ₜ[R] x, s ⊗ₜ[R] y, t ⊗ₜ[R] z] =
      r * s * t * algebraMap R S (a ![x, y, z]) :=
  baseChangeFinThree_tmul a r s t x y z

/-- A determinant identity between two alternating trilinear forms is preserved by scalar
extension. The equivalence `e` identifies the scalar extension of `M⁺` with the dual of the
scalar extension of `M`; its pure-tensor evaluation is stated explicitly so that this theorem
does not require freeness or projectivity. -/
theorem baseChangeFinThree_mul_eq_det
    (a : M [⋀^Fin 3]→ₗ[R] R) (d : Module.Dual R M [⋀^Fin 3]→ₗ[R] R)
    (e : S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M))
    (he : ∀ (r s : S) (f : Module.Dual R M) (x : M),
      e (r ⊗ₜ[R] f) (s ⊗ₜ[R] x) = r * s * algebraMap R S (f x))
    (had : ∀ (x : Fin 3 → M) (f : Fin 3 → Module.Dual R M),
      a x * d f = Matrix.det (fun i j ↦ f i (x j)))
    (x₀ x₁ x₂ : S ⊗[R] M) (q₀ q₁ q₂ : S ⊗[R] Module.Dual R M) :
    baseChangeFinThree (S := S) a x₀ x₁ x₂ *
      baseChangeFinThree (S := S) d q₀ q₁ q₂ =
        Matrix.det !![e q₀ x₀, e q₀ x₁, e q₀ x₂;
          e q₁ x₀, e q₁ x₁, e q₁ x₂;
          e q₂ x₀, e q₂ x₁, e q₂ x₂] := by
  induction x₀ using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, add_mul]
    rw [hx, hy]
    simp_rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    ring
  | tmul s₀ v₀ =>
    induction x₁ using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, add_mul]
      rw [hx, hy]
      simp_rw [Matrix.det_fin_three]
      simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
      ring
    | tmul s₁ v₁ =>
      induction x₂ using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, add_mul]
        rw [hx, hy]
        simp_rw [Matrix.det_fin_three]
        simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
        ring
      | tmul s₂ v₂ =>
        induction q₀ using TensorProduct.inductionOn with
        | add x y hx hy =>
          simp only [map_add, LinearMap.add_apply, mul_add]
          rw [hx, hy]
          simp_rw [Matrix.det_fin_three]
          simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
            Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
            Matrix.cons_val]
          ring
        | tmul r₀ f₀ =>
          induction q₁ using TensorProduct.inductionOn with
          | add x y hx hy =>
            simp only [map_add, LinearMap.add_apply, mul_add]
            rw [hx, hy]
            simp_rw [Matrix.det_fin_three]
            simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
              Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
              Matrix.cons_val]
            ring
          | tmul r₁ f₁ =>
            induction q₂ using TensorProduct.inductionOn with
            | add x y hx hy =>
              simp only [map_add, mul_add]
              rw [hx, hy]
              simp_rw [Matrix.det_fin_three]
              simp [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
                Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
                Matrix.cons_val]
              ring
            | tmul r₂ f₂ =>
              simp only [baseChangeFinThree_tmul]
              have had' := had ![v₀, v₁, v₂] ![f₀, f₁, f₂]
              change a ![v₀, v₁, v₂] * d ![f₀, f₁, f₂] =
                Matrix.det (Matrix.of fun i j ↦
                  (![f₀, f₁, f₂] i) (![v₀, v₁, v₂] j)) at had'
              rw [Matrix.det_fin_three] at had'
              simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
                Matrix.cons_val_one, Matrix.cons_val] at had'
              have had'' := congrArg (algebraMap R S) had'
              simp only [map_mul, map_sub, map_add] at had''
              rw [Matrix.det_fin_three]
              simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val',
                Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
                Matrix.cons_val]
              simp only [he]
              calc
                s₀ * s₁ * s₂ * algebraMap R S (a ![v₀, v₁, v₂]) *
                    (r₀ * r₁ * r₂ * algebraMap R S (d ![f₀, f₁, f₂])) =
                    (s₀ * s₁ * s₂ * r₀ * r₁ * r₂) *
                      (algebraMap R S (a ![v₀, v₁, v₂]) *
                        algebraMap R S (d ![f₀, f₁, f₂])) := by ring
                _ = (s₀ * s₁ * s₂ * r₀ * r₁ * r₂) *
                    (algebraMap R S (f₀ v₀) * algebraMap R S (f₁ v₁) *
                        algebraMap R S (f₂ v₂) -
                      algebraMap R S (f₀ v₀) * algebraMap R S (f₁ v₂) *
                        algebraMap R S (f₂ v₁) -
                      algebraMap R S (f₀ v₁) * algebraMap R S (f₁ v₀) *
                        algebraMap R S (f₂ v₂) +
                      algebraMap R S (f₀ v₁) * algebraMap R S (f₁ v₂) *
                        algebraMap R S (f₂ v₀) +
                      algebraMap R S (f₀ v₂) * algebraMap R S (f₁ v₀) *
                        algebraMap R S (f₂ v₁) -
                      algebraMap R S (f₀ v₂) * algebraMap R S (f₁ v₁) *
                        algebraMap R S (f₂ v₀)) := by rw [had'']
                _ = _ := by ring

end AlternatingMap
