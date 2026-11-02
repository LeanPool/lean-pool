/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.BaseChangeProjective
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of conic algebras (the final paragraph of `GPR 16.1`)

A conic algebra `(A, n)` over `k` gives a conic algebra `(S ⊗[k] A, n_S)` over every commutative
`k`-algebra `S`. This is what lets the classification arguments localize, and it is a prerequisite
for Cayley–Dickson doubling (Layer 6), whose compatibility with base change is `GPR 18.x`.

## Main definitions

* `ConicAlgebra.baseChangeOfProjective` : the conic algebra `S ⊗[k] A`.

## Main results

* `ConicAlgebra.mul_add_mul_baseChangeOfProjective` : the linearized degree-two identity holds on
  `S ⊗[k] A`. It is proved *before* the degree-two identity itself, because it is bi-additive and
  so reduces to pure tensors, whereas the degree-two identity is quadratic and its additivity step
  is exactly the linearized identity.
* `ConicAlgebra.baseChangeOfProjective_norm_tmul`, `ConicAlgebra.baseChangeOfProjective_trace_tmul`,
  `ConicAlgebra.baseChangeOfProjective_conj_tmul` : norm, trace and conjugation on pure tensors.

## Implementation notes

**Finitely generated projective, and why the name says so.** The norm is base changed with
`QuadraticForm.baseChangeOfProjective` (`QuadraticForm/BaseChangeProjective.lean`), which needs
`A` finitely generated projective over `k` but — unlike mathlib's `QuadraticForm.baseChange` —
nothing about `2`. So this is *not* base change of conic algebras in general, and the name carries
the restriction to the call site rather than burying it in a docstring: a hypothesis on a
**definition** is against overview §2, and one that is invisible would be worse.

The final paragraph of `GPR 16.1` has no such restriction, because a quadratic form base changes
over an arbitrary
module: `q_S` is the unique form on `S ⊗[k] M` with `q_S(s ⊗ m) = s² q(m)` and the expected
polar form.
Proving that needs quadratic maps as degree-two polynomial laws (Roby); mathlib now has polynomial
laws (`PolynomialLaw`) but does not yet relate them to `QuadraticMap`, and this project does not
either. `baseChangeOfProjective` sidesteps it by choosing a bilinear `b` with `b(x, x) = q(x)`,
which exists whenever the module is projective (`QuadraticMap.hasBilinRepr_of_projective`) — though
not only then: the zero form has one on every module, and when `2` is invertible half the polar form
represents every form. Nothing downstream needs the general case: composition algebras are finitely
generated projective by definition, and Cayley–Dickson doubling preserves that. See the TODO below.

**The multiplication is mathlib's.** `S ⊗[k] A` carries `NonAssocRing` from
`Mathlib/RingTheory/TensorProduct/Basic.lean`, which builds the multiplication on a tensor product
of two possibly non-associative algebras. Nothing has to be constructed here beyond the norm.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.1.
* N. Roby, *Lois polynômes et lois formelles en théorie des modules*, Ann. Sci. ÉNS **80** (1963),
  213–348: quadratic maps as degree-two polynomial laws, which is what general base change needs.

## TODO

* Base change of a quadratic form over an **arbitrary** module, hence the full statement following
  `GPR 16.1` without the
  projectivity hypothesis. This is missing from mathlib too, and is all that stands between
  `ConicAlgebra.baseChangeOfProjective` and `ConicAlgebra.baseChange`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

open QuadraticMap (polar)

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
variable (S : Type w) [CommRing S] [Algebra k S] (C : ConicAlgebra k A)

/-! ### The base-changed norm -/

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The norm of the base-changed algebra on a pure tensor. -/
theorem baseChangeOfProjective_norm_tmul (s : S) (a : A) :
    (C.norm.baseChangeOfProjective S) (s ⊗ₜ[k] a) = C.norm a • (s * s) :=
  QuadraticForm.baseChangeOfProjective_tmul _ _ _

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The polar form of the base-changed norm on pure tensors. -/
theorem baseChangeOfProjective_polar_tmul (s s' : S) (a a' : A) :
    polar (C.norm.baseChangeOfProjective S) (s ⊗ₜ[k] a) (s' ⊗ₜ[k] a') =
      polar C.norm a a' • (s * s') := by
  have h := QuadraticForm.polarBilin_baseChangeOfProjective (A := S) C.norm
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h (s ⊗ₜ[k] a)) (s' ⊗ₜ[k] a')

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The trace of the base-changed algebra on a pure tensor: `t(s ⊗ a) = t(a) • s`. -/
theorem baseChangeOfProjective_trace_tmul (s : S) (a : A) :
    polar (C.norm.baseChangeOfProjective S) 1 (s ⊗ₜ[k] a) = C.trace a • s := by
  rw [show (1 : S ⊗[k] A) = (1 : S) ⊗ₜ[k] (1 : A) from rfl, baseChangeOfProjective_polar_tmul,
    one_mul]
  rfl

/-! ### The degree-two identity -/

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
variable {S} in
/-- Moving a scalar of `k` out of the `S`-action on a pure tensor. -/
private theorem smul_smul_tmul (c : k) (s s' : S) (a : A) :
    (c • s) • (s' ⊗ₜ[k] a) = c • ((s * s') ⊗ₜ[k] a) := by
  rw [smul_assoc, TensorProduct.smul_tmul', smul_eq_mul]

/-- **The linearized degree-two identity on `S ⊗[k] A`.** Both sides are additive in each
argument, so this reduces to pure tensors, where it is `ConicAlgebra.mul_add_mul` in `A`. -/
theorem mul_add_mul_baseChangeOfProjective (x y : S ⊗[k] A) :
    x * y + y * x =
      polar (C.norm.baseChangeOfProjective S) 1 x • y +
        polar (C.norm.baseChangeOfProjective S) 1 y • x -
        polar (C.norm.baseChangeOfProjective S) x y • (1 : S ⊗[k] A) := by
  induction x with
  | add x₁ x₂ h₁ h₂ =>
    simp only [add_mul, mul_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    linear_combination (norm := module) h₁ + h₂
  | tmul s a =>
    induction y with
    | add y₁ y₂ h₁ h₂ =>
      simp only [add_mul, mul_add, QuadraticMap.polar_add_right]
      linear_combination (norm := module) h₁ + h₂
    | tmul s' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        baseChangeOfProjective_trace_tmul, baseChangeOfProjective_trace_tmul,
        baseChangeOfProjective_polar_tmul, show s' * s = s * s' from mul_comm _ _,
        ← TensorProduct.tmul_add, C.mul_add_mul a a',
        show (1 : S ⊗[k] A) = (1 : S) ⊗ₜ[k] (1 : A) from rfl, smul_smul_tmul, smul_smul_tmul,
        smul_smul_tmul, mul_comm s' s, mul_one]
      simp only [TensorProduct.tmul_sub, TensorProduct.tmul_add, TensorProduct.tmul_smul]

/-- **The degree-two identity on `S ⊗[k] A`.** On pure tensors it is the identity in `A`; the
additivity step is `ConicAlgebra.mul_add_mul_baseChangeOfProjective`. -/
theorem mul_self_baseChangeOfProjective (x : S ⊗[k] A) :
    x * x = polar (C.norm.baseChangeOfProjective S) 1 x • x -
      (C.norm.baseChangeOfProjective S) x • (1 : S ⊗[k] A) := by
  induction x with
  | tmul s a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeOfProjective_trace_tmul,
      baseChangeOfProjective_norm_tmul, C.mul_self_eq a,
      show (1 : S ⊗[k] A) = (1 : S) ⊗ₜ[k] (1 : A) from rfl]
    simp only [TensorProduct.tmul_sub, TensorProduct.tmul_smul]
    rw [smul_smul_tmul, smul_smul_tmul, mul_one]
  | add x y hx hy =>
    have hnorm : (C.norm.baseChangeOfProjective S) (x + y) =
        (C.norm.baseChangeOfProjective S) x + (C.norm.baseChangeOfProjective S) y +
          polar (C.norm.baseChangeOfProjective S) x y := by
      simp only [QuadraticMap.polar]; ring
    rw [add_mul, mul_add, mul_add,
      show x * x + x * y + (y * x + y * y) = x * x + y * y + (x * y + y * x) by abel,
      hx, hy, mul_add_mul_baseChangeOfProjective S C x y, QuadraticMap.polar_add_right, hnorm]
    module

/-- **Base change of a conic algebra** (the final paragraph of `GPR 16.1`). -/
noncomputable def baseChangeOfProjective : ConicAlgebra S (S ⊗[k] A) where
  norm := C.norm.baseChangeOfProjective S
  norm_one := by
    rw [show (1 : S ⊗[k] A) = (1 : S) ⊗ₜ[k] (1 : A) from rfl,
      baseChangeOfProjective_norm_tmul, C.norm_one, mul_one, one_smul]
  mul_self := mul_self_baseChangeOfProjective S C

@[simp] theorem baseChangeOfProjective_norm :
    (C.baseChangeOfProjective S).norm = C.norm.baseChangeOfProjective S := rfl

theorem baseChangeOfProjective_norm_apply_tmul (s : S) (a : A) :
    (C.baseChangeOfProjective S).norm (s ⊗ₜ[k] a) = C.norm a • (s * s) :=
  baseChangeOfProjective_norm_tmul S C s a

@[simp] theorem baseChangeOfProjective_trace_apply_tmul (s : S) (a : A) :
    (C.baseChangeOfProjective S).trace (s ⊗ₜ[k] a) = C.trace a • s :=
  baseChangeOfProjective_trace_tmul S C s a

/-- Conjugation of the base change is the base change of the conjugation. -/
@[simp] theorem baseChangeOfProjective_conj_tmul (s : S) (a : A) :
    (C.baseChangeOfProjective S).conj (s ⊗ₜ[k] a) = s ⊗ₜ[k] C.conj a := by
  rw [conj_apply, baseChangeOfProjective_trace_apply_tmul, conj_apply,
    show (1 : S ⊗[k] A) = (1 : S) ⊗ₜ[k] (1 : A) from rfl, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, smul_smul_tmul, mul_one]

end ConicAlgebra
