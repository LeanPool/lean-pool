/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Inseparable
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# An anisotropic witness for `GPR 19.4`

`Composition/Inseparable.lean` proves `GPR 19.4` in general — a commutative algebra over a field of
characteristic two all of whose squares are scalars is a conic algebra with identically vanishing
polar form, and is not a composition algebra once its dimension exceeds one — and exhibits the dual
numbers `𝔽₂[ε]` as a witness. The dual numbers are **not** anisotropic (`ε² = 0`), so they do not
witness the sharpness claim the example exists to make: that anisotropy and non-singularity part
company in characteristic two.

This file supplies an anisotropic witness. It must be a purely inseparable field extension of
exponent one, so the base field must be imperfect; the smallest is `𝔽₂(t)`, and the extension is
`𝔽₂(t)(√t)`.

## The construction

`X² - t` is irreducible over `𝔽₂(t)` because `t` is not a square there — the `intDegree` of a
square is even, and `intDegree t = 1`. So `AdjoinRoot (X² - C t)` is a field, of dimension two over
`𝔽₂(t)`.

Every square in it is a scalar. This is not a coordinate computation: the set of elements whose
square is a scalar is closed under addition (in characteristic two the cross terms of `(x + y)²`
are `2xy = 0`), under multiplication (by commutativity), contains the image of the base field, and
contains the root; since the root generates, it is everything (`Algebra.adjoin_induction`).

Anisotropy is then free, and this is the point of using a field rather than a ring: by
`ConicAlgebra.anisotropic_inseparable_iff` the norm is anisotropic exactly when the algebra has no
nonzero square-zero element, which in a field is `mul_self_eq_zero`.

## Main results

* `RatFunc.sq_ne_X` : `t` is not a square in `K(t)`, for any field `K`.
* `ConicAlgebra.insepSqrt` : the field `𝔽₂(t)(√t)`.
* `ConicAlgebra.insepSqrtConic` : its conic structure, with the squaring map as norm.
* `ConicAlgebra.anisotropic_insepSqrtConic` : **its norm is anisotropic**.
* `ConicAlgebra.polar_insepSqrtConic` : its polar form vanishes identically.
* `ConicAlgebra.not_isComposition_insepSqrtConic` : it is not a composition algebra.

Together these separate anisotropy from non-singularity, which is what `GPR 19.4` is for.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.4, 19.11.
-/

@[expose] public section

open Polynomial

namespace RatFunc

/-- **`t` is not a square in `K(t)`.** The `intDegree` of a nonzero square is even, while
`intDegree t = 1`. This is what makes `K(t)` imperfect in characteristic two. -/
theorem sq_ne_X {K : Type*} [Field K] (b : RatFunc K) : b * b ≠ RatFunc.X := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa using h.symm)
  have hdeg : b.intDegree + b.intDegree = 1 := by
    rw [← RatFunc.intDegree_mul hb hb, h, RatFunc.intDegree_X]
  omega

end RatFunc

namespace ConicAlgebra

/-- The imperfect base field `𝔽₂(t)`. -/
abbrev InsepBase : Type := RatFunc (ZMod 2)

/-- The polynomial `X² - t` over `𝔽₂(t)`. -/
noncomputable abbrev insepPoly : InsepBase[X] := X ^ 2 - C RatFunc.X

theorem irreducible_insepPoly : Irreducible insepPoly :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b ↦ by
    rw [pow_two]; exact RatFunc.sq_ne_X b

noncomputable instance : Fact (Irreducible insepPoly) := ⟨irreducible_insepPoly⟩

/-- The purely inseparable quadratic extension `𝔽₂(t)(√t)`. -/
abbrev insepSqrt : Type := AdjoinRoot insepPoly

theorem insepPoly_ne_zero : insepPoly ≠ 0 := irreducible_insepPoly.ne_zero

/-- `𝔽₂(t)(√t)` has dimension two over `𝔽₂(t)`. -/
theorem finrank_insepSqrt : Module.finrank InsepBase insepSqrt = 2 := by
  rw [(AdjoinRoot.powerBasis insepPoly_ne_zero).finrank,
    AdjoinRoot.powerBasis_dim insepPoly_ne_zero]
  exact natDegree_X_pow_sub_C

noncomputable instance : Module.Finite InsepBase insepSqrt :=
  (AdjoinRoot.powerBasis insepPoly_ne_zero).finite

/-- `𝔽₂(t)` has characteristic two. -/
theorem insepBase_two_eq_zero : (2 : InsepBase) = 0 := by
  have h : ((2 : ℕ) : InsepBase) = 0 := CharP.cast_eq_zero InsepBase 2
  simpa using h

/-- **Every square in `𝔽₂(t)(√t)` is a scalar.**

The set of such elements is a subalgebra — closed under addition because in characteristic two the
cross terms of `(x + y)²` are `2xy`, and under multiplication by commutativity — and it contains
the root, whose square is `t`. Since the root generates, it is everything. -/
theorem exists_mul_self_eq_algebraMap (x : insepSqrt) :
    ∃ c : InsepBase, x * x = algebraMap InsepBase insepSqrt c := by
  have hx : x ∈ Algebra.adjoin InsepBase ({AdjoinRoot.root insepPoly} : Set insepSqrt) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨RatFunc.X, ?_⟩
      rw [← pow_two, AdjoinRoot.algebraMap_eq]
      exact root_X_pow_sub_C_pow 2 RatFunc.X
  | algebraMap r => exact ⟨r * r, by rw [map_mul]⟩
  | add y z _ _ ihy ihz =>
      obtain ⟨c, hc⟩ := ihy
      obtain ⟨d, hd⟩ := ihz
      refine ⟨c + d, ?_⟩
      have hcross : y * z + z * y = 0 := by
        rw [mul_comm z y, ← two_mul, ← map_ofNat (algebraMap InsepBase insepSqrt) 2,
          insepBase_two_eq_zero]
        simp
      rw [map_add, ← hc, ← hd, mul_add, add_mul, add_mul]
      linear_combination hcross
  | mul y z _ _ ihy ihz =>
      obtain ⟨c, hc⟩ := ihy
      obtain ⟨d, hd⟩ := ihz
      exact ⟨c * d, by rw [map_mul, ← hc, ← hd]; ring⟩

/-- The norm: the squaring map, read as a function to the base field. -/
noncomputable def insepSqrtNorm (x : insepSqrt) : InsepBase :=
  (exists_mul_self_eq_algebraMap x).choose

theorem insepSqrtNorm_spec (x : insepSqrt) : x * x = insepSqrtNorm x • (1 : insepSqrt) := by
  rw [Algebra.smul_def, mul_one]
  exact (exists_mul_self_eq_algebraMap x).choose_spec

/-- **`GPR 19.4` with an anisotropic witness**: the conic structure on `𝔽₂(t)(√t)` whose norm is
the squaring map. -/
noncomputable def insepSqrtConic : ConicAlgebra InsepBase insepSqrt :=
  inseparable insepBase_two_eq_zero insepSqrtNorm insepSqrtNorm_spec

/-- The polar form vanishes identically. -/
@[simp] theorem polar_insepSqrtConic (x y : insepSqrt) :
    QuadraticMap.polar insepSqrtConic.norm x y = 0 :=
  polar_inseparableNorm insepBase_two_eq_zero insepSqrtNorm insepSqrtNorm_spec x y

/-- The trace vanishes identically and the conjugation is the identity. -/
@[simp] theorem trace_insepSqrtConic (x : insepSqrt) : insepSqrtConic.trace x = 0 :=
  trace_inseparable insepBase_two_eq_zero insepSqrtNorm insepSqrtNorm_spec x

@[simp] theorem conj_insepSqrtConic (x : insepSqrt) : insepSqrtConic.conj x = x :=
  conj_inseparable insepBase_two_eq_zero insepSqrtNorm insepSqrtNorm_spec x

/-- **The norm is anisotropic.** This is what the dual numbers could not witness: in a field the
only square-zero element is zero, so `ConicAlgebra.anisotropic_inseparable_iff` applies. -/
theorem anisotropic_insepSqrtConic : insepSqrtConic.norm.Anisotropic := by
  rw [insepSqrtConic, anisotropic_inseparable_iff]
  exact fun x hx ↦ mul_self_eq_zero.mp hx

/-- **`GPR 19.4`.** An anisotropic conic algebra whose polar form vanishes identically, hence
which is not a composition algebra. Anisotropy and non-singularity therefore genuinely part
company in characteristic two. -/
theorem not_isComposition_insepSqrtConic : ¬ insepSqrtConic.IsComposition.{0, 0, 0} :=
  not_isComposition_inseparable insepBase_two_eq_zero insepSqrtNorm insepSqrtNorm_spec
    (by rw [finrank_insepSqrt]; norm_num)

end ConicAlgebra
