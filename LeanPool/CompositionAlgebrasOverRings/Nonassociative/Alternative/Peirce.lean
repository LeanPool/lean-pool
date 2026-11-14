/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Defs

/-!
# Peirce projections in alternative algebras

Let `c` be an idempotent in a unital alternative algebra and put `c₀ = c` and
`c₁ = 1 - c`. This file constructs the four Peirce projections

`x ↦ (cᵢ * x) * cⱼ`.

The projections are complete, idempotent, and pairwise orthogonal. This is the linear-algebraic
core of the singular Peirce decomposition [GPR, Exc. 14.12]. The range of the `(i, j)` projection is
the Peirce component `Aᵢⱼ`.

## Main definitions

* `IsAlternative.peirceIdempotent`: the complementary idempotents `c` and `1 - c`.
* `IsAlternative.peirceProjection`: the four Peirce projections.
* `IsAlternative.peirceComponent`: their ranges.

## Main results

* `IsAlternative.peirceProjection_idem`: each Peirce projection is idempotent.
* `IsAlternative.peirceProjection_comp_eq_zero`: distinct Peirce projections are orthogonal.
* `IsAlternative.sum_peirceProjection_apply`: the four projections sum to the identity.
* `IsAlternative.mul_mem_peirceComponent_of_opposite`: opposite off-diagonal components
  multiply into a diagonal component.
* `IsAlternative.mul_mem_peirceComponent_swap`: one off-diagonal component squares into the
  opposite component.
* `IsAlternative.finite_peirceComponent`, `IsAlternative.projective_peirceComponent`: Peirce
  components inherit finite projectivity from the ambient module.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 14.12.
-/

@[expose] public section

universe u v

namespace IsAlternative

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The two complementary idempotents attached to `c`, indexed by `Bool`. The index `false`
denotes `c`, and `true` denotes `1 - c`. -/
def peirceIdempotent (c : A) : Bool → A
  | false => c
  | true => 1 - c

@[simp] theorem peirceIdempotent_false (c : A) : peirceIdempotent c false = c := rfl

@[simp] theorem peirceIdempotent_true (c : A) : peirceIdempotent c true = 1 - c := rfl

/-- Both elements of the complementary pair attached to an idempotent are idempotent. -/
theorem peirceIdempotent_mul_self {c : A} (hc : c * c = c) (i : Bool) :
    peirceIdempotent c i * peirceIdempotent c i = peirceIdempotent c i := by
  cases i
  · exact hc
  · simp only [peirceIdempotent_true, sub_mul, mul_sub, one_mul, mul_one, hc]
    abel

/-- Distinct elements of the complementary pair multiply to zero. -/
theorem peirceIdempotent_mul_eq_zero {c : A} (hc : c * c = c) {i j : Bool}
    (hij : i ≠ j) : peirceIdempotent c i * peirceIdempotent c j = 0 := by
  cases i <;> cases j <;> simp_all [peirceIdempotent, mul_sub, sub_mul]

/-- Multiplication on the left by one of the two complementary idempotents. -/
def peirceLeftProjection (c : A) (i : Bool) : A →ₗ[R] A :=
  LinearMap.mulLeft R (peirceIdempotent c i)

/-- Multiplication on the right by one of the two complementary idempotents. -/
def peirceRightProjection (c : A) (j : Bool) : A →ₗ[R] A :=
  LinearMap.mulRight R (peirceIdempotent c j)

/-- The `(i, j)` Peirce projection `x ↦ (cᵢ * x) * cⱼ`. -/
def peirceProjection (c : A) (i j : Bool) : A →ₗ[R] A :=
  (peirceRightProjection (R := R) c j).comp (peirceLeftProjection (R := R) c i)

omit [IsScalarTower R A A] in
@[simp] theorem peirceLeftProjection_apply (c x : A) (i : Bool) :
    peirceLeftProjection (R := R) c i x = peirceIdempotent c i * x := rfl

omit [SMulCommClass R A A] in
@[simp] theorem peirceRightProjection_apply (c x : A) (j : Bool) :
    peirceRightProjection (R := R) c j x = x * peirceIdempotent c j := rfl

@[simp] theorem peirceProjection_apply (c x : A) (i j : Bool) :
    peirceProjection (R := R) c i j x =
      (peirceIdempotent c i * x) * peirceIdempotent c j := rfl

section Alternative

variable [IsAlternative A]

/-- The two complementary idempotents associate across an arbitrary middle element. This is the
flexible law, expanded linearly when either idempotent is `1 - c`. -/
theorem peirce_associate (c x : A) (i j : Bool) :
    (peirceIdempotent c i * x) * peirceIdempotent c j =
      peirceIdempotent c i * (x * peirceIdempotent c j) := by
  cases i <;> cases j <;>
    simp only [peirceIdempotent_false, peirceIdempotent_true, mul_sub, sub_mul, one_mul, mul_one,
      flexible]

/-- Two complementary left multiplications associate. -/
theorem peirce_left_associate (c x : A) (i j : Bool) :
    peirceIdempotent c i * (peirceIdempotent c j * x) =
      (peirceIdempotent c i * peirceIdempotent c j) * x := by
  cases i <;> cases j <;>
    simp only [peirceIdempotent_false, peirceIdempotent_true, sub_mul, mul_sub, one_mul, mul_one,
      mul_mul_self_left]

/-- Two complementary right multiplications associate. -/
theorem peirce_right_associate (c x : A) (i j : Bool) :
    (x * peirceIdempotent c i) * peirceIdempotent c j =
      x * (peirceIdempotent c i * peirceIdempotent c j) := by
  cases i <;> cases j <;>
    simp only [peirceIdempotent_false, peirceIdempotent_true, sub_mul, mul_sub, one_mul, mul_one,
      mul_self_mul_right]

/-- Each Peirce projection is idempotent. -/
theorem peirceProjection_idem {c : A} (hc : c * c = c) (i j : Bool) :
    (peirceProjection (R := R) c i j).comp (peirceProjection (R := R) c i j) =
      peirceProjection (R := R) c i j := by
  ext x
  simp only [LinearMap.comp_apply, peirceProjection_apply]
  rw [← peirce_associate c (peirceIdempotent c i * x) i j]
  rw [peirce_right_associate c (peirceIdempotent c i *
    (peirceIdempotent c i * x)) j j]
  rw [peirce_left_associate c x i i]
  simp only [peirceIdempotent_mul_self hc]

/-- Peirce projections with distinct left indices have zero composite. -/
theorem peirceProjection_comp_eq_zero_of_left {c : A} (hc : c * c = c) {i j k l : Bool}
    (hik : i ≠ k) :
    (peirceProjection (R := R) c i j).comp (peirceProjection (R := R) c k l) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, peirceProjection_apply, LinearMap.zero_apply]
  rw [← peirce_associate c (peirceIdempotent c k * x) i l]
  rw [peirce_left_associate c x i k]
  simp only [peirceIdempotent_mul_eq_zero hc hik, zero_mul]

/-- Peirce projections with distinct right indices have zero composite. -/
theorem peirceProjection_comp_eq_zero_of_right {c : A} (hc : c * c = c) {i j k l : Bool}
    (hjl : j ≠ l) :
    (peirceProjection (R := R) c i j).comp (peirceProjection (R := R) c k l) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, peirceProjection_apply, LinearMap.zero_apply]
  rw [← peirce_associate c (peirceIdempotent c k * x) i l]
  rw [peirce_right_associate c (peirceIdempotent c i *
    (peirceIdempotent c k * x)) l j]
  simp only [peirceIdempotent_mul_eq_zero hc (Ne.symm hjl), mul_zero]

/-- Distinct Peirce projections are pairwise orthogonal. -/
theorem peirceProjection_comp_eq_zero {c : A} (hc : c * c = c) {i j k l : Bool}
    (h : (i, j) ≠ (k, l)) :
    (peirceProjection (R := R) c i j).comp (peirceProjection (R := R) c k l) = 0 := by
  by_cases hik : i = k
  · exact peirceProjection_comp_eq_zero_of_right hc fun hjl ↦ h (Prod.ext hik hjl)
  · exact peirceProjection_comp_eq_zero_of_left hc hik

end Alternative

/-- The four Peirce projections decompose every element. -/
theorem sum_peirceProjection_apply (c x : A) :
    peirceProjection (R := R) c false false x +
        peirceProjection (R := R) c false true x +
      peirceProjection (R := R) c true false x +
        peirceProjection (R := R) c true true x = x := by
  simp only [peirceProjection_apply, peirceIdempotent_false, peirceIdempotent_true, mul_sub,
    sub_mul, one_mul, mul_one]
  abel

/-- The `(i, j)` Peirce component is the range of the corresponding projection. -/
def peirceComponent (c : A) (i j : Bool) : Submodule R A :=
  LinearMap.range (peirceProjection (R := R) c i j)

section Alternative

variable [IsAlternative A]

/-- An element belongs to a Peirce component exactly when its projection is itself. -/
theorem mem_peirceComponent_iff {c : A} (hc : c * c = c) {x : A} (i j : Bool) :
    x ∈ peirceComponent (R := R) c i j ↔ peirceProjection (R := R) c i j x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (peirceProjection_idem hc i j) y
  · intro hx
    exact ⟨x, hx⟩

/-- The intrinsic characterization of a Peirce component: `x` lies in `Aᵢⱼ` exactly when
`cᵢ * x = x = x * cⱼ` [GPR, Exc. 14.12]. -/
theorem mem_peirceComponent_iff_mul_eq {c : A} (hc : c * c = c) {x : A} (i j : Bool) :
    x ∈ peirceComponent (R := R) c i j ↔
      peirceIdempotent c i * x = x ∧ x * peirceIdempotent c j = x := by
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · simp only [peirceProjection_apply]
      rw [← peirce_associate c (peirceIdempotent c i * y) i j]
      rw [peirce_left_associate c y i i, peirceIdempotent_mul_self hc]
    · simp only [peirceProjection_apply]
      rw [peirce_right_associate c (peirceIdempotent c i * y) j j]
      rw [peirceIdempotent_mul_self hc]
  · rintro ⟨hleft, hright⟩
    rw [mem_peirceComponent_iff hc, peirceProjection_apply, hleft, hright]

/-- Each complementary idempotent belongs to its diagonal Peirce component. -/
theorem peirceIdempotent_mem_peirceComponent {c : A} (hc : c * c = c) (i : Bool) :
    peirceIdempotent c i ∈ peirceComponent (R := R) c i i :=
  (mem_peirceComponent_iff_mul_eq hc i i).mpr
    ⟨peirceIdempotent_mul_self hc i, peirceIdempotent_mul_self hc i⟩

/-- A complementary idempotent acts on the left of a Peirce component by either the identity or
zero, according to its left index. -/
theorem peirceIdempotent_mul_of_mem {c : A} (hc : c * c = c) {x : A} {k l : Bool}
    (hx : x ∈ peirceComponent (R := R) c k l) (i : Bool) :
    peirceIdempotent c i * x = if i = k then x else 0 := by
  have hkx := (mem_peirceComponent_iff_mul_eq hc k l).mp hx |>.1
  by_cases hik : i = k
  · simpa [hik] using hkx
  · rw [ite_eq_right hik, ← hkx, peirce_left_associate,
      peirceIdempotent_mul_eq_zero hc hik, zero_mul]

/-- A complementary idempotent acts on the right of a Peirce component by either the identity or
zero, according to its right index. -/
theorem mul_peirceIdempotent_of_mem {c : A} (hc : c * c = c) {x : A} {k l : Bool}
    (hx : x ∈ peirceComponent (R := R) c k l) (j : Bool) :
    x * peirceIdempotent c j = if j = l then x else 0 := by
  have hxl := (mem_peirceComponent_iff_mul_eq hc k l).mp hx |>.2
  by_cases hjl : j = l
  · simpa [hjl] using hxl
  · rw [ite_eq_right hjl, ← hxl, peirce_right_associate,
      peirceIdempotent_mul_eq_zero hc (Ne.symm hjl), mul_zero]

/-- Opposite off-diagonal Peirce components multiply into the corresponding diagonal component:
`Aᵢⱼ Aⱼᵢ ⊆ Aᵢᵢ` for `i ≠ j` [GPR, Exc. 14.12]. -/
theorem mul_mem_peirceComponent_of_opposite {c : A} (hc : c * c = c)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ peirceComponent (R := R) c i j)
    (hy : y ∈ peirceComponent (R := R) c j i) :
    x * y ∈ peirceComponent (R := R) c i i := by
  have hxei : x * peirceIdempotent c i = 0 := by
    rw [mul_peirceIdempotent_of_mem hc hx, ite_eq_right hij]
  have heiy : peirceIdempotent c i * y = 0 := by
    rw [peirceIdempotent_mul_of_mem hc hy, ite_eq_right hij]
  have heix : peirceIdempotent c i * x = x := by
    rw [peirceIdempotent_mul_of_mem hc hx, ite_eq_left rfl]
  have hyei : y * peirceIdempotent c i = y := by
    rw [mul_peirceIdempotent_of_mem hc hy, ite_eq_left rfl]
  apply (mem_peirceComponent_iff_mul_eq hc i i).mpr
  constructor
  · have ha : associator (peirceIdempotent c i) x y = 0 := by
      rw [associator_swap_left, associator, hxei, heiy, zero_mul, mul_zero, sub_self, neg_zero]
    exact ((associator_eq_zero_iff _ _ _).mp ha).symm.trans (congr_arg (· * y) heix)
  · have ha : associator x y (peirceIdempotent c i) = 0 := by
      rw [associator_swap_right, associator, hxei, heiy, zero_mul, mul_zero, sub_self, neg_zero]
    exact ((associator_eq_zero_iff _ _ _).mp ha).trans (congr_arg (x * ·) hyei)

/-- Multiplying two elements of one off-diagonal Peirce component lands in the opposite
component: `Aᵢⱼ Aᵢⱼ ⊆ Aⱼᵢ` for `i ≠ j` [GPR, Exc. 14.12]. -/
theorem mul_mem_peirceComponent_swap {c : A} (hc : c * c = c)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ peirceComponent (R := R) c i j)
    (hy : y ∈ peirceComponent (R := R) c i j) :
    x * y ∈ peirceComponent (R := R) c j i := by
  have hejx : peirceIdempotent c j * x = 0 := by
    rw [peirceIdempotent_mul_of_mem hc hx, ite_eq_right (Ne.symm hij)]
  have hxej : x * peirceIdempotent c j = x := by
    rw [mul_peirceIdempotent_of_mem hc hx, ite_eq_left rfl]
  have hxei : x * peirceIdempotent c i = 0 := by
    rw [mul_peirceIdempotent_of_mem hc hx, ite_eq_right hij]
  have hejy : peirceIdempotent c j * y = 0 := by
    rw [peirceIdempotent_mul_of_mem hc hy, ite_eq_right (Ne.symm hij)]
  have hyei : y * peirceIdempotent c i = 0 := by
    rw [mul_peirceIdempotent_of_mem hc hy, ite_eq_right hij]
  have heiy : peirceIdempotent c i * y = y := by
    rw [peirceIdempotent_mul_of_mem hc hy, ite_eq_left rfl]
  apply (mem_peirceComponent_iff_mul_eq hc j i).mpr
  constructor
  · have hinner : associator x (peirceIdempotent c j) y = x * y := by
      rw [associator, hxej, hejy, mul_zero, sub_zero]
    have ha := associator_swap_left (peirceIdempotent c j) x y
    rw [associator, hejx, zero_mul, zero_sub, hinner] at ha
    exact neg_injective ha
  · have hinner : associator x (peirceIdempotent c i) y = -(x * y) := by
      rw [associator, hxei, heiy, zero_mul, zero_sub]
    have ha := associator_swap_right x y (peirceIdempotent c i)
    rw [associator, hyei, mul_zero, sub_zero, hinner, neg_neg] at ha
    exact ha

/-- A Peirce projection acts as the identity on its component and as zero on every other
component. -/
theorem peirceProjection_apply_of_mem {c : A} (hc : c * c = c) {i j k l : Bool}
    (x : peirceComponent (R := R) c k l) :
    peirceProjection (R := R) c i j x = if (i, j) = (k, l) then x else 0 := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  by_cases h : (i, j) = (k, l)
  · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    rw [ite_eq_left rfl]
    exact (LinearMap.congr_fun (peirceProjection_idem (R := R) hc i j) y).trans hy
  · rw [ite_eq_right h]
    exact LinearMap.congr_fun (peirceProjection_comp_eq_zero (R := R) hc h) y

/-- The map sending an element to its four Peirce components. -/
def peirceDecompose (c : A) :
    A →ₗ[R] ((p : Bool × Bool) → peirceComponent (R := R) c p.1 p.2) where
  toFun x p := ⟨peirceProjection (R := R) c p.1 p.2 x, ⟨x, rfl⟩⟩
  map_add' x y := by
    funext p
    exact Subtype.ext (map_add (peirceProjection (R := R) c p.1 p.2) x y)
  map_smul' r x := by
    funext p
    exact Subtype.ext (map_smul (peirceProjection (R := R) c p.1 p.2) r x)

/-- Sum the four coordinates in a family of Peirce components. -/
def peirceRecombine (c : A) :
    ((p : Bool × Bool) → peirceComponent (R := R) c p.1 p.2) →ₗ[R] A where
  toFun x := ∑ p, (x p : A)
  map_add' x y := by
    simpa only [Pi.add_apply, Submodule.coe_add] using
      (Finset.sum_add_distrib : ∑ p, ((x p : A) + y p) = _)
  map_smul' r x := by
    rw [Finset.smul_sum]
    rfl

omit [IsAlternative A] in
/-- Recombining the Peirce coordinates of an element returns that element. -/
theorem peirceRecombine_decompose {c : A} (x : A) :
    peirceRecombine (R := R) c (peirceDecompose (R := R) c x) = x := by
  rw [show peirceRecombine (R := R) c (peirceDecompose (R := R) c x) =
    ∑ p : Bool × Bool, peirceProjection (R := R) c p.1 p.2 x by rfl]
  rw [Fintype.sum_prod_type]
  simpa [Fintype.univ_bool, add_assoc, add_comm, add_left_comm] using
    sum_peirceProjection_apply (R := R) c x

/-- Decomposing a sum of Peirce coordinates returns the original coordinates. -/
theorem peirceDecompose_recombine {c : A} (hc : c * c = c)
    (x : (p : Bool × Bool) → peirceComponent (R := R) c p.1 p.2) :
    peirceDecompose (R := R) c (peirceRecombine (R := R) c x) = x := by
  funext p
  apply Subtype.ext
  change peirceProjection (R := R) c p.1 p.2 (∑ q, (x q : A)) = x p
  rw [map_sum]
  rw [Finset.sum_eq_single p]
  · simpa using peirceProjection_apply_of_mem (R := R) hc (i := p.1) (j := p.2) (x p)
  · intro q _ hqp
    simpa [Ne.symm hqp] using peirceProjection_apply_of_mem (R := R) hc (i := p.1)
      (j := p.2) (x q)
  · simp

/-- The singular Peirce decomposition of an alternative algebra [GPR, Exc. 14.12]. -/
def peirceDecomposition {c : A} (hc : c * c = c) :
    A ≃ₗ[R] ((p : Bool × Bool) → peirceComponent (R := R) c p.1 p.2) where
  __ := peirceDecompose (R := R) c
  invFun := peirceRecombine (R := R) c
  left_inv := peirceRecombine_decompose
  right_inv := peirceDecompose_recombine hc

omit [IsAlternative A] in
/-- A Peirce component is finite when the ambient module is finite: it is the image of a
projection. -/
theorem finite_peirceComponent [Module.Finite R A] {c : A} (i j : Bool) :
    Module.Finite R (peirceComponent (R := R) c i j) :=
  Module.Finite.of_surjective
    (peirceProjection (R := R) c i j).rangeRestrict
    (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)

/-- A Peirce component is projective when the ambient module is projective: its projection splits
the inclusion. -/
theorem projective_peirceComponent [Module.Projective R A] {c : A} (hc : c * c = c)
    (i j : Bool) : Module.Projective R (peirceComponent (R := R) c i j) := by
  let p := (peirceProjection (R := R) c i j).rangeRestrict
  have hp : p.comp (peirceComponent (R := R) c i j).subtype = LinearMap.id := by
    ext x
    exact (mem_peirceComponent_iff hc i j).mp x.property
  exact Module.Projective.of_split (peirceComponent (R := R) c i j).subtype p hp

end Alternative

end IsAlternative
