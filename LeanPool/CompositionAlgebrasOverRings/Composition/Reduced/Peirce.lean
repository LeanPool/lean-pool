/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Defs
public import LeanPool.CompositionAlgebrasOverRings.Module.Invertible
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Peirce

/-!
# Peirce decomposition at an elementary idempotent

This file specializes the singular Peirce decomposition [GPR, Exc. 14.12] to an elementary
idempotent in a multiplicative conic alternative algebra. It proves [GPR, Exc. 19.35(1)--(6)]: the
diagonal components, existence of Peirce coordinates, and the coordinate formulas for the norm,
polar form, trace, and conjugation. Under regularity it also proves that the two off-diagonal
components are in duality under the polar form, and it constructs the alternating trace trilinear
form at the end of the exercise. `GPR 19.11` supplies regularity for a constant-rank composition
algebra of rank other than one.

## Main results

* `ConicAlgebra.IsElementaryIdempotent.eq_trace_smul_peirceIdempotent`: an element of a diagonal
  Peirce component is its trace times the corresponding idempotent.
* `ConicAlgebra.IsElementaryIdempotent.peirceComponent_same`: `Cᵢᵢ = k cᵢ`.
* `ConicAlgebra.IsElementaryIdempotent.norm_peirceElement`: the norm formula (3).
* `ConicAlgebra.IsElementaryIdempotent.polar_peirceElement`: the polar formula (4).
* `ConicAlgebra.IsElementaryIdempotent.trace_peirceElement`: the trace formula (5).
* `ConicAlgebra.IsElementaryIdempotent.conj_peirceElement`: the conjugation formula (6).
* `ConicAlgebra.IsElementaryIdempotent.mul_add_mul_eq_zero_of_mem_peirceComponent`:
  multiplication within an off-diagonal component is alternating.
* `ConicAlgebra.IsElementaryIdempotent.mul_eq_neg_polar_smul_peirceIdempotent`: the product of
  opposite off-diagonal components.
* `ConicAlgebra.IsElementaryIdempotent.offDiagonalDuality`: the duality `C₁₂ ≃ C₂₁*` when
  the norm is regular.
* `ConicAlgebra.IsElementaryIdempotent.isLocallyFreeRankOne_offDiagonal`: in rank four the
  off-diagonal components are line bundles, the rank count in `GPR 22.13`.
* `ConicAlgebra.IsElementaryIdempotent.mul_eq_zero_of_mem_offDiagonal_of_rankAtStalk_eq_four`:
  multiplication within either off-diagonal component vanishes in rank four.
* `ConicAlgebra.IsElementaryIdempotent.peirceTraceAlternating`: the alternating form
  `(x, y, z) ↦ t((xy)z)` on either off-diagonal component.

The duality theorem is stated with the regularity it consumes; its composition-algebra corollary
uses `GPR 19.11` under a constant-rank hypothesis. The hyperbolic presentation assembled from
these coordinates is in `Composition/Reduced/Hyperbolic.lean`, and the rank-four twisted-matrix
classification is in `Composition/Reduced/TwistedMatrix.lean`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 14.12,
  Exc. 19.35.
-/

@[expose] public section

universe u v

namespace ConicAlgebra.IsElementaryIdempotent

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  {C : ConicAlgebra k A} {c : A}

omit [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A] in
/-- Each member of the complementary pair attached to an elementary idempotent is elementary. -/
theorem peirceIdempotent (hc : C.IsElementaryIdempotent c) (i : Bool) :
    C.IsElementaryIdempotent (IsAlternative.peirceIdempotent c i) := by
  cases i
  · exact hc
  · simpa [IsAlternative.peirceIdempotent, hc.conj_eq] using hc.conj

/-- An element of a diagonal Peirce component is its trace times the corresponding elementary
idempotent [GPR, Exc. 19.35(1)]. -/
theorem eq_trace_smul_peirceIdempotent (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {x : A} {i : Bool}
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i i) :
    x = C.trace x • IsAlternative.peirceIdempotent c i := by
  let d := IsAlternative.peirceIdempotent c i
  have hd : C.IsElementaryIdempotent d := hc.peirceIdempotent i
  have hdx : d * x = x := (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self i i).mp hx |>.1
  have hxd : x * d = x := (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self i i).mp hx |>.2
  have hnx : C.norm x = 0 := by
    calc
      C.norm x = C.norm (d * x) := congr_arg C.norm hdx.symm
      _ = C.norm d * C.norm x := hmul.norm_mul d x
      _ = 0 := by rw [hd.norm_eq_zero, zero_mul]
  have hndx : C.norm (d + x) = 0 := by
    have hfix : d * (d + x) = d + x := by rw [mul_add, hd.mul_self, hdx]
    calc
      C.norm (d + x) = C.norm (d * (d + x)) := congr_arg C.norm hfix.symm
      _ = C.norm d * C.norm (d + x) := hmul.norm_mul d (d + x)
      _ = 0 := by rw [hd.norm_eq_zero, zero_mul]
  have hxx := C.mul_self_eq x
  rw [hnx, zero_smul, sub_zero] at hxx
  have hsum := C.mul_self_eq (d + x)
  rw [hndx, zero_smul, sub_zero] at hsum
  simp only [add_mul, mul_add, hd.mul_self, hdx, hxd, hxx, map_add, hd.trace_eq_one,
    one_smul, add_smul] at hsum
  have hcancel : d + x + (x + C.trace x • x) =
      d + x + (C.trace x • d + C.trace x • x) := hsum.trans (by module)
  have hcancel' : x + C.trace x • x = C.trace x • d + C.trace x • x :=
    add_left_cancel hcancel
  change x = C.trace x • d
  exact add_right_cancel hcancel'

/-- The diagonal Peirce component `Cᵢᵢ` is the scalar line `k cᵢ`
[GPR, Exc. 19.35(1)]. -/
theorem peirceComponent_same (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (i : Bool) :
    IsAlternative.peirceComponent (R := k) c i i =
      k ∙ IsAlternative.peirceIdempotent c i := by
  apply le_antisymm
  · intro x hx
    rw [hc.eq_trace_smul_peirceIdempotent hmul hx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self
      (x := IsAlternative.peirceIdempotent c i) i i).mpr
      ⟨IsAlternative.peirceIdempotent_mul_self hc.mul_self i,
        IsAlternative.peirceIdempotent_mul_self hc.mul_self i⟩

/-- A diagonal Peirce component at an elementary idempotent is linearly equivalent to the base
ring, by `a ↦ a cᵢ`; the inverse is the trace [GPR, Exc. 19.35(1)]. -/
def diagonalEquiv (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative) (i : Bool) :
    k ≃ₗ[k] IsAlternative.peirceComponent (R := k) c i i where
  toFun a := ⟨a • IsAlternative.peirceIdempotent c i, by
    rw [hc.peirceComponent_same hmul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
  invFun x := C.trace x
  map_add' a b := by ext; exact add_smul a b _
  map_smul' a b := by ext; exact mul_smul a b _
  left_inv a := by simp [map_smul, (hc.peirceIdempotent i).trace_eq_one]
  right_inv x := Subtype.ext (hc.eq_trace_smul_peirceIdempotent hmul x.property).symm

omit [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A] in
/-- Conjugation exchanges the two complementary idempotents. -/
theorem conj_peirceIdempotent (hc : C.IsElementaryIdempotent c) (i : Bool) :
    C.conj (IsAlternative.peirceIdempotent c i) =
      IsAlternative.peirceIdempotent c (!i) := by
  cases i
  · exact hc.conj_eq
  · simpa [IsAlternative.peirceIdempotent] using (hc.peirceIdempotent true).conj_eq

/-- Every Peirce component is totally singular for the quadratic norm: each of its elements has
norm zero. -/
theorem norm_eq_zero_of_mem_peirceComponent (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {x : A} {i j : Bool}
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j) : C.norm x = 0 := by
  let d := IsAlternative.peirceIdempotent c i
  have hd : C.IsElementaryIdempotent d := hc.peirceIdempotent i
  have hdx : d * x = x :=
    (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self i j).mp hx |>.1
  calc
    C.norm x = C.norm (d * x) := congr_arg C.norm hdx.symm
    _ = C.norm d * C.norm x := hmul.norm_mul d x
    _ = 0 := by rw [hd.norm_eq_zero, zero_mul]

/-- Peirce components with the same left index are mutually orthogonal for the polar form. -/
theorem polar_eq_zero_of_mem_peirceComponent_of_left_eq
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {x y : A} {i j l : Bool}
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c i l) :
    QuadraticMap.polar C.norm x y = 0 := by
  have hix : IsAlternative.peirceIdempotent c i * x = x :=
    (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self i j).mp hx |>.1
  calc
    QuadraticMap.polar C.norm x y = QuadraticMap.polar C.norm
        (IsAlternative.peirceIdempotent c i * x) y := congr_arg (fun z ↦
          QuadraticMap.polar C.norm z y) hix.symm
    _ = QuadraticMap.polar C.norm x
        (C.conj (IsAlternative.peirceIdempotent c i) * y) :=
      hmul.polar_mul_left _ _ _
    _ = QuadraticMap.polar C.norm x
        (IsAlternative.peirceIdempotent c (!i) * y) := by rw [hc.conj_peirceIdempotent]
    _ = 0 := by
      rw [IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self hy]
      cases i <;> simp

/-- Peirce components with the same right index are mutually orthogonal for the polar form. -/
theorem polar_eq_zero_of_mem_peirceComponent_of_right_eq
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {x y : A} {i m j : Bool}
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c m j) :
    QuadraticMap.polar C.norm x y = 0 := by
  have hxj : x * IsAlternative.peirceIdempotent c j = x :=
    (IsAlternative.mem_peirceComponent_iff_mul_eq hc.mul_self i j).mp hx |>.2
  calc
    QuadraticMap.polar C.norm x y = QuadraticMap.polar C.norm
        (x * IsAlternative.peirceIdempotent c j) y := congr_arg (fun z ↦
          QuadraticMap.polar C.norm z y) hxj.symm
    _ = QuadraticMap.polar C.norm x
        (y * C.conj (IsAlternative.peirceIdempotent c j)) :=
      hmul.polar_mul_right _ _ _
    _ = QuadraticMap.polar C.norm x
        (y * IsAlternative.peirceIdempotent c (!j)) := by rw [hc.conj_peirceIdempotent]
    _ = 0 := by
      rw [IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self hy]
      cases j <;> simp

/-- An off-diagonal Peirce component has trace zero. -/
theorem trace_eq_zero_of_mem_peirceComponent (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {x : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j) : C.trace x = 0 := by
  have hi : IsAlternative.peirceIdempotent c i ∈
      IsAlternative.peirceComponent (R := k) c i i :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self i
  have hj : IsAlternative.peirceIdempotent c j ∈
      IsAlternative.peirceComponent (R := k) c j j :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self j
  have hsum : IsAlternative.peirceIdempotent c i +
      IsAlternative.peirceIdempotent c j = 1 := by
    cases i <;> cases j <;> simp_all [IsAlternative.peirceIdempotent]
  rw [trace_apply, ← hsum, QuadraticMap.polar_add_left,
    hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul hi hx,
    hc.polar_eq_zero_of_mem_peirceComponent_of_right_eq hmul hj hx, add_zero]

/-- Every element of an off-diagonal Peirce component has square zero. -/
theorem mul_self_eq_zero_of_mem_peirceComponent (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {x : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j) : x * x = 0 := by
  rw [C.mul_self_eq, hc.trace_eq_zero_of_mem_peirceComponent hmul hij hx,
    hc.norm_eq_zero_of_mem_peirceComponent hmul hx, zero_smul, zero_smul, sub_zero]

/-- Multiplication restricted to one off-diagonal Peirce component is alternating:
`x * y + y * x = 0` [GPR, Exc. 14.12]. This is the linearization of the square-zero rule and does
not divide by `2`. -/
theorem mul_add_mul_eq_zero_of_mem_peirceComponent
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c i j) :
    x * y + y * x = 0 := by
  have hxy : x + y ∈ IsAlternative.peirceComponent (R := k) c i j :=
    (IsAlternative.peirceComponent (R := k) c i j).add_mem hx hy
  have hsum := hc.mul_self_eq_zero_of_mem_peirceComponent hmul hij hxy
  calc
    x * y + y * x = y * x + x * y := add_comm _ _
    _ = 0 := by
      simpa only [add_mul, mul_add,
        hc.mul_self_eq_zero_of_mem_peirceComponent hmul hij hx,
        hc.mul_self_eq_zero_of_mem_peirceComponent hmul hij hy, zero_add, add_zero] using hsum

/-- Products in one off-diagonal Peirce component anticommute [GPR, Exc. 14.12]. This formulation is
valid in characteristic `2`, where the negation may be invisible. -/
theorem mul_eq_neg_mul_of_mem_peirceComponent
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c i j) :
    x * y = -(y * x) := by
  rw [eq_neg_iff_add_eq_zero]
  exact hc.mul_add_mul_eq_zero_of_mem_peirceComponent hmul hij hx hy

/-- The product of elements in opposite off-diagonal Peirce components is their negative polar
pairing times the corresponding diagonal idempotent [GPR, Exc. 14.12, Exc. 19.35]:
`xy = -n(x, y)cᵢ` for `x ∈ Cᵢⱼ` and `y ∈ Cⱼᵢ`. -/
theorem mul_eq_neg_polar_smul_peirceIdempotent
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c j i) :
    x * y = -QuadraticMap.polar C.norm x y • IsAlternative.peirceIdempotent c i := by
  have hxy : x * y ∈ IsAlternative.peirceComponent (R := k) c i i :=
    IsAlternative.mul_mem_peirceComponent_of_opposite hc.mul_self hij hx hy
  calc
    x * y = C.trace (x * y) • IsAlternative.peirceIdempotent c i :=
      hc.eq_trace_smul_peirceIdempotent hmul hxy
    _ = -QuadraticMap.polar C.norm x y • IsAlternative.peirceIdempotent c i := by
      rw [hmul.trace_mul, hc.trace_eq_zero_of_mem_peirceComponent hmul hij hx,
        hc.trace_eq_zero_of_mem_peirceComponent hmul (Ne.symm hij) hy, zero_mul, zero_sub]

/-- The Peirce trace trilinear form vanishes when its first two arguments agree. -/
theorem trace_mul_mul_self_left (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {i j : Bool} (hij : i ≠ j)
    (x y : IsAlternative.peirceComponent (R := k) c i j) :
    C.trace (((x : A) * x) * y) = 0 := by
  rw [hc.mul_self_eq_zero_of_mem_peirceComponent hmul hij x.property, zero_mul, map_zero]

/-- The Peirce trace trilinear form vanishes when its last two arguments agree. -/
theorem trace_mul_mul_self_right (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {i j : Bool} (hij : i ≠ j)
    (x y : IsAlternative.peirceComponent (R := k) c i j) :
    C.trace (((x : A) * y) * y) = 0 := by
  rw [IsAlternative.mul_self_mul_right, hc.mul_self_eq_zero_of_mem_peirceComponent hmul hij
    y.property, mul_zero, map_zero]

/-- The Peirce trace trilinear form vanishes when its outside arguments agree. -/
theorem trace_mul_mul_self_outer (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {i j : Bool} (hij : i ≠ j)
    (x y : IsAlternative.peirceComponent (R := k) c i j) :
    C.trace (((x : A) * y) * x) = 0 := by
  have htrace : C.trace (x : A) = 0 :=
    hc.trace_eq_zero_of_mem_peirceComponent hmul hij x.property
  have hnorm : C.norm (x : A) = 0 := hc.norm_eq_zero_of_mem_peirceComponent hmul x.property
  have hpolar : QuadraticMap.polar C.norm ((x : A) * y) x = 0 := by
    rw [hmul.polar_mul_left, C.conj_mul_self, hnorm, zero_smul,
      QuadraticMap.polar_zero_right]
  rw [hmul.trace_mul, htrace, mul_zero, hpolar, sub_zero]

/-- The trilinear form `(x, y, z) ↦ t((xy)z)` on a Peirce component. -/
def peirceTraceTrilinear (C : ConicAlgebra k A) (c : A) (i j : Bool) :
    MultilinearMap k
      (fun _ : Fin 3 ↦ IsAlternative.peirceComponent (R := k) c i j) k :=
  MultilinearMap.mk' (fun x ↦ C.trace (((x 0 : A) * x 1) * x 2)) (by
    intro x m y z
    fin_cases m <;> simp [Function.update, Fin.ext_iff, add_mul, mul_add])
    (by
      intro x m r y
      fin_cases m <;> simp [Function.update, Fin.ext_iff, smul_mul_assoc, mul_smul_comm])

omit [IsAlternative A] in
@[simp] theorem peirceTraceTrilinear_apply (C : ConicAlgebra k A) (c : A) (i j : Bool)
    (x : Fin 3 → IsAlternative.peirceComponent (R := k) c i j) :
    peirceTraceTrilinear C c i j x = C.trace (((x 0 : A) * x 1) * x 2) := rfl

/-- The alternating trilinear form on an off-diagonal Peirce component at the end of
[GPR, Exc. 19.35]. -/
def peirceTraceAlternating (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    {i j : Bool} (hij : i ≠ j) :
    IsAlternative.peirceComponent (R := k) c i j [⋀^Fin 3]→ₗ[k] k where
  __ := peirceTraceTrilinear C c i j
  map_eq_zero_of_eq' x m n hmn hne := by
    change C.trace (((x 0 : A) * x 1) * x 2) = 0
    fin_cases m <;> fin_cases n
    · exact (hne rfl).elim
    · have h : x 0 = x 1 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_left hmul hij (x 1) (x 2)
    · have h : x 0 = x 2 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_outer hmul hij (x 2) (x 1)
    · have h : x 1 = x 0 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_left hmul hij (x 0) (x 2)
    · exact (hne rfl).elim
    · have h : x 1 = x 2 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_right hmul hij (x 0) (x 2)
    · have h : x 2 = x 0 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_outer hmul hij (x 0) (x 1)
    · have h : x 2 = x 1 := by
        convert hmn using 1 <;> apply congr_arg x <;> apply Fin.ext <;> rfl
      rw [h]
      exact hc.trace_mul_mul_self_right hmul hij (x 0) (x 1)
    · exact (hne rfl).elim

@[simp] theorem peirceTraceAlternating_apply (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) {i j : Bool} (hij : i ≠ j)
    (x : Fin 3 → IsAlternative.peirceComponent (R := k) c i j) :
    hc.peirceTraceAlternating hmul hij x = C.trace (((x 0 : A) * x 1) * x 2) := rfl

/-- The element with Peirce coordinates `(a₁, x₁₂, x₂₁, a₂)` relative to an elementary
idempotent `c`; see [GPR, Exc. 19.35(2)]. -/
def peirceElement (c : A) (a₁ a₂ : k)
    (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ : IsAlternative.peirceComponent (R := k) c true false) : A :=
  a₁ • IsAlternative.peirceIdempotent c false + x₁₂ + x₂₁ +
    a₂ • IsAlternative.peirceIdempotent c true

/-- The four projections recover the corresponding Peirce coordinates. -/
theorem peirceProjection_peirceElement (hc : C.IsElementaryIdempotent c)
    (a₁ a₂ : k) (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ : IsAlternative.peirceComponent (R := k) c true false) (i j : Bool) :
    IsAlternative.peirceProjection (R := k) c i j
      (peirceElement c a₁ a₂ x₁₂ x₂₁) =
        if (i, j) = (false, false) then a₁ • IsAlternative.peirceIdempotent c false
        else if (i, j) = (false, true) then x₁₂
        else if (i, j) = (true, false) then x₂₁
        else a₂ • IsAlternative.peirceIdempotent c true := by
  simp only [peirceElement, map_add, map_smul]
  have hc₀ : IsAlternative.peirceIdempotent c false ∈
      IsAlternative.peirceComponent (R := k) c false false :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self false
  have hc₁ : IsAlternative.peirceIdempotent c true ∈
      IsAlternative.peirceComponent (R := k) c true true :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self true
  have hproj (a b : Bool) {x : A}
      (hx : x ∈ IsAlternative.peirceComponent (R := k) c a b) :
      IsAlternative.peirceProjection (R := k) c i j x =
        if (i, j) = (a, b) then x else 0 := by
    have h := IsAlternative.peirceProjection_apply_of_mem (R := k) hc.mul_self
      (i := i) (j := j) (⟨x, hx⟩ : IsAlternative.peirceComponent (R := k) c a b)
    split_ifs with hij
    · simpa [hij] using h
    · simpa [hij] using h
  rw [hproj false false hc₀, hproj false true x₁₂.property,
    hproj true false x₂₁.property, hproj true true hc₁]
  cases i <;> cases j <;> simp

/-- Every element has Peirce coordinates as in [GPR, Exc. 19.35(2)]. -/
theorem exists_eq_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (x : A) :
    ∃ (a₁ a₂ : k) (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
      (x₂₁ : IsAlternative.peirceComponent (R := k) c true false),
      x = peirceElement c a₁ a₂ x₁₂ x₂₁ := by
  let x₁₁ : IsAlternative.peirceComponent (R := k) c false false :=
    ⟨IsAlternative.peirceProjection (R := k) c false false x, ⟨x, rfl⟩⟩
  let x₁₂ : IsAlternative.peirceComponent (R := k) c false true :=
    ⟨IsAlternative.peirceProjection (R := k) c false true x, ⟨x, rfl⟩⟩
  let x₂₁ : IsAlternative.peirceComponent (R := k) c true false :=
    ⟨IsAlternative.peirceProjection (R := k) c true false x, ⟨x, rfl⟩⟩
  let x₂₂ : IsAlternative.peirceComponent (R := k) c true true :=
    ⟨IsAlternative.peirceProjection (R := k) c true true x, ⟨x, rfl⟩⟩
  refine ⟨C.trace x₁₁, C.trace x₂₂, x₁₂, x₂₁, ?_⟩
  have h₁₁ := hc.eq_trace_smul_peirceIdempotent hmul x₁₁.property
  have h₂₂ := hc.eq_trace_smul_peirceIdempotent hmul x₂₂.property
  have hdecomp := IsAlternative.sum_peirceProjection_apply (R := k) c x
  change x = C.trace x₁₁ • IsAlternative.peirceIdempotent c false + x₁₂ + x₂₁ +
    C.trace x₂₂ • IsAlternative.peirceIdempotent c true
  rw [← h₁₁, ← h₂₂]
  exact hdecomp.symm

/-- The norm in Peirce coordinates [GPR, Exc. 19.35(3)]. -/
theorem norm_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (a₁ a₂ : k) (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ : IsAlternative.peirceComponent (R := k) c true false) :
    C.norm (peirceElement c a₁ a₂ x₁₂ x₂₁) =
      a₁ * a₂ + QuadraticMap.polar C.norm x₁₂ x₂₁ := by
  have hc₁ : IsAlternative.peirceIdempotent c false ∈
      IsAlternative.peirceComponent (R := k) c false false :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self false
  have hc₂ : IsAlternative.peirceIdempotent c true ∈
      IsAlternative.peirceComponent (R := k) c true true :=
    IsAlternative.peirceIdempotent_mem_peirceComponent hc.mul_self true
  have hn₁ : C.norm (IsAlternative.peirceIdempotent c false) = 0 :=
    (hc.peirceIdempotent false).norm_eq_zero
  have hn₂ : C.norm (IsAlternative.peirceIdempotent c true) = 0 :=
    (hc.peirceIdempotent true).norm_eq_zero
  have hn₁₂ : C.norm (x₁₂ : A) = 0 :=
    hc.norm_eq_zero_of_mem_peirceComponent hmul x₁₂.property
  have hn₂₁ : C.norm (x₂₁ : A) = 0 :=
    hc.norm_eq_zero_of_mem_peirceComponent hmul x₂₁.property
  have h₁₁₁₂ : QuadraticMap.polar C.norm
      (IsAlternative.peirceIdempotent c false) x₁₂ = 0 :=
    hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul hc₁ x₁₂.property
  have h₁₁₂₁ : QuadraticMap.polar C.norm
      (IsAlternative.peirceIdempotent c false) x₂₁ = 0 :=
    hc.polar_eq_zero_of_mem_peirceComponent_of_right_eq hmul hc₁ x₂₁.property
  have h₁₂₂₂ : QuadraticMap.polar C.norm x₁₂
      (IsAlternative.peirceIdempotent c true) = 0 :=
    hc.polar_eq_zero_of_mem_peirceComponent_of_right_eq hmul x₁₂.property hc₂
  have h₂₁₂₂ : QuadraticMap.polar C.norm x₂₁
      (IsAlternative.peirceIdempotent c true) = 0 :=
    hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul x₂₁.property hc₂
  have h₁₁₂₂ : QuadraticMap.polar C.norm
      (IsAlternative.peirceIdempotent c false)
      (IsAlternative.peirceIdempotent c true) = 1 := by
    simpa [IsAlternative.peirceIdempotent, hc.conj_eq] using hc.polar_conj
  simp only [peirceElement, C.norm_add, QuadraticMap.map_smul,
    QuadraticMap.polar_add_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hn₁, hn₂, hn₁₂, hn₂₁,
    h₁₁₁₂, h₁₁₂₁, h₁₂₂₂, h₂₁₂₂, h₁₁₂₂]
  ring

/-- The polar form in Peirce coordinates [GPR, Exc. 19.35(4)]. -/
theorem polar_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (a₁ a₂ b₁ b₂ : k)
    (x₁₂ y₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ y₂₁ : IsAlternative.peirceComponent (R := k) c true false) :
    QuadraticMap.polar C.norm (peirceElement c a₁ a₂ x₁₂ x₂₁)
        (peirceElement c b₁ b₂ y₁₂ y₂₁) =
      a₁ * b₂ + a₂ * b₁ + QuadraticMap.polar C.norm x₁₂ y₂₁ +
        QuadraticMap.polar C.norm x₂₁ y₁₂ := by
  rw [QuadraticMap.polar]
  have hadd :
      peirceElement c a₁ a₂ x₁₂ x₂₁ + peirceElement c b₁ b₂ y₁₂ y₂₁ =
        peirceElement c (a₁ + b₁) (a₂ + b₂) (x₁₂ + y₁₂) (x₂₁ + y₂₁) := by
    simp only [peirceElement, add_smul, Submodule.coe_add]
    module
  rw [hadd, hc.norm_peirceElement hmul, hc.norm_peirceElement hmul,
    hc.norm_peirceElement hmul]
  simp only [Submodule.coe_add, QuadraticMap.polar_add_left,
    QuadraticMap.polar_add_right]
  rw [QuadraticMap.polar_comm C.norm y₁₂ x₂₁]
  ring

/-- The trace in Peirce coordinates [GPR, Exc. 19.35(5)]. -/
theorem trace_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (a₁ a₂ : k) (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ : IsAlternative.peirceComponent (R := k) c true false) :
    C.trace (peirceElement c a₁ a₂ x₁₂ x₂₁) = a₁ + a₂ := by
  let z₁₂ : IsAlternative.peirceComponent (R := k) c false true := 0
  let z₂₁ : IsAlternative.peirceComponent (R := k) c true false := 0
  have hone : peirceElement c 1 1 z₁₂ z₂₁ = 1 := by
    simp [peirceElement, z₁₂, z₂₁, IsAlternative.peirceIdempotent]
  rw [trace_apply, ← hone, hc.polar_peirceElement hmul]
  simp [z₁₂, z₂₁, add_comm]

/-- Conjugation in Peirce coordinates [GPR, Exc. 19.35(6)]: it exchanges the diagonal
coefficients and negates the off-diagonal components. -/
theorem conj_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (a₁ a₂ : k) (x₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ : IsAlternative.peirceComponent (R := k) c true false) :
    C.conj (peirceElement c a₁ a₂ x₁₂ x₂₁) =
      peirceElement c a₂ a₁ (-x₁₂) (-x₂₁) := by
  rw [ConicAlgebra.conj_apply, hc.trace_peirceElement hmul]
  simp only [peirceElement, IsAlternative.peirceIdempotent, Submodule.coe_neg]
  module

/-- The polar pairing from `C₁₂` to the dual of `C₂₁`. -/
def offDiagonalPairing (C : ConicAlgebra k A) (c : A) :
    IsAlternative.peirceComponent (R := k) c false true →ₗ[k]
      Module.Dual k (IsAlternative.peirceComponent (R := k) c true false) :=
  (QuadraticMap.polarBilin C.norm).domRestrict₁₂
    (IsAlternative.peirceComponent (R := k) c false true)
    (IsAlternative.peirceComponent (R := k) c true false)

omit [IsAlternative A] in
@[simp] theorem offDiagonalPairing_apply (C : ConicAlgebra k A) (c : A)
    (x : IsAlternative.peirceComponent (R := k) c false true)
    (y : IsAlternative.peirceComponent (R := k) c true false) :
    offDiagonalPairing C c x y = QuadraticMap.polar C.norm x y := rfl

/-- Under regularity, the off-diagonal Peirce components are in duality under the polar form,
as in [GPR, Exc. 19.35]. -/
theorem bijective_offDiagonalPairing (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    Function.Bijective (offDiagonalPairing C c) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    apply hreg.1
    ext z
    simp only [Submodule.coe_zero, map_zero, LinearMap.zero_apply]
    change QuadraticMap.polar C.norm x z = 0
    have hdecomp := IsAlternative.sum_peirceProjection_apply (R := k) c z
    have h₀₀ : IsAlternative.peirceProjection (R := k) c false false z ∈
        IsAlternative.peirceComponent (R := k) c false false := ⟨z, rfl⟩
    have h₀₁ : IsAlternative.peirceProjection (R := k) c false true z ∈
        IsAlternative.peirceComponent (R := k) c false true := ⟨z, rfl⟩
    have h₁₁ : IsAlternative.peirceProjection (R := k) c true true z ∈
        IsAlternative.peirceComponent (R := k) c true true := ⟨z, rfl⟩
    have hpair := LinearMap.mem_ker.mp hx
    have h₁₀ : offDiagonalPairing C c x
        ⟨IsAlternative.peirceProjection (R := k) c true false z, ⟨z, rfl⟩⟩ = 0 := by
      rw [hpair]
      rfl
    rw [← hdecomp, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right]
    rw [hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul x.property h₀₀,
      hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul x.property h₀₁,
      show QuadraticMap.polar C.norm x
          (IsAlternative.peirceProjection (R := k) c true false z) = 0 from h₁₀,
      hc.polar_eq_zero_of_mem_peirceComponent_of_right_eq hmul x.property h₁₁]
    simp
  · intro f
    let p₂₁ : A →ₗ[k] IsAlternative.peirceComponent (R := k) c true false :=
      (IsAlternative.peirceProjection (R := k) c true false).rangeRestrict
    let F : Module.Dual k A := f.comp p₂₁
    obtain ⟨a, ha⟩ := hreg.2 F
    let x₁₂ : IsAlternative.peirceComponent (R := k) c false true :=
      ⟨IsAlternative.peirceProjection (R := k) c false true a, ⟨a, rfl⟩⟩
    refine ⟨x₁₂, ?_⟩
    ext y
    have hdecomp := IsAlternative.sum_peirceProjection_apply (R := k) c a
    have h₀₀ : IsAlternative.peirceProjection (R := k) c false false a ∈
        IsAlternative.peirceComponent (R := k) c false false := ⟨a, rfl⟩
    have h₁₀ : IsAlternative.peirceProjection (R := k) c true false a ∈
        IsAlternative.peirceComponent (R := k) c true false := ⟨a, rfl⟩
    have h₁₁ : IsAlternative.peirceProjection (R := k) c true true a ∈
        IsAlternative.peirceComponent (R := k) c true true := ⟨a, rfl⟩
    have hpolar : QuadraticMap.polar C.norm a y =
        QuadraticMap.polar C.norm x₁₂ y := by
      rw [← hdecomp, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
        QuadraticMap.polar_add_left]
      rw [hc.polar_eq_zero_of_mem_peirceComponent_of_right_eq hmul h₀₀ y.property,
        hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul h₁₀ y.property,
        hc.polar_eq_zero_of_mem_peirceComponent_of_left_eq hmul h₁₁ y.property]
      simp [x₁₂]
    have hp₂₁ : p₂₁ (y : A) = y :=
      Subtype.ext ((IsAlternative.mem_peirceComponent_iff hc.mul_self true false).mp y.property)
    have hay := LinearMap.congr_fun ha (y : A)
    change QuadraticMap.polar C.norm a y = f (p₂₁ (y : A)) at hay
    rw [hp₂₁] at hay
    exact hpolar.symm.trans hay

/-- The linear equivalence expressing the duality between `C₁₂` and `C₂₁`
[GPR, Exc. 19.35]. -/
noncomputable def offDiagonalDuality (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    IsAlternative.peirceComponent (R := k) c false true ≃ₗ[k]
      Module.Dual k (IsAlternative.peirceComponent (R := k) c true false) :=
  LinearEquiv.ofBijective (offDiagonalPairing C c)
    (hc.bijective_offDiagonalPairing hmul hreg)

/-- **The rank count in `GPR 22.13`.** At an elementary idempotent in a constant-rank-four
composition algebra with regular norm, both off-diagonal Peirce components have constant rank
one. Thus each is a line bundle. -/
theorem rankAtStalk_offDiagonal_eq_one [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (hreg : C.norm.IsGPRRegular)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) (i : Bool) :
    Module.rankAtStalk (R := k)
      (IsAlternative.peirceComponent (R := k) c i (!i)) = 1 := by
  let X (a b : Bool) := IsAlternative.peirceComponent (R := k) c a b
  let (a b : Bool) : Module.Finite k (X a b) :=
    IsAlternative.finite_peirceComponent a b
  let (a b : Bool) : Module.Projective k (X a b) :=
    IsAlternative.projective_peirceComponent hc.mul_self a b
  have hdiag (a : Bool) : Module.rankAtStalk (R := k) (X a a) =
      Module.rankAtStalk (R := k) k :=
    Module.rankAtStalk_eq_of_equiv (hc.diagonalEquiv hmul a).symm
  have hoff : Module.rankAtStalk (R := k) (X false true) =
      Module.rankAtStalk (R := k) (X true false) := by
    calc
      Module.rankAtStalk (R := k) (X false true) =
          Module.rankAtStalk (R := k) (Module.Dual k (X true false)) :=
        Module.rankAtStalk_eq_of_equiv (hc.offDiagonalDuality hmul hreg)
      _ = Module.rankAtStalk (R := k) (X true false) := TauCeti.Module.rankAtStalk_dual _ _
  change Module.rankAtStalk (R := k) (X i (!i)) = 1
  ext p
  let : Nontrivial k := ⟨⟨0, 1, fun h ↦ p.2.ne_top <|
    (Ideal.eq_top_iff_one p.asIdeal).mpr <| by simpa [h] using p.asIdeal.zero_mem⟩⟩
  have htotal := congrFun
    (Module.rankAtStalk_eq_of_equiv
      (IsAlternative.peirceDecomposition (R := k) hc.mul_self)) p
  rw [hA] at htotal
  simp only [Pi.one_apply] at htotal ⊢
  rw [Module.rankAtStalk_pi] at htotal
  rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type] at htotal
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, add_assoc] at htotal
  rw [congrFun (hdiag false) p, congrFun (hdiag true) p,
    Module.rankAtStalk_self, congrFun hoff p] at htotal
  simp only [Pi.one_apply] at htotal
  dsimp [X] at htotal ⊢
  cases i
  · change Module.rankAtStalk
      (IsAlternative.peirceComponent (R := k) c false true) p = 1
    have heq := congrFun hoff p
    dsimp [X] at heq
    rw [heq]
    omega
  · change Module.rankAtStalk
      (IsAlternative.peirceComponent (R := k) c true false) p = 1
    omega

/-- **The line-bundle step in `GPR 22.13`.** In a rank-four composition algebra with an
elementary idempotent, each off-diagonal Peirce component is finite projective of constant rank
one. The regularity needed for the duality and rank count is supplied by `GPR 19.11`. -/
theorem isLocallyFreeRankOne_offDiagonal [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) (i : Bool) :
    Module.IsLocallyFreeRankOne k
      (IsAlternative.peirceComponent (R := k) c i (!i)) := by
  let : Module.Finite k
      (IsAlternative.peirceComponent (R := k) c i (!i)) :=
    IsAlternative.finite_peirceComponent i (!i)
  let : Module.Projective k
      (IsAlternative.peirceComponent (R := k) c i (!i)) :=
    IsAlternative.projective_peirceComponent hc.mul_self i (!i)
  exact ⟨inferInstance, inferInstance,
    hc.rankAtStalk_offDiagonal_eq_one hcomp.isMultiplicative
      (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)) hA i⟩

/-- **The vanishing product needed in `GPR 22.13`.** In a rank-four composition algebra,
multiplication of any two elements in the same off-diagonal Peirce component is zero. The
component is a line bundle, and its internal multiplication is alternating because every element
squares to zero. -/
theorem mul_eq_zero_of_mem_offDiagonal_of_rankAtStalk_eq_four
    [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    {x y : A} {i j : Bool} (hij : i ≠ j)
    (hx : x ∈ IsAlternative.peirceComponent (R := k) c i j)
    (hy : y ∈ IsAlternative.peirceComponent (R := k) c i j) : x * y = 0 := by
  have hji : j = !i := by cases i <;> cases j <;> simp_all
  subst j
  let X := IsAlternative.peirceComponent (R := k) c i (!i)
  let B : LinearMap.BilinMap k X A :=
    (LinearMap.mul k A).compl₁₂ X.subtype X.subtype
  have hline : Module.IsLocallyFreeRankOne k X := by
    simpa [X] using hc.isLocallyFreeRankOne_offDiagonal hcomp hA i
  have hB : B = 0 := hline.bilinMap_eq_zero_of_map_self_eq_zero B fun z ↦
    hc.mul_self_eq_zero_of_mem_peirceComponent hcomp.isMultiplicative hij z.property
  have hxy := LinearMap.congr_fun₂ hB (⟨x, hx⟩ : X) (⟨y, hy⟩ : X)
  simpa [B] using hxy

/-- The complete Peirce-coordinate multiplication formula in rank four, the multiplication table
used in the converse half of `GPR 22.13`. -/
theorem mul_peirceElement_of_rankAtStalk_eq_four [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (a₁ a₂ b₁ b₂ : k)
    (x₁₂ y₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ y₂₁ : IsAlternative.peirceComponent (R := k) c true false) :
    peirceElement c a₁ a₂ x₁₂ x₂₁ * peirceElement c b₁ b₂ y₁₂ y₂₁ =
      peirceElement c
        (a₁ * b₁ - QuadraticMap.polar C.norm x₁₂ y₂₁)
        (a₂ * b₂ - QuadraticMap.polar C.norm y₁₂ x₂₁)
        (a₁ • y₁₂ + b₂ • x₁₂) (b₁ • x₂₁ + a₂ • y₂₁) := by
  let c₁ := IsAlternative.peirceIdempotent c false
  let c₂ := IsAlternative.peirceIdempotent c true
  have hc₁ := IsAlternative.peirceIdempotent_mul_self hc.mul_self false
  have hc₂ := IsAlternative.peirceIdempotent_mul_self hc.mul_self true
  have hc₁c₂ :=
    IsAlternative.peirceIdempotent_mul_eq_zero hc.mul_self (by decide : false ≠ true)
  have hc₂c₁ :=
    IsAlternative.peirceIdempotent_mul_eq_zero hc.mul_self (by decide : true ≠ false)
  have hleft (x : IsAlternative.peirceComponent (R := k) c false true) : c₁ * x = x := by
    simpa [c₁] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property false
  have hright (x : IsAlternative.peirceComponent (R := k) c false true) : x * c₂ = x := by
    simpa [c₂] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property true
  have hleft0 (x : IsAlternative.peirceComponent (R := k) c false true) : c₂ * x = 0 := by
    simpa [c₂] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property true
  have hright0 (x : IsAlternative.peirceComponent (R := k) c false true) : x * c₁ = 0 := by
    simpa [c₁] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property false
  have hleft' (x : IsAlternative.peirceComponent (R := k) c true false) : c₂ * x = x := by
    simpa [c₂] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property true
  have hright' (x : IsAlternative.peirceComponent (R := k) c true false) : x * c₁ = x := by
    simpa [c₁] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property false
  have hleft0' (x : IsAlternative.peirceComponent (R := k) c true false) : c₁ * x = 0 := by
    simpa [c₁] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property false
  have hright0' (x : IsAlternative.peirceComponent (R := k) c true false) : x * c₂ = 0 := by
    simpa [c₂] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property true
  have h₁₂₁₂ : (x₁₂ : A) * y₁₂ = 0 :=
    hc.mul_eq_zero_of_mem_offDiagonal_of_rankAtStalk_eq_four hcomp hA (by decide)
      x₁₂.property y₁₂.property
  have h₂₁₂₁ : (x₂₁ : A) * y₂₁ = 0 :=
    hc.mul_eq_zero_of_mem_offDiagonal_of_rankAtStalk_eq_four hcomp hA (by decide)
      x₂₁.property y₂₁.property
  have h₁₂₂₁ := hc.mul_eq_neg_polar_smul_peirceIdempotent hcomp.isMultiplicative
    (by decide : false ≠ true) x₁₂.property y₂₁.property
  have h₂₁₁₂ := hc.mul_eq_neg_polar_smul_peirceIdempotent hcomp.isMultiplicative
    (by decide : true ≠ false) x₂₁.property y₁₂.property
  simp only [IsAlternative.peirceIdempotent_false,
    IsAlternative.peirceIdempotent_true] at h₁₂₂₁ h₂₁₁₂
  dsimp [c₁, c₂] at hc₁ hc₂ hc₁c₂ hc₂c₁ hleft hright
  dsimp [c₁, c₂] at hleft0 hright0 hleft' hright' hleft0' hright0'
  simp only [peirceElement, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    IsAlternative.peirceIdempotent_false, IsAlternative.peirceIdempotent_true]
  rw [hc₁, hc₁c₂, hc₂c₁, hc₂, hleft y₁₂, hleft0' y₂₁, hleft0 y₁₂,
    hleft' y₂₁, hright0 x₁₂, hright x₁₂, hright' x₂₁, hright0' x₂₁,
    h₁₂₁₂, h₂₁₂₁, h₁₂₂₁, h₂₁₁₂]
  simp only [smul_zero, add_zero, zero_add, Submodule.coe_add,
    Submodule.coe_smul]
  rw [QuadraticMap.polar_comm C.norm x₂₁ y₁₂]
  module

/-- For a constant-rank composition algebra of rank other than one, `C₁₂` and `C₂₁` are in
duality under the polar form [GPR, Exc. 19.35]. Regularity is supplied by `GPR 19.11`. -/
noncomputable def offDiagonalDualityOfIsComposition [Module.Finite k A]
    [Module.Projective k A] (hc : C.IsElementaryIdempotent c)
    (hcomp : C.IsComposition.{u, v, u}) {r : ℕ}
    (hrank : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : r ≠ 1) :
    IsAlternative.peirceComponent (R := k) c false true ≃ₗ[k]
      Module.Dual k (IsAlternative.peirceComponent (R := k) c true false) :=
  hc.offDiagonalDuality hcomp.isMultiplicative
    (hcomp.isGPRRegular_of_rankAtStalk_ne_one hrank hr)

end ConicAlgebra.IsElementaryIdempotent
