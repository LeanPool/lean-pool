/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic

/-!
# Multiplicative conic algebras and norm-associativity

A conic algebra is **multiplicative** (`GPR 19.1`; the older literature says its norm *permits
composition*) if `n(xy) = n(x) n(y)` for all `x, y`. This is the second half of the definition of a
composition algebra (`GPR 19.5`, Layer 7), the first half being a regularity condition on the norm.

The point of this file is that multiplicativity is much stronger than it looks: linearizing it
twice turns the *quadratic* statement `n(xy) = n(x)n(y)` into a *bilinear* one, and that bilinear
identity is exactly `GPR`'s **norm-associativity**

  `n(xy, z) = n(y, (conj x)z)`,   `n(xy, z) = n(x, z(conj y))`,

which is the workhorse of the whole composition-algebra theory. Everything here holds in an
arbitrary conic algebra over an arbitrary commutative ring: no alternativity, no regularity, no
projectivity, and nothing on `2`. Only additivity of the norm's polar form is used.

## Main definitions

* `ConicAlgebra.IsMultiplicative` : `n(xy) = n(x) n(y)`.
* `ConicAlgebra.HasTwoSidedInverses` : every nonzero element has a two-sided multiplicative
  inverse. ⚠ This is **weaker** than being a division algebra in the sense of `GPR 8.6`; see its
  docstring.

## Main results

* `QuadraticForm.polar_mul_mul_right_of_map_mul`, `QuadraticForm.polar_mul_mul_left_of_map_mul`,
  `QuadraticForm.polar_mul_add_polar_mul_of_map_mul` : the linearizations `GPR (19.1.3)`–`(19.1.5)`
  for any quadratic form permitting composition on a non-associative ring, with no conic structure.
* `ConicAlgebra.IsMultiplicative.polar_mul_mul_right`,
  `ConicAlgebra.IsMultiplicative.polar_mul_mul_left` : the first linearization, in either variable,
  `n(xz, yz) = n(x, y) n(z)` and `n(xy, xz) = n(x) n(y, z)`.
* `ConicAlgebra.IsMultiplicative.polar_mul_add_polar_mul` : the second linearization,
  `n(xz, yw) + n(xw, yz) = n(x, y) n(z, w)`.
* `ConicAlgebra.IsMultiplicative.polar_mul_left` : **norm-associativity**,
  `n(xy, z) = n(y, (conj x)z)`.
* `ConicAlgebra.IsMultiplicative.polar_mul_right` : norm-associativity on the other side,
  `n(xy, z) = n(x, z(conj y))`.
* `ConicAlgebra.IsMultiplicative.trace_mul` : `t(xy) = t(x)t(y) - n(x, y)`.
* `ConicAlgebra.IsMultiplicative.anisotropic_iff_noZeroDivisors_of_isDomain` : over a domain,
  the norm is anisotropic exactly when the algebra has no zero divisors.
* `ConicAlgebra.isMultiplicative_baseRing` : the base ring, with norm the squaring map, is
  multiplicative.

## Implementation notes

`n(x, y)` above is `QuadraticMap.polar C.norm x y`, the **un-halved** polar form
(overview §6(a)); the two linearizations below are obtained by additivity alone, so every
statement here is valid in characteristic 2.

The two norm-associativity identities are genuinely two statements, not one applied to the
opposite algebra: `A` is not assumed associative, commutative or alternative, so there is no
symmetry to exploit. They are proved the same way, by specializing the second linearization at
`y = 1` and at `w = 1` respectively.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.5,
  16.12--16.13, 19.1, 22.18.
-/

@[expose] public section

universe u v

/-! ### Quadratic forms permitting composition -/

open QuadraticMap

namespace QuadraticForm

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  {Q : QuadraticForm k A}

/-- **`GPR (19.1.4)`**: a quadratic form permitting composition satisfies
`n(xz, yz) = n(x, y) n(z)`. Only right distributivity is used; compare
`ConicAlgebra.IsMultiplicative.polar_mul_mul_right`, the same identity for a conic norm. -/
theorem polar_mul_mul_right_of_map_mul (hmul : ∀ x y : A, Q (x * y) = Q x * Q y) (x y z : A) :
    polar Q (x * z) (y * z) = polar Q x y * Q z := by
  have hadd : x * z + y * z = (x + y) * z := (add_mul x y z).symm
  simp only [QuadraticMap.polar, hadd, hmul]
  ring

/-- **`GPR (19.1.3)`**: a quadratic form permitting composition satisfies
`n(xy, xz) = n(x) n(y, z)`. Only left distributivity is used; compare
`ConicAlgebra.IsMultiplicative.polar_mul_mul_left`. -/
theorem polar_mul_mul_left_of_map_mul (hmul : ∀ x y : A, Q (x * y) = Q x * Q y) (x y z : A) :
    polar Q (x * y) (x * z) = Q x * polar Q y z := by
  have hadd : x * y + x * z = x * (y + z) := (mul_add x y z).symm
  simp only [QuadraticMap.polar, hadd, hmul]
  ring

/-- **`GPR (19.1.5)`**: a quadratic form permitting composition satisfies
`n(xz, yw) + n(xw, yz) = n(x, y) n(z, w)`. This is `GPR`'s
`n(xy, wz) + n(wy, xz) = n(x, w) n(y, z)` with the variables renamed, in the shape of
`ConicAlgebra.IsMultiplicative.polar_mul_add_polar_mul`; it is `(19.1.4)` linearized in `z`. -/
theorem polar_mul_add_polar_mul_of_map_mul (hmul : ∀ x y : A, Q (x * y) = Q x * Q y)
    (x y z w : A) :
    polar Q (x * z) (y * w) + polar Q (x * w) (y * z) = polar Q x y * polar Q z w := by
  have key := polar_mul_mul_right_of_map_mul hmul x y (z + w)
  simp only [mul_add, polar_add_left, polar_add_right, QuadraticMap.map_add Q z w] at key
  linear_combination key - polar_mul_mul_right_of_map_mul hmul x y z -
    polar_mul_mul_right_of_map_mul hmul x y w

end QuadraticForm

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] (C : ConicAlgebra k A)

/-- A conic algebra is **multiplicative** (`GPR 19.1`) if its norm permits composition:
`n(xy) = n(x) n(y)`.

This is a property of the pair `(A, n)`, not of `A` alone — the norm is data — so it is a
predicate on `C : ConicAlgebra k A` rather than a typeclass on `A`. It carries no regularity and
no projectivity: those are separate axes (overview §2), and a composition algebra
(`GPR 19.5`) is a conic algebra having all three. -/
def IsMultiplicative : Prop := ∀ x y : A, C.norm (x * y) = C.norm x * C.norm y

/-- **Every nonzero element has a two-sided inverse**: for each `x ≠ 0` there is `y` with
`x * y = 1` and `y * x = 1`.

⚠ **This property is weaker than being a division algebra as defined in `GPR 8.6`, and is
deliberately not called `IsDivision`.** `GPR 8.6` calls `A` a division algebra when `A ≠ 0` and, for
every `u ≠ 0`, the left and right multiplications `L_u` and `R_u` are bijective. Without
associativity a two-sided inverse does not give that: the real sedenions have an anisotropic norm,
so every nonzero `x` has the two-sided inverse `n(x)⁻¹ (conj x)`, yet they are not a division
algebra (`GPR Exc. 19.29(e)`). For a unital *alternative* algebra the two notions agree, given
`1 ≠ 0` (`GPR 13.8`); in particular they agree for composition algebras, which are alternative. Both
facts are formalized in `Conic/Division.lean` and `Composition/Sedenion.lean`:
`ConicAlgebra.isDivision_iff_hasTwoSidedInverses` is `GPR 13.8` for alternative conic algebras over
a field, and `ConicAlgebra.hasTwoSidedInverses_realSedenion` with
`ConicAlgebra.not_isDivision_realSedenion` is the sedenion example. Theorems stated with
`HasTwoSidedInverses` are about this weaker property; the classification theorems over a field are
also stated with `IsDivision`.

The property depends only on the multiplication, but is placed in the conic-algebra namespace
because it is used here in the classification of composition algebras. It does not assert
associativity. -/
def HasTwoSidedInverses (_C : ConicAlgebra k A) : Prop :=
  ∀ {x : A}, x ≠ 0 → ∃ y : A, x * y = 1 ∧ y * x = 1

namespace IsMultiplicative

variable {C}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Multiplicativity of the norm, as a rewrite rule. `ConicAlgebra.IsMultiplicative` is a `def`,
so it has to be unfolded before `rw`/`simp` can use it. -/
theorem norm_mul (h : C.IsMultiplicative) (x y : A) :
    C.norm (x * y) = C.norm x * C.norm y := h x y

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **First linearization of multiplicativity**, in the left variable: `n(xz, yz) = n(x, y) n(z)`.

Obtained from `n((x + y)z) = n(x + y) n(z)` by subtracting `n(xz) = n(x)n(z)` and
`n(yz) = n(y)n(z)`; only right distributivity and additivity are used. -/
theorem polar_mul_mul_right (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm (x * z) (y * z) = QuadraticMap.polar C.norm x y * C.norm z :=
  QuadraticForm.polar_mul_mul_right_of_map_mul h x y z

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **First linearization of multiplicativity**, in the right variable: `n(xy, xz) = n(x) n(y, z)`.

Not a consequence of `ConicAlgebra.IsMultiplicative.polar_mul_mul_right` — `A` is not assumed
commutative — but proved the same way, from `n(x(y + z)) = n(x) n(y + z)`. -/
theorem polar_mul_mul_left (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm (x * y) (x * z) = C.norm x * QuadraticMap.polar C.norm y z :=
  QuadraticForm.polar_mul_mul_left_of_map_mul h x y z

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **Second linearization of multiplicativity**: `n(xz, yw) + n(xw, yz) = n(x, y) n(z, w)`.

This is the bilinear shadow of `n(xy) = n(x)n(y)`, and the identity from which both halves of
norm-associativity below are read off. It is
`ConicAlgebra.IsMultiplicative.polar_mul_mul_right` linearized in its second variable. -/
theorem polar_mul_add_polar_mul (h : C.IsMultiplicative) (x y z w : A) :
    QuadraticMap.polar C.norm (x * z) (y * w) + QuadraticMap.polar C.norm (x * w) (y * z)
      = QuadraticMap.polar C.norm x y * QuadraticMap.polar C.norm z w :=
  QuadraticForm.polar_mul_add_polar_mul_of_map_mul h x y z w

omit [SMulCommClass k A A] in
/-- **Norm-associativity** (`GPR 16.12(4)`, obtained from multiplicativity by `GPR 17.2(a)`):
`n(xy, z) = n(y, (conj x)z)`.

The left factor may be moved across the polar form at the cost of conjugating it. Specialize the
second linearization at `y = 1`, where `n(x, 1) = t(x)`, and use `conj x = t(x)·1 - x`. -/
theorem polar_mul_left (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm (x * y) z = QuadraticMap.polar C.norm y (C.conj x * z) := by
  have key := h.polar_mul_add_polar_mul x 1 y z
  rw [one_mul, one_mul, QuadraticMap.polar_comm C.norm x 1, ← trace_apply] at key
  rw [conj_apply, sub_mul, smul_mul_assoc, one_mul, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, smul_eq_mul, QuadraticMap.polar_comm C.norm y (x * z)]
  linear_combination key

omit [IsScalarTower k A A] in
/-- **Norm-associativity**, the other side (`GPR 16.12(3)` and `17.2(a)`):
`n(xy, z) = n(x, z(conj y))`.

Not a consequence of `ConicAlgebra.IsMultiplicative.polar_mul_left` — `A` is not assumed
associative or commutative — but proved the same way, specializing the second linearization at
`w = 1`. -/
theorem polar_mul_right (h : C.IsMultiplicative) (x y z : A) :
    QuadraticMap.polar C.norm (x * y) z = QuadraticMap.polar C.norm x (z * C.conj y) := by
  have key := h.polar_mul_add_polar_mul x z y 1
  rw [mul_one, mul_one, QuadraticMap.polar_comm C.norm y 1, ← trace_apply] at key
  rw [conj_apply, mul_sub, mul_smul_comm, mul_one, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, smul_eq_mul]
  linear_combination key

omit [IsScalarTower k A A] in
/-- In a multiplicative conic algebra, the trace of a product is
`t(xy) = t(x)t(y) - n(x, y)` [GPR, 16.12(5), 16.13]. -/
theorem trace_mul (h : C.IsMultiplicative) (x y : A) :
    C.trace (x * y) = C.trace x * C.trace y - QuadraticMap.polar C.norm x y := by
  rw [trace_apply, QuadraticMap.polar_comm, h.polar_mul_right x y 1, one_mul, conj_apply,
    QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_comm C.norm x 1, ← trace_apply, smul_eq_mul]
  ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The norm of a product of conjugates: `n((conj x)(conj y)) = n(x) n(y)`. -/
theorem norm_conj_mul_conj (h : C.IsMultiplicative) (x y : A) :
    C.norm (C.conj x * C.conj y) = C.norm x * C.norm y := by
  rw [h.norm_mul, norm_conj, norm_conj]

omit [IsScalarTower k A A] in
/-- Over a domain, a multiplicative conic algebra has anisotropic norm if and only if it has no
zero divisors. Indeed, multiplicativity sends a zero product to a zero product of norms; in the
other direction, a null vector annihilates its conjugate, which is zero only when the original
vector is zero. This is the zero-divisor step used in `GPR 22.19`. -/
theorem anisotropic_iff_noZeroDivisors_of_isDomain [IsDomain k]
    (h : C.IsMultiplicative) : C.norm.Anisotropic ↔ NoZeroDivisors A := by
  constructor
  · intro hani
    refine ⟨fun {x y} hxy ↦ ?_⟩
    have hnorm : C.norm x * C.norm y = 0 := by
      rw [← h.norm_mul, hxy, map_zero]
    rcases mul_eq_zero.mp hnorm with hx | hy
    · exact Or.inl (hani x hx)
    · exact Or.inr (hani y hy)
  · intro hzero x hx
    have hmul : x * C.conj x = 0 := by
      rw [C.mul_conj_self, hx, zero_smul]
    rcases hzero.eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx | hx
    · exact hx
    · have := congrArg C.conj hx
      simpa only [C.conj_conj, map_zero] using this

omit [IsScalarTower k A A] in
/-- Over a field, every nonzero element of a multiplicative conic algebra has a two-sided inverse
if and only if its norm is anisotropic. Forwards, a null nonzero element cannot have an inverse
because norms multiply. Backwards, `n(x)⁻¹ (conj x)` is a two-sided inverse. This is the step of
`GPR 22.18` that `GPR` phrases with division algebras; `HasTwoSidedInverses` is weaker than that
notion in general, and agrees with it for composition algebras
(`ConicAlgebra.IsComposition.isDivision_iff_hasTwoSidedInverses`). -/
theorem hasTwoSidedInverses_iff_anisotropic {K : Type*} [Field K] {B : Type*} [NonAssocRing B]
    [Module K B] [SMulCommClass K B B] [IsScalarTower K B B] {D : ConicAlgebra K B}
    (h : D.IsMultiplicative) : D.HasTwoSidedInverses ↔ D.norm.Anisotropic := by
  constructor
  · intro hdiv x hx
    by_contra hx0
    obtain ⟨y, hxy, -⟩ := hdiv hx0
    have hnorm := congrArg D.norm hxy
    rw [h.norm_mul, hx, zero_mul, D.norm_one] at hnorm
    exact zero_ne_one hnorm
  · intro hani x hx
    have hn : D.norm x ≠ 0 := fun hnx ↦ hx (hani x hnx)
    refine ⟨(D.norm x)⁻¹ • D.conj x, ?_, ?_⟩
    · rw [mul_smul_comm, D.mul_conj_self, smul_smul, inv_mul_cancel₀ hn, one_smul]
    · rw [smul_mul_assoc, D.conj_mul_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

end IsMultiplicative

variable (k) in
/-- The base ring is a multiplicative conic algebra: `(xy)² = x² y²`. Together with
`QuadraticForm.isGPRNonsingular_rankOne` this makes `k` the rank-one composition algebra. -/
theorem isMultiplicative_baseRing : (baseRing k).IsMultiplicative := fun x y ↦ by
  simp only [baseRing_norm_apply]
  ring

end ConicAlgebra
