/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import LeanPool.CompositionAlgebrasOverRings.Conic.Defs
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Defs

/-!
# Trace, conjugation, and the conic calculus

The trace and the conjugation of a conic algebra (`GPR 16.1`–`16.6`), and the identities they
satisfy. Everything here is derived from the two axioms of `ConicAlgebra`; no regularity, no
projectivity, and no assumption that `2` is invertible.

## Main definitions

* `ConicAlgebra.trace` : `t(x) = n(1, x)`, the un-halved polar form of the norm at the unit.
  Note `t(1) = 2`, not `1`.
* `ConicAlgebra.conj` : `x ↦ t(x) • 1 - x`, a `k`-linear involution.
* `ConicAlgebra.traceDefect` : `t(x)t(y) - n(x, y) - t(xy)`, the obstruction to conjugation being
  an anti-homomorphism.

## Main results

* `ConicAlgebra.conj_conj` : conjugation is an involution.
* `ConicAlgebra.add_conj` : `x + conj x = t(x) • 1`.
* `ConicAlgebra.mul_conj_self`, `ConicAlgebra.conj_mul_self` : `x (conj x) = (conj x) x = n(x) • 1`.
* `ConicAlgebra.trace_conj`, `ConicAlgebra.norm_conj` : trace and norm are conjugation-invariant.
* `ConicAlgebra.mul_add_mul` : the linearized degree-two identity
  `xy + yx = t(x) • y + t(y) • x - n(x, y) • 1`.
* `ConicAlgebra.conj_mul_conj` : `(conj y) (conj x) = conj (xy) + traceDefect x y • 1`, the sharp
  unconditional statement of how far conjugation is from being an anti-homomorphism.
* `ConicAlgebra.traceDefect_smul_eq_smul_one` : in an **alternative** conic algebra,
  `traceDefect x y • x` is a scalar multiple of `1`.
* `ConicAlgebra.traceDefect_eq_zero`, `ConicAlgebra.conj_mul` : over a **field**, conjugation of an
  alternative conic algebra is an anti-homomorphism, `conj (xy) = (conj y) (conj x)`.

## Implementation notes

Conjugation is **not** mathlib's `star`. `Star` is a typeclass on the type `A`, but the conjugation
of a conic algebra is a function of the norm, which is data attached to `C : ConicAlgebra k A` and
need not be unique; two conic structures on the same algebra have different conjugations. So `conj`
is a field-free definition taking `C` as an argument, and no `StarRing` instance is (or can be)
declared.

⚠ **Alternativity alone does not make conjugation an anti-homomorphism over a ring.** The
obstruction `traceDefect x y = t(x)t(y) - n(x, y) - t(xy)` vanishes identically over a field, but
not over an arbitrary commutative ring, even for **associative** `A`. This is not new: `GPR 16.10`
gives the exact criterion (conjugation is an involution iff the obstruction lies in `Ann(A)`), the
projectivity hypotheses in `GPR 16.14(b)` and `GPR 17.6` are there for this reason, and `GPR` says
so explicitly in `17.4` ("one might be tempted to conjecture that conic alternative algebras are
multiplicative. But, according to Exc. 17.8 below, this is not so"). Counterexample: let `k = ℤ/4`,
let `M = (ℤ/2)²` as a `k`-module with basis `m₁, m₂`, let `β : M × M → k` be the `k`-bilinear form
with `β(m₁, m₂) = 2` and `β = 0` on the other three pairs of basis vectors, and put
`A = k·1 ⊕ M` with

  `(a·1 + m)(b·1 + p) = (ab + β(m, p))·1 + (a p + b m)`.

Then `A` is associative — associativity of the `M`-component asks `β(m, p) q = β(p, q) m`, and both
sides lie in `2 · M = 0` — and `n(a·1 + m) = a² - β(m, m)` with `t(a·1 + m) = 2a` makes it a conic
algebra. But `traceDefect m₁ m₂ = β(m₂, m₁) - β(m₁, m₂) = -2 ≠ 0`, so
`conj (m₁ m₂) = 2·1 ≠ 0 = conj m₂ · conj m₁`. Here `A` is finitely generated but *not* projective;
projectivity of `A` (which every composition algebra has) is the hypothesis that rules such examples
out in general, via a localization argument — `GPR 16.14(b)`. It is a small variant of
`GPR Exc. 17.8`, due to McCrimmon; see `Conic/TraceDefectCounterexample.lean`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.1–16.6 (the
  conic calculus), 16.10 and 16.14 (when conjugation is an involution), 17.6 and Exc. 17.8 (the
  role of projectivity, and McCrimmon's counterexample without it).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section CommRing

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] (C : ConicAlgebra k A)

/-! ### Norm identities -/

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem norm_add (x y : A) :
    C.norm (x + y) = C.norm x + C.norm y + QuadraticMap.polar C.norm x y := by
  simp only [QuadraticMap.polar]; ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem norm_sub (x y : A) :
    C.norm (x - y) = C.norm x + C.norm y - QuadraticMap.polar C.norm x y := by
  rw [sub_eq_add_neg, C.norm_add x (-y), QuadraticMap.polar_neg_right, QuadraticMap.map_neg]
  ring

/-! ### The trace -/

/-- The **trace** of a conic algebra: `t(x) = n(1, x)`, the un-halved polar form of the norm,
evaluated at the unit (`GPR 16.2`).

⚠ `t(1) = 2`, not `1`: this is `QuadraticMap.polar`, not `QuadraticMap.associated`. -/
def trace : A →ₗ[k] k := C.norm.polarBilin 1

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem trace_apply (x : A) : C.trace x = QuadraticMap.polar C.norm 1 x := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem trace_one : C.trace (1 : A) = 2 := by
  rw [trace_apply, QuadraticMap.polar_self, C.norm_one]
  simp

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The degree-two identity, in terms of the trace: `x² = t(x) • x - n(x) • 1`. -/
theorem mul_self_eq (x : A) : x * x = C.trace x • x - C.norm x • (1 : A) := C.mul_self x

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The **linearized degree-two identity**: `xy + yx = t(x) • y + t(y) • x - n(x, y) • 1`.

This is the workhorse of the conic calculus, and holds in every conic algebra — no alternativity,
no regularity. It is obtained from the degree-two identity at `x + y` by subtracting the identities
at `x` and at `y`; only additivity is used, so it is valid in characteristic 2. -/
theorem mul_add_mul (x y : A) :
    x * y + y * x =
      C.trace x • y + C.trace y • x - QuadraticMap.polar C.norm x y • (1 : A) := by
  have hx := C.mul_self_eq x
  have hy := C.mul_self_eq y
  have hxy := C.mul_self_eq (x + y)
  rw [add_mul, mul_add, mul_add, map_add, C.norm_add] at hxy
  linear_combination (norm := module) hxy - hx - hy

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The linearized degree-two identity, solved for `y * x`. -/
theorem mul_comm_eq (x y : A) :
    y * x = C.trace x • y + C.trace y • x - QuadraticMap.polar C.norm x y • (1 : A) - x * y := by
  linear_combination (norm := module) C.mul_add_mul x y

/-! ### Conjugation -/

/-- The **conjugation** of a conic algebra: `conj x = t(x) • 1 - x` (`GPR 16.2`), as a `k`-linear
map.

It is not mathlib's `star`: the conjugation depends on the norm, which is data, so it cannot be a
typeclass on `A`. -/
def conj : A →ₗ[k] A := (LinearMap.toSpanSingleton k A 1).comp C.trace - LinearMap.id

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem conj_apply (x : A) : C.conj x = C.trace x • (1 : A) - x := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem add_conj (x : A) : x + C.conj x = C.trace x • (1 : A) := by
  rw [conj_apply]; abel

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem conj_one : C.conj (1 : A) = 1 := by
  rw [conj_apply, trace_one, two_smul]; abel

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem trace_conj (x : A) : C.trace (C.conj x) = C.trace x := by
  rw [conj_apply, map_sub, map_smul, trace_one, smul_eq_mul]; ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Conjugation is an involution (`GPR 16.2`). -/
@[simp] theorem conj_conj (x : A) : C.conj (C.conj x) = x := by
  rw [conj_apply (x := C.conj x), trace_conj, conj_apply]; abel

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem norm_conj (x : A) : C.norm (C.conj x) = C.norm x := by
  rw [conj_apply, C.norm_sub, QuadraticMap.map_smul, C.norm_one, QuadraticMap.polar_smul_left,
    ← trace_apply, smul_eq_mul, smul_eq_mul, mul_one]
  ring

omit [IsScalarTower k A A] in
/-- `x (conj x) = n(x) • 1` (`GPR 16.2`). -/
@[simp] theorem mul_conj_self (x : A) : x * C.conj x = C.norm x • (1 : A) := by
  rw [conj_apply, mul_sub, mul_smul_comm, mul_one, C.mul_self_eq]; abel

omit [SMulCommClass k A A] in
/-- `(conj x) x = n(x) • 1` (`GPR 16.2`). -/
@[simp] theorem conj_mul_self (x : A) : C.conj x * x = C.norm x • (1 : A) := by
  rw [conj_apply, sub_mul, smul_mul_assoc, one_mul, C.mul_self_eq]; abel

/-! ### The base ring

`ConicAlgebra.baseRing k` is `k` with norm `x ↦ x²`. Its trace is doubling and its conjugation is
the **identity** — the degenerate case that starts the Cayley–Dickson tower, and the reason the
first double is commutative (`ConicAlgebra.mul_comm_cay`). -/

section BaseRing

variable (k) in
@[simp] theorem baseRing_trace_apply (x : k) : (baseRing k).trace x = 2 * x := by
  rw [trace_apply, QuadraticMap.polar, baseRing_norm_apply, baseRing_norm_apply,
    baseRing_norm_apply]
  ring

variable (k) in
/-- The conjugation of the base ring is the identity: `conj x = t(x)·1 - x = 2x - x = x`. -/
@[simp] theorem baseRing_conj_apply (x : k) : (baseRing k).conj x = x := by
  rw [conj_apply, baseRing_trace_apply, smul_eq_mul, mul_one]
  ring

end BaseRing

/-! ### The obstruction to anti-multiplicativity of the conjugation -/

/-- The **trace defect** `t(x)t(y) - n(x, y) - t(xy)`: the obstruction to conjugation being an
anti-homomorphism, by `ConicAlgebra.conj_mul_conj`.

This name is ours, not `GPR`'s, but the quantity is: `traceDefect x y = n(x, conj y) - t(xy)`, the
negative of the obstruction `t(x, y) - n(x, conj y)` appearing in `GPR 16.5(11)` and `GPR 16.10`
(where `t(x, y)` denotes the *bilinear* trace `t(xy)`, and `n(x, conj y) = t(x)t(y) - n(x, y)` by
`GPR 16.5(10)`). Equivalently it is the difference of the two sides of the identity
`t(xy) = t(x)t(y) - n(x, y)`, which holds in every composition algebra but not in every conic
algebra. See the ⚠ in the module docstring for an associative conic algebra over `ℤ/4` with nonzero
trace defect. -/
def traceDefect (x y : A) : k :=
  C.trace x * C.trace y - QuadraticMap.polar C.norm x y - C.trace (x * y)

/-- **How far conjugation is from being an anti-homomorphism**, exactly, in any conic algebra
(`GPR 16.5(11)`): `(conj y) (conj x) = conj (xy) + traceDefect x y • 1`. -/
theorem conj_mul_conj (x y : A) :
    C.conj y * C.conj x = C.conj (x * y) + C.traceDefect x y • (1 : A) := by
  have hyx := C.mul_comm_eq x y
  simp only [conj_apply, traceDefect, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one]
  rw [hyx]
  module

/-- Conjugation is an anti-homomorphism exactly where the trace defect vanishes. Globally,
`GPR 16.10(a)`: conjugation is an involution iff `traceDefect x y ∈ Ann(A)` for all `x, y`, which
for the faithful `A` we care about means it vanishes. -/
theorem conj_mul_of_traceDefect_eq_zero {x y : A} (h : C.traceDefect x y = 0) :
    C.conj (x * y) = C.conj y * C.conj x := by
  rw [C.conj_mul_conj, h, zero_smul, add_zero]

/-- The conjugation of `C` is an **involution** (`GPR 16.9` ff.): an anti-automorphism of `A`.

Only anti-multiplicativity is asked for, because the rest is automatic: `conj` is `k`-linear by
construction, fixes `1` (`ConicAlgebra.conj_one`) and squares to the identity
(`ConicAlgebra.conj_conj`), all with no hypotheses. By `ConicAlgebra.conj_mul_conj` this condition
says exactly that the trace defect lies in `Ann(A)`, which is `GPR 16.10(a)`.

It holds for alternative `C` over a field (`ConicAlgebra.conj_mul`) and, more generally, whenever
`A` is finitely generated projective (`ConicAlgebra.conjIsInvolution_of_projective`), but not in
general — see `Conic/TraceDefectCounterexample.lean`. -/
def ConjIsInvolution : Prop := ∀ x y : A, C.conj (x * y) = C.conj y * C.conj x

theorem conjIsInvolution_of_traceDefect_eq_zero (h : ∀ x y : A, C.traceDefect x y = 0) :
    C.ConjIsInvolution := fun x y ↦ C.conj_mul_of_traceDefect_eq_zero (h x y)

variable (k) in
/-- The conjugation of the base ring is an involution, trivially: it is the identity
(`ConicAlgebra.baseRing_conj_apply`), and `k` is commutative. This is what starts the
Cayley–Dickson tower. -/
theorem conjIsInvolution_baseRing : (baseRing k).ConjIsInvolution := fun x y ↦ by
  rw [baseRing_conj_apply, baseRing_conj_apply, baseRing_conj_apply, mul_comm]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- Anti-multiplicativity, as a rewrite rule. `ConicAlgebra.ConjIsInvolution` is a `def`, so it
has to be unfolded before `simp` can use it. -/
theorem ConjIsInvolution.conj_mul (h : C.ConjIsInvolution) (x y : A) :
    C.conj (x * y) = C.conj y * C.conj x := h x y

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem traceDefect_self (x : A) : C.traceDefect x x = 0 := by
  rw [traceDefect, QuadraticMap.polar_self, C.mul_self_eq, map_sub, map_smul, map_smul, trace_one,
    smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem traceDefect_one_left (y : A) : C.traceDefect 1 y = 0 := by
  rw [traceDefect, trace_one, one_mul, ← trace_apply]
  ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem traceDefect_one_right (x : A) : C.traceDefect x 1 = 0 := by
  rw [traceDefect, trace_one, mul_one, QuadraticMap.polar_comm, ← trace_apply]
  ring

omit [SMulCommClass k A A] in
theorem traceDefect_smul_left (a : k) (x y : A) :
    C.traceDefect (a • x) y = a * C.traceDefect x y := by
  rw [traceDefect, traceDefect, map_smul, QuadraticMap.polar_smul_left, smul_mul_assoc a x y,
    map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The trace defect is alternating: `traceDefect x y + traceDefect y x = 0`. Consequently it
vanishes on the diagonal (`traceDefect_self`) and is antisymmetric. -/
theorem traceDefect_add_traceDefect_swap (x y : A) :
    C.traceDefect x y + C.traceDefect y x = 0 := by
  have h := congrArg C.trace (C.mul_add_mul x y)
  simp only [map_add, map_sub, map_smul, trace_one, smul_eq_mul] at h
  rw [traceDefect, traceDefect, QuadraticMap.polar_comm C.norm y x]
  linear_combination -h

end CommRing

/-! ### Alternative conic algebras

In an alternative conic algebra the trace defect is still not visibly zero, but it is *almost* so:
`traceDefect x y • x` is a scalar multiple of the unit. Over a field that forces it to vanish. -/

section Alternative

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A] (C : ConicAlgebra k A)

omit [SMulCommClass k A A] in
/-- Left alternativity plus the degree-two identity: `x(xy) = t(x) • xy - n(x) • y`. -/
theorem mul_mul_self_eq (x y : A) : x * (x * y) = C.trace x • (x * y) - C.norm x • y := by
  rw [IsAlternative.mul_mul_self_left, C.mul_self_eq, sub_mul, smul_mul_assoc, smul_mul_assoc,
    one_mul]

/-- Flexibility plus the degree-two identity, expanding `x(yx)`. -/
theorem mul_mul_comm_eq (x y : A) :
    x * (y * x) = (C.trace y * C.trace x - QuadraticMap.polar C.norm x y) • x
      - (C.trace y * C.norm x) • (1 : A) + C.norm x • y := by
  rw [C.mul_comm_eq x y, mul_sub, mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
    mul_one, C.mul_self_eq, C.mul_mul_self_eq]
  module

/-- **The trace defect is almost zero in an alternative conic algebra**: `traceDefect x y • x` is a
scalar multiple of `1`.

Over a field this forces `traceDefect x y = 0` (`traceDefect_eq_zero`): if the scalar were nonzero,
`x` would lie in `k · 1`, where the defect vanishes anyway. Over a general commutative ring it does
not — see the ⚠ in the module docstring. -/
theorem traceDefect_smul_eq_smul_one (x y : A) :
    C.traceDefect x y • x
      = (C.trace y * C.norm x - QuadraticMap.polar C.norm x (x * y)) • (1 : A) := by
  have h := C.mul_add_mul x (x * y)
  rw [IsAlternative.flexible, C.mul_mul_self_eq, C.mul_mul_comm_eq] at h
  rw [traceDefect]
  linear_combination (norm := module) h

end Alternative

/-! ### Alternative conic algebras over a field

Over a field, the conjugation of an alternative conic algebra is an anti-homomorphism. -/

section Field

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] [IsAlternative A] (C : ConicAlgebra K A)

/-- Over a **field**, the trace defect of an alternative conic algebra vanishes:
`t(xy) = t(x)t(y) - n(x, y)`.

⚠ The field hypothesis is doing real work; see the ⚠ in the module docstring for an associative
conic algebra over `ℤ/4` whose trace defect is nonzero. -/
theorem traceDefect_eq_zero (x y : A) : C.traceDefect x y = 0 := by
  by_cases hx : ∃ a : K, x = a • (1 : A)
  · obtain ⟨a, rfl⟩ := hx
    rw [C.traceDefect_smul_left, C.traceDefect_one_left, mul_zero]
  · by_contra h
    refine hx ⟨(C.traceDefect x y)⁻¹ *
      (C.trace y * C.norm x - QuadraticMap.polar C.norm x (x * y)), ?_⟩
    rw [mul_smul, ← C.traceDefect_smul_eq_smul_one x y, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The trace is "multiplicative up to the norm" over a field: `t(xy) = t(x)t(y) - n(x, y)`. -/
theorem trace_mul (x y : A) :
    C.trace (x * y) = C.trace x * C.trace y - QuadraticMap.polar C.norm x y := by
  have := C.traceDefect_eq_zero x y
  rw [traceDefect] at this
  linear_combination -this

/-- **Conjugation is an algebra anti-homomorphism** for an alternative conic algebra over a field:
`conj (xy) = conj y * conj x`. -/
theorem conj_mul (x y : A) : C.conj (x * y) = C.conj y * C.conj x :=
  C.conj_mul_of_traceDefect_eq_zero (C.traceDefect_eq_zero x y)

end Field

end ConicAlgebra
