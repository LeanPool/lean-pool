/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import LeanPool.CompositionAlgebrasOverRings.Conic.Kirmse
public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective

/-!
# Recognizing a conic algebra by a multiplicative norm (`GPR 19.3`)

`GPR 19.3` starts from a *pre-composition algebra* (`GPR 19.1`): a unital algebra `A` over a
commutative ring `k`, projective as a `k`-module, carrying a quadratic form `n` that is
non-degenerate in `GPR`'s sense (`QuadraticMap.radical n = ⊥`, i.e.
`QuadraticForm.IsGPRNondegenerate`) and permits composition, `n 1 = 1` and `n(xy) = n(x) n(y)`.
It concludes:

1. `A` is a conic algebra with norm `n`;
2. `A` is alternative;
3. `n` is the unique conic norm on `A`;
4. the polar radical `A⊥ = {x | n(x, y) = 0 for all y}` (`GPR`'s `C⊥`) is an ideal contained in
   the centre, and `2 A⊥ = n(x, y) A⊥ = 0` for all `x, y`.

This file proves all four. Throughout, `n(x, y)` is the **un-halved** polar form
`QuadraticMap.polar n x y` (overview §6(a)), and nothing is assumed about `2`.

## Relation to `Conic/Kirmse.lean`

`Conic/Kirmse.lean` proves the alternativity statement of `GPR 19.3`
(`ConicAlgebra.IsMultiplicative.isAlternative`) with the conic structure, i.e. the degree-two
identity `x² = t(x) x - n(x) 1`, as an *input*. Clause 1 removes that input:
`ConicAlgebra.ofMultiplicative` builds the conic structure from the bare form, and
`ConicAlgebra.isAlternative_ofMultiplicative` feeds it to the Kirmse theorem. Clause 2 thus
uses `GPR`'s argument in two halves, the degree-two identity here and Kirmse's identities there.

## Proof outline

*Clause 1* follows `GPR`. Linearizing `n(xy) = n(x) n(y)` gives `(19.1.3)`–`(19.1.5)` using
only distributivity (`QuadraticForm.polar_mul_mul_left_of_map_mul` and its companions in
`Conic/Multiplicative.lean`); with `t(y) := n(1, y)` they give `n(xy, x) = n(x) t(y)` `(19.3.1)` and
`t(x²) = t(x)² - 2 n(x)` `(19.3.2)`. Then `w := x² - t(x) x + n(x) 1` satisfies `n(w, y) = 0` for
all `y` and `n(w) = 0`, so `w` lies in the radical of `n`, which is zero.

*Clause 4*: the ideal property is norm-associativity (`GPR (16.12.3)`, `(16.12.4)`). On `A⊥` the
form `n` is additive, and its zeros there form the radical, so `n` is injective on `A⊥`; this
gives centrality (`(xy)z` and `x(yz)` lie in `A⊥` and have the same norm) and `2 A⊥ = 0` exactly
as in `GPR`. For `n(x, y) A⊥ = 0` the proof departs from `GPR`, which uses that conjugation fixes
`A⊥` together with `GPR (16.12.5)`. Here `(19.1.4)` gives `n(x, y) n(z) = n(xz, yz) = 0` for
`z ∈ A⊥`, since `xz ∈ A⊥`. Hence `n(n(x, y) z) = n(x, y)² n(z) = 0`, and `n(x, y) z ∈ A⊥`, so it
lies in the radical.

## Main definitions

* `ConicAlgebra.ofMultiplicative` : the conic algebra with norm `n`, from `n 1 = 1`,
  `n(xy) = n(x) n(y)` and `n.IsGPRNondegenerate` (`GPR 19.3`, first assertion).
* `ConicAlgebra.IsMultiplicative.polarRadical` : the polar radical `A⊥` of a multiplicative conic
  algebra, as a two-sided ideal.

## Main results

* `QuadraticForm.mul_self_sub_polar_smul_add_smul_mem_radical_of_map_mul`,
  `QuadraticForm.mul_self_eq_of_map_mul` : the degree-two identity, up to the radical and exactly.
* `ConicAlgebra.isMultiplicative_ofMultiplicative`, `ConicAlgebra.isAlternative_ofMultiplicative` :
  the constructed conic algebra is multiplicative and alternative (`GPR 19.3`).
* `ConicAlgebra.eq_ofMultiplicative` : on a finitely generated projective algebra, every conic
  structure is the constructed one; in particular its norm is `n` (`GPR 19.3`, via `GPR 16.16`).
* `ConicAlgebra.IsMultiplicative.mul_mem_ker_polarBilin_left`,
  `ConicAlgebra.IsMultiplicative.mul_mem_ker_polarBilin_right` : `A⊥` is an ideal.
* `QuadraticMap.injOn_ker_polarBilin` (in `QuadraticForm/Regularity.lean`) : a form with
  vanishing radical is injective on `A⊥`.
* `ConicAlgebra.IsMultiplicative.mem_center_of_mem_ker_polarBilin` : `A⊥` is central.
* `QuadraticMap.two_smul_eq_zero_of_mem_ker_polarBilin` (in `QuadraticForm/Regularity.lean`) :
  `2 A⊥ = 0`.
* `ConicAlgebra.IsMultiplicative.polar_smul_eq_zero_of_mem_ker_polarBilin` : `n(x, y) A⊥ = 0`.

## Implementation notes

**Hypotheses.** `GPR` assumes `A` projective throughout. Clauses 1, 2 and 4 need no hypothesis
on the module, and are stated without one (overview §2). Clause 4 is stated for an arbitrary
multiplicative conic algebra `C`, with `C.norm.IsGPRNondegenerate` only where it is consumed; the
ideal property needs no regularity at all. It applies to `ConicAlgebra.ofMultiplicative n …`,
whose norm is `n` by definition.

⚠ **Clause 3 assumes finite generation, which `GPR` does not.** `GPR 16.16` asks only that the
algebra be projective; the project's `ConicAlgebra.norm_eq_of_projective`, which is used here,
also assumes `Module.Finite`.

⚠ **`A⊥` is the kernel of the polar form, not the radical of `n`.** `GPR` writes `Rad(Dn)` for the
former and `Rad(n)` for the latter; they are `LinearMap.ker (QuadraticMap.polarBilin n)` and
`QuadraticMap.radical n` in mathlib. The radical is zero by hypothesis, but `A⊥` need not be:
`x ↦ x²` on `𝔽₂` has zero polar form. When `2 ∈ kˣ` the two agree
(`QuadraticMap.radical_eq_ker_polarBilin`), so clause 4 has content only when `2` is not a unit.

The linearizations of multiplicativity are needed for a bare quadratic form, because the conic
structure is not yet available; `Conic/Multiplicative.lean` proves them in that form and derives
the conic versions from them. The facts about the kernel of the polar form use no algebra
structure and live in `QuadraticForm/Regularity.lean`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.4, 16.12, 16.16,
  19.1, 19.3.
-/

@[expose] public section

universe u v

open QuadraticMap

/-! ### The degree-two identity from a multiplicative form -/

namespace QuadraticForm

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  {Q : QuadraticForm k A}

/-- `GPR (19.3.1)`: `n(xy, x) = n(x) t(y)` with `t(y) = n(1, y)`; `(19.1.3)` at `z = 1`. -/
private theorem polar_mul_self_of_map_mul (hmul : ∀ x y : A, Q (x * y) = Q x * Q y) (x y : A) :
    polar Q (x * y) x = Q x * polar Q 1 y := by
  have h := polar_mul_mul_left_of_map_mul hmul x y 1
  rwa [mul_one, polar_comm Q y 1] at h

/-- `GPR (19.3.2)`: `t(x²) = t(x)² - 2 n(x)`; `(19.1.5)` at `y = x`, `w = z = 1` (in `GPR`'s
variables). -/
private theorem polar_mul_self_one_of_map_mul (hmul : ∀ x y : A, Q (x * y) = Q x * Q y)
    (x : A) : polar Q (x * x) 1 = polar Q 1 x ^ 2 - 2 * Q x := by
  have h := polar_mul_add_polar_mul_of_map_mul hmul x 1 x 1
  rw [mul_one, mul_one, one_mul, polar_self, polar_comm Q x 1, nsmul_eq_mul] at h
  push_cast at h
  linear_combination h

/-- **The degree-two defect lies in the radical** (`GPR 19.3`, proof): if `Q` permits
composition and `Q 1 = 1`, then `w = x² - t(x) x + Q(x) 1`, with `t(x) = n(1, x)`, satisfies
`n(w, y) = 0` for all `y` and `Q w = 0`. The first is `(19.1.5)` at `z = x`, `w = 1` (in `GPR`'s
variables), combined with `(19.3.1)`; the second expands `Q w` into six terms, which cancel by
`(19.3.1)` at `y = x` and `(19.3.2)`. No regularity, no hypothesis on `2`, and none on the
module. -/
theorem mul_self_sub_polar_smul_add_smul_mem_radical_of_map_mul (hone : Q 1 = 1)
    (hmul : ∀ x y : A, Q (x * y) = Q x * Q y) (x : A) :
    x * x - polar Q 1 x • x + Q x • (1 : A) ∈ Q.radical := by
  have hsub (a b : A) : Q (a - b) = Q a + Q b - polar Q a b := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, polar_neg_right, QuadraticMap.map_neg]
    ring
  refine ⟨?_, LinearMap.ext fun y ↦ ?_⟩
  · rw [QuadraticMap.map_add Q, hsub]
    simp only [hmul, QuadraticMap.map_smul, hone, polar_sub_left, polar_smul_left,
      polar_smul_right, polar_mul_self_of_map_mul hmul, polar_mul_self_one_of_map_mul hmul,
      polar_comm Q x 1, smul_eq_mul]
    ring
  · have h := polar_mul_add_polar_mul_of_map_mul hmul x 1 y x
    rw [one_mul, one_mul, polar_mul_self_of_map_mul hmul, polar_comm Q x 1,
      polar_comm Q y x] at h
    rw [polarBilin_apply_apply, LinearMap.zero_apply, polar_add_left, polar_sub_left,
      polar_smul_left, polar_smul_left, smul_eq_mul, smul_eq_mul]
    linear_combination h

/-- **The degree-two identity from a multiplicative norm** (`GPR 19.3`): if `Q 1 = 1`,
`Q (xy) = Q x * Q y`, and `Q` is non-degenerate in `GPR`'s sense (`Q.radical = ⊥`), then
`x² = t(x) x - Q(x) 1` with `t(x) = n(1, x)`. This is the axiom `ConicAlgebra.mul_self`. -/
theorem mul_self_eq_of_map_mul (hone : Q 1 = 1) (hmul : ∀ x y : A, Q (x * y) = Q x * Q y)
    (hrad : Q.IsGPRNondegenerate) (x : A) :
    x * x = polar Q 1 x • x - Q x • (1 : A) := by
  have hw := mul_self_sub_polar_smul_add_smul_mem_radical_of_map_mul hone hmul x
  rw [show Q.radical = ⊥ from hrad, Submodule.mem_bot] at hw
  rw [← sub_eq_zero, ← hw]
  abel

end QuadraticForm

/-! ### The conic structure -/

namespace ConicAlgebra

section OfMultiplicative

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]

/-- **`GPR 19.3`, first assertion: a quadratic form permitting composition makes the algebra
conic.** Given a quadratic form `n` with `n 1 = 1` and `n(xy) = n(x) n(y)` whose radical vanishes
(`GPR`'s non-degeneracy, `QuadraticForm.IsGPRNondegenerate`), this is the conic algebra with norm
`n`; the degree-two identity is `QuadraticForm.mul_self_eq_of_map_mul`.

`GPR` assumes the algebra projective (a pre-composition algebra, `GPR 19.1`); the construction
does not need it. -/
def ofMultiplicative (n : QuadraticForm k A) (hone : n 1 = 1)
    (hmul : ∀ x y : A, n (x * y) = n x * n y) (hrad : n.IsGPRNondegenerate) :
    ConicAlgebra k A where
  norm := n
  norm_one := hone
  mul_self := QuadraticForm.mul_self_eq_of_map_mul hone hmul hrad

variable (n : QuadraticForm k A) (hone : n 1 = 1) (hmul : ∀ x y : A, n (x * y) = n x * n y)
  (hrad : n.IsGPRNondegenerate)

@[simp] theorem ofMultiplicative_norm : (ofMultiplicative n hone hmul hrad).norm = n := rfl

/-- The conic algebra `ConicAlgebra.ofMultiplicative n …` is multiplicative: its norm is `n`. -/
theorem isMultiplicative_ofMultiplicative :
    (ofMultiplicative n hone hmul hrad).IsMultiplicative :=
  hmul

include hone hmul hrad in
/-- **`GPR 19.3`, alternativity: an algebra with a non-degenerate quadratic form permitting
composition is alternative.** Here non-degenerate is `GPR`'s sense, `n.radical = ⊥`. The conic
structure is `ConicAlgebra.ofMultiplicative`, and alternativity is then Kirmse's theorem
`ConicAlgebra.IsMultiplicative.isAlternative`. No hypothesis on the module and none on `2`. -/
theorem isAlternative_ofMultiplicative [SMulCommClass k A A] [IsScalarTower k A A] :
    IsAlternative A :=
  (isMultiplicative_ofMultiplicative n hone hmul hrad).isAlternative hrad

/-- **`GPR 19.3`, uniqueness of the norm.** On a finitely generated projective algebra, every
conic structure `D` is `ConicAlgebra.ofMultiplicative n …`; in particular `D.norm = n`, and `n` is
the only non-degenerate quadratic form permitting composition. This is `GPR 16.16`
(`ConicAlgebra.norm_eq_of_projective`).

⚠ `GPR 16.16` assumes only projectivity; `ConicAlgebra.norm_eq_of_projective` also assumes finite
generation, and so does this theorem. -/
theorem eq_ofMultiplicative [Module.Finite k A] [Module.Projective k A] (D : ConicAlgebra k A) :
    D = ofMultiplicative n hone hmul hrad :=
  ConicAlgebra.ext (norm_eq_of_projective D _)

end OfMultiplicative

/-! ### The polar radical of a multiplicative conic algebra -/

namespace IsMultiplicative

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] {C : ConicAlgebra k A}

omit [SMulCommClass k A A] in
/-- **The polar radical is a left ideal** (`GPR 19.3`): if `n(z, ·) = 0` then `n(xz, ·) = 0`, by
norm-associativity `n(xz, y) = n(z, (conj x) y)` (`GPR (16.12.4)`). No regularity is needed. -/
theorem mul_mem_ker_polarBilin_left (h : C.IsMultiplicative) (x : A) {z : A}
    (hz : z ∈ LinearMap.ker C.norm.polarBilin) : x * z ∈ LinearMap.ker C.norm.polarBilin :=
  mem_ker_polarBilin_iff.mpr fun y ↦ by
    rw [h.polar_mul_left, mem_ker_polarBilin_iff.mp hz]

omit [IsScalarTower k A A] in
/-- **The polar radical is a right ideal** (`GPR 19.3`): if `n(z, ·) = 0` then `n(zx, ·) = 0`, by
norm-associativity `n(zx, y) = n(z, y (conj x))` (`GPR (16.12.3)`). No regularity is needed. -/
theorem mul_mem_ker_polarBilin_right (h : C.IsMultiplicative) {z : A}
    (hz : z ∈ LinearMap.ker C.norm.polarBilin) (x : A) : z * x ∈ LinearMap.ker C.norm.polarBilin :=
  mem_ker_polarBilin_iff.mpr fun y ↦ by
    rw [h.polar_mul_right, mem_ker_polarBilin_iff.mp hz]

/-- The **polar radical** `C⊥ = Rad(D n_C) = {x | n(x, y) = 0 for all y}` of a multiplicative
conic algebra, as a two-sided ideal (`GPR 19.3`). Its carrier is the kernel of the polar form
`LinearMap.ker C.norm.polarBilin`, which is also a `k`-submodule. ⚠ It is not the radical
`QuadraticMap.radical C.norm` of the norm; see the module docstring. -/
def polarRadical (h : C.IsMultiplicative) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (LinearMap.ker C.norm.polarBilin) (zero_mem _) add_mem neg_mem
    (fun hy ↦ h.mul_mem_ker_polarBilin_left _ hy) (fun hx ↦ h.mul_mem_ker_polarBilin_right hx _)

@[simp] theorem mem_polarRadical (h : C.IsMultiplicative) {z : A} :
    z ∈ h.polarRadical ↔ z ∈ LinearMap.ker C.norm.polarBilin :=
  TwoSidedIdeal.mem_mk' ..

/-- **The polar radical is central** (`GPR 19.3`): for a multiplicative conic algebra whose norm
has vanishing radical, every `z` with `n(z, ·) = 0` lies in the centre `Set.center A` (`GPR 8.4`:
it commutes with everything and associates in every position). The elements `(xy)z` and `x(yz)`
lie in the polar radical and have the same norm `n(x) n(y) n(z)`, so they are equal because the
norm is injective there (`QuadraticMap.injOn_ker_polarBilin`); likewise for the other positions
and for `xz = zx`. -/
theorem mem_center_of_mem_ker_polarBilin (h : C.IsMultiplicative)
    (hrad : C.norm.IsGPRNondegenerate) {z : A} (hz : z ∈ LinearMap.ker C.norm.polarBilin) :
    z ∈ Set.center A := by
  have hinj := injOn_ker_polarBilin (show C.norm.radical = ⊥ from hrad)
  rw [Set.mem_center_iff]
  refine ⟨fun a ↦ ?_, fun b c ↦ ?_, fun a b ↦ ?_⟩
  · exact hinj (h.mul_mem_ker_polarBilin_right hz a) (h.mul_mem_ker_polarBilin_left a hz)
      (by rw [h.norm_mul, h.norm_mul, mul_comm])
  · exact hinj (h.mul_mem_ker_polarBilin_right hz _)
      (h.mul_mem_ker_polarBilin_right (h.mul_mem_ker_polarBilin_right hz b) c)
      (by simp only [h.norm_mul]; ring)
  · exact hinj (h.mul_mem_ker_polarBilin_left _ hz)
      (h.mul_mem_ker_polarBilin_left a (h.mul_mem_ker_polarBilin_left b hz))
      (by simp only [h.norm_mul]; ring)

omit [SMulCommClass k A A] in
/-- **The polar form kills the polar radical** (`GPR 19.3`: `n(x, y) C⊥ = 0`). For `z` with
`n(z, ·) = 0`, `GPR (19.1.4)` gives `n(x, y) n(z) = n(xz, yz) = 0`, since `xz` is again in the
polar radical. So `n(n(x, y) z) = n(x, y)² n(z) = 0`, and `n(x, y) z` lies in the radical of the
norm, which vanishes. The argument differs from `GPR`'s, which goes through `GPR (16.12.5)` and
the fact that conjugation fixes the polar radical. -/
theorem polar_smul_eq_zero_of_mem_ker_polarBilin (h : C.IsMultiplicative)
    (hrad : C.norm.IsGPRNondegenerate) (x y : A) {z : A}
    (hz : z ∈ LinearMap.ker C.norm.polarBilin) : polar C.norm x y • z = 0 := by
  have h0 : polar C.norm x y * C.norm z = 0 := by
    rw [← h.polar_mul_mul_right x y z]
    exact mem_ker_polarBilin_iff.mp (h.mul_mem_ker_polarBilin_left x hz) (y * z)
  have hmem : polar C.norm x y • z ∈ C.norm.radical :=
    ⟨by rw [QuadraticMap.map_smul, smul_eq_mul, mul_assoc, h0, mul_zero],
      LinearMap.mem_ker.mp (Submodule.smul_mem _ _ hz)⟩
  rwa [show C.norm.radical = ⊥ from hrad, Submodule.mem_bot] at hmem

end IsMultiplicative

end ConicAlgebra
