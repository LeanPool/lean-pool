/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson

/-!
# Commutativity and associativity of the double (`GPR 18.14(a),(b)`)

`Cay(B, μ)` is associative **if and only if** `B` is commutative and associative with involutive
conjugation (`GPR 18.14(b)`), and commutative **if and only if** `B` is the base ring
(`GPR 18.14(a)`). This file proves the directions that build algebras, and packages them as `Ring`,
`CommRing` and `Algebra` structures on the double so that the Cayley–Dickson tower can be iterated.

The two results play different roles. Associativity of `Cay(B, μ)` is what
`ConicAlgebra.isMultiplicative_cay` and `ConicAlgebra.isAlternative_cay` need of *their* input, so
it is what carries the tower from one rung to the next. Commutativity is needed only once, to get
the tower started: `mul_assoc_cay` asks its input to be commutative, and the first double
`Cay(k, μ)` is the last rung for which that is true.

Iteration is the whole point. `ConicAlgebra.isMultiplicative_cay` (`GPR 18.15`) and
`ConicAlgebra.isAlternative_cay` (`GPR 18.14(c)`) both require their input `B` to be *associative*,
which for a double `Cay(B₀, μ₀)` is exactly what this file supplies. Without it the tower stops one
rung up from the base ring.

## The computation

Write `x = (a, b)`, `y = (c, d)`, `z = (e, f)`. Both components of `(xy)z` and of `x(yz)` expand
into four terms each, and they match term by term using only

* anti-multiplicativity of the conjugation of `B`, to push `conj` through the products it meets
  (`conj (fc) = (conj c) (conj f)`, `conj (d (conj e)) = e (conj d)`), and
* commutativity and associativity of `B`, to reorder the resulting monomials.

The conjugates `conj a, conj c, conj e, …` are never expanded via `conj z = t(z)·1 - z`; they behave
as atoms throughout. This is unlike `Conic/CayleyDicksonAlternative.lean`, where eliminating the
conjugation first is what makes the cancellations linear — here commutativity does that job instead,
and `ring` closes both components.

## Main results

* `ConicAlgebra.mul_assoc_cay` : **`GPR 18.14(b)`, `⇐`**.
* `ConicAlgebra.mul_comm_cay` : **`GPR 18.14(a)`, `⇐`**.
* `ConicAlgebra.exists_mul_ne_mul_cay`, `ConicAlgebra.exists_mul_mul_ne_mul_mul_cay` : explicit
  witnesses for the failure of commutativity and of associativity.
* `ConicAlgebra.Cay.ring`, `ConicAlgebra.Cay.algebra`, `ConicAlgebra.Cay.commRing` : the resulting
  structures.

## Implementation notes

`Cay.ring` and `Cay.algebra` are **`def`s, not instances**: associativity of the double depends on
hypotheses on `B` (`CommRing`, and involutivity of the conjugation) that instance search cannot
discharge, and a global instance would be unsound. Use them with `letI` at the point where the next
rung of the tower is built. `Cay.algebra` is `Algebra.ofModule`, which needs exactly the
`SMulCommClass`/`IsScalarTower` pair the double already carries.

⚠ The involutivity hypothesis does *not* follow from commutativity and associativity over an
arbitrary base — see the trace-defect counterexample over `ℤ/4` — but it does as soon as `B` is
finitely generated projective, or the base is a field.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.13,
  18.14(a),(b).
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {B : Type v} [CommRing k] [CommRing B] [Algebra k B]
  (C : ConicAlgebra k B) (μ : k)

/-- **`GPR 18.14(b)`, `⇐`.** If `B` is commutative associative and its conjugation is an
involution, then `Cay(B, μ)` is associative, for every scalar `μ`. -/
theorem mul_assoc_cay (hconj : C.ConjIsInvolution) (x y z : Cay C μ) :
    x * y * z = x * (y * z) := by
  have halg : ∀ r : k, C.conj (algebraMap k B r) = algebraMap k B r := fun r ↦ by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, conj_one]
  refine Cay.ext ?_ ?_ <;>
    simp only [Cay.fst_mul, Cay.snd_mul, map_add, hconj.conj_mul, conj_conj, mul_add, add_mul,
      Algebra.smul_def, halg] <;>
    ring

/-- The double of a commutative associative conic algebra with involutive conjugation, as a
`Ring`. A `def`, not an instance: see the module docstring. -/
@[instance_reducible] def Cay.ring (hconj : C.ConjIsInvolution) : Ring (Cay C μ) :=
  { (inferInstance : NonAssocRing (Cay C μ)) with
    mul_assoc := mul_assoc_cay C μ hconj }

/-- The double as a `k`-algebra, given the `Ring` structure of `ConicAlgebra.Cay.ring`. Built by
`Algebra.ofModule` from the `SMulCommClass`/`IsScalarTower` instances the double already has. -/
@[instance_reducible] def Cay.algebra (hconj : C.ConjIsInvolution) :
    letI := Cay.ring C μ hconj
    Algebra k (Cay C μ) :=
  letI := Cay.ring C μ hconj
  Algebra.ofModule (fun r x y ↦ by exact smul_mul_assoc r x y)
    (fun r x y ↦ by exact mul_smul_comm r x y)

/-! ### Failure of commutativity and associativity (`GPR 18.14(a),(b)`, `⇒`)

The contrapositives, in the explicit form the tower needs: a witness that `B`'s conjugation is not
the identity produces a witness that the double is not commutative, and a witness that `B` is not
commutative produces a witness that the double is not associative. These are what show the
Cayley–Dickson tower really does lose a property at each step rather than merely failing to
preserve it. -/

section Failure

variable {k' : Type u} {B' : Type v} [CommRing k'] [NonAssocRing B'] [Module k' B']
  [SMulCommClass k' B' B'] [IsScalarTower k' B' B'] (C' : ConicAlgebra k' B') (μ' : k')

omit [SMulCommClass k' B' B'] [IsScalarTower k' B' B'] in
/-- **`Cay(B, μ)` is not commutative** as soon as the conjugation of `B` moves some element:
`(u, 0)(0, 1) = (0, u)` while `(0, 1)(u, 0) = (0, conj u)`. -/
theorem exists_mul_ne_mul_cay {u : B'} (h : C'.conj u ≠ u) :
    ∃ x y : Cay C' μ', x * y ≠ y * x := by
  set x : Cay C' μ' := ((u, 0) : B' × B') with hx
  set y : Cay C' μ' := ((0, 1) : B' × B') with hy
  refine ⟨x, y, fun hcon ↦ h ?_⟩
  have h2 : (x * y).2 = (y * x).2 := by rw [hcon]
  have hx1 : x.1 = u := rfl
  have hx2 : x.2 = (0 : B') := rfl
  have hy1 : y.1 = (0 : B') := rfl
  have hy2 : y.2 = (1 : B') := rfl
  simp only [Cay.snd_mul, hx1, hx2, hy1, hy2, map_zero, mul_zero, add_zero, zero_add,
    one_mul] at h2
  exact h2.symm

omit [SMulCommClass k' B' B'] [IsScalarTower k' B' B'] in
/-- **`Cay(B, μ)` is not associative** as soon as `B` is not commutative. With `x = (0, 1)`,
`y = (conj a, 0)` and `z = (conj c, 0)`, the second components of `(xy)z` and `x(yz)` are `ac` and
`ca`. -/
theorem exists_mul_mul_ne_mul_mul_cay (hconj : C'.ConjIsInvolution) {a c : B'}
    (h : a * c ≠ c * a) : ∃ x y z : Cay C' μ', x * y * z ≠ x * (y * z) := by
  set x : Cay C' μ' := ((0, 1) : B' × B') with hx
  set y : Cay C' μ' := ((C'.conj a, 0) : B' × B') with hy
  set z : Cay C' μ' := ((C'.conj c, 0) : B' × B') with hz
  refine ⟨x, y, z, fun hcon ↦ h ?_⟩
  have h2 : (x * y * z).2 = (x * (y * z)).2 := by rw [hcon]
  have hx1 : x.1 = (0 : B') := rfl
  have hx2 : x.2 = (1 : B') := rfl
  have hy1 : y.1 = C'.conj a := rfl
  have hy2 : y.2 = (0 : B') := rfl
  have hz1 : z.1 = C'.conj c := rfl
  have hz2 : z.2 = (0 : B') := rfl
  simp only [Cay.snd_mul, Cay.fst_mul, hx1, hx2, hy1, hy2, hz1, hz2, map_zero, mul_zero,
    zero_mul, add_zero, zero_add, smul_zero, one_mul, mul_one, conj_conj,
    hconj.conj_mul] at h2
  exact h2

end Failure

/-! ### Commutativity (`GPR 18.14(a)`) -/

/-- If the conjugation of a commutative `B` is the **identity** then `Cay(B, μ)` is commutative.

Both products come out as `(ac + μ db, da + bc)`; only commutativity of `B` is used, since with
`conj = id` there is nothing left for the conjugation to do. The hypothesis holds for the base ring
(`ConicAlgebra.baseRing_conj_apply`) and essentially only there — `GPR 18.14(a)` says
`Cay(B, μ)` is commutative exactly when `B = k`. -/
theorem mul_comm_cay (hconj : ∀ u : B, C.conj u = u) (x y : Cay C μ) : x * y = y * x := by
  refine Cay.ext ?_ ?_ <;>
    simp only [Cay.fst_mul, Cay.snd_mul, hconj, Algebra.smul_def] <;> ring

/-- With the conjugation of `B` the identity, the conjugation is automatically an involution: the
condition `conj (xy) = conj y * conj x` reduces to `xy = yx`. -/
theorem conjIsInvolution_of_conj_eq_id (hconj : ∀ u : B, C.conj u = u) : C.ConjIsInvolution :=
  fun x y ↦ by rw [hconj, hconj, hconj, mul_comm]

/-- The double of a commutative conic algebra whose conjugation is the identity, as a `CommRing`.
This is the instance that gets the Cayley–Dickson tower off the ground: it makes `Cay(k, μ₁)`
commutative, which is what `ConicAlgebra.mul_assoc_cay` needs in order to make `Cay(Cay(k, μ₁), μ₂)`
associative. A `def`, not an instance — see the module docstring. -/
@[instance_reducible] def Cay.commRing (hconj : ∀ u : B, C.conj u = u) : CommRing (Cay C μ) :=
  { Cay.ring C μ (conjIsInvolution_of_conj_eq_id C hconj) with
    mul_comm := mul_comm_cay C μ hconj }

end ConicAlgebra
