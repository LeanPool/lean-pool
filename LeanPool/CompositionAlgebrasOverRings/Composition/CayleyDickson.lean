/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Defs
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonMultiplicative

/-!
# Doubling a composition algebra (`GPR 19.14`, one direction)

If `B` is an **associative** composition algebra whose norm is **regular**, and `μ ∈ kˣ`, then
`Cay(B, μ)` is again a composition algebra. This is the engine of the tower: it produces the
quaternion algebras from the quadratic étale algebras and the octonion algebras from the quaternion
algebras, and — because octonion algebras are not associative — it stops there.

This is the direction `⇐` of `GPR 19.14`, which is an equivalence: conversely, if `Cay(B, μ)` is
a composition algebra then `B` is a regular associative composition algebra and `μ` is a unit, and
in that case the double is regular. The converse, the regularity of the double, and the
equivalence itself (`ConicAlgebra.isComposition_cay_iff`) are in
`Composition/CayleyDicksonIff.lean`.

Each of the three clauses of `ConicAlgebra.IsComposition` is supplied by an earlier file:

* the module is finitely generated projective because `B × B` is (instances in
  `Conic/CayleyDickson.lean`);
* the norm `n_B ⊥ ⟨-μ⟩ n_B` is non-singular by `GN (C.8.3)`
  (`QuadraticForm.IsGPRRegular.prod_isGPRNonsingular`), together with the fact that rescaling by a
  unit preserves non-singularity (`QuadraticForm.IsGPRNonsingular.smul_of_isUnit`);
* the norm is multiplicative by `GPR Exc. 18.18` (`ConicAlgebra.isMultiplicative_cay`), which is
  where
  associativity of `B` is spent.

## Why the hypotheses are what they are

**`μ` must be a unit** — `Cay(B, 0)` has `(0, v)` in the radical of its norm for every `v`, so
non-singularity fails at once. The construction itself still takes an arbitrary `μ`
(overview §6(d)); the unit hypothesis lives here, on the theorem.

**The norm of `B` must be regular, not merely non-singular.** This is the asymmetry of
`GN (C.8.3)`, and it is not an artefact: over a field of characteristic 2 the rank-one form `⟨1⟩`
is non-singular but `⟨1⟩ ⊥ ⟨-1⟩ = ⟨1⟩ ⊥ ⟨1⟩` sends `(a, b)` to `(a + b) ^ 2` and so has a nonzero
radical. Concretely, `Cay(k, μ)` in characteristic 2 is the inseparable algebra `k[x]/(x² - μ)`,
which is *not* a composition algebra — which is exactly why `GPR 19.16(b)` starts the doubling
tower at a **regular rank-2** subalgebra rather than at `k`, and why `GPR 19.4` is a conic algebra
and not a composition algebra. The regularity hypothesis here is the same phenomenon seen from the
constructive side.

**`B` must be associative**, for multiplicativity (`GPR Exc. 18.18`). Nothing is assumed about the
conjugation of `B`, and nothing about `2`.

## Main results

* `ConicAlgebra.IsComposition.cay` : `Cay(B, μ)` is a composition algebra.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 18.18, 19.14.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European J. Math. **11** (2025), art. 42,
  (C.8.3).
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

variable {k : Type u} {B : Type v} [CommRing k] [Ring B] [Algebra k B] [Module.Finite k B]
  [Module.Projective k B] {C : ConicAlgebra k B}

omit [Module.Finite k B] [Module.Projective k B] in
/-- The Cayley–Dickson norm is the orthogonal sum `n_B ⊥ ⟨-μ⟩ n_B`, spelled with mathlib's
`QuadraticMap.prod`. This is `ConicAlgebra.cayNorm` unfolded across the type synonym, and is what
lets `GN (C.8.3)` be applied to it. -/
theorem cay_norm_eq_prod (C : ConicAlgebra k B) (μ : k) :
    (C.cay μ).norm = QuadraticMap.prod C.norm ((-μ) • C.norm) := rfl

/-- **Non-singularity of the doubled norm.** For `n_B` regular and `μ` a unit, `n_B ⊥ ⟨-μ⟩ n_B` is
non-singular.

`GN (C.8.3)` needs the *first* summand regular and the second only non-singular; `n_B` regular
gives both, the second via `GN (C.8.1)` and `QuadraticForm.IsGPRNonsingular.smul_of_isUnit`. -/
theorem isGPRNonsingular_cay_norm (C : ConicAlgebra k B) {μ : k} (hμ : IsUnit μ)
    (hreg : C.norm.IsGPRRegular) :
    QuadraticForm.IsGPRNonsingular.{u, v, w} (C.cay μ).norm :=
  hreg.prod_isGPRNonsingular (hreg.isGPRNonsingular.smul_of_isUnit hμ.neg)

/-- **`Cay(B, μ)` is a composition algebra**, for `B` an associative conic algebra with regular
multiplicative norm and `μ` a unit.

Note that `B` is *not* required to be a composition algebra on the nose: what is used is that its
norm is regular (which implies non-singular, `GN (C.8.1)`) and multiplicative. Over a base in which
`2` is invertible the two hypotheses coincide with `C.IsComposition` by
`QuadraticForm.isGPRRegular_iff_isGPRNonsingular`; in characteristic 2 regularity is genuinely
stronger, and genuinely needed — see the module docstring. -/
theorem IsComposition.cay (C : ConicAlgebra k B) {μ : k} (hμ : IsUnit μ)
    (hreg : C.norm.IsGPRRegular) (hmul : C.IsMultiplicative) :
    (C.cay μ).IsComposition.{u, v, w} where
  isGPRNonsingular := isGPRNonsingular_cay_norm C hμ hreg
  isMultiplicative := isMultiplicative_cay C μ hmul

/-- **The doubling theorem in the form the tower uses**, when `2` is invertible: an *associative
composition algebra* doubles to a composition algebra at any unit scalar.

Here the regularity hypothesis of `ConicAlgebra.IsComposition.cay` is discharged from
non-singularity by `GN (C.8.2)`, so the input is literally `C.IsComposition`. This is the step
`ℂ = Cay(ℝ, -1)`, `ℍ = Cay(ℂ, -1)`, `𝕆 = Cay(ℍ, -1)` — and it fails to apply once more only
because `𝕆` is not associative. -/
theorem IsComposition.cay_of_invertible_two [Invertible (2 : k)] (C : ConicAlgebra k B) {μ : k}
    (hμ : IsUnit μ) (h : C.IsComposition.{u, v, u}) : (C.cay μ).IsComposition.{u, v, w} :=
  IsComposition.cay C hμ h.isGPRRegular h.isMultiplicative

end ConicAlgebra
