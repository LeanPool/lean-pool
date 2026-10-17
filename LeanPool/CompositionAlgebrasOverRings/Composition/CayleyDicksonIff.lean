/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Alternative
public import LeanPool.CompositionAlgebrasOverRings.Composition.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Composition.Tower
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonConverse

/-!
# When is a Cayley–Dickson double a composition algebra? (`GPR 19.14`)

**`GPR 19.14`.** Let `B` be a conic `k`-algebra and `μ ∈ k`. Then `Cay(B, μ)` is a composition
algebra if and only if `B` is a regular associative composition algebra and `μ` is invertible; in
that case `Cay(B, μ)` is a regular composition algebra.

## Relation to `Composition/CayleyDickson.lean`

That file proves the direction `⇐` without the regularity of the double:
`ConicAlgebra.IsComposition.cay` (for `B` a `Ring`). This file supplies the rest:

* the clause "in this case `Cay(B, μ)` is regular", `ConicAlgebra.isGPRRegular_cay_norm`: by
  `GPR (18.5)` the doubled norm is `n_B ⊥ (-μ) n_B`, and an orthogonal sum of regular forms is
  regular, as is a unit multiple of a regular form;
* the direction `⇒`, as five separate consequences of `(C.cay μ).IsComposition`;
* the equivalence itself, `ConicAlgebra.isComposition_cay_iff`, for `B` a `NonAssocRing`, so that
  associativity of `B` is part of the statement rather than of the instances.

## The converse

Suppose `Cay(B, μ)` is a composition algebra. `GPR` obtains the invertibility of `μ` and the
regularity of `B` fibre by fibre, over the residue fields and the localizations of `k`. Here both
are read off from the regularity of the double, which is the only step that passes through fields.

1. A composition algebra is alternative (`ConicAlgebra.IsComposition.isAlternative_general`, the
   project's form of `GPR 19.13`), so `B` is associative by `GPR 18.15(b)`
   (`ConicAlgebra.isAlternative_cay_iff_of_projective`).
2. The rank of `Cay(B, μ)` at every prime is twice that of `B`, hence never `1`. So the norm of the
   double is regular by `GPR 19.11`, in the pointwise form
   `ConicAlgebra.IsComposition.isGPRRegular_of_forall_rankAtStalk_ne_one`: the rank need not be
   constant, since the proof of `GPR 19.11` only looks at one field at a time.
3. A regular orthogonal sum has regular summands. So `n_B` and `(-μ) n_B` are regular.
4. The polar map of `(-μ) n_B` is onto the dual, and `B` has a linear form taking the value `1` at
   `1` (`GPR 16.7`, `ConicAlgebra.isUnimodular_one`). Its preimage `x` satisfies
   `-μ · n_B(x, 1) = 1`, so `μ` is a unit.
5. `B` is closed under the multiplication of the double, with `(u, 0)(u', 0) = (uu', 0)` and
   `n(u, 0) = n_B(u)`. So `n_B` permits composition
   (`ConicAlgebra.isMultiplicative_of_isMultiplicative_cay`), and it is non-singular because it is
   regular (`GN (C.8.1)`).

⚠ The Lean statement `(C.cay μ).IsComposition` needs the module `B × B` to be finitely generated
projective, and that instance is found from `B`. So `B` is assumed finitely generated projective
throughout, where `GPR` derives this from the corresponding property of `Cay(B, μ)`, of which `B`
is a direct summand. The two hypotheses are equivalent.

The facts about quadratic forms used in steps 3 and 4 — `QuadraticForm.isGPRRegular_prod_iff`,
`QuadraticForm.IsGPRRegular.smul_of_isUnit` and `QuadraticForm.isUnit_of_isGPRRegular_smul` — are
in `QuadraticForm/Regularity.lean`, and the pointwise form of `GPR 19.11` used in step 2 is in
`Composition/RankDichotomy.lean`.

## Main results

* `ConicAlgebra.isGPRRegular_cay_norm` : the norm of `Cay(B, μ)` is regular when `n_B` is and `μ` is
  a unit (the last clause of `GPR 19.14`).
* `ConicAlgebra.IsComposition.mul_assoc_of_cay`, `ConicAlgebra.IsComposition.isGPRRegular_of_cay`,
  `ConicAlgebra.IsComposition.isUnit_of_cay`, `ConicAlgebra.IsComposition.of_cay`,
  `ConicAlgebra.IsComposition.isGPRRegular_cay_norm_of_cay` : **`GPR 19.14`, `⇒`**.
* `ConicAlgebra.isComposition_cay_iff` : **`GPR 19.14`**.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.12, 16.7, 18.5,
  18.15, 19.11, 19.13, 19.14.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European J. Math. **11** (2025), art. 42,
  (C.8.1), C.8(f).
-/

@[expose] public section

universe u v w

namespace ConicAlgebra

/-! ### `GPR 19.14` -/

section CayleyDickson

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [SMulCommClass k B B] [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B]
  {C : ConicAlgebra k B} {μ : k}

omit [Module.Finite k B] [Module.Projective k B] in
/-- **The last clause of `GPR 19.14`: the double of a regular norm is regular.** If `n_B` is regular
and `μ` is a unit, then the norm `n_B ⊥ (-μ) n_B` of `Cay(B, μ)` (`GPR (18.5)`) is regular, being
an orthogonal sum of regular forms. Nothing is assumed about the multiplication of `B`, about the
module `B`, or about `2`. -/
theorem isGPRRegular_cay_norm (C : ConicAlgebra k B) (hμ : IsUnit μ)
    (hreg : C.norm.IsGPRRegular) : (C.cay μ).norm.IsGPRRegular :=
  hreg.prod (hreg.smul_of_isUnit hμ.neg)

/-- **`GPR 19.14`, `⇒`: the double is regular.** If `Cay(B, μ)` is a composition algebra then its
norm is regular. The rank of the double is twice that of `B` at every prime
(`ConicAlgebra.rankAtStalk_cay`), hence never `1`, so `GPR 19.11` applies. -/
theorem IsComposition.isGPRRegular_cay_norm_of_cay (h : (C.cay μ).IsComposition.{u, v, u}) :
    (C.cay μ).norm.IsGPRRegular :=
  h.isGPRRegular_of_forall_rankAtStalk_ne_one fun p ↦ by
    rw [rankAtStalk_cay]
    simp only [Pi.mul_apply, Pi.ofNat_apply]
    omega

/-- **`GPR 19.14`, `⇒`: `B` is associative.** A composition algebra is alternative
(`ConicAlgebra.IsComposition.isAlternative_general`), and the double of a finitely generated
projective conic algebra is alternative exactly when the algebra is associative (`GPR 18.15(b)`). -/
theorem IsComposition.mul_assoc_of_cay (h : (C.cay μ).IsComposition.{u, v, u}) (a b c : B) :
    a * b * c = a * (b * c) :=
  (isAlternative_cay_iff_of_projective C μ).mp h.isAlternative_general a b c

/-- **`GPR 19.14`, `⇒`: the norm of `B` is regular.** The norm of the double is the regular form
`n_B ⊥ (-μ) n_B` (`GPR (18.5)`), and the summands of a regular orthogonal sum are regular. -/
theorem IsComposition.isGPRRegular_of_cay (h : (C.cay μ).IsComposition.{u, v, u}) :
    C.norm.IsGPRRegular :=
  QuadraticForm.IsGPRRegular.of_prod_left (Q₂ := (-μ) • C.norm) h.isGPRRegular_cay_norm_of_cay

/-- **`GPR 19.14`, `⇒`: `μ` is a unit.** The form `(-μ) n_B` is a summand of the regular norm of
the double, so it is regular, and the unit of `B` is unimodular (`GPR 16.7`); hence `-μ` is a
unit. -/
theorem IsComposition.isUnit_of_cay (h : (C.cay μ).IsComposition.{u, v, u}) : IsUnit μ :=
  (IsUnit.neg_iff μ).mp <| QuadraticForm.isUnit_of_isGPRRegular_smul
    (QuadraticForm.IsGPRRegular.of_prod_right (Q₁ := C.norm) h.isGPRRegular_cay_norm_of_cay)
    C.isUnimodular_one

/-- **`GPR 19.14`, `⇒`: `B` is a composition algebra.** Its norm is regular, hence non-singular
(`GN (C.8.1)`), and it permits composition because `B` sits in the double as the elements
`(u, 0)`, on which the norm and the product are those of `B`. -/
theorem IsComposition.of_cay (h : (C.cay μ).IsComposition.{u, v, u}) :
    C.IsComposition.{u, v, w} where
  isGPRNonsingular := h.isGPRRegular_of_cay.isGPRNonsingular
  isMultiplicative := isMultiplicative_of_isMultiplicative_cay C μ h.isMultiplicative

/-- **`GPR 19.14`.** For a finitely generated projective conic algebra `B` and any `μ ∈ k`, the
double `Cay(B, μ)` is a composition algebra if and only if `B` is associative, `B` is a composition
algebra with regular norm, and `μ` is a unit. In that case the double is regular as well
(`ConicAlgebra.isGPRRegular_cay_norm`).

`B` is only a `NonAssocRing` here, so associativity is part of the statement. The direction `⇐` is
`ConicAlgebra.IsComposition.cay`, applied to the `Ring` structure that associativity provides. -/
theorem isComposition_cay_iff :
    (C.cay μ).IsComposition.{u, v, u} ↔
      (∀ a b c : B, a * b * c = a * (b * c)) ∧ C.IsComposition.{u, v, u} ∧
        C.norm.IsGPRRegular ∧ IsUnit μ := by
  refine ⟨fun h ↦ ⟨h.mul_assoc_of_cay, h.of_cay, h.isGPRRegular_of_cay, h.isUnit_of_cay⟩, ?_⟩
  rintro ⟨hassoc, hC, hreg, hμ⟩
  let : Ring B := { (inferInstance : NonAssocRing B) with mul_assoc := hassoc }
  let : Algebra k B := Algebra.ofModule
    (fun r (x y : B) ↦ by exact smul_mul_assoc r x y)
    (fun r (x y : B) ↦ by exact (smul_comm r x y).symm)
  exact IsComposition.cay C hμ hreg hC.isMultiplicative

end CayleyDickson

end ConicAlgebra
