/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Peirce
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.TwistedMatrix

/-!
# The norm of a reduced composition algebra is hyperbolic (`GPR 22.9(iv)`)

At an elementary idempotent `c`, the Peirce decomposition writes an element as

  `a₁ c + x₁₂ + x₂₁ + a₂ (conj c)`

and `GPR Exc. 19.35(3)` gives its norm as `a₁a₂ + n(x₁₂, x₂₁)`. When the norm is regular, the
polar pairing identifies `C₁₂` with `C₂₁*`. Consequently the whole norm is the hyperbolic form
`QuadraticForm.dualProd k (k × C₂₁)` of `k ⊕ C₂₁`. This file packages that coordinate calculation
as an isometry equivalence and completes clause (iv) of `GPR 22.9`.

## Main definitions

* `ConicAlgebra.IsElementaryIdempotent.peirceHyperbolicEquiv` : the Peirce-coordinate linear
  equivalence from the hyperbolic module on `k ⊕ C₂₁` to the algebra.
* `ConicAlgebra.IsElementaryIdempotent.peirceHyperbolicIsometryEquiv` : the same map as an
  isometry of quadratic forms.

## Main results

* `ConicAlgebra.IsElementaryIdempotent.norm_peirceHyperbolicEquiv` : the coordinate map carries
  the norm to the hyperbolic form.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 19.35, 22.9.
-/

@[expose] public section

universe u v

namespace ConicAlgebra.IsElementaryIdempotent

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  {C : ConicAlgebra k A} {c : A}

/-- The lower-left Peirce component used as one half of the hyperbolic presentation. -/
abbrev HyperbolicModule (c : A) :=
  IsAlternative.peirceComponent (R := k) c true false

/-- The Peirce-coordinate map from the hyperbolic module on `k ⊕ C₂₁` to the algebra.
The first hyperbolic coordinate is a functional on `k ⊕ C₂₁`; `dualProdEquiv` separates it
into its scalar and `C₂₁*` parts, and off-diagonal duality turns the latter into the `C₁₂`
coordinate. -/
noncomputable def peirceHyperbolicTo (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    (Module.Dual k (k × HyperbolicModule (k := k) c) ×
      (k × HyperbolicModule (k := k) c)) →ₗ[k] A := by
  let e := hc.offDiagonalDuality hmul hreg
  let d := dualProdEquiv k (HyperbolicModule (k := k) c)
  exact
    { toFun := fun x ↦
        peirceElement c x.2.1 (d.symm x.1).1 (e.symm (-(d.symm x.1).2)) x.2.2
      map_add' := fun x y ↦ by
        simp only [map_add, Prod.fst_add, Prod.snd_add, map_neg, neg_add_rev,
          peirceElement, add_smul, Submodule.coe_add]
        module
      map_smul' := fun a x ↦ by
        change peirceElement c (a * x.2.1) (d.symm (a • x.1)).1
          (e.symm (-(d.symm (a • x.1)).2)) (a • x.2.2) =
            a • peirceElement c x.2.1 (d.symm x.1).1 (e.symm (-(d.symm x.1).2)) x.2.2
        rw [map_smul]
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [show -(a • (d.symm x.1).2) = a • (-(d.symm x.1).2) by module, map_smul]
        simp only [peirceElement, mul_smul, Submodule.coe_smul, smul_add]
        module }

@[simp] theorem peirceHyperbolicTo_apply (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : Module.Dual k (k × HyperbolicModule (k := k) c) ×
      (k × HyperbolicModule (k := k) c)) :
    peirceHyperbolicTo hc hmul hreg x =
      peirceElement c x.2.1
        ((dualProdEquiv k (HyperbolicModule (k := k) c)).symm x.1).1
        ((hc.offDiagonalDuality hmul hreg).symm
          (-((dualProdEquiv k (HyperbolicModule (k := k) c)).symm x.1).2)) x.2.2 :=
  rfl

/-- The Peirce-coordinate map from the hyperbolic module is bijective. -/
theorem bijective_peirceHyperbolicTo (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    Function.Bijective (peirceHyperbolicTo hc hmul hreg) := by
  let e := hc.offDiagonalDuality hmul hreg
  let d := dualProdEquiv k (HyperbolicModule (k := k) c)
  constructor
  · intro x y hxy
    have hproj (i j : Bool) := congrArg
      (IsAlternative.peirceProjection (R := k) c i j) hxy
    apply Prod.ext
    · apply d.symm.injective
      apply Prod.ext
      · have h := congrArg C.trace (hproj true true)
        rw [peirceHyperbolicTo_apply, peirceHyperbolicTo_apply,
          hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
        simp only [Prod.mk.injEq, Bool.true_eq_false, and_self, false_and, and_false,
          ite_false] at h
        have ht : C.trace (IsAlternative.peirceIdempotent c true) = 1 :=
          (hc.peirceIdempotent true).trace_eq_one
        simpa only [map_smul, ht, smul_eq_mul, mul_one] using h
      · apply neg_injective
        apply e.symm.injective
        have h := hproj false true
        rw [peirceHyperbolicTo_apply, peirceHyperbolicTo_apply,
          hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
        simpa using h
    · apply Prod.ext
      · have h := congrArg C.trace (hproj false false)
        rw [peirceHyperbolicTo_apply, peirceHyperbolicTo_apply,
          hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
        simpa [hc.trace_eq_one] using h
      · have h := hproj true false
        rw [peirceHyperbolicTo_apply, peirceHyperbolicTo_apply,
          hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
        simpa using h
  · intro a
    obtain ⟨a₁, a₂, x₁₂, x₂₁, ha⟩ := hc.exists_eq_peirceElement hmul a
    let x : Module.Dual k (k × HyperbolicModule (k := k) c) ×
        (k × HyperbolicModule (k := k) c) :=
      (d (a₂, -(e x₁₂)), (a₁, x₂₁))
    refine ⟨x, ?_⟩
    rw [ha, peirceHyperbolicTo_apply]
    change peirceElement c a₁ (d.symm (d (a₂, -(e x₁₂)))).1
      (e.symm (-(d.symm (d (a₂, -(e x₁₂)))).2)) x₂₁ = _
    rw [d.symm_apply_apply, neg_neg, e.symm_apply_apply]

/-- The Peirce-coordinate linear equivalence from the hyperbolic module on `k ⊕ C₂₁` to
`A`. -/
noncomputable def peirceHyperbolicEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    (Module.Dual k (k × HyperbolicModule (k := k) c) ×
      (k × HyperbolicModule (k := k) c)) ≃ₗ[k] A :=
  LinearEquiv.ofBijective (peirceHyperbolicTo hc hmul hreg)
    (hc.bijective_peirceHyperbolicTo hmul hreg)

@[simp] theorem peirceHyperbolicEquiv_apply (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : Module.Dual k (k × HyperbolicModule (k := k) c) ×
      (k × HyperbolicModule (k := k) c)) :
    hc.peirceHyperbolicEquiv hmul hreg x = hc.peirceHyperbolicTo hmul hreg x :=
  rfl

/-- **`GPR 22.9(iv)`: the Peirce-coordinate equivalence identifies the norm with the hyperbolic
form `QuadraticForm.dualProd k (k × C₂₁)`.** -/
theorem norm_peirceHyperbolicEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : Module.Dual k (k × HyperbolicModule (k := k) c) ×
      (k × HyperbolicModule (k := k) c)) :
    C.norm (hc.peirceHyperbolicEquiv hmul hreg x) =
      QuadraticForm.dualProd k (k × HyperbolicModule (k := k) c) x := by
  let e := hc.offDiagonalDuality hmul hreg
  let d := dualProdEquiv k (HyperbolicModule (k := k) c)
  rw [peirceHyperbolicEquiv_apply, peirceHyperbolicTo_apply,
    hc.norm_peirceElement hmul, QuadraticForm.dualProd_apply]
  have hd : x.1 x.2 =
      (d.symm x.1).1 * x.2.1 - (d.symm x.1).2 x.2.2 := by
    conv_lhs => rw [← d.apply_symm_apply x.1]
    exact dualProdEquiv_apply _ _
  change x.2.1 * (d.symm x.1).1 + e (e.symm (-(d.symm x.1).2)) x.2.2 = x.1 x.2
  rw [e.apply_symm_apply, hd, LinearMap.neg_apply]
  ring

/-- **The norm of a reduced regular multiplicative conic algebra is hyperbolic**, `GPR 22.9(iv)`.
The displayed isometry uses the hyperbolic form `QuadraticForm.dualProd k (k × C₂₁)`. -/
noncomputable def peirceHyperbolicIsometryEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    (QuadraticForm.dualProd k (k × HyperbolicModule (k := k) c)).IsometryEquiv C.norm where
  toLinearEquiv := hc.peirceHyperbolicEquiv hmul hreg
  map_app' := hc.norm_peirceHyperbolicEquiv hmul hreg

end ConicAlgebra.IsElementaryIdempotent
