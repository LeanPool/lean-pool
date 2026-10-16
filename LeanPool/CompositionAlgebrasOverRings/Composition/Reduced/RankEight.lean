/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.TwistedZorn

/-!
# Reduced composition algebras of rank eight (`GPR 22.15`)

At an elementary idempotent `c`, put `M = C₂₁`. Regularity identifies `C₁₂` with `M*`
through the polar form. Multiplication within the two off-diagonal Peirce components then gives
the associated vector products

  `M × M → M*`,  `M* × M* → M`.

The second linearization of norm multiplicativity is exactly their Binet–Cauchy identity. Thus
the Peirce-coordinate map identifies the algebra with the twisted Zorn vector matrices attached
to this vector-product pair. In constant rank eight the rank count makes `M` projective of
constant rank three. This is Petersson's converse theorem `GPR 22.15`, in vector-product-pair
form. `GPR 22.15` states it with an **orientation** `θ` of `M`, as `C ≅ Zor(M, θ)`; that form is
`Composition/Reduced/OrientedRankEight.lean`, which builds from any vector-product pair on a
rank-three module the orientation inducing it.

## Main definitions

* `ConicAlgebra.IsElementaryIdempotent.peirceVectorProductPair` : the vector products read from
  Peirce multiplication.
* `ConicAlgebra.IsElementaryIdempotent.twistedZorEquiv` : the Peirce-coordinate equivalence from
  the resulting twisted Zorn algebra.

## Main results

* `ConicAlgebra.IsElementaryIdempotent.isomorphic_twistedZor` : the twisted Zorn algebra is
  isomorphic to the original algebra.
* `ConicAlgebra.IsElementaryIdempotent.rankAtStalk_twistingModule_eq_three` : in rank eight the
  twisting module has constant rank three.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 19.35, 22.15.
-/

@[expose] public section

universe u v

namespace ConicAlgebra.IsElementaryIdempotent

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  {C : ConicAlgebra k A} {c : A}

/-- The lower-left Peirce component used as the twisting module in `GPR 22.15`. -/
abbrev ZornTwistingModule (c : A) :=
  IsAlternative.peirceComponent (R := k) c true false

/-- Multiplication of two elements of the lower-left Peirce component `ZornTwistingModule c`,
which lands in the upper-right component. -/
noncomputable def lowerProduct (hc : C.IsElementaryIdempotent c) :
    ZornTwistingModule (k := k) c →ₗ[k] ZornTwistingModule (k := k) c →ₗ[k]
      IsAlternative.peirceComponent (R := k) c false true :=
  LinearMap.mk₂ k (fun x y ↦
      ⟨(x : A) * y, IsAlternative.mul_mem_peirceComponent_swap hc.mul_self
        (by decide) x.property y.property⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul ..))
    (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc ..))
    (fun _ _ _ ↦ Subtype.ext (mul_add ..))
    (fun _ _ _ ↦ Subtype.ext (mul_smul_comm ..))

/-- Multiplication of two elements of the upper-right Peirce component, which lands in
`ZornTwistingModule c`. -/
noncomputable def upperProduct (hc : C.IsElementaryIdempotent c) :
    IsAlternative.peirceComponent (R := k) c false true →ₗ[k]
      IsAlternative.peirceComponent (R := k) c false true →ₗ[k]
        ZornTwistingModule (k := k) c :=
  LinearMap.mk₂ k (fun x y ↦
      ⟨(x : A) * y, IsAlternative.mul_mem_peirceComponent_swap hc.mul_self
        (by decide) x.property y.property⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul ..))
    (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc ..))
    (fun _ _ _ ↦ Subtype.ext (mul_add ..))
    (fun _ _ _ ↦ Subtype.ext (mul_smul_comm ..))

@[simp] theorem lowerProduct_apply (hc : C.IsElementaryIdempotent c)
    (x y : ZornTwistingModule (k := k) c) :
    (hc.lowerProduct x y : A) = (x : A) * y := rfl

@[simp] theorem upperProduct_apply (hc : C.IsElementaryIdempotent c)
    (x y : IsAlternative.peirceComponent (R := k) c false true) :
    (hc.upperProduct x y : A) = (x : A) * y := rfl

/-- **The vector-product pair read from Peirce multiplication.** The two products are
multiplication within `C₂₁` and `C₁₂`, transported across polar duality. Their
Binet–Cauchy identity is the second linearization of norm multiplicativity. -/
noncomputable def peirceVectorProductPair (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    Module.VectorProductPair k (ZornTwistingModule (k := k) c) := by
  let e := hc.offDiagonalDuality hmul hreg
  let cross := hc.lowerProduct.compr₂ e.toLinearMap
  let crossDual := hc.upperProduct.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  refine ⟨cross, crossDual, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change e (hc.lowerProduct x x) = 0
    rw [show hc.lowerProduct x x = 0 by
      apply Subtype.ext
      exact hc.mul_self_eq_zero_of_mem_peirceComponent hmul (by decide) x.property]
    exact map_zero e
  · intro φ
    change hc.upperProduct (e.symm φ) (e.symm φ) = 0
    apply Subtype.ext
    exact hc.mul_self_eq_zero_of_mem_peirceComponent hmul (by decide)
      (e.symm φ).property
  · intro x y
    change e (hc.lowerProduct x y) x = 0
    change QuadraticMap.polar C.norm ((x : A) * y) x = 0
    rw [hmul.polar_mul_left, C.conj_mul_self,
      hc.norm_eq_zero_of_mem_peirceComponent hmul x.property, zero_smul,
      QuadraticMap.polar_zero_right]
  · intro φ ψ
    change φ (hc.upperProduct (e.symm φ) (e.symm ψ)) = 0
    calc
      φ (hc.upperProduct (e.symm φ) (e.symm ψ)) =
          e (e.symm φ) (hc.upperProduct (e.symm φ) (e.symm ψ)) := by
        rw [e.apply_symm_apply]
      _ = QuadraticMap.polar C.norm (e.symm φ)
          ((e.symm φ : A) * e.symm ψ) := rfl
      _ = 0 := by
        rw [QuadraticMap.polar_comm, hmul.polar_mul_left, C.conj_mul_self,
          hc.norm_eq_zero_of_mem_peirceComponent hmul (e.symm φ).property, zero_smul,
          QuadraticMap.polar_zero_right]
  · intro x y φ ψ
    let x₁₂ := e.symm φ
    let y₁₂ := e.symm ψ
    have hlin := hmul.polar_mul_add_polar_mul (x : A) x₁₂ (y : A) y₁₂
    have hxy := hc.mul_eq_neg_polar_smul_peirceIdempotent hmul
      (by decide : true ≠ false) x.property y₁₂.property
    have hyx := hc.mul_eq_neg_polar_smul_peirceIdempotent hmul
      (by decide : false ≠ true) x₁₂.property y.property
    change e (hc.lowerProduct x y)
      (hc.upperProduct (e.symm φ) (e.symm ψ)) = _
    change QuadraticMap.polar C.norm ((x : A) * y) ((x₁₂ : A) * y₁₂) =
      φ x * ψ y - φ y * ψ x
    rw [hxy, hyx, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_comm C.norm
        (IsAlternative.peirceIdempotent c true)
        (IsAlternative.peirceIdempotent c false),
      show QuadraticMap.polar C.norm
          (IsAlternative.peirceIdempotent c false)
          (IsAlternative.peirceIdempotent c true) = 1 by
        simpa [IsAlternative.peirceIdempotent, hc.conj_eq] using hc.polar_conj] at hlin
    rw [← e.apply_symm_apply φ, ← e.apply_symm_apply ψ]
    change _ = e x₁₂ x * e y₁₂ y - e x₁₂ y * e y₁₂ x
    have he (z : IsAlternative.peirceComponent (R := k) c false true)
        (m : ZornTwistingModule (k := k) c) :
        e z m = QuadraticMap.polar C.norm z m := rfl
    rw [he, he, he, he]
    rw [QuadraticMap.polar_comm C.norm x x₁₂,
      QuadraticMap.polar_comm C.norm y y₁₂] at hlin
    rw [QuadraticMap.polar_comm C.norm y₁₂ x]
    linear_combination hlin

/-- The complete Peirce-coordinate multiplication formula. It is the twisted Zorn multiplication
formula before naming the two same-component products as vector products. -/
theorem mul_peirceElement (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (a₁ a₂ b₁ b₂ : k)
    (x₁₂ y₁₂ : IsAlternative.peirceComponent (R := k) c false true)
    (x₂₁ y₂₁ : ZornTwistingModule (k := k) c) :
    peirceElement c a₁ a₂ x₁₂ x₂₁ * peirceElement c b₁ b₂ y₁₂ y₂₁ =
      peirceElement c
        (a₁ * b₁ - QuadraticMap.polar C.norm x₁₂ y₂₁)
        (a₂ * b₂ - QuadraticMap.polar C.norm y₁₂ x₂₁)
        (a₁ • y₁₂ + b₂ • x₁₂ + hc.lowerProduct x₂₁ y₂₁)
        (b₁ • x₂₁ + a₂ • y₂₁ + hc.upperProduct x₁₂ y₁₂) := by
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
  have hleft' (x : ZornTwistingModule (k := k) c) : c₂ * x = x := by
    simpa [c₂] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property true
  have hright' (x : ZornTwistingModule (k := k) c) : x * c₁ = x := by
    simpa [c₁] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property false
  have hleft0' (x : ZornTwistingModule (k := k) c) : c₁ * x = 0 := by
    simpa [c₁] using IsAlternative.peirceIdempotent_mul_of_mem hc.mul_self x.property false
  have hright0' (x : ZornTwistingModule (k := k) c) : x * c₂ = 0 := by
    simpa [c₂] using IsAlternative.mul_peirceIdempotent_of_mem hc.mul_self x.property true
  have h₁₂₂₁ := hc.mul_eq_neg_polar_smul_peirceIdempotent hmul
    (by decide : false ≠ true) x₁₂.property y₂₁.property
  have h₂₁₁₂ := hc.mul_eq_neg_polar_smul_peirceIdempotent hmul
    (by decide : true ≠ false) x₂₁.property y₁₂.property
  simp only [IsAlternative.peirceIdempotent_false,
    IsAlternative.peirceIdempotent_true] at h₁₂₂₁ h₂₁₁₂
  dsimp [c₁, c₂] at hc₁ hc₂ hc₁c₂ hc₂c₁ hleft hright
  dsimp [c₁, c₂] at hleft0 hright0 hleft' hright' hleft0' hright0'
  simp only [peirceElement, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    IsAlternative.peirceIdempotent_false, IsAlternative.peirceIdempotent_true]
  rw [hc₁, hc₁c₂, hc₂c₁, hc₂, hleft y₁₂, hleft0' y₂₁, hleft0 y₁₂,
    hleft' y₂₁, hright0 x₁₂, hright x₁₂, hright' x₂₁, hright0' x₂₁,
    h₁₂₂₁, h₂₁₁₂]
  simp only [smul_zero, add_zero, zero_add, Submodule.coe_add, Submodule.coe_smul,
    lowerProduct_apply, upperProduct_apply]
  rw [QuadraticMap.polar_comm C.norm x₂₁ y₁₂]
  module

/-- The Peirce-coordinate map from the twisted Zorn algebra obtained from multiplication back to
the original algebra. -/
noncomputable def twistedZorToPeirce (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    TwistedZor (hc.peirceVectorProductPair hmul hreg) →ₗ[k] A := by
  let e := hc.offDiagonalDuality hmul hreg
  exact
    { toFun := fun x ↦ peirceElement c x.1.1 x.2.1 (e.symm x.1.2) x.2.2
      map_add' := fun x y ↦ by
        simp only [TwistedZor.fst_add, TwistedZor.snd_add, Prod.fst_add, Prod.snd_add,
          map_add, peirceElement, add_smul, Submodule.coe_add]
        module
      map_smul' := fun a x ↦ by
        change peirceElement c (a * x.1.1) (a * x.2.1) (e.symm (a • x.1.2))
          (a • x.2.2) = a • peirceElement c x.1.1 x.2.1 (e.symm x.1.2) x.2.2
        rw [map_smul]
        simp only [peirceElement, mul_smul, Submodule.coe_smul, smul_add] }

@[simp] theorem twistedZorToPeirce_apply (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : TwistedZor (hc.peirceVectorProductPair hmul hreg)) :
    hc.twistedZorToPeirce hmul hreg x = peirceElement c x.1.1 x.2.1
      ((hc.offDiagonalDuality hmul hreg).symm x.1.2) x.2.2 := rfl

/-- The Peirce-coordinate map from the associated twisted Zorn algebra is bijective. -/
theorem bijective_twistedZorToPeirce (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    Function.Bijective (hc.twistedZorToPeirce hmul hreg) := by
  let e := hc.offDiagonalDuality hmul hreg
  constructor
  · intro x y hxy
    have hproj (i j : Bool) := congrArg
      (IsAlternative.peirceProjection (R := k) c i j) hxy
    apply TwistedZor.ext
    · have h := congrArg C.trace (hproj false false)
      rw [twistedZorToPeirce_apply, twistedZorToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simpa [hc.trace_eq_one] using h
    · have h := hproj false true
      rw [twistedZorToPeirce_apply, twistedZorToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      exact e.symm.injective (by simpa using h)
    · have h := congrArg C.trace (hproj true true)
      rw [twistedZorToPeirce_apply, twistedZorToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_self, false_and, and_false,
        ite_false] at h
      have ht : C.trace (IsAlternative.peirceIdempotent c true) = 1 :=
        (hc.peirceIdempotent true).trace_eq_one
      simpa only [map_smul, ht, smul_eq_mul, mul_one] using h
    · have h := hproj true false
      rw [twistedZorToPeirce_apply, twistedZorToPeirce_apply,
        hc.peirceProjection_peirceElement, hc.peirceProjection_peirceElement] at h
      simpa using h
  · intro a
    obtain ⟨a₁, a₂, x₁₂, x₂₁, ha⟩ := hc.exists_eq_peirceElement hmul a
    let x : TwistedZor (hc.peirceVectorProductPair hmul hreg) :=
      (((a₁, e x₁₂), (a₂, x₂₁)) :
        (k × Module.Dual k (ZornTwistingModule (k := k) c)) ×
          (k × ZornTwistingModule (k := k) c))
    refine ⟨x, ?_⟩
    rw [ha, twistedZorToPeirce_apply]
    change peirceElement c a₁ a₂ (e.symm (e x₁₂)) x₂₁ = _
    rw [e.symm_apply_apply]

/-- The linear equivalence underlying the converse construction of `GPR 22.15`. -/
noncomputable def twistedZorEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    TwistedZor (hc.peirceVectorProductPair hmul hreg) ≃ₗ[k] A :=
  LinearEquiv.ofBijective (hc.twistedZorToPeirce hmul hreg)
    (hc.bijective_twistedZorToPeirce hmul hreg)

@[simp] theorem twistedZorEquiv_apply (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : TwistedZor (hc.peirceVectorProductPair hmul hreg)) :
    hc.twistedZorEquiv hmul hreg x = hc.twistedZorToPeirce hmul hreg x := rfl

/-- The twisted Zorn equivalence preserves the norm. -/
theorem norm_twistedZorEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x : TwistedZor (hc.peirceVectorProductPair hmul hreg)) :
    C.norm (hc.twistedZorEquiv hmul hreg x) =
      twistedZorNorm (hc.peirceVectorProductPair hmul hreg) x := by
  let e := hc.offDiagonalDuality hmul hreg
  rw [twistedZorEquiv_apply, twistedZorToPeirce_apply, hc.norm_peirceElement hmul,
    twistedZorNorm_apply]
  change x.1.1 * x.2.1 + e (e.symm x.1.2) x.2.2 = _
  rw [e.apply_symm_apply]

/-- The twisted Zorn equivalence preserves the identity. -/
theorem twistedZorEquiv_one (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    hc.twistedZorEquiv hmul hreg 1 = 1 := by
  rw [twistedZorEquiv_apply, twistedZorToPeirce_apply]
  simp only [TwistedZor.one_fst_fst, TwistedZor.one_fst_snd, TwistedZor.one_snd_fst,
    TwistedZor.one_snd_snd, map_zero]
  simp [peirceElement, IsAlternative.peirceIdempotent]

/-- The twisted Zorn equivalence preserves multiplication. -/
theorem twistedZorEquiv_mul (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (x y : TwistedZor (hc.peirceVectorProductPair hmul hreg)) :
    hc.twistedZorEquiv hmul hreg (x * y) =
      hc.twistedZorEquiv hmul hreg x * hc.twistedZorEquiv hmul hreg y := by
  let e := hc.offDiagonalDuality hmul hreg
  rw [twistedZorEquiv_apply, twistedZorEquiv_apply, twistedZorEquiv_apply,
    twistedZorToPeirce_apply, twistedZorToPeirce_apply, twistedZorToPeirce_apply,
    hc.mul_peirceElement hmul]
  simp only [TwistedZor.mul_fst_fst, TwistedZor.mul_fst_snd, TwistedZor.mul_snd_fst,
    TwistedZor.mul_snd_snd]
  have hpolar (f : Module.Dual k (ZornTwistingModule (k := k) c))
      (z : ZornTwistingModule (k := k) c) :
      QuadraticMap.polar C.norm (e.symm f) z = f z := by
    change e (e.symm f) z = f z
    rw [e.apply_symm_apply]
  congr 1
  · rw [hpolar]
  · rw [hpolar]
  · apply e.injective
    simp [peirceVectorProductPair, lowerProduct]

/-- The norm isometry underlying the converse construction of `GPR 22.15`. -/
noncomputable def twistedZorIsometryEquiv (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    (twistedZor (hc.peirceVectorProductPair hmul hreg)).norm.IsometryEquiv C.norm where
  toLinearEquiv := hc.twistedZorEquiv hmul hreg
  map_app' := hc.norm_twistedZorEquiv hmul hreg

/-- **The converse construction of `GPR 22.15`:** a regular multiplicative conic algebra with
an elementary idempotent is a twisted Zorn algebra on its lower-left Peirce component. -/
theorem isomorphic_twistedZor (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    (twistedZor (hc.peirceVectorProductPair hmul hreg)).Isomorphic C :=
  ⟨hc.twistedZorIsometryEquiv hmul hreg, hc.twistedZorEquiv_one hmul hreg,
    hc.twistedZorEquiv_mul hmul hreg⟩

/-- **The rank count in `GPR 22.15`.** At an elementary idempotent in a constant-rank-eight
composition algebra with regular norm, both off-diagonal Peirce components have constant rank
three. -/
theorem rankAtStalk_twistingModule_eq_three [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hmul : C.IsMultiplicative)
    (hreg : C.norm.IsGPRRegular)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    Module.rankAtStalk (R := k) (ZornTwistingModule (k := k) c) = 3 := by
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
  change Module.rankAtStalk (R := k) (X true false) = 3
  ext p
  let : Nontrivial k := ⟨⟨0, 1, fun h ↦ p.2.ne_top <|
    (Ideal.eq_top_iff_one p.asIdeal).mpr <| by simpa [h] using p.asIdeal.zero_mem⟩⟩
  have htotal := congrFun
    (Module.rankAtStalk_eq_of_equiv
      (IsAlternative.peirceDecomposition (R := k) hc.mul_self)) p
  rw [hA] at htotal
  rw [Module.rankAtStalk_pi] at htotal
  rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type] at htotal
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, add_assoc] at htotal
  rw [congrFun (hdiag false) p, congrFun (hdiag true) p,
    Module.rankAtStalk_self, congrFun hoff p] at htotal
  simp only [Pi.ofNat_apply] at htotal ⊢
  dsimp [X] at htotal ⊢
  omega

/-- In a reduced composition algebra of constant rank eight, the lower-left Peirce component is
finite projective of constant rank three. The regularity is supplied by `GPR 19.11`. -/
theorem rankAtStalk_twistingModule_eq_three_of_isComposition
    [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    Module.rankAtStalk (R := k) (ZornTwistingModule (k := k) c) = 3 :=
  hc.rankAtStalk_twistingModule_eq_three hcomp.isMultiplicative
    (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)) hA

/-- **`GPR 22.15` (Petersson), converse form:** a reduced constant-rank-eight composition algebra
is the twisted Zorn algebra whose vector products are its off-diagonal Peirce multiplication. -/
theorem isomorphic_twistedZor_of_rankAtStalk_eq_eight
    [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
    (twistedZor (hc.peirceVectorProductPair hcomp.isMultiplicative hreg)).Isomorphic C :=
  hc.isomorphic_twistedZor hcomp.isMultiplicative
    (hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega))

end ConicAlgebra.IsElementaryIdempotent
