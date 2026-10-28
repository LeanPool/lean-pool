/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebras.Composition.Classification
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Real
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonMultiplicative
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Euclidean composition algebras as composition algebras over `ℝ`

The `CompositionAlgebras` project develops Hurwitz's theorem for *Euclidean* composition algebras:
a real vector space with a unital bilinear product and a positive definite symmetric bilinear form
whose quadratic form is multiplicative (`CompositionAlgebra`). This file shows that such an
algebra is a composition algebra over `ℝ` in the sense of `GPR 19.5`, and deduces three of that
project's main results from the general theory developed here.

## Main definitions

* `CompositionAlgebra.normForm` : the norm form `x ↦ ⟪x, x⟫` of a Euclidean composition algebra,
  as a quadratic form.
* `CompositionAlgebra.toConicAlgebra` : a nontrivial Euclidean composition algebra is a conic
  algebra over `ℝ` with this norm.

## Main results

* `CompositionAlgebra.isComposition_toConicAlgebra` : a nontrivial finite-dimensional Euclidean
  composition algebra is a composition algebra over `ℝ` with positive definite norm.
* `CompositionAlgebra.ViaConic.finrank_eq_one_or_two_or_four_or_eight` : its dimension is `1`, `2`,
  `4` or `8` (`GPR 19.18`).
* `CompositionAlgebra.ViaConic.exists_isCompIso_of_finrank_eq` : two such algebras of the same
  dimension are isomorphic as composition algebras (`GPR 23.13`).
* `CompositionAlgebra.ViaConic.hurwitz_classification` : such an algebra is isomorphic to `ℝ`,
  `ℂ`, `ℍ` or `𝕆`, with the unit, product and norm preserved.
* `CompositionAlgebra.ViaConic.cd_comp` : the Cayley–Dickson double of a nontrivial associative
  Euclidean composition algebra satisfies the composition law (`GPR Exc. 18.18`).

The last three restate `CompositionAlgebra.finrank_eq_one_or_two_or_four_or_eight`,
`CompositionAlgebra.hurwitz_classification` and the composition law of
`CompositionAlgebra.CD.instCompositionAlgebra`. The statements use that project's definitions,
including its composition algebra structures on `ℝ`, `ℂ`, `ℍ` and `𝕆`, but the proofs do not use
its doubling chain or its Cayley–Dickson computation. The fourth main result there,
`Octonion.nucleus_real`, is a computation in the concrete octonions and is not addressed here.

## Implementation notes

The double `CompositionAlgebra.CD D` is literally the Cayley–Dickson double `Cay(D, -1)` of
`GPR 18.3`: both are `D × D` with product `(a, b)(c, d) = (ac - (conj d) b, da + b (conj c))`. The
composition law is transported along the identity map.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 18.3, 19.5, 19.18,
  23.13, Exc. 18.18.
-/

@[expose] public section

universe u v

namespace CompositionAlgebra

variable (C : Type u) [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
  [CompositionAlgebra C]

/-- The norm form `x ↦ ⟪x, x⟫` of a Euclidean composition algebra, as a quadratic form. -/
def normForm : QuadraticForm ℝ C := LinearMap.BilinMap.toQuadraticMap B

variable {C} in
@[simp] theorem normForm_apply (x : C) : normForm C x = nf x := rfl

variable {C} in
theorem polar_normForm (x y : C) : QuadraticMap.polar (normForm C) x y = 2 * ip x y := by
  rw [normForm, LinearMap.BilinMap.polar_toQuadraticMap, B_symm y x]
  simp only [ip]
  ring

theorem posDef_normForm : (normForm C).PosDef := fun _ hx ↦ nf_pos hx

theorem anisotropic_normForm : (normForm C).Anisotropic := (posDef_normForm C).anisotropic

/-- The norm of a Euclidean composition algebra is non-singular. Over `ℝ`, where `2` is
invertible, this is vanishing of the radical, which anisotropy gives. -/
theorem isGPRNonsingular_normForm [FiniteDimensional ℝ C] :
    (normForm C).IsGPRNonsingular.{0, u, 0} := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  refine (QuadraticForm.isGPRNonsingular_iff_nondegenerate _).mpr
    (QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr ?_)
  exact (Submodule.eq_bot_iff _).mpr fun x hx ↦ anisotropic_normForm C x hx.1

variable [Nontrivial C]

/-- **A nontrivial Euclidean composition algebra is a conic algebra** over `ℝ`, with norm `nf`.
The degree-two identity is `sq_eq`. -/
def toConicAlgebra : ConicAlgebra ℝ C where
  norm := normForm C
  norm_one := nf_one
  mul_self x := by
    rw [polar_normForm, ip_symm]
    exact sq_eq x

@[simp] theorem toConicAlgebra_norm : (toConicAlgebra C).norm = normForm C := rfl

variable {C} in
/-- The conjugation of the conic algebra is the conjugation `cstar` of the Euclidean one. -/
theorem conj_toConicAlgebra (x : C) : (toConicAlgebra C).conj x = cstar x := by
  rw [ConicAlgebra.conj_apply, ConicAlgebra.trace_apply, toConicAlgebra_norm, polar_normForm,
    ip_symm, cstar_apply]

/-- **A nontrivial finite-dimensional Euclidean composition algebra is a composition algebra over
`ℝ`** in the sense of `GPR 19.5`. -/
theorem isComposition_toConicAlgebra [FiniteDimensional ℝ C] :
    (toConicAlgebra C).IsComposition.{0, u, 0} where
  isGPRNonsingular := isGPRNonsingular_normForm C
  isMultiplicative := comp

namespace ViaConic

section Hurwitz

variable [FiniteDimensional ℝ C]

/-- **Hurwitz's dimension theorem, from `GPR 19.18`.** A nontrivial finite-dimensional Euclidean
composition algebra has dimension `1`, `2`, `4` or `8`. -/
theorem finrank_eq_one_or_two_or_four_or_eight :
    Module.finrank ℝ C = 1 ∨ Module.finrank ℝ C = 2 ∨ Module.finrank ℝ C = 4 ∨
      Module.finrank ℝ C = 8 :=
  (isComposition_toConicAlgebra C).finrank_eq_one_or_two_or_four_or_eight

variable {C} {D : Type v} [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D]
  [SMulCommClass ℝ D D] [CompositionAlgebra D] [Nontrivial D] [FiniteDimensional ℝ D]

/-- **Euclidean composition algebras of the same dimension are isomorphic**, by an isomorphism
preserving the unit, the product and the norm form. Both norms are positive definite of the same
dimension, so `GPR 23.13` applies. -/
theorem exists_isCompIso_of_finrank_eq (h : Module.finrank ℝ C = Module.finrank ℝ D) :
    ∃ f : C ≃ₗ[ℝ] D, IsCompIso f := by
  obtain ⟨e, he1, hmul⟩ := (isComposition_toConicAlgebra C).isomorphic_of_anisotropic
    (isComposition_toConicAlgebra D) (anisotropic_normForm C) (anisotropic_normForm D) h
  exact ⟨e.toLinearEquiv, he1, hmul, e.map_app⟩

variable (C) in
open scoped Quaternion in
/-- **Hurwitz's theorem (classification form), from the general theory.** A nontrivial
finite-dimensional Euclidean composition algebra is isomorphic to `ℝ`, `ℂ`, `ℍ` or `𝕆` by an
isomorphism preserving the unit, the product and the norm form. -/
theorem hurwitz_classification :
    (∃ f : C ≃ₗ[ℝ] ℝ, IsCompIso f) ∨ (∃ f : C ≃ₗ[ℝ] ℂ, IsCompIso f) ∨
      (∃ f : C ≃ₗ[ℝ] ℍ[ℝ], IsCompIso f) ∨ (∃ f : C ≃ₗ[ℝ] Octonion, IsCompIso f) := by
  rcases finrank_eq_one_or_two_or_four_or_eight C with h | h | h | h
  · exact Or.inl (exists_isCompIso_of_finrank_eq (h.trans Real.finrank_comp.symm))
  · exact Or.inr (Or.inl (exists_isCompIso_of_finrank_eq (h.trans Complex.finrank_comp.symm)))
  · exact Or.inr (Or.inr (Or.inl
      (exists_isCompIso_of_finrank_eq (h.trans Quaternion.finrank_comp.symm))))
  · exact Or.inr (Or.inr (Or.inr
      (exists_isCompIso_of_finrank_eq (h.trans Octonion.finrank_comp.symm))))

end Hurwitz

section CayleyDickson

variable {D : Type u} [Ring D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
  [CompositionAlgebra D] [Nontrivial D]

/-- **The Cayley–Dickson double of an associative Euclidean composition algebra satisfies the
composition law**, from `GPR Exc. 18.18`. `CD D` is `Cay(D, -1)`, whose norm is multiplicative
because `D` is associative with multiplicative norm. Finite dimension is not needed.

This is the `B_comp` field of `CD.instCompositionAlgebra`. It is stated with `CD.bilin` rather
than `nf` so that the statement does not pass through that instance. -/
theorem cd_comp (x y : CD D) : CD.bilin (x * y) (x * y) = CD.bilin x x * CD.bilin y y := by
  let : Algebra ℝ D := Algebra.ofModule smul_mul_assoc mul_smul_comm
  let toCay (z : CD D) : ConicAlgebra.Cay (toConicAlgebra D) (-1) :=
    ConicAlgebra.Cay.mk z.fst z.snd
  have hmul : toCay (x * y) = toCay x * toCay y := by
    refine ConicAlgebra.Cay.ext ?_ ?_
    · rw [ConicAlgebra.Cay.fst_mul]
      simp only [toCay, ConicAlgebra.Cay.fst_mk, ConicAlgebra.Cay.snd_mk, CD.fst_mul,
        conj_toConicAlgebra, neg_one_smul, sub_eq_add_neg]
    · rw [ConicAlgebra.Cay.snd_mul]
      simp only [toCay, ConicAlgebra.Cay.fst_mk, ConicAlgebra.Cay.snd_mk, CD.snd_mul,
        conj_toConicAlgebra]
  have h := ConicAlgebra.isMultiplicative_cay (toConicAlgebra D) (-1) comp (toCay x) (toCay y)
  rw [← hmul, ConicAlgebra.cay_norm_apply, ConicAlgebra.cay_norm_apply,
    ConicAlgebra.cay_norm_apply] at h
  simp only [toCay, ConicAlgebra.Cay.fst_mk, ConicAlgebra.Cay.snd_mk, toConicAlgebra_norm,
    normForm_apply] at h
  simp only [CD.bilin_apply, ← nf_eq_ip]
  linarith

end CayleyDickson

end ViaConic

end CompositionAlgebra
