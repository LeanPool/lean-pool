/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Transition
public import LeanPool.QuillenSuslin.Dilation
public import LeanPool.QuillenSuslin.GlueMaps
public import LeanPool.QuillenSuslin.Glue

import Mathlib.RingTheory.Localization.Algebra

/-!
# Quillen patching for two comaximal elements

Let `a, b ∈ A` be comaximal and `M` a finitely presented `A[X]`-module that becomes extended
after inverting `a` and after inverting `b`. Then `M ≅ A[X] ⊗[A] M(0)` (Quillen 1976, proof of
Theorem 1, p. 168). The normalised isomorphisms over `A_a[X]` and `A_b[X]` differ over
`A_ab[X]` by an automorphism `θ` of `A_ab[X] ⊗ M(0)` with `θ(0) = 1`; identifying
automorphisms with units of `(A_ab ⊗ End M(0))[X]` (`endPoly`), Quillen's dilation lemma writes
`θ` as a product of units coming from `A_a` and from `A_b`, which correct the two isomorphisms so
that they glue.

## Main results

* `isAwayMap_tensorMap`: localising the coefficients of `B ⊗ E` is an `IsAwayMap`.
* `exists_unit_endPoly_eq`: normalised automorphisms come from units with constant term `1`.
* `nonempty_linearEquiv_fibre_of_isCoprime`: the patching step for two comaximal elements.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

theorem dilate_zero {S : Type*} [Ring S] [Algebra A S] (p : S[X]) :
    dilate (0 : A) p = C (p.coeff 0) := by
  ext n
  rw [coeff_dilate, coeff_C, map_zero]
  rcases n with _ | n
  · simp
  · simp

/-- Localising the first factor of `B ⊗[A] E` away from `f` is an `IsAwayMap`. -/
theorem isAwayMap_tensorMap {B B' : Type*} [CommRing B] [CommRing B'] [Algebra A B]
    [Algebra A B'] (f : A) (β : B →ₐ[A] B')
    [hβ : IsLocalizedModule (Submonoid.powers f) β.toLinearMap]
    (hu : IsUnit (algebraMap A B' f)) (E : Type*) [Ring E] [Algebra A E] :
    IsAwayMap f (Algebra.TensorProduct.map β (AlgHom.id A E)) := by
  have hfun : ⇑(Algebra.TensorProduct.map β (AlgHom.id A E)) =
      ⇑(AlgebraTensorModule.rTensor A E β.toLinearMap) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul b e => rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  have hl : IsLocalizedModule (Submonoid.powers f)
    (AlgebraTensorModule.rTensor A E β.toLinearMap) := inferInstance
  refine ⟨?_, fun y => ?_, fun r hr => ?_⟩
  · rw [Algebra.TensorProduct.algebraMap_apply]
    exact hu.map (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[A] E)
  · obtain ⟨⟨x, ⟨_, e, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (AlgebraTensorModule.rTensor A E β.toLinearMap) y
    refine ⟨e, x, ?_⟩
    rw [hfun, ← hx, ← map_pow, ← Algebra.smul_def]
    rfl
  · rw [hfun] at hr
    obtain ⟨⟨_, e, rfl⟩, he⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := AlgebraTensorModule.rTensor A E β.toLinearMap) (x₁ := r) (x₂ := 0)
      (by rw [hr, map_zero])
    refine ⟨e, ?_⟩
    rw [← map_pow, ← Algebra.smul_def]
    simpa [Submonoid.smul_def] using he

section Units

variable (N : Type*) [AddCommGroup N] [Module A N] (B : Type*) [CommRing B] [Algebra A B]

/-- The automorphism of `B[X] ⊗[A] N` given by a unit of `(B ⊗[A] End_A N)[X]`. -/
def endPolyEquiv (ψ : (B ⊗[A] Module.End A N)[X]ˣ) :
    (B[X] ⊗[A] N) ≃ₗ[B[X]] (B[X] ⊗[A] N) :=
  LinearEquiv.ofLinearMap (endPoly N B ψ) (endPoly N B ↑ψ⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, Units.mul_inv, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, Units.inv_mul, map_one]; rfl)

theorem endPolyEquiv_apply (ψ : (B ⊗[A] Module.End A N)[X]ˣ) (x : B[X] ⊗[A] N) :
    endPolyEquiv N B ψ x = endPoly N B ψ x := rfl

/-- An automorphism of `B[X] ⊗[A] N` that reduces to the identity at zero comes from a unit
of `(B ⊗[A] End_A N)[X]` with constant term `1`, for `B` flat and `N` finitely presented. -/
theorem exists_unit_endPoly_eq [Module.Flat A B] [Module.FinitePresentation A N]
    (θ : (B[X] ⊗[A] N) ≃ₗ[B[X]] (B[X] ⊗[A] N)) (hθ : ∀ x, reduce N B (θ x) = reduce N B x) :
    ∃ θ' : (B ⊗[A] Module.End A N)[X]ˣ,
      (∀ x, endPoly N B θ' x = θ x) ∧ (θ' : (B ⊗[A] Module.End A N)[X]).coeff 0 = 1 := by
  let e := RingEquiv.ofBijective (endPoly (A := A) N B) (endPoly_bijective N B)
  let θu : (Module.End B[X] (B[X] ⊗[A] N))ˣ :=
    ⟨θ.toLinearMap, θ.symm.toLinearMap, by ext; simp, by ext; simp⟩
  let θ' := Units.map e.symm.toMonoidHom θu
  have hθ' : endPoly N B θ' = θ.toLinearMap := by
    change e (e.symm θ.toLinearMap) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨θ', fun x => by rw [hθ']; rfl, ?_⟩
  apply endCoeff_injective (A := A) N B
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := reduce_surjective (A := A) N B y
  rw [← reduce_endPoly, hθ', map_one, one_apply_eq_self]
  exact hθ x

end Units

section Localization

variable (a : A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away a B]

theorem isLocalization_polynomial_away :
    letI := Polynomial.algebra A B
    IsLocalization (Submonoid.powers (C a)) B[X] := by
  let _ := Polynomial.algebra A B
  have := Polynomial.isLocalization (Submonoid.powers a) B
  rwa [Submonoid.map_powers] at this

/-- The localisation map `A[X] ⊗[A] N → B[X] ⊗[A] N`. -/
def locP (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A B
    A[X] ⊗[A] N →ₗ[A[X]] B[X] ⊗[A] N :=
  letI := Polynomial.algebra A B
  AlgebraTensorModule.map (Algebra.linearMap A[X] B[X]) LinearMap.id

theorem locP_tmul (N : Type*) [AddCommGroup N] [Module A N] (p : A[X]) (n : N) :
    locP B N (p ⊗ₜ n) = (p.map (algebraMap A B) ⊗ₜ n : B[X] ⊗[A] N) := rfl

/-- Localising `A[X] ⊗[A] N` at the image of any submonoid `S` of `A` gives
`(S⁻¹A)[X] ⊗[A] N`. -/
theorem isLocalizedModule_locP_of_isLocalization (S : Submonoid A) (L : Type*) [CommRing L]
    [Algebra A L] [IsLocalization S L] (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A L
    IsLocalizedModule (S.map C) (locP L N) := by
  let _ := Polynomial.algebra A L
  have := Polynomial.isLocalization S L
  let e := (AlgebraTensorModule.cancelBaseChange A A[X] L[X] L[X] N).restrictScalars A[X]
  have h : e.toLinearMap ∘ₗ TensorProduct.mk A[X] L[X] (A[X] ⊗[A] N) 1 = locP L N := by
    ext
    simp [e, locP_tmul, Algebra.smul_def]
  rw [← h]
  infer_instance

/-- Base change of an `A[X]`-module along `A[X] → (S⁻¹A)[X]` is a localisation at the image
of `S`. -/
theorem isLocalizedModule_mk_polynomial_of_isLocalization (S : Submonoid A) (L : Type*)
    [CommRing L] [Algebra A L] [IsLocalization S L] (M : Type*) [AddCommGroup M]
    [Module A[X] M] :
    letI := Polynomial.algebra A L
    IsLocalizedModule (S.map C) (TensorProduct.mk A[X] L[X] M 1) := by
  let _ := Polynomial.algebra A L
  have := Polynomial.isLocalization S L
  infer_instance

theorem isLocalizedModule_locP (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A B
    IsLocalizedModule (Submonoid.powers (C a)) (locP B N) := by
  have := isLocalizedModule_locP_of_isLocalization (Submonoid.powers a) B N
  rwa [Submonoid.map_powers] at this

theorem isLocalizedModule_mk_polynomial (M : Type*) [AddCommGroup M] [Module A[X] M] :
    letI := Polynomial.algebra A B
    IsLocalizedModule (Submonoid.powers (C a)) (TensorProduct.mk A[X] B[X] M 1) := by
  have := isLocalizedModule_mk_polynomial_of_isLocalization (Submonoid.powers a) B M
  rwa [Submonoid.map_powers] at this

end Localization

theorem isLocalizedModule_algHom (b : A) (B B' : Type*) [CommRing B] [CommRing B'] [Algebra A B]
    [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [IsLocalization.Away (algebraMap A B b) B'] :
    IsLocalizedModule (Submonoid.powers b) (IsScalarTower.toAlgHom A B B').toLinearMap := by
  have : IsLocalizedModule (Submonoid.powers (algebraMap A B b)) (Algebra.linearMap B B') :=
    inferInstance
  exact IsLocalizedModule.restrictScalars_powers b (Algebra.linearMap B B')

section Factor

variable {a b : A} {Ba Bb Bab : Type*} [CommRing Ba] [CommRing Bb] [CommRing Bab] [Algebra A Ba]
  [Algebra A Bb] [Algebra A Bab] [IsLocalization.Away a Ba] [IsLocalization.Away b Bb]
  [IsLocalization.Away (a * b) Bab] [Algebra Ba Bab] [Algebra Bb Bab] [IsScalarTower A Ba Bab]
  [IsScalarTower A Bb Bab]

/-- The coefficient map `Ba ⊗[A] E → Bab ⊗[A] E`. -/
abbrev tensorLeftMap (E : Type*) [Ring E] [Algebra A E] (B B' : Type*) [CommRing B]
    [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B'] :
    B ⊗[A] E →ₐ[A] B' ⊗[A] E :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B B') (AlgHom.id A E)

variable (Ba Bb) in
/-- **Quillen's factorisation.** For comaximal `a, b`, a unit `θ` of `(A_ab ⊗ E)[X]` with
`θ(0) = 1` is `ψ_a ψ_b⁻¹` for units `ψ_a` of `(A_a ⊗ E)[X]` and `ψ_b` of `(A_b ⊗ E)[X]`. -/
theorem exists_factor_unit (hab : IsCoprime a b) (E : Type*) [Ring E] [Algebra A E]
    (θ : (Bab ⊗[A] E)[X]ˣ) (hθ : (θ : (Bab ⊗[A] E)[X]).coeff 0 = 1) :
    ∃ (ψa : (Ba ⊗[A] E)[X]ˣ) (ψb : (Bb ⊗[A] E)[X]ˣ),
      (θ : (Bab ⊗[A] E)[X]) *
          (ψb : (Bb ⊗[A] E)[X]).map (tensorLeftMap (A := A) E Bb Bab : Bb ⊗[A] E →+* Bab ⊗[A] E) =
        (ψa : (Ba ⊗[A] E)[X]).map (tensorLeftMap (A := A) E Ba Bab : Ba ⊗[A] E →+* Bab ⊗[A] E) := by
  have : IsLocalization.Away (b * a) Bab := by rw [mul_comm]; infer_instance
  have : IsLocalization.Away (algebraMap A Ba b) Bab := isLocalization_away_algebraMap_of_mul b a
  have : IsLocalization.Away (algebraMap A Bb a) Bab := isLocalization_away_algebraMap_of_mul a b
  have := isLocalizedModule_algHom b Ba Bab
  have := isLocalizedModule_algHom a Bb Bab
  have hιa : IsAwayMap b (tensorLeftMap (A := A) E Ba Bab) := isAwayMap_tensorMap b _
    (IsLocalization.Away.isUnit_of_dvd (a * b) (dvd_mul_left b a)) E
  have hιb : IsAwayMap a (tensorLeftMap (A := A) E Bb Bab) := isAwayMap_tensorMap a _
    (IsLocalization.Away.isUnit_of_dvd (a * b) (dvd_mul_right a b)) E
  obtain ⟨k₁, hk₁⟩ := hιa.exists_unit_lift_dilation θ
  obtain ⟨k₂, hk₂⟩ := hιb.exists_unit_lift_dilation θ
  obtain ⟨α, β, hαβ⟩ := hab.pow (m := k₂) (n := k₁)
  obtain ⟨ψa, -, hψa⟩ := hk₁ 1 (α * a ^ k₂)
    (Ideal.mem_span_singleton'.mpr ⟨β, by rw [← hαβ]; ring⟩)
  obtain ⟨ψb, -, hψb⟩ := hk₂ 0 (α * a ^ k₂)
    (Ideal.mem_span_singleton'.mpr ⟨-α, by ring⟩)
  rw [dilate_one] at hψa
  rw [dilate_zero, hθ, C_1] at hψb
  let D := Units.map (dilate (α * a ^ k₂) : (Bab ⊗[A] E)[X] →+* _).toMonoidHom θ
  set x := (ψb : (Bb ⊗[A] E)[X]).map
    (tensorLeftMap (A := A) E Bb Bab : Bb ⊗[A] E →+* Bab ⊗[A] E)
  have hx : x = ↑D⁻¹ := by
    calc x = x * ((D : (Bab ⊗[A] E)[X]) * ↑D⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = (x * dilate (α * a ^ k₂) (θ : (Bab ⊗[A] E)[X])) * ↑D⁻¹ := by rw [mul_assoc]; rfl
      _ = ↑D⁻¹ := by rw [hψb, one_mul]
  have hD : dilate (α * a ^ k₂) (θ : (Bab ⊗[A] E)[X]) * x = 1 := by
    rw [hx]
    exact Units.mul_inv D
  refine ⟨ψa, ψb, ?_⟩
  rw [← hψa, mul_assoc, hD, mul_one]

end Factor

end LeanPool.QuillenSuslin

