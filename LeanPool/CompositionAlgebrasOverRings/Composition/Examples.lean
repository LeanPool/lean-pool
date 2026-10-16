/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Octonion
public import LeanPool.CompositionAlgebrasOverRings.Conic.Division
public import Mathlib.Basic.Real.Basic

/-!
# The classical tower `ℝ, ℂ, ℍ, 𝕆`

Specializing the Cayley–Dickson tower of `Composition/Octonion.lean` to `μ₁ = μ₂ = μ₃ = -1` over
an ordered field gives the classical chain of composition algebras in which every nonzero element
is invertible, of ranks `1, 2, 4, 8` — division algebras in the sense of `GPR 8.6`, being
alternative. Over `ℝ` these are the reals, the complex numbers, the quaternions and the octonions.

The mechanism is that a negative scalar keeps the norm **positive definite**: the norm of
`Cay(B, μ)` is `n_B(u) - μ n_B(v)`, and for `μ < 0` that is a sum of two non-negative terms which
vanishes only when both do. A positive definite form is anisotropic, and an anisotropic norm makes
every nonzero element invertible, because `x (conj x) = n(x)·1` exhibits `n(x)⁻¹ · (conj x)` as a
two-sided inverse of `x`.

Note that the inverse is obtained here **without** alternativity or associativity: the identity
`x (conj x) = (conj x) x = n(x)·1` holds in every conic algebra, so the inverse is immediate once
`n(x)` is a unit (`ConicAlgebra.hasTwoSidedInverses_of_anisotropic`). ⚠ That is **not** yet division
in the sense of `GPR 8.6` (bijective left and right multiplication by nonzero elements): the real
sedenions are anisotropic, so have such inverses, but have zero divisors (`GPR Exc. 19.29(e)`,
`ConicAlgebra.not_isDivision_realSedenion`). Alternativity is what upgrades the inverse to division
— `(conj x)(xy) = n(x) y` — and the four algebras here are alternative
(`ConicAlgebra.isDivision_of_anisotropic`, applied in `ConicAlgebra.isDivision_realOctonion`).

## Main results

* `ConicAlgebra.PosDef.cay` : `μ < 0` preserves positive definiteness under doubling.
* `ConicAlgebra.posDef_cay₈`, `ConicAlgebra.exists_inv_cay₈` : the rank-8 member of the tower at
  negative scalars is positive definite, hence every nonzero element is invertible.
* `ConicAlgebra.RealOctonion` : the real octonions `𝕆`, with `finrank_realOctonion` (rank 8),
  `isComposition_realOctonion`, `isAlternative_realOctonion`, `exists_inv_realOctonion` and
  `isDivision_realOctonion` (`𝕆` is a division algebra in the sense of `GPR 8.6`).
* `ConicAlgebra.exists_mul_ne_mul_realQuaternion`,
  `ConicAlgebra.exists_mul_mul_ne_mul_mul_realOctonion` : `ℍ` is not commutative and `𝕆` is not
  associative — the explicit witnesses that the tower stops.

## Relation to mathlib's `ℂ` and `ℍ`

`ConicAlgebra.Cay₂ ℝ (-1)` and `ConicAlgebra.Cay₄ ℝ (-1) (-1)` are identified with mathlib's
`Complex` and `Quaternion ℝ` in `Composition/ComplexQuaternion.lean`
(`ConicAlgebra.realComplexAlgEquiv`, `ConicAlgebra.realQuaternionAlgEquiv`), as isometries carrying
the conjugation to `star`. Nothing in this file depends on those identifications.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.18, 23.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

/-! ### Positive definiteness under doubling -/

section Ordered

variable {k : Type u} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
  {B : Type v} [NonAssocRing B] [Module k B] [SMulCommClass k B B] [IsScalarTower k B B]

/-- **Doubling at a negative scalar preserves positive definiteness.** The norm of `Cay(B, μ)` is
`n_B(u) - μ n_B(v)`; for `μ < 0` both terms are non-negative, and at least one is strictly
positive
unless `u = v = 0`. -/
theorem PosDef.cay (C : ConicAlgebra k B) {μ : k} (hμ : μ < 0) (h : C.norm.PosDef) :
    (C.cay μ).norm.PosDef := by
  intro x hx
  rw [cay_norm_apply]
  rcases eq_or_ne x.1 0 with h1 | h1
  · have h2 : x.2 ≠ 0 := fun h2 ↦ hx (Cay.ext h1 h2)
    have : 0 < -μ * C.norm x.2 := mul_pos (neg_pos.mpr hμ) (h _ h2)
    nlinarith [h.nonneg x.1]
  · nlinarith [h _ h1, h.nonneg x.2, neg_pos.mpr hμ]

variable (k) in
/-- The norm of the base ring, `x ↦ x²`, is positive definite. -/
theorem posDef_baseRing : (baseRing k).norm.PosDef := fun x hx ↦ by
  rw [baseRing_norm_apply]
  exact mul_self_pos.mpr hx

variable (k)

theorem posDef_cay₂ {μ₁ : k} (h₁ : μ₁ < 0) : (cay₂ k μ₁).norm.PosDef :=
  PosDef.cay _ h₁ (posDef_baseRing k)

theorem posDef_cay₄ {μ₁ μ₂ : k} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0) :
    (cay₄ k μ₁ μ₂).norm.PosDef :=
  PosDef.cay _ h₂ (posDef_cay₂ k h₁)

/-- The rank-8 member of the tower at negative scalars has **positive definite** norm — over
`ℝ`, the sum of eight squares. -/
theorem posDef_cay₈ {μ₁ μ₂ μ₃ : k} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0)
    (h₃ : μ₃ < 0) :
    (cay₈ k μ₁ μ₂ μ₃).norm.PosDef :=
  PosDef.cay _ h₃ (posDef_cay₄ k h₁ h₂)

end Ordered

section OrderedField

variable (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the rank-8 member of the tower at negative scalars over an ordered field, **every nonzero
element is invertible**. -/
theorem exists_inv_cay₈ {μ₁ μ₂ μ₃ : K} (h₁ : μ₁ < 0) (h₂ : μ₂ < 0)
    (h₃ : μ₃ < 0)
    {x : Cay₈ K μ₁ μ₂ μ₃} (hx : x ≠ 0) : ∃ y, x * y = 1 ∧ y * x = 1 :=
  (cay₈ K μ₁ μ₂ μ₃).hasTwoSidedInverses_of_anisotropic (posDef_cay₈ K h₁ h₂ h₃).anisotropic hx

end OrderedField

/-! ### The real octonions

⚠ `RealComplex` and `RealQuaternion` are the Cayley–Dickson doubles, not mathlib's `Complex` and
`Quaternion ℝ`. The identifying `AlgEquiv`s are `ConicAlgebra.realComplexAlgEquiv` and
`ConicAlgebra.realQuaternionAlgEquiv`, in `Composition/ComplexQuaternion.lean`. -/

/-- `ℂ` as a Cayley–Dickson double, `Cay(ℝ, -1)`. -/
abbrev RealComplex : Type := Cay₂ ℝ (-1)

/-- `ℍ` as a Cayley–Dickson double, `Cay(ℂ, -1)`. -/
abbrev RealQuaternion : Type := Cay₄ ℝ (-1) (-1)

/-- **The real octonions `𝕆`**, `Cay(ℍ, -1)`. mathlib has no octonions; this is the
definition of
record here. -/
abbrev RealOctonion : Type := Cay₈ ℝ (-1) (-1) (-1)

/-- The conic structure on `𝕆`. -/
noncomputable abbrev realOctonion : ConicAlgebra ℝ RealOctonion := cay₈ ℝ (-1) (-1) (-1)

theorem finrank_realComplex : Module.finrank ℝ RealComplex = 2 := finrank_cay₂ ℝ _

theorem finrank_realQuaternion : Module.finrank ℝ RealQuaternion = 4 :=
  finrank_cay₄ ℝ _ _

/-- **`𝕆` has dimension 8 over `ℝ`.** -/
theorem finrank_realOctonion : Module.finrank ℝ RealOctonion = 8 :=
  finrank_cay₈ ℝ _ _ _

/-- **`𝕆` is alternative.** -/
theorem isAlternative_realOctonion : IsAlternative RealOctonion := inferInstance

/-- **The norm of `𝕆` is positive definite** — the sum of eight squares. -/
theorem posDef_realOctonion : realOctonion.norm.PosDef :=
  posDef_cay₈ ℝ (by norm_num) (by norm_num) (by norm_num)

/-- **Every nonzero octonion is invertible.** -/
theorem exists_inv_realOctonion {x : RealOctonion} (hx : x ≠ 0) :
    ∃ y, x * y = 1 ∧ y * x = 1 :=
  exists_inv_cay₈ ℝ (by norm_num) (by norm_num) (by norm_num) hx

/-- **`𝕆` is a division algebra** in the sense of `GPR 8.6`: it is alternative with anisotropic
norm, so `GPR 13.8` applies (`ConicAlgebra.isDivision_of_anisotropic`). -/
theorem isDivision_realOctonion : IsDivision RealOctonion :=
  have : Nontrivial RealOctonion :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_realOctonion]; norm_num)
  realOctonion.isDivision_of_anisotropic posDef_realOctonion.anisotropic

/-! ### Where the tower breaks

`ℍ` is not commutative and `𝕆` is not associative, with explicit witnesses. These are what stop
the tower: `ConicAlgebra.mul_assoc_cay` needs its input commutative, so `𝕆` gets no `Ring`
structure, and `ConicAlgebra.isMultiplicative_cay` and `ConicAlgebra.isAlternative_cay` need their
input associative, so the sedenions `Cay(𝕆, μ)` get neither a multiplicative norm nor
alternativity. -/

/-- The conjugation of `ℂ` moves `i`, which is what makes `ℍ` non-commutative. -/
theorem conj_i_ne_i : (cay₂ ℝ (-1)).conj ((0, 1) : ℝ × ℝ) ≠ ((0, 1) : ℝ × ℝ) := by
  have hc : (cay₂ ℝ (-1)).conj ((0, 1) : ℝ × ℝ) =
      (((baseRing ℝ).conj 0, -(1 : ℝ)) : ℝ × ℝ) :=
    cay_conj_apply _
  intro hcon
  rw [hc] at hcon
  have h2 := congrArg Prod.snd hcon
  norm_num at h2

/-- **`ℍ` is not commutative.** -/
theorem exists_mul_ne_mul_realQuaternion : ∃ x y : RealQuaternion, x * y ≠ y * x :=
  exists_mul_ne_mul_cay _ _ conj_i_ne_i

/-- **`𝕆` is not associative** — so the tower cannot be continued by the theorems that built
it,
and the sedenions are neither alternative nor multiplicative. -/
theorem exists_mul_mul_ne_mul_mul_realOctonion :
    ∃ x y z : RealOctonion, x * y * z ≠ x * (y * z) :=
  let ⟨_, _, h⟩ := exists_mul_ne_mul_realQuaternion
  exists_mul_mul_ne_mul_mul_cay _ _ (conjIsInvolution_cay₄ ℝ (-1) (-1)) h

/-- **`𝕆` is a composition algebra** of rank 8 over `ℝ`. -/
theorem isComposition_realOctonion : realOctonion.IsComposition.{0, 0, 0} :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  isComposition_cay₈ ℝ (-1) (-1) (-1) (IsUnit.neg isUnit_one) (IsUnit.neg isUnit_one)
    (IsUnit.neg isUnit_one)

end ConicAlgebra
