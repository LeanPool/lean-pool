/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Examples
public import LeanPool.CompositionAlgebrasOverRings.Conic.Division
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankOneTwoFourEight

/-!
# The sedenions: a conic algebra that is not a composition algebra (`GPR 19.23`)

The fourth rung of the Cayley–Dickson tower, `Cay(𝕆, μ)` of rank `16`, is a conic algebra — the
doubling construction has no hypotheses at all — but it is not a composition algebra. This is the
example that shows the tower really does stop, rather than merely resisting the theorems that
built it.

Three separate statements are proved, in increasing strength:

* the sedenions are **not alternative**, the converse half of `GPR 18.14(c)` applied to the
  non-associativity of `𝕆`;
* their norm is **non-singular but not multiplicative** — so the failure is in the composition law
  itself, not in a degeneracy of the norm;
* **no** conic structure on a sixteen-dimensional space is a composition algebra, by the rank
  dichotomy `GPR 19.18`. This last one does not look at the multiplication at all.

## Two independent routes

The first two statements go through alternativity: `𝕆` is not associative
(`ConicAlgebra.exists_mul_mul_ne_mul_mul_realOctonion`), so `Cay(𝕆, μ)` is not alternative
(`ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne`), and over a field every composition algebra is
alternative (`GPR 19.3`). This is the route `GPR` takes.

The third goes through the rank: `16 ∉ {1, 2, 4, 8}`. It is strictly stronger — it rules out every
conic norm on the underlying module at once, rather than the one that doubling produces — and it
needs no witness and no computation with associators.

## Inverses without division

Separately, the sedenions are the example of `GPR Exc. 19.29(e)`: their norm is positive definite,
so every nonzero sedenion has a two-sided inverse, yet they have explicit zero divisors and so are
not a division algebra in the sense of `GPR 8.6`. This separates `ConicAlgebra.HasTwoSidedInverses`
from `IsDivision`, and shows that the alternativity hypothesis of `GPR 13.8` cannot be dropped.

That the norm is non-singular is what makes the second statement sharp. A conic algebra can fail to
be a composition algebra because its norm is degenerate (`GPR 19.4` in characteristic two is that
example, with an identically zero polar form); the sedenions fail for the opposite reason. Their
norm is the sixteen-fold orthogonal sum of `⟨1⟩` over `ℝ`, as non-singular as a form can be, and
what fails is `n(xy) = n(x)n(y)`. This is the converse half of `GPR Exc. 18.18` in this one
instance, obtained without proving that converse in general.

## Main results

* `ConicAlgebra.RealSedenion`, `ConicAlgebra.realSedenion` : the algebra and its conic structure.
* `ConicAlgebra.not_isAlternative_realSedenion` : **not alternative**.
* `ConicAlgebra.not_isMultiplicative_realSedenion` : **the norm does not permit composition**.
* `ConicAlgebra.not_isComposition_conicAlgebra_realSedenion` : no conic structure on the sedenions
  is a composition algebra.
* `ConicAlgebra.IsComposition.not_cay_of_mul_mul_ne` : the general statement over a field, of which
  the sedenions are the instance.
* `ConicAlgebra.posDef_realSedenion`, `ConicAlgebra.hasTwoSidedInverses_realSedenion` : the norm is
  positive definite, so every nonzero sedenion has a two-sided inverse.
* `ConicAlgebra.exists_mul_eq_zero_realSedenion`, `ConicAlgebra.not_isDivision_realSedenion` :
  **`GPR Exc. 19.29(e)`** — the sedenions have zero divisors, so they are not a division algebra in
  the sense of `GPR 8.6`, despite their two-sided inverses.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6, 13.8,
  18.14(c), Exc. 18.18, 19.3, 19.18, 19.23, Exc. 19.29.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

/-! ### The general statement over a field -/

section Field

variable {F : Type u} {B : Type v} [Field F] [NonAssocRing B] [Module F B]
  [SMulCommClass F B B] [IsScalarTower F B B] [Module.Finite F B] [Module.Projective F B]

/-- **The double of a non-associative conic algebra over a field is not a composition algebra.**

`ConicAlgebra.not_isAlternative_cay_of_mul_mul_ne` — the converse half of `GPR 18.14(c)` — says the
double is not alternative, and over a field every composition algebra is alternative
(`GPR 19.3`, `ConicAlgebra.IsComposition.isAlternative`). No hypothesis on `μ`. -/
theorem IsComposition.not_cay_of_mul_mul_ne (C : ConicAlgebra F B) (μ : F) {a b c : B}
    (hne : a * b * c ≠ a * (b * c)) : ¬ (C.cay μ).IsComposition.{u, v, u} := fun h ↦
  not_isAlternative_cay_of_mul_mul_ne C μ hne h.isAlternative

end Field

/-! ### The sedenions over `ℝ` -/

/-- **The real sedenions**, `Cay(𝕆, -1)`: the fourth rung of the Cayley–Dickson tower over `ℝ`,
of dimension `16`. -/
abbrev RealSedenion : Type := Cay realOctonion (-1)

/-- The conic structure on the sedenions. Doubling needs no hypotheses, so this exists exactly as
the earlier rungs do; what fails is everything *after* `GPR 18.4`. -/
noncomputable abbrev realSedenion : ConicAlgebra ℝ RealSedenion := realOctonion.cay (-1)

/-- **The sedenions have dimension 16.** -/
theorem finrank_realSedenion : Module.finrank ℝ RealSedenion = 16 := by
  rw [Cay.finrank_cay, finrank_realOctonion]

/-- **The sedenions are not alternative.** `𝕆` is not associative, and by the converse half of
`GPR 18.14(c)` that is exactly the obstruction. -/
theorem not_isAlternative_realSedenion : ¬ IsAlternative RealSedenion :=
  let ⟨_, _, _, h⟩ := exists_mul_mul_ne_mul_mul_realOctonion
  not_isAlternative_cay_of_mul_mul_ne realOctonion (-1) h

/-- **The sedenion norm is non-singular.** It is `n_𝕆 ⊥ ⟨1⟩ n_𝕆`, and `GN (C.8.3)` builds
non-singularity of an orthogonal sum out of *regularity* of the first summand — which the octonion
norm has, since `2` is invertible in `ℝ`.

This is what makes `ConicAlgebra.not_isMultiplicative_realSedenion` sharp: the sedenions are not a
composition algebra because composition fails, not because the norm degenerates. -/
theorem isGPRNonsingular_realSedenion :
    QuadraticForm.IsGPRNonsingular.{0, 0, 0} realSedenion.norm := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hreg : realOctonion.norm.IsGPRRegular :=
    isComposition_realOctonion.isGPRNonsingular.isGPRRegular
  exact hreg.prod_isGPRNonsingular
    (hreg.isGPRNonsingular.smul_of_isUnit (by norm_num : IsUnit (-(-1 : ℝ))))

/-- **`GPR 19.23`.** The sedenion norm does not permit composition: `n(xy) = n(x)n(y)` fails.

Its norm is non-singular, so were it multiplicative the sedenions would be a composition algebra of
dimension `16`, which `GPR 19.18` forbids. This is the converse half of `GPR Exc. 18.18` in this
instance, obtained without proving that converse in general. -/
theorem not_isMultiplicative_realSedenion : ¬ realSedenion.IsMultiplicative := fun hmul ↦
  not_isComposition_of_finrank_notMem realSedenion
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    ⟨isGPRNonsingular_realSedenion, hmul⟩

/-- **The sedenions are not a composition algebra**, for the conic structure the Cayley–Dickson
process gives them. -/
theorem not_isComposition_realSedenion : ¬ realSedenion.IsComposition.{0, 0, 0} := fun h ↦
  not_isMultiplicative_realSedenion h.isMultiplicative

/-- **No conic structure on the sedenions is a composition algebra.** The rank dichotomy
`GPR 19.18` rules out dimension `16` outright, for every choice of conic norm at once — this looks
at the underlying module only, never at the multiplication. -/
theorem not_isComposition_conicAlgebra_realSedenion (C : ConicAlgebra ℝ RealSedenion) :
    ¬ C.IsComposition.{0, 0, 0} :=
  not_isComposition_of_finrank_notMem C
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)
    (by rw [finrank_realSedenion]; norm_num) (by rw [finrank_realSedenion]; norm_num)

/-! ### `GPR Exc. 19.29(e)`: inverses without division

The sedenion norm is positive definite, so every nonzero sedenion `x` has the two-sided inverse
`n(x)⁻¹ (conj x)`; yet the sedenions have zero divisors, so they are not a division algebra in the
sense of `GPR 8.6`. This is the example separating `ConicAlgebra.HasTwoSidedInverses` from
`IsDivision`, and it is why `GPR 13.8` needs alternativity.

The zero divisors are explicit. Write `e₀, …, e₁₅` for the coordinate basis of
`Cay(Cay(Cay(Cay(ℝ, -1), -1), -1), -1)`, numbering the two components `u, v` of `u + v j` at each
level as the lower and upper half; then `(e₄ + e₉)(e₇ + e₁₀) = 0`. -/

/-- **The norm of the real sedenions is positive definite** — the sum of sixteen squares. Doubling
at a negative scalar preserves positive definiteness (`ConicAlgebra.PosDef.cay`). -/
theorem posDef_realSedenion : realSedenion.norm.PosDef :=
  PosDef.cay realOctonion (by norm_num) posDef_realOctonion

/-- **Every nonzero sedenion has a two-sided inverse**, `n(x)⁻¹ (conj x)`, since the norm is
anisotropic. -/
theorem hasTwoSidedInverses_realSedenion : realSedenion.HasTwoSidedInverses :=
  realSedenion.hasTwoSidedInverses_of_anisotropic posDef_realSedenion.anisotropic

/-- **The real sedenions have zero divisors**: `(e₄ + e₉)(e₇ + e₁₀) = 0`, in the coordinates
described above. The product is checked coordinate by coordinate. -/
theorem exists_mul_eq_zero_realSedenion :
    ∃ x y : RealSedenion, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  refine ⟨Cay.mk (Cay.mk 0 (Cay.mk (Cay.mk 1 0) (Cay.mk 0 0)))
      (Cay.mk (Cay.mk (Cay.mk 0 1) (Cay.mk 0 0)) 0),
    Cay.mk (Cay.mk 0 (Cay.mk (Cay.mk 0 0) (Cay.mk 0 1)))
      (Cay.mk (Cay.mk (Cay.mk 0 0) (Cay.mk 1 0)) 0), fun h ↦ ?_, fun h ↦ ?_, ?_⟩
  · have := congrArg (fun z : RealSedenion ↦ z.1.2.1.1) h
    simp only [Cay.fst_mk, Cay.snd_mk, Cay.fst_zero, Cay.snd_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun z : RealSedenion ↦ z.1.2.2.2) h
    simp only [Cay.fst_mk, Cay.snd_mk, Cay.fst_zero, Cay.snd_zero] at this
    exact one_ne_zero this
  · refine Cay.ext ?_ ?_ <;> refine Cay.ext ?_ ?_ <;> refine Cay.ext ?_ ?_ <;>
      refine Cay.ext ?_ ?_ <;>
      simp only [Cay.fst_mul, Cay.snd_mul, Cay.fst_mk, Cay.snd_mk, cay_conj_mk,
        baseRing_conj_apply, Cay.fst_add, Cay.snd_add, Cay.fst_smul, Cay.snd_smul, Cay.fst_neg,
        Cay.snd_neg, Cay.fst_zero, Cay.snd_zero, mul_zero, zero_mul, add_zero, zero_add,
        neg_zero, smul_zero, map_zero] <;>
      norm_num

/-- **`GPR Exc. 19.29(e)`: the real sedenions are not a division algebra** in the sense of
`GPR 8.6`, although their norm is anisotropic and every nonzero sedenion has a two-sided inverse
(`ConicAlgebra.hasTwoSidedInverses_realSedenion`). So `HasTwoSidedInverses` is strictly weaker than
`IsDivision`, and the alternativity hypothesis of `GPR 13.8`
(`ConicAlgebra.isDivision_iff_hasTwoSidedInverses`) cannot be dropped. -/
theorem not_isDivision_realSedenion : ¬ IsDivision RealSedenion :=
  let ⟨_, _, hx, hy, hxy⟩ := exists_mul_eq_zero_realSedenion
  not_isDivision_of_mul_eq_zero hx hy hxy

end ConicAlgebra
