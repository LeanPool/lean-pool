/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.BaseChange
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticSubalgebra
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `GPR 19.16(b)`: rank greater than one gives a separable quadratic subalgebra

A composition algebra `A` of rank at least two contains an element `u` whose discriminant
`t(u)² - 4n(u)` is a unit. By `GPR 19.8` (`Composition/QuadraticSubalgebra.lean`) the subalgebra
`k[u] = k·1 + k·u` is then free of rank two with regular norm — a *separable* quadratic subalgebra
— which is where the Cayley–Dickson tower of `GPR 19.17` starts.

Starting the tower at a rank-two subalgebra rather than at `k·1` is not a convenience: in
characteristic 2 the norm `⟨1⟩` of `k·1` is non-singular but not regular, and
`ConicAlgebra.IsComposition.cay` needs a **regular** input (`Composition/CayleyDickson.lean`).
The content of this file is exactly that the obstruction can always be avoided.

The field case is proved first and is the whole mathematical content; the passage to an LG ring is
the usual one, and reuses the machinery of the representation lemma
(`QuadraticForm/Representation.lean`) verbatim.

## Main results

* `ConicAlgebra.IsComposition.exists_isUnit_elementDiscriminant` : over a **field**.
* `ConicAlgebra.IsComposition.exists_isRegularRankTwoComposition` : the same, packaged as
  `GPR 19.8(i)` — a regular rank-two composition subalgebra.
* `ConicAlgebra.discriminantForm` : `u ↦ t(u)² - 4n(u)` as a quadratic form, so that `GPR 11.8`
  can turn it into a polynomial and the LG axiom can be applied to it.
* `ConicAlgebra.IsComposition.exists_isUnit_elementDiscriminant_of_isLGRing`,
  `ConicAlgebra.IsComposition.exists_isRegularRankTwoComposition_of_isLGRing`,
  `ConicAlgebra.IsComposition.exists_isRegularRankTwoComposition_of_rankAtStalk` : **`GPR
  19.16(b)`** over an LG ring, with the rank hypothesis stated at the residue fields (the form the
  proof consumes) and in terms of `Module.rankAtStalk` (the form callers will have).

## Implementation notes

The two characteristics need different arguments over a field, and the characteristic-2 one is the
reason the statement is about the *discriminant* rather than about the trace.

* **`2 ≠ 0`.** If every discriminant vanishes then `n` vanishes on `ker t`, hence so does the polar
  form (`ker t` is a subspace, and `polar n u 1 = t(u)`), so `ker t` lies in the radical of `n`.
  Over a field the radical of a composition norm vanishes
  (`ConicAlgebra.IsComposition.isGPRNondegenerate`), so `t` is injective and the dimension is at
  most one.

* **`2 = 0`.** Here `t(u)² - 4n(u) = t(u)²`, so the hypothesis says exactly that the trace vanishes
  identically, and no information about `n` is available over the base field: `t ≡ 0` is consistent
  with a nonzero radical-free norm (`GPR 19.4`, the purely inseparable example, is a *conic*
  algebra of this shape). The argument therefore moves to the algebraic closure — legitimate
  precisely because non-singularity is stable under base change
  (`ConicAlgebra.IsComposition.baseChangeOfProjective`), which is what that stability is *for*.
  There, two steps: the polar form vanishes identically
  (`ConicAlgebra.IsMultiplicative.polar_eq_zero_of_trace_eq_zero`, a short consequence of the
  second linearization of multiplicativity), and then every element `x` equals `d • 1` for `d` a
  square root of `n(x)`, because `x + d • 1` lies in the radical. So the dimension is at most one
  there too, and dimension does not change under base change.

Note that the characteristic-2 argument uses no alternativity and no regularity beyond the
vanishing of the radical over the algebraic closure; in particular it does not go through
`GPR 19.3`.

Over an LG ring the discriminant is fed to the LG axiom as a polynomial. `A` need not be free, so
— exactly as in `QuadraticForm.exists_isUnit_apply_of_hasFullSupport` — the discriminant form is
pulled back along a presentation `kⁿ ↠ A`, where `GPR 11.8` applies. The residue-field hypothesis
of the axiom is discharged by the field case, since the base change of a composition algebra is a
composition algebra (`Composition/BaseChange.lean`) and the rank is unchanged. Note that the
representation lemma itself is *not* used: the discriminant form is not non-singular, so it is the
LG axiom and not `GPR 11.26` that does the work.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.8, 19.16(b).
-/

@[expose] public section

universe u v

open scoped TensorProduct

open QuadraticMap (polar)

namespace ConicAlgebra

/-- A module spanned by a single element has dimension at most one. Used both here and in
`Composition/Fields/SepClosed.lean`, to produce an element outside `K · 1`. -/
theorem finrank_le_one_of_forall_exists_smul {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] (a : M) (h : ∀ x : M, ∃ d : K, x = d • a) :
    Module.finrank K M ≤ 1 := by
  have hrange : LinearMap.range (LinearMap.toSpanSingleton K M a) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    obtain ⟨d, rfl⟩ := h x
    exact ⟨d, rfl⟩
  have hle := LinearMap.finrank_range_le (LinearMap.toSpanSingleton K M a)
  rwa [hrange, finrank_top, Module.finrank_self] at hle

section Field

variable {F : Type u} {A : Type v} [Field F] [NonAssocRing A] [Module F A]
  [SMulCommClass F A A] [IsScalarTower F A A] {C : ConicAlgebra F A}

omit [SMulCommClass F A A] [IsScalarTower F A A] in
/-- **In characteristic 2 a traceless multiplicative conic norm has zero polar form.**

Specialize the second linearization `n(xz, yw) + n(xw, yz) = n(x, y) n(z, w)` at `z = x`, `w = y`.
The degree-two identity turns `x²` and `y²` into multiples of `1`, so the first term is a multiple
of `n(1, 1) = t(1) = 0`; the linearized degree-two identity turns `yx` into `n(x, y)·1 + xy`, so the
second term is a combination of `t(xy) = 0` and `n(xy, xy) = 2n(xy) = 0`. What is left is
`n(x, y)² = 0`.

Neither alternativity nor regularity is used, and the hypothesis is on the trace, not on the
algebra. -/
theorem IsMultiplicative.polar_eq_zero_of_trace_eq_zero (h : C.IsMultiplicative) (h2 : (2 : F) = 0)
    (ht : ∀ x : A, C.trace x = 0) (x y : A) : polar C.norm x y = 0 := by
  have h11 : polar C.norm (1 : A) (1 : A) = 0 := by rw [← C.trace_apply, ht]
  have hxy1 : polar C.norm (x * y) (1 : A) = 0 := by
    rw [QuadraticMap.polar_comm, ← C.trace_apply, ht]
  have hxyxy : polar C.norm (x * y) (x * y) = 0 := by
    rw [QuadraticMap.polar_self, two_smul]
    linear_combination C.norm (x * y) * h2
  have hxx : x * x = -(C.norm x • (1 : A)) := by rw [C.mul_self_eq, ht, zero_smul, zero_sub]
  have hyy : y * y = -(C.norm y • (1 : A)) := by rw [C.mul_self_eq, ht, zero_smul, zero_sub]
  have hyx : y * x = -(polar C.norm x y • (1 : A)) - x * y := by
    have hmm := C.mul_add_mul x y
    rw [ht, ht, zero_smul, zero_smul, zero_add, zero_sub] at hmm
    linear_combination (norm := module) hmm
  have key := h.polar_mul_add_polar_mul x y x y
  rw [hxx, hyy, hyx] at key
  simp only [QuadraticMap.polar_neg_left, QuadraticMap.polar_neg_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, QuadraticMap.polar_sub_right,
    smul_eq_mul, h11, hxy1, hxyxy] at key
  exact mul_self_eq_zero.mp (by linear_combination -key)

omit [SMulCommClass F A A] [IsScalarTower F A A] in
/-- **Over an algebraically closed field of characteristic 2, a traceless multiplicative conic
algebra with vanishing radical is spanned by `1`.**

Every `x` has `n(x) = d²` for some `d`, and then `n(x + d • 1) = n(x) + d² = 2n(x) = 0` while the
polar form vanishes identically by
`ConicAlgebra.IsMultiplicative.polar_eq_zero_of_trace_eq_zero`; so `x + d • 1` lies in the radical,
which is zero. -/
theorem IsMultiplicative.exists_eq_smul_one_of_isAlgClosed [IsAlgClosed F] (h : C.IsMultiplicative)
    (h2 : (2 : F) = 0) (ht : ∀ x : A, C.trace x = 0) (hrad : C.norm.radical = ⊥) (x : A) :
    ∃ d : F, x = d • (1 : A) := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (C.norm x) (n := 2) two_pos
  refine ⟨-d, ?_⟩
  have hmem : x + d • (1 : A) ∈ C.norm.radical := by
    refine ⟨?_, ?_⟩
    · rw [C.norm_add, QuadraticMap.map_smul, C.norm_one,
        h.polar_eq_zero_of_trace_eq_zero h2 ht, smul_eq_mul, mul_one, ← sq, hd, add_zero]
      linear_combination C.norm x * h2
    · ext z
      simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
      exact h.polar_eq_zero_of_trace_eq_zero h2 ht _ z
  rw [hrad, Submodule.mem_bot] at hmem
  rw [neg_smul]
  linear_combination (norm := module) hmem

variable [Module.Finite F A] [Module.Projective F A]

omit [SMulCommClass F A A] [IsScalarTower F A A] [Module.Finite F A] [Module.Projective F A] in
/-- If the trace of a conic algebra over a field is injective, the algebra has dimension at most
one. Used in characteristic `≠ 2`, where `ker t` is shown to lie in the radical of the norm. -/
private theorem finrank_le_one_of_trace_injective (hinj : Function.Injective C.trace) :
    Module.finrank F A ≤ 1 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (f := C.trace) hinj

/-- **The field case of `GPR 19.16(b)`.** A composition algebra of dimension at least two over a
field contains an element of nonzero — hence invertible — discriminant, so by `GPR 19.8` it
contains a separable quadratic subalgebra.

The two characteristics are genuinely different arguments; see the module docstring. -/
theorem IsComposition.exists_isUnit_elementDiscriminant (h : C.IsComposition.{u, v, u})
    (hrank : 1 < Module.finrank F A) : ∃ u : A, IsUnit (C.elementDiscriminant u) := by
  by_contra hcon
  have hzero : ∀ u : A, C.elementDiscriminant u = 0 := fun u ↦
    not_not.mp fun hne ↦ hcon ⟨u, isUnit_iff_ne_zero.mpr hne⟩
  rcases eq_or_ne (2 : F) 0 with h2 | h2
  · -- Characteristic 2: the trace vanishes identically, and the algebraic closure is a line.
    have ht : ∀ x : A, C.trace x = 0 := by
      intro x
      have hx := hzero x
      rw [elementDiscriminant, show (4 : F) = 2 * 2 by norm_num, h2, zero_mul, zero_mul,
        sub_zero] at hx
      exact pow_eq_zero_iff two_ne_zero |>.mp hx
    set K := AlgebraicClosure F with hKdef
    have hK := h.baseChangeOfProjective K
    have h2K : (2 : K) = 0 := by
      have hmap : algebraMap F K (2 : F) = 0 := by rw [h2, map_zero]
      rwa [map_ofNat] at hmap
    have htK : ∀ X : K ⊗[F] A, (C.baseChangeOfProjective K).trace X = 0 := by
      intro X
      induction X with
      | tmul s a => rw [baseChangeOfProjective_trace_apply_tmul, ht, zero_smul]
      | add X Y hX hY => rw [map_add, hX, hY, add_zero]
    have hrankK : 1 < Module.finrank K (K ⊗[F] A) := by rwa [Module.finrank_baseChange]
    exact absurd hrankK (not_lt.mpr (finrank_le_one_of_forall_exists_smul (1 : K ⊗[F] A)
      (hK.isMultiplicative.exists_eq_smul_one_of_isAlgClosed h2K htK hK.isGPRNondegenerate)))
  · -- Characteristic ≠ 2: the kernel of the trace lies in the radical of the norm.
    have h4 : (4 : F) ≠ 0 := fun h4 ↦ h2 <| by
      have h22 : (2 : F) * 2 = 0 := by linear_combination h4
      rcases mul_eq_zero.mp h22 with hz | hz <;> exact hz
    have hrad : C.norm.radical = ⊥ := h.isGPRNondegenerate
    have hnorm : ∀ u : A, C.trace u = 0 → C.norm u = 0 := by
      intro u hu
      have hu' := hzero u
      rw [elementDiscriminant, hu] at hu'
      have h4n : (4 : F) * C.norm u = 0 := by linear_combination -hu'
      rcases mul_eq_zero.mp h4n with hz | hz
      · exact absurd hz h4
      · exact hz
    have hker : ∀ u : A, C.trace u = 0 → u = 0 := by
      intro u hu
      have hmem : u ∈ C.norm.radical := by
        refine ⟨hnorm u hu, ?_⟩
        ext y
        set c : F := (2 : F)⁻¹ * C.trace y with hc
        set y₀ : A := y - c • (1 : A) with hy₀
        have hty₀ : C.trace y₀ = 0 := by
          rw [hy₀, map_sub, map_smul, C.trace_one, smul_eq_mul, hc]
          field_simp
          ring
        have h1 : polar C.norm u (1 : A) = 0 := by
          rw [QuadraticMap.polar_comm, ← C.trace_apply, hu]
        have h0 : polar C.norm u y₀ = 0 := by
          have hadd := C.norm_add u y₀
          rw [hnorm u hu, hnorm y₀ hty₀,
            hnorm _ (by rw [map_add, hu, hty₀, add_zero])] at hadd
          linear_combination -hadd
        have hy : y = y₀ + c • (1 : A) := by rw [hy₀]; abel
        rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, hy,
          QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, h0, h1, smul_zero, add_zero]
      rwa [hrad, Submodule.mem_bot] at hmem
    refine absurd hrank
      (not_lt.mpr (finrank_le_one_of_trace_injective (C := C) fun X Y hXY ↦ ?_))
    have hsub := hker (X - Y) (by rw [map_sub, hXY, sub_self])
    linear_combination (norm := module) hsub

/-- **The field case of `GPR 19.16(b)`, packaged.** A composition algebra of dimension at least two
over a field contains a regular rank-two composition subalgebra `k[u]` (`GPR 19.8(i)`). -/
theorem IsComposition.exists_isRegularRankTwoComposition (h : C.IsComposition.{u, v, u})
    (hrank : 1 < Module.finrank F A) : ∃ u : A, C.IsRegularRankTwoComposition u := by
  obtain ⟨u, hu⟩ := h.exists_isUnit_elementDiscriminant hrank
  exact ⟨u, (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mpr hu⟩

end Field

/-! ### Globalization over an LG ring -/

section LGRing

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  (C : ConicAlgebra k A)

/-- The element discriminant `t(u)² - 4n(u)` of `GPR 19.8`, as a **quadratic form** on `A`.

The trace is linear and the norm is quadratic, so this is quadratic; packaging it as a
`QuadraticForm` is what lets `GPR 11.8` turn it into a polynomial and hence hand it to the LG
axiom. -/
def discriminantForm : QuadraticForm k A := QuadraticMap.sq.comp C.trace - (4 : k) • C.norm

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
@[simp] theorem discriminantForm_apply (u : A) :
    C.discriminantForm u = C.elementDiscriminant u := by
  simp only [discriminantForm, sub_apply, smul_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, smul_eq_mul, elementDiscriminant]
  ring

/-- The discriminant form commutes with base change: on `1 ⊗ₜ a` both sides are the image of
`t(a)² - 4n(a)`, and a quadratic form on a base changed module is determined by those values. -/
theorem discriminantForm_baseChangeOfProjective (S : Type w) [CommRing S] [Algebra k S] :
    (C.baseChangeOfProjective S).discriminantForm =
      C.discriminantForm.baseChangeOfProjective S := by
  refine _root_.baseChange_ext fun a ↦ ?_
  rw [discriminantForm_apply, QuadraticForm.baseChangeOfProjective_tmul, discriminantForm_apply,
    elementDiscriminant, elementDiscriminant, baseChangeOfProjective_trace_apply_tmul,
    baseChangeOfProjective_norm_apply_tmul]
  simp only [Algebra.smul_def, map_sub, map_pow, map_mul, map_ofNat, mul_one]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The dimension of the fibre `(k ⧸ 𝔪) ⊗ A` is mathlib's `Module.rankAtStalk` at `𝔪`.

The two differ only in which model of the residue field they use: `rankAtStalk` goes through
`Ideal.ResidueField`, the residue field of the localization, whereas the LG axiom speaks about
`k ⧸ 𝔪`. For `𝔪` maximal these agree, and base change along the comparison map does not change
the rank. -/
theorem finrank_quotient_tensor_eq_rankAtStalk (𝔪 : Ideal k) [𝔪.IsMaximal] :
    Module.finrank (k ⧸ 𝔪) ((k ⧸ 𝔪) ⊗[k] A) =
      Module.rankAtStalk A ⟨𝔪, inferInstance⟩ := by
  let : Field (k ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  rw [← Ideal.finrank_fiber_eq_rankAtStalk,
    ← Module.finrank_baseChange (R := 𝔪.ResidueField) (S := k ⧸ 𝔪)
      (M' := (k ⧸ 𝔪) ⊗[k] A),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k (k ⧸ 𝔪) 𝔪.ResidueField
      𝔪.ResidueField A).finrank_eq]

/-- **`GPR 19.16(b)`.** Over an LG ring, a composition algebra whose rank exceeds one at every
residue field contains an element of invertible discriminant.

This is where the LG axiom is applied, and the shape is that of the representation lemma
(`QuadraticForm/Representation.lean`): `A` need not be free, so pull the discriminant form back
along a presentation `kⁿ ↠ A`, where `GPR 11.8` writes it as a polynomial. Over each residue field
the base changed algebra is again a composition algebra
(`ConicAlgebra.IsComposition.baseChangeOfProjective`) of dimension at least two, so
`exists_isUnit_elementDiscriminant` supplies the required unit value there, and `π ⊗ κ` stays
surjective so the witness lifts to the free module. The LG axiom then descends a witness to `k`. -/
theorem IsComposition.exists_isUnit_elementDiscriminant_of_isLGRing {C : ConicAlgebra k A}
    (hLG : IsLGRing k) (h : C.IsComposition.{u, v, u})
    (hrank : ∀ (𝔪 : Ideal k) [𝔪.IsMaximal],
      1 < Module.finrank (k ⧸ 𝔪) ((k ⧸ 𝔪) ⊗[k] A)) :
    ∃ u : A, IsUnit (C.elementDiscriminant u) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' k A
  set bm : Module.Basis (Fin n) k (Fin n → k) := Pi.basisFun k (Fin n) with hbm
  set q' : QuadraticForm k (Fin n → k) := C.discriminantForm.comp π with hq'
  have hrep : (QuadraticForm.toMvPolynomial q' bm).RepresentsUnit k := by
    refine (hLG n _).mpr fun 𝔪 _ ↦ ?_
    let : Field (k ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    obtain ⟨x, hx⟩ :=
      (h.baseChangeOfProjective (k ⧸ 𝔪)).exists_isUnit_elementDiscriminant (hrank 𝔪)
    rw [← discriminantForm_apply, C.discriminantForm_baseChangeOfProjective] at hx
    obtain ⟨y, rfl⟩ := LinearMap.baseChange_surjective (k ⧸ 𝔪) hπ x
    set b' := Algebra.TensorProduct.basis (k ⧸ 𝔪) bm with hb'
    refine ⟨fun i ↦ b'.repr y i, ?_⟩
    have hy : ∑ i, b'.repr y i • ((1 : k ⧸ 𝔪) ⊗ₜ[k] bm i) = y := by
      simpa [hb', Algebra.TensorProduct.basis_apply] using b'.sum_repr y
    rw [QuadraticForm.aeval_toMvPolynomial, hy, hq',
      QuadraticForm.baseChangeOfProjective_comp, QuadraticMap.comp_apply]
    exact hx
  obtain ⟨t, ht⟩ := hrep
  rw [QuadraticForm.aeval_toMvPolynomial_self] at ht
  have hsum : ∑ i, t i • bm i = t := by
    simpa [hbm] using (Pi.basisFun k (Fin n)).sum_repr t
  rw [hsum, hq', QuadraticMap.comp_apply, discriminantForm_apply] at ht
  exact ⟨π t, ht⟩

/-- **`GPR 19.16(b)`, packaged.** Over an LG ring, a composition algebra of rank greater than one
contains a regular rank-two composition subalgebra `k[u]` — the subalgebra the Cayley–Dickson
tower starts from. -/
theorem IsComposition.exists_isRegularRankTwoComposition_of_isLGRing {C : ConicAlgebra k A}
    (hLG : IsLGRing k) (h : C.IsComposition.{u, v, u})
    (hrank : ∀ (𝔪 : Ideal k) [𝔪.IsMaximal],
      1 < Module.finrank (k ⧸ 𝔪) ((k ⧸ 𝔪) ⊗[k] A)) :
    ∃ u : A, C.IsRegularRankTwoComposition u := by
  obtain ⟨u, hu⟩ := h.exists_isUnit_elementDiscriminant_of_isLGRing hLG hrank
  exact ⟨u, (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mpr hu⟩

/-- **`GPR 19.16(b)`, in the project's standard rank language.** Over an LG ring, a composition
algebra of rank greater than one everywhere on `Spec k` contains a regular rank-two composition
subalgebra. This is the form the Cayley–Dickson tower of `GPR 19.17` will consume, where the rank
is constant and greater than one. -/
theorem IsComposition.exists_isRegularRankTwoComposition_of_rankAtStalk {C : ConicAlgebra k A}
    (hLG : IsLGRing k) (h : C.IsComposition.{u, v, u})
    (hrank : ∀ 𝔭 : PrimeSpectrum k, 1 < Module.rankAtStalk A 𝔭) :
    ∃ u : A, C.IsRegularRankTwoComposition u :=
  h.exists_isRegularRankTwoComposition_of_isLGRing hLG fun 𝔪 _ ↦ by
    rw [finrank_quotient_tensor_eq_rankAtStalk]
    exact hrank _

end LGRing

end ConicAlgebra
