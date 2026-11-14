/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Splitting off a regular submodule

Let `(M, q)` be a quadratic form over a commutative ring and `N ⊆ M` a submodule on which the
restriction of `q` is **regular** — its polar form is a bijection `N ≃ N*`. Then `N` splits off
orthogonally:

  `M = N ⊕ Nᗮ`   and   `q = q|_N ⊥ q|_{Nᗮ}`,

where `Nᗮ` is the orthogonal complement of `N` for the polar form of `q` (mathlib's
`LinearMap.BilinForm.orthogonal`).

## Why regularity, and not less

Regularity is used twice and both times essentially. *Surjectivity* of `N → N*` produces the
projection: the functional `n ↦ q(x, n)` on `N` is realized by an actual element of `N`, and
subtracting it lands `x` in `Nᗮ`. *Injectivity* gives `N ∩ Nᗮ = 0`. Neither follows from
non-singularity of `q` on `M`, and over a field of characteristic 2 the difference is not cosmetic:
the polar form of a non-singular form of odd rank has a kernel, so its span is a submodule that
does not split off.

Nothing here needs `M` to be projective, finitely generated, or `2` to be invertible; those enter
only in `QuadraticForm.IsGPRNonsingular.comp_polarOrthogonal_subtype`, where non-singularity of
the complement is deduced by base change.

## Main definitions

* `QuadraticForm.polarProj` : the projection `M →ₗ[R] N` attached to a regular restriction.
* `QuadraticForm.polarOrthogonal` : `Nᗮ`, a readable spelling of mathlib's
  `LinearMap.BilinForm.orthogonal` applied to the polar form.
* `QuadraticForm.orthogonalDecomposition` : the linear equivalence `N × Nᗮ ≃ₗ[R] M` given by
  addition.

## Main results

* `QuadraticForm.orthogonalDecompositionIsometryEquiv` : the orthogonal splitting packaged as an
  isometry equivalence.

* `QuadraticForm.comp_orthogonalDecomposition` : `q` pulls back to `q|_N ⊥ q|_{Nᗮ}`.
* `QuadraticForm.nontrivial_baseChange_polarOrthogonal` : the complement is nonzero over every
  field where `N` is strictly smaller than `M`. This is how the full-support hypothesis of the
  representation lemma is met in practice.
* `QuadraticForm.IsGPRNonsingular.comp_polarOrthogonal_subtype` : the complement of a regular
  submodule in a non-singular form is non-singular. This is what feeds the representation lemma
  (`GPR 11.26`).
* `QuadraticForm.eq_top_of_isGPRRegular_of_rankAtStalk_eq` : a regular submodule of full rank is
  everything — the complement has rank zero, hence vanishes.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.11, 19.16.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, C.8.
-/

@[expose] public section

universe u v t

open QuadraticMap (polar)

open scoped TensorProduct

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M} {N : Submodule R M}

variable (Q N) in
/-- `Nᗮ`, the orthogonal complement of `N` for the polar form of `Q`.

This is mathlib's `LinearMap.BilinForm.orthogonal` applied to `QuadraticMap.polarBilin Q`; the
abbreviation exists only so that statements about it are readable, and is reducible, so mathlib's
`LinearMap.BilinForm.mem_orthogonal_iff` applies unchanged. -/
abbrev polarOrthogonal : Submodule R M :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) N

theorem mem_polarOrthogonal_iff {m : M} :
    m ∈ Q.polarOrthogonal N ↔ ∀ n ∈ N, polar Q n m = 0 :=
  Iff.rfl

section Regular

variable (hreg : QuadraticForm.IsGPRRegular (Q.comp N.subtype))
include hreg

/-- **The orthogonal projection onto a regular submodule.**

`x` is sent to the unique element of `N` representing the functional `n ↦ q(x, n)` through the
polar form of `q|_N`. Uniqueness — hence linearity — is exactly regularity of the restriction. -/
noncomputable def polarProj : M →ₗ[R] N :=
  (LinearEquiv.ofBijective
      (QuadraticMap.polarBilin (Q.comp N.subtype)) hreg).symm.toLinearMap ∘ₗ
    N.subtype.dualMap ∘ₗ Q.polarBilin

/-- The defining property of the projection: it does not change the polar form against `N`. -/
theorem polar_polarProj (x : M) (n : N) :
    polar Q (polarProj hreg x : M) (n : M) = polar Q x (n : M) := by
  have h : (QuadraticMap.polarBilin (Q.comp N.subtype)) (polarProj hreg x) =
      N.subtype.dualMap (Q.polarBilin x) :=
    (LinearEquiv.ofBijective (QuadraticMap.polarBilin (Q.comp N.subtype)) hreg).apply_symm_apply _
  exact congrFun (congrArg DFunLike.coe h) n

/-- Every `x` decomposes as its projection plus a vector orthogonal to `N`. -/
theorem sub_polarProj_mem_polarOrthogonal (x : M) :
    x - (polarProj hreg x : M) ∈ Q.polarOrthogonal N := by
  refine (mem_polarOrthogonal_iff).mpr fun n hn ↦ ?_
  rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_comm Q n x,
    QuadraticMap.polar_comm Q n (polarProj hreg x : M),
    polar_polarProj hreg x ⟨n, hn⟩, sub_self]

/-- The projection is the identity on `N`, by injectivity of the restricted polar form. -/
theorem polarProj_coe (a : N) : polarProj hreg (a : M) = a := by
  refine hreg.1 (LinearMap.ext fun n ↦ ?_)
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  exact polar_polarProj hreg (a : M) n

/-- The projection kills the orthogonal complement. -/
theorem polarProj_eq_zero {b : M} (hb : b ∈ Q.polarOrthogonal N) : polarProj hreg b = 0 := by
  refine hreg.1 (LinearMap.ext fun n ↦ ?_)
  rw [QuadraticMap.polarBilin_apply_apply, map_zero, LinearMap.zero_apply]
  change polar Q (polarProj hreg b : M) (n : M) = 0
  rw [polar_polarProj hreg b n, QuadraticMap.polar_comm]
  exact (mem_polarOrthogonal_iff).mp hb n n.2

/-- **`M = N ⊕ Nᗮ`.** Addition is a linear equivalence `N × Nᗮ ≃ₗ[R] M` when the restriction of
`q` to `N` is regular. -/
noncomputable def orthogonalDecomposition : (N × (Q.polarOrthogonal N)) ≃ₗ[R] M :=
  LinearEquiv.ofBijective (N.subtype.coprod (Q.polarOrthogonal N).subtype) <| by
    constructor
    · intro p q hpq
      have h : (p.1 : M) + (p.2 : M) = (q.1 : M) + (q.2 : M) := hpq
      have hz : (p.1 : M) - (q.1 : M) = (q.2 : M) - (p.2 : M) := by
        linear_combination (norm := module) h
      have hmem : (p.1 : M) - (q.1 : M) ∈ Q.polarOrthogonal N := by
        rw [hz]
        exact sub_mem (q.2).2 (p.2).2
      have h1 : p.1 = q.1 := by
        have hp := polarProj_eq_zero hreg hmem
        rwa [map_sub, polarProj_coe, polarProj_coe, sub_eq_zero] at hp
      refine Prod.ext h1 (Subtype.ext ?_)
      rw [h1] at h
      exact add_left_cancel h
    · intro x
      refine ⟨(polarProj hreg x,
        ⟨x - (polarProj hreg x : M), sub_polarProj_mem_polarOrthogonal hreg x⟩), ?_⟩
      change (polarProj hreg x : M) + (x - (polarProj hreg x : M)) = x
      abel

@[simp] theorem orthogonalDecomposition_apply (p : N × (Q.polarOrthogonal N)) :
    orthogonalDecomposition hreg p = (p.1 : M) + (p.2 : M) := rfl

/-- **The orthogonal splitting of the form**: `q = q|_N ⊥ q|_{Nᗮ}`.

The cross term vanishes by the definition of `Nᗮ`, which is the whole point. -/
theorem comp_orthogonalDecomposition :
    Q.comp (orthogonalDecomposition hreg).toLinearMap =
      QuadraticMap.prod (Q.comp N.subtype) (Q.comp (Q.polarOrthogonal N).subtype) := by
  refine QuadraticMap.ext fun p ↦ ?_
  have hcross : polar Q (p.1 : M) (p.2 : M) = 0 :=
    (mem_polarOrthogonal_iff).mp (p.2).2 (p.1 : M) (p.1).2
  have hadd := QuadraticMap.map_add Q (p.1 : M) (p.2 : M)
  rw [hcross, add_zero] at hadd
  rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, orthogonalDecomposition_apply, hadd,
    QuadraticMap.prod_apply, QuadraticMap.comp_apply, QuadraticMap.comp_apply,
    Submodule.subtype_apply, Submodule.subtype_apply]

/-- The orthogonal decomposition packaged as an isometry between the orthogonal sum of the two
restricted forms and the ambient form. -/
noncomputable def orthogonalDecompositionIsometryEquiv :
    ((Q.comp N.subtype).prod
      (Q.comp (Q.polarOrthogonal N).subtype)).IsometryEquiv Q where
  toLinearEquiv := orthogonalDecomposition hreg
  map_app' p := by
    have h := congrFun (congrArg DFunLike.coe (comp_orthogonalDecomposition hreg)) p
    exact h

/-- A regular submodule of a finitely generated module is finitely generated: it is a direct
summand, being the image of the projection. -/
theorem finite_of_comp_isGPRRegular [Module.Finite R M] : Module.Finite R N :=
  Module.Finite.of_surjective (polarProj hreg) fun a ↦ ⟨(a : M), polarProj_coe hreg a⟩

/-- A regular submodule of a projective module is projective. -/
theorem projective_of_comp_isGPRRegular [Module.Projective R M] : Module.Projective R N :=
  Module.Projective.of_split N.subtype (polarProj hreg) (LinearMap.ext (polarProj_coe hreg))

/-- The complement of a regular submodule is finitely generated when the ambient module is. -/
theorem finite_polarOrthogonal [Module.Finite R M] :
    Module.Finite R (Q.polarOrthogonal N) := by
  have : Module.Finite R (N × (Q.polarOrthogonal N)) :=
    Module.Finite.equiv (orthogonalDecomposition hreg).symm
  exact Module.Finite.of_surjective (LinearMap.snd R N (Q.polarOrthogonal N))
    fun b ↦ ⟨(0, b), rfl⟩

/-- The complement of a regular submodule is projective when the ambient module is. -/
theorem projective_polarOrthogonal [Module.Projective R M] :
    Module.Projective R (Q.polarOrthogonal N) := by
  have : Module.Projective R (N × (Q.polarOrthogonal N)) :=
    Module.Projective.of_equiv (orthogonalDecomposition hreg).symm
  exact Module.Projective.of_split (LinearMap.inr R N (Q.polarOrthogonal N))
    (LinearMap.snd R N (Q.polarOrthogonal N)) (LinearMap.ext fun _ ↦ rfl)

end Regular

/-- **The complement of a regular submodule in a non-singular form is non-singular.**

Base change the orthogonal splitting `q ≅ q|_N ⊥ q|_{Nᗮ}` to a field and read off the right
summand (`GN (C.8.3)`, `QuadraticForm.IsGPRNonsingular.of_prod_right`). This is the hypothesis the
representation lemma `GPR 11.26` consumes. -/
theorem IsGPRNonsingular.comp_polarOrthogonal_subtype [Module.Finite R M] [Module.Projective R M]
    {Q : QuadraticForm R M} {N : Submodule R M}
    (hreg : QuadraticForm.IsGPRRegular (Q.comp N.subtype))
    (hQ : QuadraticForm.IsGPRNonsingular.{u, v, t} Q) :
    haveI := finite_polarOrthogonal hreg
    haveI := projective_polarOrthogonal hreg
    QuadraticForm.IsGPRNonsingular.{u, v, t} (Q.comp (Q.polarOrthogonal N).subtype) := by
  have := finite_polarOrthogonal hreg
  have := projective_polarOrthogonal hreg
  have := finite_of_comp_isGPRRegular hreg
  have := projective_of_comp_isGPRRegular hreg
  have h := hQ.comp_linearEquiv (orthogonalDecomposition hreg)
  rw [comp_orthogonalDecomposition hreg] at h
  exact h.of_prod_right

/-- **The complement is visible in the rank.** Over a field `F ∈ R`-alg in which `N` is strictly
smaller than `M`, the base change of the complement is nonzero.

Base change is exact on the splitting `M = N ⊕ Nᗮ`, so the three ranks add up; a vanishing
complement would force the two ranks to agree. This is what supplies `Module.HasFullSupport` for
the representation lemma `GPR 11.26`. -/
theorem nontrivial_baseChange_polarOrthogonal [Module.Finite R M]
    {Q : QuadraticForm R M} {N : Submodule R M}
    (hreg : QuadraticForm.IsGPRRegular (Q.comp N.subtype)) (F : Type t) [Field F] [Algebra R F]
    (hlt : Module.finrank F (F ⊗[R] N) < Module.finrank F (F ⊗[R] M)) :
    Nontrivial (F ⊗[R] (Q.polarOrthogonal N)) := by
  have := finite_polarOrthogonal hreg
  have := finite_of_comp_isGPRRegular hreg
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have e : (F ⊗[R] M) ≃ₗ[F] (F ⊗[R] N) × (F ⊗[R] (Q.polarOrthogonal N)) :=
    ((orthogonalDecomposition hreg).baseChange R F _ M).symm.trans
      (TensorProduct.prodRight R F F N (Q.polarOrthogonal N))
  have hrk : Module.finrank F (F ⊗[R] M) =
      Module.finrank F (F ⊗[R] N) + Module.finrank F (F ⊗[R] (Q.polarOrthogonal N)) := by
    rw [e.finrank_eq, Module.finrank_prod]
  have hzero : Module.finrank F (F ⊗[R] (Q.polarOrthogonal N)) = 0 :=
    Module.finrank_eq_zero_of_subsingleton F (F ⊗[R] (Q.polarOrthogonal N))
  omega

/-- **A regular submodule of full rank is everything.** If the restriction of `Q` to `N` is regular
and `N` has the same constant rank as `M` at every prime, the orthogonal complement has rank zero,
hence is trivial, hence `N = ⊤`.

This is the criterion that turns a doubling that has run out of room into a surjection; the
subalgebra form of it is `ConicAlgebra.mem_of_isGPRRegular_of_rankAtStalk_eq`. -/
theorem eq_top_of_isGPRRegular_of_rankAtStalk_eq [Module.Finite R M] [Module.Projective R M]
    {Q : QuadraticForm R M} {N : Submodule R M}
    (hreg : QuadraticForm.IsGPRRegular (Q.comp N.subtype)) {r : ℕ}
    (hM : Module.rankAtStalk (R := R) M = fun _ ↦ r)
    (hN : Module.rankAtStalk (R := R) N = fun _ ↦ r) : N = ⊤ := by
  have := finite_of_comp_isGPRRegular hreg
  have := projective_of_comp_isGPRRegular hreg
  have := finite_polarOrthogonal hreg
  have := projective_polarOrthogonal hreg
  have hzero : Module.rankAtStalk (R := R) (Q.polarOrthogonal N) = 0 := by
    have hsum := Module.rankAtStalk_eq_of_equiv (orthogonalDecomposition hreg)
    rw [Module.rankAtStalk_prod, hM, hN] at hsum
    funext p
    have := congrFun hsum p
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
    omega
  have : Subsingleton (Q.polarOrthogonal N) :=
    (Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)).mp hzero
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  have hx : x - (polarProj hreg x : M) = 0 := by
    have := Subsingleton.elim
      (⟨x - (polarProj hreg x : M), sub_polarProj_mem_polarOrthogonal hreg x⟩ :
        Q.polarOrthogonal N) 0
    exact congrArg Subtype.val this
  have hxe : x = ((polarProj hreg x : N) : M) := by rw [← sub_eq_zero]; exact hx
  rw [hxe]
  exact (polarProj hreg x).2

end QuadraticForm
