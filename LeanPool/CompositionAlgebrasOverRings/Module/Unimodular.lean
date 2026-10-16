/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Unimodular elements of a module

An element `m` of an `R`-module `M` is **unimodular** when some linear functional takes the value
`1` at `m`. This is mathlib's `Module.IsUnimodular R m`, which the library uses throughout.
`GPR 9.13` defines unimodularity differently, by asking that `R·m` be free of rank 1 and a direct
summand of `M`, and observes there that the two agree. This file proves that agreement and supplies
the API the rest of the library needs beyond what mathlib provides.

This is not a norm-theoretic notion — no quadratic form is in sight here — but it is the piece
`QuadraticForm/Isotropic.lean` needs to state GPR-sense isotropy correctly (`GPR 11.17`): a
**unimodular** null vector, not merely a nonzero one. See overview §6(c).

## Main definitions

* `LinearMap.equivProdKerOfApplyEqOne` : the splitting `M ≃ R × ker l` determined by a functional
  `l` with `l m = 1`.

## Main results

* `Module.isUnimodular_iff_injective_toSpanSingleton_and_isComplemented_span` : the equivalence
  noted in **`GPR 9.13`** — `m` is unimodular iff `R·m` is free of rank 1 (`toSpanSingleton`
  injective) and a direct summand of `M` (`Submodule.span R {m}` is complemented), which is the
  definition there.
* `Module.IsUnimodular.map` : unimodularity transports along a linear equivalence.
* `Module.IsUnimodular.units_smul` : unimodularity is unaffected by scaling by a unit.
* `Module.isUnimodular_of_ne_zero` : over a field, unimodular is *exactly* nonzero — every nonzero
  vector in a vector space is hit by a functional. This is what collapses GPR-sense isotropy onto
  mathlib's `Anisotropic` over a field; see `QuadraticForm/Isotropic.lean`.
* `Module.IsUnimodular.exists_linearEquiv_prod` : a unimodular element splits `M` as `R × M'`.

## Implementation notes

GPR also states unimodularity geometrically: `m` is unimodular iff `m ⊗ 1_{κ(𝔭)} ≠ 0` for every
`𝔭 ∈ Spec R` (i.e. `m` survives in every residue field). ⚠ That criterion needs `M` finitely
generated projective (`GPR 9.17`): in the `ℤ`-module `ℤ ⊕ ℤ/2` the element `(2, 1)` survives in
every residue field, but no linear functional takes it to `1`. Only the two algebraic formulations
above are formalized here; the geometric one is not. Note that residue fields cannot detect
whether an element is *nonzero* — `ε` in the free rank-one module over `𝔽₂[ε]/(ε²)` dies in every
residue field — so the geometric criterion genuinely uses unimodularity, not mere non-vanishing.

We use mathlib's general lattice notion `IsComplemented` (`Mathlib.Order.Disjoint`) for "direct
summand" in the `GPR 9.13` characterization rather than inventing a submodule-specific one, per
overview §0.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.13, 9.17, 11.24.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

namespace Module

/-- **`GPR 9.13`**: `m` is unimodular — hit by a functional — exactly when the cyclic submodule
`R·m` is free of rank 1 (equivalently, `r • m = 0 → r = 0`) and a direct summand of `M`, which is
how `GPR 9.13` defines unimodularity. -/
theorem isUnimodular_iff_injective_toSpanSingleton_and_isComplemented_span {M : Type v}
    [AddCommGroup M] [Module R M] {m : M} :
    IsUnimodular R m ↔
      Function.Injective (LinearMap.toSpanSingleton R M m) ∧
        IsComplemented (Submodule.span R {m}) := by
  constructor
  · -- A functional `l` with `l m = 1` splits off `R·m` with complement its kernel, and it
    -- witnesses `r • m = 0 → r = 0`.
    intro hm
    obtain ⟨l, hl⟩ := isUnimodular_iff.mp hm
    have hinj : Function.Injective (LinearMap.toSpanSingleton R M m) := by
      intro a b hab
      have h := congrArg l hab
      simpa [LinearMap.toSpanSingleton_apply, hl] using h
    refine ⟨hinj, LinearMap.ker l, ?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx1
      have hr : r = 0 := by
        have := LinearMap.mem_ker.mp hx2
        simpa [hl] using this
      simp [hr]
    · rw [codisjoint_iff_le_sup]
      intro x _
      refine Submodule.mem_sup.mpr ⟨l x • m, Submodule.mem_span_singleton.mpr ⟨l x, rfl⟩,
        x - l x • m, ?_, by abel⟩
      simp [LinearMap.mem_ker, hl]
  · -- Project onto `R·m` along a complement and undo the isomorphism `R ≃ R·m`.
    rintro ⟨hinj, N, hN⟩
    have hrange : Submodule.span R {m} = LinearMap.range (LinearMap.toSpanSingleton R M m) := by
      rw [LinearMap.span_singleton_eq_range]
    let e : R ≃ₗ[R] (Submodule.span R {m}) :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange.symm)
    refine isUnimodular_of_apply_eq_one (f := (e.symm : (Submodule.span R {m}) →ₗ[R] R) ∘ₗ
      Submodule.projectionOnto _ _ hN) ?_
    have hmem : m ∈ Submodule.span R {m} := Submodule.mem_span_singleton_self m
    have hproj : Submodule.projectionOnto _ _ hN m = ⟨m, hmem⟩ :=
      Submodule.projectionOnto_apply_left hN ⟨m, hmem⟩
    have he : e 1 = ⟨m, hmem⟩ := by
      apply Subtype.ext
      simp [e, LinearMap.toSpanSingleton_apply]
    rw [LinearMap.comp_apply, hproj, ← he]
    exact e.symm_apply_apply 1

/-- Unimodularity transports along a linear equivalence: `m` unimodular in `M` and `e : M ≃ₗ N`
give `e m` unimodular in `N`. -/
theorem IsUnimodular.map {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] {m : M}
    (hm : IsUnimodular R m) (e : M ≃ₗ[R] M') : IsUnimodular R (e m) := by
  obtain ⟨l, hl⟩ := isUnimodular_iff.mp hm
  exact isUnimodular_of_apply_eq_one (f := l ∘ₗ e.symm.toLinearMap) (by simpa using hl)

/-- Unimodularity is unaffected by scaling by a unit: if `m` is unimodular then so is `u • m` for
`u : Rˣ`, since `R·(u • m) = R·m`. -/
theorem IsUnimodular.units_smul {M : Type*} [AddCommGroup M] [Module R M] {m : M}
    (hm : IsUnimodular R m) (u : Rˣ) : IsUnimodular R (u • m) := by
  obtain ⟨l, hl⟩ := isUnimodular_iff.mp hm
  refine isUnimodular_of_apply_eq_one (f := ((u⁻¹ : Rˣ) : R) • l) ?_
  simp [Units.smul_def, hl]

/-- Over a field, unimodular is exactly nonzero: every nonzero vector of a vector space is hit by a
functional. -/
theorem isUnimodular_of_ne_zero {K : Type u} [Field K] {M : Type v} [AddCommGroup M]
    [Module K M] {x : M} (hx : x ≠ 0) : IsUnimodular K x :=
  isUnimodular_iff.mpr (Projective.exists_dual_eq_one K hx)

end Module

/-! ### Splitting off a unimodular element

A unimodular element does not merely span a complemented line — it splits `M` as `R ⊕ M'` with the
free factor *identified*, which is what an induction on the rank needs. -/

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The **splitting** determined by a functional `l` with `l m = 1`: `M ≃ R × ker l`, by
`x ↦ (l x, x - l x • m)` with inverse `(r, y) ↦ r • m + y`.

Since such an `l` is exactly a witness for `Module.IsUnimodular R m`, this says a unimodular element
splits off a free rank-one direct summand. The complement is presented concretely as `ker l`
rather than as an abstract summand so that it stays a `Submodule R M`, hence lives in the same
universe as `M` — which is what makes the induction on the rank in
`Module.free_of_rankAtStalk_eq` (`LGRing/ConstantRank.lean`) go through. -/
noncomputable def LinearMap.equivProdKerOfApplyEqOne (l : M →ₗ[R] R) (m : M) (hl : l m = 1) :
    M ≃ₗ[R] R × (LinearMap.ker l) :=
  LinearEquiv.ofLinearMap
    (l.prod ((LinearMap.id - (LinearMap.toSpanSingleton R M m) ∘ₗ l).codRestrict _ fun x ↦ by
      simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hl]))
    ((LinearMap.toSpanSingleton R M m).coprod (LinearMap.ker l).subtype)
    (by
      refine LinearMap.ext fun x ↦ ?_
      obtain ⟨r, y, hy⟩ := x
      have hfst : l (r • m + y) = r := by
        simp [LinearMap.mem_ker.mp hy, hl]
      refine Prod.ext ?_ (Subtype.ext ?_) <;>
        simp [LinearMap.toSpanSingleton_apply, hfst]
      · simp [LinearMap.mem_ker.mp hy, hl])
    (by refine LinearMap.ext fun x ↦ ?_; simp)

@[simp]
theorem LinearMap.equivProdKerOfApplyEqOne_symm_apply (l : M →ₗ[R] R) (m : M) (hl : l m = 1)
    (x : R × (LinearMap.ker l)) :
    (LinearMap.equivProdKerOfApplyEqOne l m hl).symm x = x.1 • m + (x.2 : M) :=
  rfl

/-- A unimodular element splits `M` as `R ⊕ M'` for a submodule `M'` of `M`. -/
theorem Module.IsUnimodular.exists_linearEquiv_prod {m : M} (hm : Module.IsUnimodular R m) :
    ∃ M' : Submodule R M, Nonempty (M ≃ₗ[R] R × M') := by
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hm
  exact ⟨LinearMap.ker l, ⟨LinearMap.equivProdKerOfApplyEqOne l m hl⟩⟩
