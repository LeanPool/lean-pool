/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Over a principal ideal domain, injective means divisible

Mathlib has Baer's criterion (`Module.Baer.injective`) and the case of `ℤ`
(`Module.Baer.of_divisible`). This file treats a general principal ideal domain. Divisibility is
stated without a new definition: `r • ·` is surjective for every `r ≠ 0`.

## Main statements

* `Module.Baer.of_smul_surjective`: over a commutative principal ideal ring, a divisible module
  satisfies Baer's criterion (no domain hypothesis is needed for this direction).
* `Module.injective_of_smul_surjective`: hence it is injective.
* `Module.Injective.smul_surjective`: over a domain, an injective module is divisible.
* `Module.injective_iff_smul_surjective`: the equivalence, over a principal ideal domain.
* `Module.Injective.quotient`: over a principal ideal domain, a quotient of an injective module
  is injective.
* `Module.Baer.exact_comp`: for `Q` satisfying Baer's criterion, `Hom(-, Q)` is exact.
-/

public section

universe u v

namespace Module

variable {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]

/-- Over a commutative principal ideal ring, a module on which every nonzero `r` acts
surjectively satisfies Baer's criterion: a map from the ideal `(a)` extends by `r ↦ r • q`, where
`a • q` is the image of `a`. -/
theorem Baer.of_smul_surjective [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q ↦ r • q)) : Module.Baer R Q := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases ha : a = 0
  · refine ⟨0, fun x hx ↦ ?_⟩
    subst ha
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp only [LinearMap.zero_apply]
    rw [show (⟨0, hx⟩ : Ideal.span ({0} : Set R)) = 0 from rfl, map_zero]
  · obtain ⟨q, hq⟩ := hQ a ha (g ⟨a, Ideal.mem_span_singleton_self a⟩)
    refine ⟨LinearMap.toSpanSingleton R Q q, fun x hx ↦ ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have : (⟨c * a, hx⟩ : Ideal.span ({a} : Set R)) = c • ⟨a, Ideal.mem_span_singleton_self a⟩ :=
      rfl
    simp only [LinearMap.toSpanSingleton_apply, this, map_smul]
    rw [← hq, smul_smul]

/-- Over a commutative principal ideal ring, a divisible module is injective. -/
theorem injective_of_smul_surjective [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q ↦ r • q)) : Module.Injective R Q :=
  (Baer.of_smul_surjective hQ).injective

/-- Over a domain, an injective module is divisible: the map `r • c ↦ c • q` on the ideal `(r)`
extends to `R`, and the image of `1` is a solution of `r • x = q`. -/
theorem Injective.smul_surjective [IsDomain R] [Small.{v} R] [Module.Injective R Q] {r : R}
    (hr : r ≠ 0) : Function.Surjective (fun q : Q ↦ r • q) := by
  intro q
  have hB : Module.Baer R Q := Module.Baer.of_injective inferInstance
  let e : R ≃ₗ[R] Ideal.span ({r} : Set R) :=
    LinearEquiv.toSpanNonzeroSingleton R R r hr
  obtain ⟨g', hg'⟩ := hB _ ((LinearMap.toSpanSingleton R Q q).comp e.symm.toLinearMap)
  refine ⟨g' 1, ?_⟩
  have h1 := hg' r (Ideal.mem_span_singleton_self r)
  have he : e 1 = ⟨r, Ideal.mem_span_singleton_self r⟩ := by
    ext; simp [e, LinearEquiv.toSpanNonzeroSingleton]
  have : e.symm ⟨r, Ideal.mem_span_singleton_self r⟩ = 1 := by
    rw [← he, LinearEquiv.symm_apply_apply]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    LinearMap.toSpanSingleton_apply, one_smul] at h1
  simp only
  rw [← h1, ← map_smul, smul_eq_mul, mul_one]

/-- Over a principal ideal domain, injective means divisible. -/
theorem injective_iff_smul_surjective [IsDomain R] [IsPrincipalIdealRing R] [Small.{v} R] :
    Module.Injective R Q ↔ ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q ↦ r • q) :=
  ⟨fun _ _ hr ↦ Injective.smul_surjective hr, injective_of_smul_surjective⟩

/-- Over a principal ideal domain, every quotient of an injective module is injective. -/
theorem Injective.quotient [IsDomain R] [IsPrincipalIdealRing R] [Small.{v} R]
    [Module.Injective R Q] (N : Submodule R Q) : Module.Injective R (Q ⧸ N) := by
  refine injective_of_smul_surjective fun r hr x ↦ ?_
  obtain ⟨q, rfl⟩ := N.mkQ_surjective x
  obtain ⟨q', hq'⟩ := Injective.smul_surjective (Q := Q) hr q
  exact ⟨N.mkQ q', by simp only [← map_smul]; exact congrArg _ hq'⟩

/-- For `Q` satisfying Baer's criterion, `Hom(-, Q)` is exact: if `E' → E → E''` is exact, so
is `Hom(E'', Q) → Hom(E, Q) → Hom(E', Q)`. -/
theorem Baer.exact_comp (hQ : Module.Baer R Q) {E' E E'' : Type*} [AddCommGroup E']
    [Module R E'] [AddCommGroup E] [Module R E] [AddCommGroup E''] [Module R E'']
    {f : E' →ₗ[R] E} {g : E →ₗ[R] E''} (hfg : Function.Exact f g) :
    Function.Exact (fun ψ : E'' →ₗ[R] Q ↦ ψ ∘ₗ g) (fun φ : E →ₗ[R] Q ↦ φ ∘ₗ f) := by
  intro φ
  constructor
  · intro hφ
    have hle : LinearMap.ker g ≤ LinearMap.ker φ := fun x hx ↦ by
      obtain ⟨y, rfl⟩ := (hfg x).1 hx
      exact LinearMap.congr_fun hφ y
    obtain ⟨ψ, hψ⟩ := hQ.extension_property (LinearMap.range g).subtype
      (Submodule.injective_subtype _)
      (((LinearMap.ker g).liftQ φ hle).comp g.quotKerEquivRange.symm.toLinearMap)
    refine ⟨ψ, LinearMap.ext fun x ↦ ?_⟩
    have := LinearMap.congr_fun hψ ⟨g x, LinearMap.mem_range_self g x⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply] at this
    exact this
  · rintro ⟨ψ, rfl⟩
    simp only [LinearMap.comp_assoc, hfg.linearMap_comp_eq_zero, LinearMap.comp_zero]

end Module
