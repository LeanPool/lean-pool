/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The operator `T†T` with its maximal domain

Definitions only. Given a partially defined operator `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert
spaces, this module packages `T†T` as a `LinearPMap` on `H₀` with domain
`{x ∈ D(T) | T x ∈ D(T†)}`, using Mathlib's `LinearPMap.adjoint` (notation `T†`) and
`LinearPMap.comp`. Mathlib's `comp` requires every value of the inner operator to lie in the domain
of the outer one, so `T` is first restricted to that domain with `LinearPMap.domRestrict`.

This is the object of von Neumann's theorem (`T` closed and densely defined ⟹ `T†T` self-adjoint
with dense domain), which is **not** proved here; see `Analysis/Semigroup/VonNeumann.lean`.
Everything here is definitional or `rfl`-level glue. No measure, no log-concavity and no KLS
content.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]

/-- The domain of `T†T`, as a submodule of `H₀`: those `x ∈ D(T)` with `T x ∈ D(T†)`. -/
def adjointCompDomain (T : H₀ →ₗ.[ℝ] H₁) : Submodule ℝ H₀ :=
  (Submodule.comap T.toFun T†.domain).map T.domain.subtype

/-- Membership in the domain of `T†T`. -/
theorem mem_adjointCompDomain {T : H₀ →ₗ.[ℝ] H₁} {x : H₀} :
    x ∈ adjointCompDomain T ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain := by
  constructor
  · rintro ⟨⟨y, hy⟩, h, rfl⟩
    exact ⟨hy, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- The domain of `T†T` lies inside the domain of `T`. -/
theorem adjointCompDomain_le (T : H₀ →ₗ.[ℝ] H₁) : adjointCompDomain T ≤ T.domain :=
  fun _ hx => (mem_adjointCompDomain.mp hx).1

/-- On the restricted domain, `T` takes values in `D(T†)`; this is the side condition that
`LinearPMap.comp` demands. -/
theorem domRestrict_mem_adjoint_domain (T : H₀ →ₗ.[ℝ] H₁)
    (x : ↥(adjointCompDomain T ⊓ T.domain)) :
    T.domRestrict (adjointCompDomain T) x ∈ T†.domain := by
  obtain ⟨hx, h⟩ := mem_adjointCompDomain.mp x.2.1
  rw [T.domRestrict_apply (y := ⟨x, hx⟩) rfl]
  exact h

/-- `T†T` with its maximal domain `{x ∈ D(T) | T x ∈ D(T†)}`. -/
def adjointComp (T : H₀ →ₗ.[ℝ] H₁) : H₀ →ₗ.[ℝ] H₀ :=
  T†.comp (T.domRestrict (adjointCompDomain T)) (domRestrict_mem_adjoint_domain T)

/-- The domain of `adjointComp T`, in the form `LinearPMap.domRestrict` produces it. -/
theorem adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) :
    (adjointComp T).domain = adjointCompDomain T ⊓ T.domain := rfl

/-- The domain of `adjointComp T` is exactly `adjointCompDomain T`. -/
theorem adjointComp_domain_eq (T : H₀ →ₗ.[ℝ] H₁) :
    (adjointComp T).domain = adjointCompDomain T :=
  inf_eq_left.mpr (adjointCompDomain_le T)

/-- Points of the domain of `T†T` are points of the domain of `T`. -/
theorem mem_domain_of_mem_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    (x : H₀) ∈ T.domain :=
  x.2.2

/-- `adjointComp T x = T† (T x)`. -/
theorem adjointComp_apply (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    adjointComp T x =
      T†
        ⟨T ⟨x, x.2.2⟩, by
          simpa [T.domRestrict_apply (y := ⟨x, x.2.2⟩) rfl] using
            domRestrict_mem_adjoint_domain T x⟩ := by
  change T† ⟨T.domRestrict (adjointCompDomain T) x, _⟩ = _
  congr 1

end FunctionalInequalities.Analysis.Semigroup
