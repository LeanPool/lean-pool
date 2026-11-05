/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Hyperbolic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.HyperbolicPair
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.OrthogonalComplement

/-!
# A hyperbolic pair splits off a hyperbolic plane

If `(u, v)` is a hyperbolic pair of `(M, q)` — `q u = q v = 0` and `q(u, v) = 1` — then the
submodule `R u ⊕ R v` they span is free of rank two, the restriction of `q` to it is the
hyperbolic plane `(a, b) ↦ ab`, and that restriction is **regular**. So the plane splits off
orthogonally:

  `q ≅ ⟨plane⟩ ⊥ q|_{(Ru ⊕ Rv)ᗮ}`.

Nothing here needs `M` finitely generated or projective, `q` regular, or `2` invertible. The
regularity that the orthogonal splitting of `QuadraticForm/OrthogonalComplement.lean` consumes is
regularity of the *restricted* form, and that is supplied by the pair itself: the plane is
hyperbolic, and hyperbolic forms on finitely generated projective — here free of rank two —
modules are regular.

This is the missing half of `GPR 11.17`: `QuadraticForm/Isotropic.lean` turns an isotropic vector
into a hyperbolic pair (`isGPRIsotropic_iff_exists_isHyperbolicPair`), and this file turns the pair
into a splitting.

## Main definitions

* `QuadraticMap.IsHyperbolicPair.planeEmbedding` : the map `(a, b) ↦ a u + b v`.
* `QuadraticMap.IsHyperbolicPair.planeSubmodule` : its range, `R u ⊕ R v`.

## Main results

* `QuadraticMap.IsHyperbolicPair.isGPRRegular_comp_planeSubmodule_subtype` : the restriction of
  `q` to `R u ⊕ R v` is regular.
* `QuadraticMap.IsHyperbolicPair.isometryEquivPlaneProd` : **`q ≅ plane ⊥ q|_{(Ru ⊕ Rv)ᗮ}`**.
* `QuadraticForm.isGPRRegular_plane` : the hyperbolic plane is regular over any commutative ring.

## Implementation notes

The embedding is injective because the pair recovers coordinates: `q(a u + b v, v) = a` and
`q(a u + b v, u) = b`, using `q(u, u) = 2 q u = 0` and `q(v, v) = 0`. This is why no hypothesis on
`M` is needed — the splitting is entirely local to the plane.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.11, 11.17.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978,
  I, (3.3).
-/

@[expose] public section

universe u v

open QuadraticMap (polar)

namespace QuadraticForm

variable (R : Type u) [CommRing R]

/-- **The hyperbolic plane is regular** over any commutative ring: `(a, b) ↦ ab` is the pairing of
`R` against `R`, so `QuadraticForm.isGPRRegular_of_basis_pairing` applies to the one-element basis
of `R`. No hypothesis on `2`. -/
theorem isGPRRegular_plane : QuadraticForm.IsGPRRegular (plane R) :=
  isGPRRegular_of_basis_pairing (Module.Basis.singleton Unit R) fun x ↦ by simp

/-- The hyperbolic plane is non-singular. -/
theorem isGPRNonsingular_plane : QuadraticForm.IsGPRNonsingular.{u, u, v} (plane R) :=
  isGPRNonsingular_of_basis_pairing (Module.Basis.singleton Unit R) fun x ↦ by simp

end QuadraticForm

namespace QuadraticMap.IsHyperbolicPair

open QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M} {u v : M}

variable (u v) in
/-- The map `R × R → M`, `(a, b) ↦ a u + b v`, whose image is the plane spanned by a hyperbolic
pair. Defined for any two vectors; it is the hypothesis `IsHyperbolicPair` that makes it injective
and an isometry from `QuadraticForm.plane`. -/
def planeEmbedding : (R × R) →ₗ[R] M :=
  (LinearMap.toSpanSingleton R M u).comp (LinearMap.fst R R R) +
    (LinearMap.toSpanSingleton R M v).comp (LinearMap.snd R R R)

@[simp] theorem planeEmbedding_apply (x : R × R) :
    planeEmbedding u v x = x.1 • u + x.2 • v := rfl

variable (h : Q.IsHyperbolicPair u v)
include h

/-- The embedding carries the hyperbolic plane to `Q`. -/
theorem apply_planeEmbedding (x : R × R) :
    Q (planeEmbedding u v x) = QuadraticForm.plane R x := by
  have hadd := QuadraticMap.map_add Q (x.1 • u) (x.2 • v)
  rw [QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, h.apply_left, h.apply_right, h.polar_eq_one] at hadd
  rw [planeEmbedding_apply, hadd, QuadraticForm.plane_apply]
  ring

/-- Pairing `a u + b v` with `v` recovers `a`. -/
theorem polar_planeEmbedding_right (x : R × R) : polar Q (planeEmbedding u v x) v = x.1 := by
  rw [planeEmbedding_apply, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_left, h.polar_eq_one, h.polar_self_right]
  ring

/-- Pairing `a u + b v` with `u` recovers `b`. -/
theorem polar_planeEmbedding_left (x : R × R) : polar Q (planeEmbedding u v x) u = x.2 := by
  rw [planeEmbedding_apply, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_left, h.polar_self_left, QuadraticMap.polar_comm _ v u,
    h.polar_eq_one]
  ring

theorem injective_planeEmbedding : Function.Injective (planeEmbedding (R := R) u v) := by
  intro x y hxy
  refine Prod.ext ?_ ?_
  · rw [← h.polar_planeEmbedding_right x, ← h.polar_planeEmbedding_right y, hxy]
  · rw [← h.polar_planeEmbedding_left x, ← h.polar_planeEmbedding_left y, hxy]

variable (u v) in
/-- The submodule `R u ⊕ R v` spanned by a hyperbolic pair, presented as the range of
`QuadraticMap.IsHyperbolicPair.planeEmbedding`. -/
def planeSubmodule : Submodule R M := LinearMap.range (planeEmbedding (R := R) u v)

/-- The plane of a hyperbolic pair, as a module, is `R × R`. -/
noncomputable def planeEquiv : (R × R) ≃ₗ[R] planeSubmodule (R := R) u v :=
  LinearEquiv.ofInjective _ h.injective_planeEmbedding

@[simp] theorem planeEquiv_coe (x : R × R) :
    ((h.planeEquiv x : planeSubmodule (R := R) u v) : M) = x.1 • u + x.2 • v := rfl

/-- The restriction of `Q` to the plane of a hyperbolic pair *is* the hyperbolic plane, read
through `QuadraticMap.IsHyperbolicPair.planeEquiv`. -/
theorem comp_planeEquiv :
    (Q.comp (planeSubmodule (R := R) u v).subtype).comp h.planeEquiv.toLinearMap =
      QuadraticForm.plane R := by
  refine QuadraticMap.ext fun x ↦ ?_
  rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.subtype_apply, planeEquiv_coe]
  exact h.apply_planeEmbedding x

/-- The hyperbolic plane, as a quadratic module, *is* the plane of the pair inside `(M, Q)`. -/
noncomputable def planeIsometryEquiv :
    (QuadraticForm.plane R).IsometryEquiv (Q.comp (planeSubmodule (R := R) u v).subtype) where
  toLinearEquiv := h.planeEquiv
  map_app' x := h.apply_planeEmbedding x

/-- **The restriction of `Q` to the plane of a hyperbolic pair is regular.** This is what lets the
plane split off orthogonally, and it holds over any commutative ring with no hypothesis on `2`. -/
theorem isGPRRegular_comp_planeSubmodule_subtype :
    QuadraticForm.IsGPRRegular (Q.comp (planeSubmodule (R := R) u v).subtype) := by
  rw [← QuadraticForm.isGPRRegular_comp_linearEquiv_iff h.planeEquiv, h.comp_planeEquiv]
  exact QuadraticForm.isGPRRegular_plane R

/-- **A hyperbolic pair splits off a hyperbolic plane**: `Q ≅ plane ⊥ Q|_{(Ru ⊕ Rv)ᗮ}`.

The orthogonal complement is taken for the polar form of `Q`
(`QuadraticForm.polarOrthogonal`). -/
noncomputable def isometryEquivPlaneProd :
    ((QuadraticForm.plane R).prod
      (Q.comp (Q.polarOrthogonal (planeSubmodule (R := R) u v)).subtype)).IsometryEquiv Q :=
  (QuadraticMap.IsometryEquiv.prod h.planeIsometryEquiv
      (QuadraticMap.IsometryEquiv.refl _)).trans
    (QuadraticForm.orthogonalDecompositionIsometryEquiv
      h.isGPRRegular_comp_planeSubmodule_subtype)

end QuadraticMap.IsHyperbolicPair
