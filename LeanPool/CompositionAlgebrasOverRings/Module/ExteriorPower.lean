/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Exterior powers of finite projective modules

This file proves the perfect-duality statement for exterior powers of projective modules, which
is missing from mathlib: for a finitely generated projective module `M`, the determinant pairing
identifies `⋀ⁿ(M*)` with `( ⋀ⁿ M )*`. This is `GPR 21.7`.

mathlib has the finite free case (`exteriorPower.bijective_pairingDual`). For a finite projective
module, write `M` as a retract of a finite free module. Naturality of the
pairing transports the inverse across that retraction, avoiding any choice of local bases.

## Main results

* `exteriorPower.baseChangeLinear` : the canonical base-change map for exterior powers.
* `exteriorPower.pairingDual_naturality` : naturality of the determinant pairing.
* `exteriorPower.pairingDualEquiv` : perfect duality for every finite projective module.
* `exteriorPower.instProjective` : the exterior powers of a projective module are projective.

## References

* [GPR] Skip Garibaldi, Holger Petersson, and Michel Racine, *Albert Algebras over Commutative
  Rings*, 21.7.
-/

@[expose] public section

universe u v w

open Function

namespace exteriorPower

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The canonical map from the base change of an exterior power to the exterior power of the
base-changed module. -/
noncomputable def baseChangeLinear (S : Type w) [CommRing S] [Algebra R S] (n : ℕ) :
    TensorProduct R S (⋀[R]^n M) →ₗ[S]
      (⋀[S]^n (TensorProduct R S M)) := by
  let altR : (TensorProduct R S M) [⋀^Fin n]→ₗ[R]
      (⋀[S]^n (TensorProduct R S M)) :=
    { toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := (exteriorPower.ιMulti S n).map_eq_zero_of_eq }
  exact (exteriorPower.alternatingMapLinearEquiv
    (altR.compLinearMap (TensorProduct.mk R S M 1))).liftBaseChange S

@[simp] theorem baseChangeLinear_tmul_ιMulti (S : Type w) [CommRing S] [Algebra R S]
    (n : ℕ) (s : S) (x : Fin n → M) :
    baseChangeLinear (M := M) S n (s ⊗ₜ[R] exteriorPower.ιMulti R n x) =
      s • exteriorPower.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] x i) := by
  simp [baseChangeLinear]
  rfl

/-- The determinant pairing on exterior powers is natural in the module. -/
theorem pairingDual_naturality (n : ℕ) (f : M →ₗ[R] N) :
    pairingDual R M n ∘ₗ map n f.dualMap =
      (map n f).dualMap ∘ₗ pairingDual R N n := by
  ext g v
  simp

/-- **`GPR 21.7`.** For a finitely generated projective module, the canonical determinant
pairing `⋀ⁿ(M*) → (⋀ⁿ M)*` is bijective. -/
theorem pairingDual_bijective_of_projective [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) : Function.Bijective (pairingDual R M n) := by
  obtain ⟨d, r, hr⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hri⟩ := r.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hr)
  let P := Fin d → R
  let eP : (⋀[R]^n (Module.Dual R P)) ≃ₗ[R] Module.Dual R (⋀[R]^n P) :=
    LinearEquiv.ofBijective (pairingDual R P n)
      (bijective_pairingDual R P n)
  let inverse : Module.Dual R (⋀[R]^n M) →ₗ[R] ⋀[R]^n (Module.Dual R M) :=
    map n i.dualMap ∘ₗ eP.symm.toLinearMap ∘ₗ (map n r).dualMap
  have hinvRight : Function.RightInverse inverse (pairingDual R M n) := by
    intro F
    dsimp only [inverse, LinearMap.comp_apply]
    have hi := LinearMap.congr_fun (pairingDual_naturality n i)
      (eP.symm ((map n r).dualMap F))
    simp only [LinearMap.comp_apply] at hi
    change pairingDual R M n (map n i.dualMap
      (eP.symm ((map n r).dualMap F))) = F
    rw [hi]
    change (map n i).dualMap (eP (eP.symm ((map n r).dualMap F))) = F
    rw [eP.apply_symm_apply, ← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap,
      ← map_comp, hri, map_id, LinearMap.dualMap_id, LinearMap.id_apply]
  have hinvLeft : Function.LeftInverse inverse (pairingDual R M n) := by
    intro x
    dsimp only [inverse, LinearMap.comp_apply]
    have hr' := LinearMap.congr_fun (pairingDual_naturality n r) x
    simp only [LinearMap.comp_apply] at hr'
    rw [← hr']
    change map n i.dualMap (eP.symm (eP (map n r.dualMap x))) = x
    rw [eP.symm_apply_apply, ← LinearMap.comp_apply, ← map_comp,
      LinearMap.dualMap_comp_dualMap, hri, LinearMap.dualMap_id, map_id,
      LinearMap.id_apply]
  exact ⟨hinvLeft.injective, hinvRight.surjective⟩

/-- **`GPR 21.7`.** The canonical perfect pairing between the `n`th exterior powers of a finite
projective module and its dual. -/
noncomputable def pairingDualEquiv [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    (⋀[R]^n (Module.Dual R M)) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  LinearEquiv.ofBijective (pairingDual R M n) (pairingDual_bijective_of_projective n)

@[simp] theorem pairingDualEquiv_apply [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (x : ⋀[R]^n (Module.Dual R M)) :
    pairingDualEquiv (M := M) n x = pairingDual R M n x := rfl

end exteriorPower

/-- The exterior powers of a projective module are projective. -/
instance exteriorPower.instProjective {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  exact Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id))
    (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
