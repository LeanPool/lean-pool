/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.Reduction
public import LeanPool.HyperellipticCurves.RedJ.DVRExtension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Residue fields of DVR extensions over an algebraically closed residue field

Let `O` be a complete DVR whose residue field is algebraically closed, `K` its fraction
field, and `L/K` a finite separable extension. The integral closure `O_L` of `O` in `L` is a
complete DVR (`LeanPool.HyperellipticCurves.RedJ.DVRExtension`); here we show that its residue field
is
*canonically isomorphic* to that of `O` (`ChabautyColeman.integralClosureResidueEquiv`): the residue
extension is integral over an algebraically closed field, hence trivial. Consequently every
element of `L` has a reduction in the *fixed* residue field of `O`
(`ChabautyColeman.redres`, junk value `0` off the valuation ring), and these reductions are
compatible with `O`-embeddings `L →ₐ[O] L'` (`ChabautyColeman.redres_map`) via the induced
map of integral closures (`AlgHom.mapIntegralClosure`).

The local-ring/DVR/fraction-field properties of the integral closures appear as instance
*hypotheses* throughout; consumers derive them once from
`LeanPool.HyperellipticCurves.RedJ.DVRExtension`
(they are not registered as global instances because the fraction field `K` cannot be inferred).

This is the base-change bookkeeping for the reduction map on the Jacobian (`def:redJ`):
residue disks and their point counts live over the various `O_L`, while the reduced curve
stays over the one residue field of `O`.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace ChabautyColeman

/-! ### Local homomorphisms and residue fields of integral extensions -/

section General

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- An integral ring homomorphism between local rings is local. Mathlib's
`RingHom.IsIntegral.isLocalHom` assumes injectivity instead; here both rings are local and
no injectivity is needed (via `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`). -/
theorem isLocalHom_of_isIntegral (f : A →+* B) (hf : f.IsIntegral) : IsLocalHom f := by
  refine ⟨fun a ha ↦ by_contra fun hna ↦ ?_⟩
  have hmem : a ∈ (maximalIdeal B).comap f := by
    rw [eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf _)]
    exact (mem_maximalIdeal a).mpr hna
  exact (mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem) ha

/-- The residue-field map of an integral local homomorphism is integral. -/
theorem residueField_map_isIntegral {f : A →+* B} [IsLocalHom f] (hf : f.IsIntegral) :
    (ResidueField.map f).IsIntegral := by
  intro x
  obtain ⟨s, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hp0⟩ := hf s
  refine ⟨p.map (residue A), hp.map _, ?_⟩
  rw [eval₂_map, ResidueField.map_comp_residue, ← hom_eval₂, hp0, map_zero]

/-- An integral local homomorphism out of a local ring with algebraically closed residue
field induces an isomorphism of residue fields. -/
theorem residueField_map_bijective [IsAlgClosed (ResidueField A)] {f : A →+* B}
    [IsLocalHom f] (hf : f.IsIntegral) : Function.Bijective (ResidueField.map f) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (residueField_map_isIntegral hf)

/-- `2` is a unit in a local ring whose residue characteristic is not `2`. -/
theorem isUnit_two_of_neZero_residue [NeZero (2 : ResidueField A)] : IsUnit (2 : A) := by
  refine (residue_ne_zero_iff_isUnit 2).mp ?_
  rw [map_ofNat]; exact NeZero.ne _

end General

/-! ### The map between integral closures induced by an embedding -/

section Map

variable {O : Type*} [CommRing O] {L L' : Type*} [Field L] [Field L']
  [Algebra O L] [Algebra O L'] (σ : L →ₐ[O] L')

theorem mapIntegralClosure_injective : Function.Injective σ.mapIntegralClosure :=
  fun x y h ↦ Subtype.ext <| σ.toRingHom.injective <| by
    simpa using congrArg Subtype.val h

theorem mapIntegralClosure_isIntegral : σ.mapIntegralClosure.toRingHom.IsIntegral := by
  refine RingHom.IsIntegral.tower_top (algebraMap O (integralClosure O L)) _ ?_
  rw [show σ.mapIntegralClosure.toRingHom.comp (algebraMap O (integralClosure O L))
      = algebraMap O (integralClosure O L') from σ.mapIntegralClosure.comp_algebraMap]
  exact fun x ↦ integralClosure.isIntegral x

/-- The map between integral closures of local homomorphisms is local (integral extensions
of local rings are local). -/
instance [IsLocalRing (integralClosure O L)] [IsLocalRing (integralClosure O L')] :
    IsLocalHom σ.mapIntegralClosure.toRingHom :=
  isLocalHom_of_isIntegral _ (mapIntegralClosure_isIntegral σ)

end Map

/-! ### Reduction of finite separable extensions to the fixed residue field -/

section Tower

universe u

variable (O : Type u) [CommRing O] [IsLocalRing O]
  (L : Type u) [Field L] [Algebra O L] [IsLocalRing (integralClosure O L)]

instance : IsLocalHom (algebraMap O (integralClosure O L)) :=
  isLocalHom_of_isIntegral _ fun x ↦ integralClosure.isIntegral x

variable [IsAlgClosed (ResidueField O)]

/-- When the residue field of the local ring `O` is algebraically closed and the integral
closure `O_L` of `O` in a field `L` is local, the residue field of `O_L` is canonically
isomorphic to that of `O`: base change does not move the residue field. -/
noncomputable def integralClosureResidueEquiv :
    ResidueField O ≃+* ResidueField (integralClosure O L) :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap O (integralClosure O L)))
    (residueField_map_bijective fun x ↦ integralClosure.isIntegral x)

@[simp]
theorem integralClosureResidueEquiv_residue (a : O) :
    integralClosureResidueEquiv O L (residue O a)
      = residue (integralClosure O L) (algebraMap O (integralClosure O L) a) :=
  ResidueField.map_residue _ _

theorem integralClosureResidueEquiv_comp_residue :
    (integralClosureResidueEquiv O L : ResidueField O →+* ResidueField (integralClosure O L)).comp
        (residue O)
      = (residue (integralClosure O L)).comp (algebraMap O (integralClosure O L)) :=
  RingHom.ext fun a ↦ integralClosureResidueEquiv_residue O L a

theorem isAlgClosed_residueField_integralClosure :
    IsAlgClosed (ResidueField (integralClosure O L)) :=
  IsAlgClosed.of_ringEquiv _ _ (integralClosureResidueEquiv O L)

theorem neZero_two_residueField_integralClosure [NeZero (2 : ResidueField O)] :
    NeZero (2 : ResidueField (integralClosure O L)) :=
  ⟨fun h ↦ NeZero.ne (2 : ResidueField O) <| by
    simpa only [map_ofNat, map_zero] using congrArg (integralClosureResidueEquiv O L).symm h⟩

variable (L' : Type u) [Field L'] [Algebra O L'] [IsLocalRing (integralClosure O L')]

/-- The residue-field identifications commute with the maps induced by an `O`-embedding. -/
theorem residueField_map_mapIntegralClosure (σ : L →ₐ[O] L') (x : ResidueField O) :
    ResidueField.map σ.mapIntegralClosure.toRingHom (integralClosureResidueEquiv O L x)
      = integralClosureResidueEquiv O L' x := by
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [integralClosureResidueEquiv_residue, ResidueField.map_residue,
    integralClosureResidueEquiv_residue]
  congr 1
  exact σ.mapIntegralClosure.commutes a

end Tower

/-! ### The reduction map `L → ResidueField O` -/

section Red

universe u

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsAlgClosed (ResidueField O)]
  (L : Type u) [Field L] [Algebra O L] [IsDiscreteValuationRing (integralClosure O L)]
  [IsFractionRing (integralClosure O L) L]

/-- The reduction of an element of `L` in the *fixed* residue field of `O`: reduce integral
elements through the residue field of `O_L`, identified with that of `O` via
`ChabautyColeman.integralClosureResidueEquiv`; junk value `0` off the valuation ring. -/
noncomputable def redres (x : L) : ResidueField O :=
  (integralClosureResidueEquiv O L).symm (redK (O := integralClosure O L) x)

theorem redres_coe (t : integralClosure O L) :
    redres O L (t : L) = (integralClosureResidueEquiv O L).symm
      (residue (integralClosure O L) t) := by
  rw [redres, show (t : L) = algebraMap (integralClosure O L) L t from rfl, redK_algebraMap]

/-- `redres` read in the residue field of the integral closure: the identification sends it
back to the ordinary residue. -/
theorem integralClosureResidueEquiv_redres (t : integralClosure O L) :
    integralClosureResidueEquiv O L (redres O L (t : L))
      = residue (integralClosure O L) t := by
  rw [redres_coe]
  exact (integralClosureResidueEquiv O L).apply_symm_apply _

/-- The reduction of a polynomial over `O` that splits into linear factors with integral
roots is the product of the linear factors at the reduced roots. -/
theorem map_residue_eq_prod_of_map_integralClosure {ι : Type*} {s : Finset ι} {q : O[X]}
    {x : ι → integralClosure O L}
    (h : q.map (algebraMap O (integralClosure O L)) = ∏ i ∈ s, (X - C (x i))) :
    q.map (residue O) = ∏ i ∈ s, (X - C (redres O L (x i : L))) := by
  refine Polynomial.map_injective
    (integralClosureResidueEquiv O L : ResidueField O →+* ResidueField (integralClosure O L))
    (integralClosureResidueEquiv O L).injective ?_
  rw [Polynomial.map_map, integralClosureResidueEquiv_comp_residue, ← Polynomial.map_map, h,
    Polynomial.map_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [Polynomial.map_sub, map_X, map_C, RingEquiv.coe_toRingHom,
    integralClosureResidueEquiv_redres]

/-- Reduction commutes with evaluation: the reduced polynomial at the reduced point takes the
reduced value. -/
theorem eval_map_residue_redres (q : O[X]) (t : integralClosure O L) :
    (q.map (residue O)).eval (redres O L (t : L))
      = redres O L ((q.map (algebraMap O L)).eval (t : L)) := by
  refine (integralClosureResidueEquiv O L).injective ?_
  have hcoe : (q.map (algebraMap O L)).eval (t : L)
      = ((q.map (algebraMap O (integralClosure O L))).eval t : integralClosure O L) := by
    simpa only [aeval_def, ← eval_map] using Subalgebra.aeval_coe (integralClosure O L) t q
  rw [hcoe, integralClosureResidueEquiv_redres, ← RingEquiv.coe_toRingHom, ← eval_map_apply,
    Polynomial.map_map, integralClosureResidueEquiv_comp_residue, ← Polynomial.map_map,
    RingEquiv.coe_toRingHom, integralClosureResidueEquiv_redres, eval_map_apply]

@[simp]
theorem redres_algebraMap (a : O) : redres O L (algebraMap O L a) = residue O a := by
  rw [redres, IsScalarTower.algebraMap_apply O (integralClosure O L) L, redK_algebraMap,
    ← integralClosureResidueEquiv_residue, RingEquiv.symm_apply_apply]

theorem redres_of_not_isIntegral {x : L} (hx : ¬IsIntegral O x) : redres O L x = 0 := by
  rw [redres, redK, dite_eq_right, map_zero]
  intro hle
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact hx (ht ▸ (t.2 : IsIntegral O (t : L)))

variable (L' : Type u) [Field L'] [Algebra O L']
  [IsDiscreteValuationRing (integralClosure O L')] [IsFractionRing (integralClosure O L') L']

/-- Reduction to the fixed residue field is compatible with `O`-embeddings `L →ₐ[O] L'`. -/
theorem redres_map (σ : L →ₐ[O] L') (x : L) : redres O L' (σ x) = redres O L x := by
  by_cases hx : IsIntegral O x
  · obtain ⟨t, rfl⟩ : ∃ t : integralClosure O L, (t : L) = x := ⟨⟨x, hx⟩, rfl⟩
    have key (z : ResidueField (integralClosure O L)) :
        (integralClosureResidueEquiv O L').symm
            (ResidueField.map σ.mapIntegralClosure.toRingHom z)
          = (integralClosureResidueEquiv O L).symm z := by
      have h := residueField_map_mapIntegralClosure O L L' σ
        ((integralClosureResidueEquiv O L).symm z)
      rw [RingEquiv.apply_symm_apply] at h
      rw [h, RingEquiv.symm_apply_apply]
    rw [show σ (t : L) = (σ.mapIntegralClosure t : L') from rfl, redres_coe, redres_coe,
      show residue (integralClosure O L') (σ.mapIntegralClosure t)
        = ResidueField.map σ.mapIntegralClosure.toRingHom
            (residue (integralClosure O L) t) from (ResidueField.map_residue _ _).symm, key]
  · rw [redres_of_not_isIntegral O L hx, redres_of_not_isIntegral O L']
    exact fun h ↦ hx ((isIntegral_algHom_iff σ (RingHom.injective (σ : L →+* L'))).mp h)

end Red

end ChabautyColeman

end
