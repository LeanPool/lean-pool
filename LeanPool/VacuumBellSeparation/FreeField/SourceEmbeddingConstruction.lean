/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroNondegenerate
public import LeanPool.VacuumBellSeparation.FreeField.RealCommutation
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Staged literal construction

Exact original declarations; verification target proofs are staged separately.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory ClosedSubmodule

namespace VacuumBellSeparation

instance : SMul ℝ SpatialTestFunction where
  smul a f := ⟨fun x => a * f.1 x, contDiff_const.mul f.2.1, f.2.2.mul_left⟩

instance : Module ℝ SpatialTestFunction :=
  Function.Injective.module ℝ
    ({ toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      SpatialTestFunction →+ (EuclideanSpace ℝ (Fin 3) → ℝ))
    Subtype.val_injective (fun _ _ => rfl)

theorem spatialFourier_smul (a : ℝ) (f : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier (a • f) p = a • spatialFourier f p := by
  unfold spatialFourier
  rw [← integral_smul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (a * f.1 x : ℝ) =
    a • (Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ))
  rw [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem timeZeroOneParticle_smul (m a : ℝ) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (a • u) p = a • timeZeroOneParticle m u p := by
  change spatialFourier (a • u.1) p + Complex.I * (dispersion m p : ℂ) *
      spatialFourier (a • u.2) p = _
  rw [spatialFourier_smul, spatialFourier_smul]
  simp only [timeZeroOneParticle, Complex.real_smul]
  ring

theorem timeZeroL2_smul {m : ℝ} (hm : 0 < m) (a : ℝ) (u : TimeZeroSource) :
    timeZeroL2 hm (a • u) = a • timeZeroL2 hm u :=
  (MemLp.toLp_congr (memLp_timeZeroOneParticle hm (a • u))
    ((memLp_timeZeroOneParticle hm u).const_smul a)
    (Filter.Eventually.of_forall fun p => timeZeroOneParticle_smul m a u p)).trans
    (MemLp.toLp_const_smul a (memLp_timeZeroOneParticle hm u))

/-- The actual time-zero source map, now bundled as a real linear map. -/
noncomputable def timeZeroLinear {m : ℝ} (hm : 0 < m) :
    TimeZeroSource →ₗ[ℝ] Lp ℂ 2 (oneParticleMeasure m) where
  toFun := timeZeroL2 hm
  map_add' := timeZeroL2_add hm
  map_smul' := timeZeroL2_smul hm

theorem timeZeroLinear_injective {m : ℝ} (hm : 0 < m) :
    Function.Injective (timeZeroLinear hm) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  exact timeZeroSource_eq_zero_of_L2_eq_zero hm

/-- Both real test functions have their support inside `U`, as in Section 2.1. -/
def localizedTimeZeroSources (U : Set (EuclideanSpace ℝ (Fin 3))) :
    Submodule ℝ TimeZeroSource where
  carrier := {u | tsupport u.1.1 ⊆ U ∧ tsupport u.2.1 ⊆ U}
  zero_mem' := by
    change tsupport (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) ⊆ U ∧
      tsupport (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) ⊆ U
    simp
  add_mem' := by
    intro u v hu hv
    constructor
    · exact (tsupport_add u.1.1 v.1.1).trans (Set.union_subset hu.1 hv.1)
    · exact (tsupport_add u.2.1 v.2.1).trans (Set.union_subset hu.2 hv.2)
  smul_mem' := by
    intro a u hu
    constructor
    · exact (tsupport_smul_subset_right (fun _ => a) u.1.1).trans hu.1
    · exact (tsupport_smul_subset_right (fun _ => a) u.2.1).trans hu.2


/-- A type copy records the mass used by the covariance norm. -/
def SourceTestSpace {m : ℝ} (_hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3))) : Type :=
  localizedTimeZeroSources U


variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))


instance : AddCommGroup (SourceTestSpace hm U) :=
  inferInstanceAs (AddCommGroup (localizedTimeZeroSources U))

instance : Module ℝ (SourceTestSpace hm U) :=
  inferInstanceAs (Module ℝ (localizedTimeZeroSources U))

/-- Source test map of type `SourceTestSpace hm U →ₗ[ℝ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def sourceTestMap : SourceTestSpace hm U →ₗ[ℝ] Lp ℂ 2 (oneParticleMeasure m) :=
  (timeZeroLinear hm).comp (localizedTimeZeroSources U).subtype

theorem sourceTestMap_injective : Function.Injective (sourceTestMap hm U) :=
  (timeZeroLinear_injective hm).comp Subtype.val_injective

noncomputable instance : NormedAddCommGroup (SourceTestSpace hm U) :=
  NormedAddCommGroup.induced _ _ (sourceTestMap hm U) (sourceTestMap_injective hm U)

noncomputable instance : InnerProductSpace ℝ (SourceTestSpace hm U) :=
  InnerProductSpace.induced (sourceTestMap hm U)


/-- Source test isometry of type `SourceTestSpace hm U →ₗᵢ[ℝ] Lp ℂ 2 (oneParticleMeasure m) where
__`. -/
noncomputable def sourceTestIsometry : SourceTestSpace hm U →ₗᵢ[ℝ] Lp ℂ 2
  (oneParticleMeasure m) where
  __ := sourceTestMap hm U
  norm_map' _ := rfl

/-- The real Hilbert completion specified in Section 2.2. -/
abbrev SourceHilbert := UniformSpace.Completion (SourceTestSpace hm U)

/-- The source embedding extends the literal time-zero map isometrically. -/
noncomputable def sourceEmbedding : SourceHilbert hm U →ₗᵢ[ℝ] Lp ℂ 2 (oneParticleMeasure m) :=
  (sourceTestIsometry hm U).fromCompletion


end VacuumBellSeparation
