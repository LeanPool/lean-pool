/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.HighContrastHomogenization.Support.Sobolev.L2Ambient

/-!
# DomainMaps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Fixed-ambient domain maps

This module places every scalar domain `L²` space inside the single ambient
space `L²(ℝᵈ)`.

Main definitions and results:

* `AmbientScalarL2` is the fixed scalar ambient space.
* `restrictToDomain` restricts an ambient function to `U`.
* `zeroExtendFromDomain` is the isometric zero extension from `U`.
* `ambientSupportProjection` is their composite; it acts by the indicator of
  `U`, is idempotent and contractive, and is complementary to the projection
  onto `Uᶜ`.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- Scalar-valued `L²` on the fixed ambient space `ℝᵈ`. -/
noncomputable abbrev AmbientScalarL2 (d : ℕ) :=
  Lp ℝ 2 (volume : Measure (Vec d))

/-- Restrict an ambient `L²` function to a domain. -/
noncomputable def restrictToDomain (U : Set (Vec d)) :
    AmbientScalarL2 d →L[ℝ] ScalarL2 U :=
  LpToLpRestrictCLM (Vec d) ℝ ℝ volume 2 U

theorem restrictToDomain_coeFn (U : Set (Vec d)) (f : AmbientScalarL2 d) :
    restrictToDomain U f =ᵐ[volumeMeasureOn U] f :=
  LpToLpRestrictCLM_coeFn ℝ U f

theorem zeroExtendFromDomain_memLp (hU : MeasurableSet U)
    (f : ScalarL2 U) : MemLp (U.indicator fun x ↦ f x) 2 volume := by
  rw [memLp_indicator_iff_restrict hU]
  exact Lp.memLp f

/-- Extension by zero from a domain as a linear map on L² classes. -/
noncomputable def zeroExtendFromDomainLinearMap (hU : MeasurableSet U) :
    ScalarL2 U →ₗ[ℝ] AmbientScalarL2 d where
  toFun f := (zeroExtendFromDomain_memLp hU f).toLp (U.indicator fun x ↦ f x)
  map_add' f g := by
    classical
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU (f + g)),
       MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU f),
       MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU g),
       Lp.coeFn_add
         ((zeroExtendFromDomain_memLp hU f).toLp (U.indicator fun x ↦ f x))
         ((zeroExtendFromDomain_memLp hU g).toLp (U.indicator fun x ↦ g x)),
       ae_restrict_iff' hU |>.mp (Lp.coeFn_add f g)] with x hfg hf hg hsum hadd
    rw [hfg, hsum, Pi.add_apply, hf, hg, Set.indicator_apply, Set.indicator_apply,
      Set.indicator_apply]
    by_cases hx : x ∈ U
    · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, hadd hx, Pi.add_apply]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx, zero_add]
  map_smul' c f := by
    classical
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU (c • f)),
       MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU f),
       Lp.coeFn_smul c
         ((zeroExtendFromDomain_memLp hU f).toLp (U.indicator fun x ↦ f x)),
       ae_restrict_iff' hU |>.mp (Lp.coeFn_smul c f)] with x hcf hf hambient hsmul
    rw [RingHom.id_apply, hcf, hambient, Pi.smul_apply, hf,
      Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ U
    · rw [ite_eq_left hx, ite_eq_left hx, hsmul hx, Pi.smul_apply]
    · rw [ite_eq_right hx, ite_eq_right hx, smul_zero]

/-- Isometric zero extension from `L²(U)` into ambient `L²(ℝᵈ)`. -/
noncomputable def zeroExtendFromDomain (hU : MeasurableSet U) :
    ScalarL2 U →ₗᵢ[ℝ] AmbientScalarL2 d where
  toLinearMap := zeroExtendFromDomainLinearMap hU
  norm_map' f := by
    rw [show zeroExtendFromDomainLinearMap hU f =
        (zeroExtendFromDomain_memLp hU f).toLp (U.indicator fun x ↦ f x) from rfl,
      Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hU, Lp.norm_def]

theorem zeroExtendFromDomain_coeFn (hU : MeasurableSet U) (f : ScalarL2 U) :
    zeroExtendFromDomain hU f =ᵐ[volume] U.indicator fun x ↦ f x :=
  MemLp.coeFn_toLp (zeroExtendFromDomain_memLp hU f)

@[simp] theorem restrictToDomain_zeroExtendFromDomain
    (hU : MeasurableSet U) (f : ScalarL2 U) :
    restrictToDomain U (zeroExtendFromDomain hU f) = f := by
  apply Lp.ext
  filter_upwards
    [restrictToDomain_coeFn U (zeroExtendFromDomain hU f),
     ae_restrict_of_ae (zeroExtendFromDomain_coeFn hU f),
     self_mem_ae_restrict hU] with x hr hz hx
  rw [hr, hz, Set.indicator_of_mem]
  exact hx

/-- The ambient projection onto functions supported in `U`. -/
noncomputable def ambientSupportProjection (hU : MeasurableSet U) :
    AmbientScalarL2 d →L[ℝ] AmbientScalarL2 d :=
  (zeroExtendFromDomain hU).toContinuousLinearMap.comp (restrictToDomain U)

@[simp] theorem ambientSupportProjection_idempotent (hU : MeasurableSet U)
    (f : AmbientScalarL2 d) :
    ambientSupportProjection hU (ambientSupportProjection hU f) =
      ambientSupportProjection hU f := by
  change zeroExtendFromDomain hU
      (restrictToDomain U (zeroExtendFromDomain hU (restrictToDomain U f))) =
    zeroExtendFromDomain hU (restrictToDomain U f)
  rw [restrictToDomain_zeroExtendFromDomain]

end DivergenceFormProcess.Form
