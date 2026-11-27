/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LpMultiplication
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.Units

/-!
# Continuous functional calculus of actual bounded L2 multipliers

A measurable function taking values in a compact real set induces a
contractive unital real algebra homomorphism from the continuous functions
on that set to actual L2 multiplication operators. Polynomial uniqueness
identifies it with Mathlib's CFC on a spectral superset. No assertion that
every pointwise value belongs to the operator spectrum is needed, and the
measure is arbitrary, including zero.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace

theorem hilbertOperator_realCFC
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {K : Set ℝ} [CompactSpace K] (r : α → K) (hr : Measurable r)

local instance :
    IsometricContinuousFunctionalCalculus ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) IsSelfAdjoint :=
  hilbertOperator_realCFC

include hr in
theorem memLp_continuousMultiplier (f : C(K, ℝ)) :
    MemLp (fun x => (f (r x) : ℂ)) ⊤ μ := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp f.continuous).measurable.comp hr).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Function.comp_apply, Complex.norm_real] using f.norm_coe_le_norm (r x)

/-- Continuous linear map for the continuous multiplier, of type `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/
noncomputable def continuousMultiplier (f : C(K, ℝ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpMultiplication μ (fun x => (f (r x) : ℂ)) (memLp_continuousMultiplier μ r hr f)

theorem continuousMultiplier_ae (f : C(K, ℝ)) (v : Lp ℂ 2 μ) :
    continuousMultiplier μ r hr f v =ᵐ[μ] fun x => (f (r x) : ℂ) * v x :=
  lpMultiplication_ae μ _ _ v

theorem continuousMultiplier_norm_le (f : C(K, ℝ)) :
    ‖continuousMultiplier μ r hr f‖ ≤ ‖f‖ := by
  apply lpMultiplication_norm_le μ _ _ (norm_nonneg f)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Function.comp_apply, Complex.norm_real] using f.norm_coe_le_norm (r x)

theorem continuousMultiplier_one : continuousMultiplier μ r hr 1 = 1 := by
  exact lpMultiplication_one μ

theorem continuousMultiplier_add (f g : C(K, ℝ)) :
    continuousMultiplier μ r hr (f + g) =
      continuousMultiplier μ r hr f + continuousMultiplier μ r hr g := by
  unfold continuousMultiplier
  calc
    _ = lpMultiplication μ ((fun x => (f (r x) : ℂ)) + (fun x => (g (r x) : ℂ)))
        ((memLp_continuousMultiplier μ r hr f).add (memLp_continuousMultiplier μ r hr g)) := by
      apply lpMultiplication_congr
      exact Filter.Eventually.of_forall (fun x => by simp)
    _ = _ := lpMultiplication_add μ _ _ _ _

theorem continuousMultiplier_mul (f g : C(K, ℝ)) :
    continuousMultiplier μ r hr (f * g) =
      continuousMultiplier μ r hr f * continuousMultiplier μ r hr g := by
  have hw : MemLp ((fun x => (f (r x) : ℂ)) * (fun x => (g (r x) : ℂ))) ⊤ μ := by
    change MemLp (fun x => (f (r x) : ℂ) * (g (r x) : ℂ)) ⊤ μ
    simpa only [Complex.ofReal_mul, ContinuousMap.mul_apply] using
      memLp_continuousMultiplier μ r hr (f * g)
  unfold continuousMultiplier
  calc
    _ = lpMultiplication μ ((fun x => (f (r x) : ℂ)) * (fun x => (g (r x) : ℂ))) hw := by
      apply lpMultiplication_congr
      exact Filter.Eventually.of_forall (fun x => by simp)
    _ = _ := lpMultiplication_mul μ _ _ _ _ hw

theorem continuousMultiplier_const (c : ℝ) :
    continuousMultiplier μ r hr (.const K c) = c • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [continuousMultiplier_ae μ r hr (.const K c) v, Lp.coeFn_smul c v]
    with x hx hs
  change continuousMultiplier μ r hr (.const K c) v x = (c • v) x
  rw [hx, hs]
  simp only [ContinuousMap.const_apply, Pi.smul_apply, Complex.real_smul]

/-- Continuous linear map for the continuous multiplier hom, of type `C(K, ℝ) →ₐ[ℝ] (Lp ℂ 2 μ →L[ℂ]
Lp ℂ 2 μ) where toFun`. -/
noncomputable def continuousMultiplierHom : C(K, ℝ) →ₐ[ℝ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := continuousMultiplier μ r hr
  map_one' := continuousMultiplier_one μ r hr
  map_zero' := by
    change continuousMultiplier μ r hr (.const K 0) = 0
    rw [continuousMultiplier_const]
    exact zero_smul ℝ (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
  map_add' := continuousMultiplier_add μ r hr
  map_mul' := continuousMultiplier_mul μ r hr
  commutes' c := by
    have he : algebraMap ℝ C(K, ℝ) c = .const K c := by ext x; simp
    rw [he, continuousMultiplier_const, Algebra.algebraMap_eq_smul_one]

theorem continuousMultiplierHom_continuous : Continuous (continuousMultiplierHom μ r hr) := by
  let L := (continuousMultiplierHom μ r hr).toLinearMap.mkContinuous 1
    (fun f => by
      change ‖continuousMultiplier μ r hr f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using continuousMultiplier_norm_le μ r hr f)
  exact L.continuous

theorem continuousMultiplier_isSelfAdjoint (f : C(K, ℝ)) :
    IsSelfAdjoint (continuousMultiplier μ r hr f) :=
  lpMultiplication_isSelfAdjoint μ _ _
    (Filter.Eventually.of_forall fun _ => Complex.conj_ofReal _)

theorem continuousMultiplier_spectrum_subset :
    spectrum ℝ (continuousMultiplier μ r hr (ContinuousMap.restrict K
      (ContinuousMap.id ℝ))) ⊆ K := by
  intro t ht
  change t ∈ spectrum ℝ ((continuousMultiplierHom μ r hr) (ContinuousMap.restrict K
    (ContinuousMap.id ℝ))) at ht
  have hh : t ∈ spectrum ℝ (ContinuousMap.restrict K (ContinuousMap.id ℝ)) :=
    AlgHom.spectrum_apply_subset (continuousMultiplierHom μ r hr) (ContinuousMap.restrict K
      (ContinuousMap.id ℝ)) ht
  rw [ContinuousMap.spectrum_eq_range] at hh
  obtain ⟨x, rfl⟩ := hh
  exact x.property

theorem continuousMultiplierHom_eq_cfcHomSuperset :
    continuousMultiplierHom μ r hr =
      (cfcHomSuperset (continuousMultiplier_isSelfAdjoint μ r hr (ContinuousMap.restrict K
        (ContinuousMap.id ℝ)))
        (continuousMultiplier_spectrum_subset μ r hr)).toAlgHom := by
  apply ContinuousMap.algHom_ext_map_X (continuousMultiplierHom_continuous μ r hr)
    (cfcHomSuperset_continuous _ _)
  rw [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_X_eq_restrict_id]
  exact (cfcHomSuperset_id _ _).symm

theorem cfc_continuousMultiplier (f : ℝ → ℝ) (hf : ContinuousOn f K) :
    cfc f (continuousMultiplier μ r hr (ContinuousMap.restrict K (ContinuousMap.id ℝ))) =
      continuousMultiplier μ r hr ⟨fun x => f x, hf.domRestrict⟩ := by
  let hA := continuousMultiplier_isSelfAdjoint μ r hr (ContinuousMap.restrict K
    (ContinuousMap.id ℝ))
  let hs := continuousMultiplier_spectrum_subset μ r hr
  rw [cfc_apply f _ hA (hf.mono hs)]
  have he := congrArg (fun φ : C(K, ℝ) →ₐ[ℝ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =>
    φ ⟨fun x => f x, hf.domRestrict⟩) (continuousMultiplierHom_eq_cfcHomSuperset μ r hr)
  exact he.symm

end VacuumBellSeparation
