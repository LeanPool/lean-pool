/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorRescale

/-!
# Vanishing of the vorticity of the blow-up limit

For a suitable solution on `ℝ³ × (-12, 0)` whose weak vorticity vanishes on the
half-space `{x₃ > R₂}` throughout `(-2, 0)`, CKN's partial regularity and the
time projection (`lem:time-projection`) give, for almost every time, closed
balls of regular points on short time intervals; the continuation argument of
`thm:ess-local` (time-slice and spatial unique continuation) then makes the
weak vorticity vanish on almost
every time slice.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak vorticity of a suitable solution on `ℝ³ × (-12, 0)` vanishing on
the half-space `{x₃ > R₂}` over `(-2, 0)` vanishes on almost every time slice
of `(-2, 0)`. -/
theorem essLocal_interiorVorticityZero
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3}
    {q : ParabolicPoint → ℝ}
    (hsws : IsSuitableWeakSolution Set.univ (Ioo (-12 : ℝ) 0) 3 U DU q
      (0 : ParabolicPoint → Vec3))
    (R₂ : ℝ) (hR₂ : 0 < R₂)
    (hseed : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0))), weakVorticity DU z = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      (fun x : Vec3 => weakVorticity DU (x, t)) =ᵐ[volume] 0 := by
  have hRegularTimes := timeProjection_regularNeighborhoods_of_suitable
    (Ioo (-12 : ℝ) 0) U DU q hsws
  let G : Set ℝ := {t | t ∈ Ioo (-12 : ℝ) 0 → ∀ ρ : ℝ, 0 < ρ → ∃ δ > 0,
    closure (vec3Ball (0 : Vec3) ρ) ×ˢ Ioo (t - δ) (t + δ) ⊆
      regularPointLocus (Ioo (-12 : ℝ) 0) U}
  have hGnull : (volume : Measure ℝ) Gᶜ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hRegularTimes] with t ht htG
    exact htG ht
  -- the open set of points near which the weak vorticity vanishes
  let W : Set ParabolicPoint := {z | ∃ N : Set ParabolicPoint, IsOpen N ∧ z ∈ N ∧
    ∀ᵐ y ∂(volume.restrict N), weakVorticity DU y = 0}
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨N, hNopen, hzN, hN⟩
    exact ⟨N, fun y hy => ⟨N, hNopen, hy, hN⟩, hNopen, hzN⟩
  have hWae : ∀ᵐ y ∂(volume.restrict W), weakVorticity DU y = 0 :=
    essLocal_ae_restrict_of_local hWopen.measurableSet fun z hz => hz
  let S : Set ParabolicPoint := spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0)
  have hSmeas : MeasurableSet S :=
    (isOpen_spaceTimeSet _ _ isOpen_univ isOpen_Ioo).measurableSet
  have hcover : ∀ z ∈ S, z.2 ∈ G → z ∈ W := by
    rintro z ⟨-, hz2⟩ hzG
    let ρ : ℝ := R₂ + 1 + vec3EuclideanNorm z.1
    have hρ : R₂ < ρ := by
      have := vec3EuclideanNorm_nonneg z.1
      dsimp [ρ]
      linarith only [this]
    have hreg := hzG ⟨by linarith only [hz2.1], hz2.2⟩
    obtain ⟨ε, hε, hzero⟩ :=
      essLocal_regularSlab_vorticityZero hsws R₂ ρ hR₂ hρ hseed z.2 hz2 hreg
    refine ⟨spaceTimeSet (vec3Ball (0 : Vec3) ρ) (Ioo (z.2 - ε) (z.2 + ε)),
      isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo, ⟨?_, ?_, ?_⟩, hzero⟩
    · change vec3EuclideanNorm (z.1 - 0) < ρ
      rw [sub_zero]
      dsimp [ρ]
      linarith only [hR₂]
    · linarith only [hε]
    · linarith only [hε]
  have hbadNull : (volume : Measure ParabolicPoint)
      ((Set.univ : Set Vec3) ×ˢ Gᶜ) = 0 := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)) (Set.univ ×ˢ Gᶜ) = 0
    rw [Measure.prod_prod, hGnull, mul_zero]
  have hspace : ∀ᵐ z ∂(volume.restrict S), weakVorticity DU z = 0 := by
    refine (ae_restrict_iff' hSmeas).2 ?_
    have hW' := (ae_restrict_iff' hWopen.measurableSet).1 hWae
    have hbad' := measure_eq_zero_iff_ae_notMem.1 hbadNull
    filter_upwards [hW', hbad'] with z hzW hzbad hzS
    refine hzW (hcover z hzS ?_)
    by_contra hzG
    exact hzbad ⟨mem_univ _, hzG⟩
  -- slices
  have hprod : (volume : Measure ParabolicPoint).restrict S =
      (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo (-2 : ℝ) 0)) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      ((Set.univ : Set Vec3) ×ˢ Ioo (-2 : ℝ) 0) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod] at hspace
  have hswap := (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ).restrict (Ioo (-2 : ℝ) 0))
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hspace
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with t ht
  filter_upwards [ht] with x hx
  exact hx

end ESS
