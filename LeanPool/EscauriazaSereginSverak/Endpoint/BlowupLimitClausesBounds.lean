/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitLocalEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourcePressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsFromSource
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitable

/-!
# Uniform bounds of the blow-up sequence

Clauses (a) and the `L^{10/3}` part of (b) of `prop:blowup-limit`, for the
zero-extended rescaled fields `v^k`, `Dv^k`, `p^k` themselves: on every bounded
past cylinder `B_R × (a, 0)`, for all sufficiently large `k`, the pressure is
bounded in `L^{3/2}`, the gradient in `L²`, and the velocity in `L^{10/3}`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- For all sufficiently large `k` the zero-extended rescaled fields agree
with the ordinary Navier–Stokes rescalings on a fixed bounded past cylinder. -/
theorem blowupLimitClauses_eventually_eqOn_rescale
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) {x₀ : Vec3} {t₀ : ℝ} {r : ℕ → ℝ}
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0)) (R a : ℝ) :
    ∀ᶠ k in atTop,
      Set.EqOn (blowupVelocity x₀ t₀ (r k) u)
          (parabolicRescaleVelocity x₀ t₀ (r k) u) (vec3Ball 0 R ×ˢ Ioo a 0) ∧
        Set.EqOn (blowupGradient x₀ t₀ (r k) Du)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) (vec3Ball 0 R ×ˢ Ioo a 0) ∧
        Set.EqOn (blowupPressure x₀ t₀ (r k) p)
          (parabolicRescalePressure x₀ t₀ (r k) p) (vec3Ball 0 R ×ˢ Ioo a 0) := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hs : Tendsto (fun k => r k * R) atTop (nhds 0) := by
    simpa using hr0.mul_const R
  have ht : Tendsto (fun k => r k ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  filter_upwards [hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 4))] with k hk1 hk2
  exact blowupFields_eq_rescale_on_cylinder u Du p x₀ t₀ (r k) R a hxnorm ht₀ (hr k) hk1 hk2

/-- Clause (a) of `prop:blowup-limit`: on every bounded past cylinder the
rescaled pressures are bounded in `L^{3/2}` and the rescaled gradients in
`L²`, for all sufficiently large `k`. -/
theorem blowupLimitClauses_energy_pressure_bounds
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      IntegrableOn (fun z => |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ))
        (vec3Ball 0 R ×ˢ Ioo a 0) ∧
      IntegrableOn (fun z => spatialGradientSq (blowupVelocity x₀ t₀ (r k) u)
        (blowupGradient x₀ t₀ (r k) Du) z) (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) ∧
      (∫ z in vec3Ball 0 R ×ˢ Ioo a 0,
          |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ)) +
        (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0),
          spatialGradientSq (blowupVelocity x₀ t₀ (r k) u)
          (blowupGradient x₀ t₀ (r k) Du) z) ≤ C := by
  obtain ⟨-, Cg, Cp, hCg, hCp, hev⟩ := blowup_limit_local_energy_pressure_of_source_data
    hu hDu hp hL2 henergy hpLp hL3 hgrad (fun ψ hψ => hS2 ψ hψ) hS3 x₀ t₀ r hx₀ ht₀ hr hr0
    R a hR ha
  have hball : CKN.euclideanBall (0 : Vec3) R = vec3Ball 0 R :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hR
  have hQm' : MeasurableSet (spaceTimeSet (vec3Ball (0 : Vec3) R) (Ioo a 0)) :=
    (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo
  refine ⟨Cp + Cg / 2, by positivity, ?_⟩
  filter_upwards [hev, blowupLimitClauses_eventually_eqOn_rescale u Du p hx₀ ht₀ hr hr0 R a]
    with k hk heq
  obtain ⟨hint, hgradle, hpmem, hple⟩ := hk
  have hint' : IntegrableOn (fun z => spatialGradientSq
      (parabolicRescaleVelocity x₀ t₀ (r k) u)
      (parabolicRescaleGradient x₀ t₀ (r k) Du) z) (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) := by
    rw [← hball]
    exact hint
  have hgradle' : 2 * (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0), spatialGradientSq
      (parabolicRescaleVelocity x₀ t₀ (r k) u)
      (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ Cg := by
    rw [← hball]
    exact hgradle
  have hpoint : ∀ z ∈ spaceTimeSet (vec3Ball (0 : Vec3) R) (Ioo a 0),
      spatialGradientSq (blowupVelocity x₀ t₀ (r k) u) (blowupGradient x₀ t₀ (r k) Du) z =
        spatialGradientSq (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z := by
    intro z hz
    unfold spatialGradientSq
    rw [heq.2.1 hz]
  have hEqInt : (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0), spatialGradientSq
      (blowupVelocity x₀ t₀ (r k) u) (blowupGradient x₀ t₀ (r k) Du) z) =
      ∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0), spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z :=
    setIntegral_congr_fun hQm' hpoint
  have hpint : IntegrableOn (fun z => |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ))
      (vec3Ball 0 R ×ˢ Ioo a 0) := by
    have h := hpmem.integrable_norm_rpow (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
    simp only [Real.norm_eq_abs, ENNReal.toReal_div, ENNReal.toReal_ofNat] at h
    exact h
  refine ⟨hpint, hint'.congr_fun (fun z hz => (hpoint z hz).symm) hQm', ?_⟩
  rw [hEqInt]
  linarith only [hple, hgradle']

/-- The `L^{10/3}` part of clause (b) of `prop:blowup-limit`: on every bounded
past cylinder the zero-extended rescaled velocities are bounded in
`L^{10/3}` for all sufficiently large `k`. -/
theorem blowupLimitClauses_tenThirds_bound
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (blowupVelocity x₀ t₀ (r k) u) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (blowupVelocity x₀ t₀ (r k) u) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  obtain ⟨hSuitable, hind, hp₁, ⟨Mᵤ, hMᵤ, hsourceU⟩, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩ :=
    blowupLimitAssembly_source_pressure_data hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
  obtain ⟨B, hB, hev⟩ := blowupRescale_eventually_tenThirds_of_source_slices u Du p _
    hSuitable hind Mᵤ hMᵤ hsourceU hp₁ Mₚ hMₚ hsourceP hp₂ hharm x₀ t₀ r hx₀ ht₀ hr hr0
    R a hR ha
  have hQm : MeasurableSet (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0) :=
    (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev, blowupLimitClauses_eventually_eqOn_rescale u Du p hx₀ ht₀ hr hr0 R a]
    with k hk heq
  have hae : blowupVelocity x₀ t₀ (r k) u =ᵐ[volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)]
      parabolicRescaleVelocity x₀ t₀ (r k) u := by
    filter_upwards [ae_restrict_mem hQm] with z hz
    exact heq.1 hz
  exact ⟨(memLp_congr_ae hae).2 hk.1, (eLpNorm_congr_ae hae).trans_le hk.2⟩

end ESS

end
