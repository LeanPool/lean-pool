/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyScaling
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsRestriction

/-!
# Suitability on a fixed rescaled cylinder

The original suitable solution restricts and rescales to every fixed bounded
past cylinder once the scale is small enough (`prop:blowup-limit`).
-/

public section


open Set Filter CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- On each sufficiently small fixed cylinder, the zero-extended fields
agree pointwise with the ordinary rescalings used for suitability. -/
theorem blowupFields_eq_rescale_on_cylinder
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ r ρ a : ℝ)
    (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r)
    (hspace : r * ρ < 1 / 4)
    (htime : r ^ 2 * (-a) < 3 / 4) :
    Set.EqOn (blowupVelocity x₀ t₀ r u)
        (parabolicRescaleVelocity x₀ t₀ r u)
        (vec3Ball 0 ρ ×ˢ Ioo a 0) ∧
      Set.EqOn (blowupGradient x₀ t₀ r Du)
        (parabolicRescaleGradient x₀ t₀ r Du)
        (vec3Ball 0 ρ ×ˢ Ioo a 0) ∧
      Set.EqOn (blowupPressure x₀ t₀ r p)
        (parabolicRescalePressure x₀ t₀ r p)
        (vec3Ball 0 ρ ×ˢ Ioo a 0) := by
  have hdomain : vec3Ball 0 ρ ×ˢ Ioo a 0 ⊆
      blowupDomain x₀ t₀ r :=
    blowupCylinder_subset_domain x₀ t₀ r ρ a hx₀ ht₀ hr
      (by linarith only [hspace]) htime
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact blowupVelocity_eq_of_mem x₀ t₀ r u z (hdomain hz)
  · intro z hz
    exact blowupGradient_eq_of_mem x₀ t₀ r Du z (hdomain hz)
  · intro z hz
    exact blowupPressure_eq_of_mem x₀ t₀ r p z (hdomain hz)

/-- Navier--Stokes rescaling preserves suitability on a fixed past cylinder
inside the rescaled source region. -/
theorem blowupRescale_suitable_on_cylinder
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (x₀ : Vec3) (t₀ r ρ a : ℝ)
    (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (ha : a < 0)
    (hspace : r * ρ < 1 / 4)
    (htime : r ^ 2 * (-a) < 3 / 4) :
    IsSuitableWeakSolution (vec3Ball 0 ρ) (Ioo a 0) 3
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du)
      (parabolicRescalePressure x₀ t₀ r p)
      (0 : ParabolicPoint → Vec3) := by
  have hgeom := blowupCylinder_subset_suitableDomain
    x₀ t₀ r ρ a hx₀ ht₀ hr hspace htime
  have hΩ : vec3Ball 0 ρ ⊆
      CKN.rescaledSpace r x₀ (vec3Ball 0 (3 / 4 : ℝ)) := by
    intro x hx
    have ht : a / 2 ∈ Ioo a 0 := by
      constructor <;> linarith only [ha]
    have h := hgeom (show (x, a / 2) ∈ vec3Ball 0 ρ ×ˢ Ioo a 0 from ⟨hx, ht⟩)
    exact h.1
  have hI : Ioo a 0 ⊆ CKN.rescaledTime r t₀ (Ioo (-1) 0) := by
    intro t ht
    have hx : (0 : Vec3) ∈ vec3Ball 0 ρ := by
      simpa only [mem_vec3Ball, sub_zero, vec3EuclideanNorm_zero] using hρ
    have h := hgeom (show ((0 : Vec3), t) ∈
      vec3Ball 0 ρ ×ˢ Ioo a 0 from ⟨hx, ht⟩)
    exact h.2
  have hscaled := isSuitableWeakSolution_parabolicRescale
    u Du p (0 : ParabolicPoint → Vec3) hSuitable x₀ t₀ r hr
  have hscaled0 : IsSuitableWeakSolution
      (CKN.rescaledSpace r x₀ (vec3Ball 0 (3 / 4 : ℝ)))
      (CKN.rescaledTime r t₀ (Ioo (-1) 0)) 3
      (parabolicRescaleVelocity x₀ t₀ r u)
      (parabolicRescaleGradient x₀ t₀ r Du)
      (parabolicRescalePressure x₀ t₀ r p)
      (0 : ParabolicPoint → Vec3) := by
    have hforce :
        (fun z => r ^ 3 • (0 : ParabolicPoint → Vec3)
          (parabolicTranslate x₀ t₀ (parabolicScale r z))) =
          (0 : ParabolicPoint → Vec3) := by
      funext z
      simp
    rw [hforce] at hscaled
    exact hscaled
  exact isSuitableWeakSolution_restrict hscaled0
    (isOpen_vec3Ball 0 ρ) isOpen_Ioo ordConnected_Ioo hΩ hI

/-- The ordinary rescalings form a tail of suitable solutions on each fixed
bounded past cylinder. -/
theorem blowupRescale_eventually_suitable_on_cylinder
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (x₀ : Vec3) (t₀ ρ a : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (hρ : 0 < ρ) (ha : a < 0) :
    ∀ᶠ k in atTop,
      IsSuitableWeakSolution (vec3Ball 0 ρ) (Ioo a 0) 3
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du)
        (parabolicRescalePressure x₀ t₀ (r k) p)
        (0 : ParabolicPoint → Vec3) := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hspaceLim : Tendsto (fun k => r k * ρ) atTop (nhds 0) := by
    simpa only [zero_mul] using hr0.mul_const ρ
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  have hspace : ∀ᶠ k in atTop, r k * ρ < 1 / 4 :=
    hspaceLim.eventually (eventually_lt_nhds (by norm_num))
  have htime : ∀ᶠ k in atTop, (r k) ^ 2 * (-a) < 3 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hspace, htime] with k hsk htk
  exact blowupRescale_suitable_on_cylinder u Du p hSuitable
    x₀ t₀ (r k) ρ a hxnorm ht₀ (hr k) hρ ha hsk htk

end ESS
