/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialErrorFar

/-!
# Flatness on the initial transition near the center

Integral flatness of every order bounds the mass in a fourth-root
spatial ball during the initial cutoff transition.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Every integral flatness order yields an arbitrarily high power of the
initial transition length on a shrinking spatial ball. -/
theorem uc_initial_near_mass_le
    (ρ : ℝ) (hρ : 4 ≤ ρ)
    (v : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (ucCylinder ρ) volume)
    (hflat : UCIntegralFlatness 0 ρ 2 v)
    (N : ℕ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        let r := Real.sqrt (Real.sqrt ε)
        (∫ z in spaceTimeSet (vec3Ball 0 r) (Icc ε (2 * ε)),
          vec3EuclideanNorm (v z) ^ 2) ≤ C * ε ^ N := by
  obtain ⟨C, r₀, hC, hr₀, hflatN⟩ := hflat (4 * N)
  let δ := min (1 / 4 : ℝ) (r₀ ^ 4)
  have hδ : 0 < δ := lt_min (by norm_num) (pow_pos hr₀ _)
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε hεδ
  dsimp
  let r := Real.sqrt (Real.sqrt ε)
  obtain ⟨hr, hrρ, hr4, htime⟩ :=
    uc_initial_error_fourth_root_geometry hρ hε
      (hεδ.trans_le (min_le_left _ _))
  have hr0 : r < r₀ := by
    have hεr₀ : ε < r₀ ^ 4 := hεδ.trans_le (min_le_right _ _)
    by_contra hnot
    have hle : r₀ ≤ r := le_of_not_gt hnot
    have hpow : r₀ ^ 4 ≤ r ^ 4 := by gcongr
    linarith only [hεr₀, hpow, hr4]
  have hr2 : r ^ 2 < 2 := by
    have hεsmall : ε < 1 / 4 := hεδ.trans_le (min_le_left _ _)
    nlinarith only [hr, hr4, hεsmall]
  have hQsub : spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2)) ⊆
      ucCylinder ρ := by
    intro z hz
    exact ⟨(vec3Ball_mono hrρ.le) hz.1,
      ⟨hz.2.1, hz.2.2.trans hr2⟩⟩
  have hNsub : spaceTimeSet (vec3Ball 0 r) (Icc ε (2 * ε)) ⊆
      spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2)) := by
    intro z hz
    exact ⟨hz.1, ⟨hε.trans_le hz.2.1, hz.2.2.trans_lt htime⟩⟩
  have hIntQ : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2))) volume :=
    hInt.mono_set hQsub
  have hnonneg : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2)))),
      (0 : ℝ) ≤ vec3EuclideanNorm (v z) ^ 2 := by
    filter_upwards [] with z
    exact sq_nonneg _
  have hmass := setIntegral_mono_set hIntQ hnonneg
    (Filter.Eventually.of_forall hNsub)
  have hflatBound := hflatN r hr
    (show r < min ρ (min (Real.sqrt 2) r₀) by
      have hr2root : r < Real.sqrt 2 := by
        have hsqrt2 : 0 < Real.sqrt 2 := by positivity
        have hsqrt2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
        nlinarith only [hr, hr2, hsqrt2, hsqrt2sq]
      exact lt_min hrρ (lt_min hr2root hr0))
  have hpow : r ^ (4 * N) = ε ^ N := by
    rw [pow_mul, hr4]
  exact hmass.trans (by simpa only [hpow] using hflatBound)

end ESS
