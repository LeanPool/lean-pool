/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarTensor

/-!
# Blowup Riesz Far Uniform

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- The far-field pressure estimate is uniform over a sequence of tensors
with the same global slice bound. -/
theorem blowup_rieszPressure_exterior_uniform_mass_small
    (F : ℕ → ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ n k i j, MemLp (F n k i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (R a b M : ℝ) (hR : 0 < R) (hab : a < b)
    (hzero : ∀ (n k : ℕ) i j z,
      z.1 ∈ CKN.euclideanBall 0 ((n : ℝ) + 1) → F n k i j z = 0)
    (hinput : ∀ n k, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∀ i j : Fin 3,
        lpNorm (fun x : Vec3 => F n k i j (x,t))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ n : ℕ, ∀ k : ℕ,
      (∫⁻ z, ENNReal.ofReal (|CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) (F n k) (hF n k) z|) ^
          (3 / 2 : ℝ)
        ∂((volume.restrict (CKN.euclideanBall 0 R)).prod
          (volume.restrict (Ioo a b)))) ≤ ε := by
  obtain ⟨C, hC, hBound⟩ := blowup_rieszPressure_exterior_mass_bound
  let D : ℝ≥0∞ := ENNReal.ofReal
    (CKN.Leray.rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) * (9 * M))
  let V : ℝ≥0∞ := volume (CKN.euclideanBall (0 : Vec3) R)
  let T : ℝ≥0∞ := volume (Ioo a b)
  have hD : D < ⊤ := ENNReal.ofReal_lt_top
  have hV : V < ⊤ := CKN.volume_euclideanBall_lt_top 0 hR
  have hT : T < ⊤ := measure_Ioo_lt_top
  have hRate := blowup_far_pressure_mass_bound_tendsto_zero
    C D V T hC hD hV hT
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ 3 * ((n : ℝ) + 1) / 4 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * R)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith only [hN, hcast, hR]
  intro ε hε
  have hrhs := (ENNReal.tendsto_nhds_zero.mp hRate) ε hε
  obtain ⟨n, hn, hsmall⟩ := (hlarge.and hrhs).exists
  refine ⟨n, fun k => ?_⟩
  have hL : 0 < (n : ℝ) + 1 := by positivity
  have hmass := hBound (F n k) (hF n k) ((n : ℝ) + 1) R a b M
    hL hR hn hab (hzero n k) (hinput n k)
  exact hmass.trans (by simpa only [T, D, V] using hsmall)

end ESS
