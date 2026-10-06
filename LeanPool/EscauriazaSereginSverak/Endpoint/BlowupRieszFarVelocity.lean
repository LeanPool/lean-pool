/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarUniform

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A sequence with uniformly bounded whole-space `L³` velocity slices has
uniformly small exterior Riesz pressure on each fixed inner cylinder. -/
theorem blowup_riesz_far_velocity_uniform_mass_small
    (v : ℕ → Vec3 × ℝ → Vec3) (R a b : ℝ)
    (hR : 0 < R) (hab : a < b)
    (N : ℝ≥0∞) (hN : N < ⊤)
    (hv : ∀ n k, MemLp (v k) 3
      ((volume : Measure (Vec3 × ℝ)).restrict
        ((CKN.euclideanBall 0 ((n : ℝ) + 1))ᶜ ×ˢ Ioo a b)))
    (hslice : ∀ k, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      MemLp (fun x : Vec3 => v k (x,t)) 3 volume ∧
      eLpNorm (fun x : Vec3 => v k (x,t)) 3 volume ≤ N) :
    let F : ℕ → ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
      fun n k i j =>
        ((CKN.euclideanBall 0 ((n : ℝ) + 1))ᶜ ×ˢ Ioo a b).indicator
          (fun z => v k z i * v k z j)
    ∃ hF : ∀ n k i j, MemLp (F n k i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)),
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ n : ℕ, ∀ k : ℕ,
        (∫⁻ z, ENNReal.ofReal (|CKN.Leray.rieszPressureSpaceTime
            (3 / 2 : ℝ) (by norm_num) (F n k) (hF n k) z|) ^
            (3 / 2 : ℝ)
          ∂((volume.restrict (CKN.euclideanBall 0 R)).prod
            (volume.restrict (Ioo a b)))) ≤ ε := by
  let F : ℕ → ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n k i j =>
      ((CKN.euclideanBall 0 ((n : ℝ) + 1))ᶜ ×ˢ Ioo a b).indicator
        (fun z => v k z i * v k z j)
  have hF : ∀ n k i j, MemLp (F n k i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro n k i j
    exact blowup_exterior_velocity_tensor_memLp (v k)
      ((n : ℝ) + 1) a b (hv n k) i j
  refine ⟨hF, ?_⟩
  apply blowup_rieszPressure_exterior_uniform_mass_small F hF R a b
    (N.toReal ^ 2) hR hab
  · intro n k i j z hz
    have hznot : z ∉ (CKN.euclideanBall 0 ((n : ℝ) + 1))ᶜ ×ˢ Ioo a b := by
      intro hm
      exact hm.1 hz
    exact Set.indicator_of_notMem hznot _
  · intro n k
    exact blowup_exterior_velocity_tensor_slice_bound (v k)
      ((n : ℝ) + 1) a b N hN (hslice k)

end ESS
