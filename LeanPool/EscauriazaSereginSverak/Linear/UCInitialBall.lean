/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCDecay
public import LeanPool.EscauriazaSereginSverak.Linear.UCRestriction

/-!
# Initial trace from a Gaussian box estimate

The exponential box estimate in `lem:uc-gaussian` gives a zero trace at
every output point away from its center.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A positive Gaussian exponent in the shrinking-box estimate forces a
zero boundary value (`thm:uc`). -/
theorem uc_gaussian_box_bound_to_trace
    (R T : ℝ) (hT : 0 < T)
    (x₀ x : Vec3) (hx : x ∈ vec3Ball x₀ R)
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (spaceTimeSet (vec3Ball x₀ R) (Ico 0 T)))
    (hwloc : LocallyIntegrableOn w
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)) volume)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤)
    (b A γ : ℝ) (hb : 0 < b) (hγ : 0 < γ)
    (hbox : ∀ t : ℝ, 0 < t → t < γ →
      (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)),
        vec3EuclideanNorm (w z) ^ 2) ≤
          A * Real.exp (-(b / t))) :
    w (x, 0) = 0 := by
  let F (t : ℝ) : ℝ := Real.rpow t (-(5 / 2 : ℝ)) *
    ∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t))) (Ioo t (2 * t)),
      vec3EuclideanNorm (w z) ^ 2
  let G (t : ℝ) : ℝ := |A| *
    (Real.rpow t (-(5 / 2 : ℝ)) * Real.exp (-(b / t)))
  have hG : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [G] using
      (uc_exp_dominates_inverse_power b (5 / 2) hb).const_mul |A|
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < γ :=
    (eventually_lt_nhds hγ).filter_mono nhdsWithin_le_nhds
  have hFnonneg : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 ≤ F t := by
    filter_upwards [hpos] with t ht
    dsimp [F]
    apply mul_nonneg (Real.rpow_nonneg ht.le _)
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hFG : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), F t ≤ G t := by
    filter_upwards [hpos, hsmall] with t ht htγ
    have hI := hbox t ht htγ
    have hA : A * Real.exp (-(b / t)) ≤
        |A| * Real.exp (-(b / t)) :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
    have hpow : 0 ≤ Real.rpow t (-(5 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    have hI' := mul_le_mul_of_nonneg_left (hI.trans hA) hpow
    simpa only [F, G, mul_assoc, mul_left_comm, mul_comm] using hI'
  have hF : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hG hFnonneg hFG
  exact uc_shrinking_average_to_trace_on_cylinder R T hT x₀ x hx w
    hcont hwloc hL2 hF

end ESS
