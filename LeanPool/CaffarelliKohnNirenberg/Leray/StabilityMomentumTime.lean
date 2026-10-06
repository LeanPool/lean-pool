/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFiniteSumIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityBoundedPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityComponentConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalVelocityLp

/-!
# Stability Momentum Time

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The linear time-derivative pairing in (S3) passes to a strong local
`L³` limit. -/
theorem stability_momentum_timeTerm_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto (fun n => eLpNorm (u n - v) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, u n z i * timePartial (fun w => φ w i) z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, v z i * timePartial (fun w => φ w i) z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have huN (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hFi (n : ℕ) (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => u n z i * timePartial (fun w => φ w i) z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num)
      ((memLp_pi_iff.mp (huN n)) i)
      (stability_timePartial_memLp_top φ hφ i)
  have hGi (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => v z i * timePartial (fun w => φ w i) z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num)
      ((memLp_pi_iff.mp hv) i)
      (stability_timePartial_memLp_top φ hφ i)
  have hconvI (i : Fin 3) : Tendsto
      (fun n => ∫ z : ParabolicPoint,
        u n z i * timePartial (fun w => φ w i) z ∂μ) atTop
      (nhds (∫ z : ParabolicPoint,
        v z i * timePartial (fun w => φ w i) z ∂μ)) := by
    have hcomp := stability_tendsto_eLpNorm_component_three
      μ u v huN huConv i
    have h := stability_tendsto_integral_mul_test_of_Lthree μ
      (fun n z => u n z i) (fun z => v z i)
      (fun z => timePartial (fun w => φ w i) z)
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      (stability_timePartial_memLp_top φ hφ i) hcomp
    have heqFn (n : ℕ) :
        (∫ z, timePartial (fun w => φ w i) z • u n z i ∂μ) =
          ∫ z, u n z i * timePartial (fun w => φ w i) z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [smul_eq_mul, mul_comm]
    have heqG :
        (∫ z, timePartial (fun w => φ w i) z • v z i ∂μ) =
          ∫ z, v z i * timePartial (fun w => φ w i) z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [smul_eq_mul, mul_comm]
    simpa only [heqFn, heqG] using h
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => u n z i * timePartial (fun w => φ w i) z)
    (fun i z => v z i * timePartial (fun w => φ w i) z)
    (fun n i _ => hFi n i) (fun i _ => hGi i)
    (fun i _ => hconvI i)

end CKN
