/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticIntegral

/-!
# Stability Momentum Nonlinear

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The quadratic velocity term in (S3) passes to a strong local `L³` limit. -/
theorem stability_momentum_nonlinearTerm_tendsto
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
      ∑ i : Fin 3, ∑ j : Fin 3,
        u n z i * u n z j * spatialPartial (fun w => φ w i) j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          v z i * v z j * spatialPartial (fun w => φ w i) j z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) := by
      exact ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have huN (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hcompConv (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ u v huN huConv i
  have hQn (n : ℕ) (i j : Fin 3) :
      MemLp (fun z : ParabolicPoint => u n z i * u n z j)
        (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp ((fun z => u n z i) * (fun z => u n z j))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp (huN n)) i).mul ((memLp_pi_iff.mp (huN n)) j)
    have heq : ((fun z => u n z i) * (fun z => u n z j)) =
        (fun z => u n z i * u n z j) := by funext z; rfl
    rwa [heq] at h
  have hQ : ∀ i j : Fin 3,
      MemLp (fun z : ParabolicPoint => v z i * v z j)
        (3 / 2 : ℝ≥0∞) μ := by
    intro i j
    have h : MemLp ((fun z => v z i) * (fun z => v z j))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp hv) i).mul ((memLp_pi_iff.mp hv) j)
    have heq : ((fun z => v z i) * (fun z => v z j)) =
        (fun z => v z i * v z j) := by funext z; rfl
    rwa [heq] at h
  have hFi (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        u n z i * u n z j * spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hQn n i j)
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hGi (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        v z i * v z j * spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hQ i j)
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hconvIj (i j : Fin 3) : Tendsto
      (fun n => ∫ z : ParabolicPoint,
        u n z i * u n z j * spatialPartial (fun w => φ w i) j z ∂μ)
      atTop (nhds (∫ z : ParabolicPoint,
        v z i * v z j * spatialPartial (fun w => φ w i) j z ∂μ)) :=
    stability_tendsto_integral_quadratic_test μ
      (fun n z => u n z i) (fun n z => u n z j)
      (fun z => v z i) (fun z => v z j)
      (fun z => spatialPartial (fun w => φ w i) j z)
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      (fun n => (memLp_pi_iff.mp (huN n)) j)
      ((memLp_pi_iff.mp hv) i) ((memLp_pi_iff.mp hv) j)
      (stability_spatialPartial_memLp_top φ hφ i j)
      (hcompConv i) (hcompConv j)
  have hinner (i : Fin 3) : Tendsto
      (fun n => ∫ z : ParabolicPoint,
        ∑ j : Fin 3,
          u n z i * u n z j * spatialPartial (fun w => φ w i) j z ∂μ)
      atTop (nhds (∫ z : ParabolicPoint,
        ∑ j : Fin 3,
          v z i * v z j * spatialPartial (fun w => φ w i) j z ∂μ)) :=
    stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n j z => u n z i * u n z j * spatialPartial (fun w => φ w i) j z)
      (fun j z => v z i * v z j * spatialPartial (fun w => φ w i) j z)
      (fun n j _ => hFi n i j) (fun j _ => hGi i j)
      (fun j _ => hconvIj i j)
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => ∑ j : Fin 3,
      u n z i * u n z j * spatialPartial (fun w => φ w i) j z)
    (fun i z => ∑ j : Fin 3,
      v z i * v z j * spatialPartial (fun w => φ w i) j z)
    (fun n i _ => integrable_finsetSum Finset.univ (fun j _ => hFi n i j))
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hGi i j))
    (fun i _ => hinner i)

end CKN
