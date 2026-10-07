/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumNonlinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalGradientLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalProductMemLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalProductIntegral

/-!
# Stability Momentum Viscous

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The viscous term in (S3) passes through weak local `L²` convergence
of the gradient. -/
theorem stability_momentum_viscousTerm_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (hDv : MemLp Dv 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hDuWeak : ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))))
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, ∑ j : Fin 3,
        Du n z i j * spatialPartial (fun w => φ w i) j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Dv z i j * spatialPartial (fun w => φ w i) j z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hDN (n : ℕ) : MemLp (Du n) 2 μ :=
    stability_gradient_memLp_two_on_localBox (hsol n) hbox
  have hDi (n : ℕ) (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => Du n z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp (hDN n)) i)) j
  have hdI (i j : Fin 3) : MemLp
      (fun z : ParabolicPoint => Dv z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDv) i)) j
  have hFi (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        Du n z i j * spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) (hDi n i j)
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hGi (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        Dv z i j * spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) (hdI i j)
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hconvIj (i j : Fin 3) : Tendsto
      (fun n => ∫ z : ParabolicPoint,
        Du n z i j * spatialPartial (fun w => φ w i) j z ∂μ)
      atTop (nhds (∫ z : ParabolicPoint,
        Dv z i j * spatialPartial (fun w => φ w i) j z ∂μ)) := by
    change Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      Du n z i j * spatialPartial (fun w => φ w i) j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        Dv z i j * spatialPartial (fun w => φ w i) j z))
    have htest2 : MemLp
        (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w i) j z) 2
        ((volume.restrict Ω').prod (volume.restrict J)) :=
      stability_memLp_localBox_prod hbox
        ((stability_spatialPartial_memLp_top φ hφ i j).mono_exponent
          (by simp))
    have h := hDuWeak i j _ htest2
    have heqFn (n : ℕ) :
        (∫ z in spaceTimeSet Ω' J,
          Du n z i j * spatialPartial (fun w => φ w i) j z) =
        ∫ z : Vec3 × ℝ,
          Du n (z.1, z.2) i j * spatialPartial (fun w => φ w i) j z
          ∂((volume.restrict Ω').prod (volume.restrict J)) :=
      stability_setIntegral_localBox_eq_prod _
    have heqG :
        (∫ z in spaceTimeSet Ω' J,
          Dv z i j * spatialPartial (fun w => φ w i) j z) =
        ∫ z : Vec3 × ℝ,
          Dv (z.1, z.2) i j * spatialPartial (fun w => φ w i) j z
          ∂((volume.restrict Ω').prod (volume.restrict J)) :=
      stability_setIntegral_localBox_eq_prod _
    simpa only [heqFn, heqG] using h
  have hinner (i : Fin 3) : Tendsto
      (fun n => ∫ z : ParabolicPoint,
        ∑ j : Fin 3,
          Du n z i j * spatialPartial (fun w => φ w i) j z ∂μ)
      atTop (nhds (∫ z : ParabolicPoint,
        ∑ j : Fin 3,
          Dv z i j * spatialPartial (fun w => φ w i) j z ∂μ)) :=
    stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n j z => Du n z i j * spatialPartial (fun w => φ w i) j z)
      (fun j z => Dv z i j * spatialPartial (fun w => φ w i) j z)
      (fun n j _ => hFi n i j) (fun j _ => hGi i j)
      (fun j _ => hconvIj i j)
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => ∑ j : Fin 3,
      Du n z i j * spatialPartial (fun w => φ w i) j z)
    (fun i z => ∑ j : Fin 3,
      Dv z i j * spatialPartial (fun w => φ w i) j z)
    (fun n i _ => integrable_finsetSum Finset.univ (fun j _ => hFi n i j))
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hGi i j))
    (fun i _ => hinner i)

end CKN
