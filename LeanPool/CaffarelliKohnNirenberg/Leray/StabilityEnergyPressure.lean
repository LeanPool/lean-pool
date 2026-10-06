/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyCubic

/-!
# Stability Energy Pressure

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

private instance : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa [CKN.ofReal_threeHalves] using hreal.ennrealOfReal

/-- The pressure flux in (S4) converges under strong local convergence of
the pressure and velocity. -/
theorem stability_energy_pressureTerm_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto (fun n => eLpNorm (u n - v) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hpConv : Tendsto (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      ∑ j : Fin 3, p n z * u n z j * spatialPartial ψ j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ j : Fin 3, r z * v z j * spatialPartial ψ j z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have huN (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hpN (n : ℕ) : MemLp (p n) (3 / 2 : ℝ≥0∞) μ := by
    have hdata := (isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
    simpa only [CKN.ofReal_threeHalves] using hdata.memLp_pressure hbox
  have hr : MemLp r (3 / 2 : ℝ≥0∞) μ :=
    Lp.memLp_of_cauchy_tendsto (by
      rw [← CKN.ofReal_threeHalves]
      simpa using ENNReal.ofReal_le_ofReal
        (by norm_num : (1 : ℝ) ≤ 3 / 2)) hpN r hpConv
  have hcomp (j : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ u v huN huConv j
  have hIntN (n : ℕ) (j : Fin 3) : Integrable
      (fun z : ParabolicPoint => p n z * u n z j * spatialPartial ψ j z) μ := by
    have hprod : MemLp (p n * (fun z => u n z j)) 1 μ :=
      (hpN n).mul ((memLp_pi_iff.mp (huN n)) j)
    have htest : MemLp
        ((fun z : ParabolicPoint => spatialPartial ψ j z) •
          (p n * (fun z => u n z j))) 1 μ :=
      (stability_energySpatial_memLp_top ψ hψ j).smul hprod
    have hres : MemLp (fun z : ParabolicPoint =>
        p n z * u n z j * spatialPartial ψ j z) 1 μ := by
      convert htest using 1
      funext z
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    exact memLp_one_iff_integrable.mp hres
  have hIntG (j : Fin 3) : Integrable
      (fun z : ParabolicPoint => r z * v z j * spatialPartial ψ j z) μ := by
    have hprod : MemLp (r * (fun z => v z j)) 1 μ :=
      hr.mul ((memLp_pi_iff.mp hv) j)
    have htest : MemLp
        ((fun z : ParabolicPoint => spatialPartial ψ j z) •
          (r * (fun z => v z j))) 1 μ :=
      (stability_energySpatial_memLp_top ψ hψ j).smul hprod
    have hres : MemLp (fun z : ParabolicPoint =>
        r z * v z j * spatialPartial ψ j z) 1 μ := by
      convert htest using 1
      funext z
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    exact memLp_one_iff_integrable.mp hres
  have hconv (j : Fin 3) :=
    stability_flux_product_tendsto p (fun n z => u n z j)
      r (fun z => v z j) (fun z => spatialPartial ψ j z)
      hpN (fun n => (memLp_pi_iff.mp (huN n)) j)
      hr ((memLp_pi_iff.mp hv) j)
      (stability_energySpatial_memLp_top ψ hψ j)
      hpConv (hcomp j)
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n j z => p n z * u n z j * spatialPartial ψ j z)
    (fun j z => r z * v z j * spatialPartial ψ j z)
    (fun n j _ => hIntN n j) (fun j _ => hIntG j)
    (fun j _ => hconv j)

end CKN
