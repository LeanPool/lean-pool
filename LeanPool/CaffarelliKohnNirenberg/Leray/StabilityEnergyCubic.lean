/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyQuadratic
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFluxProduct

/-!
# Stability Energy Cubic

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

private instance : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
    hreal.ennrealOfReal

private instance : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa [CKN.ofReal_threeHalves] using hreal.ennrealOfReal

/-- The cubic velocity flux in (S4) converges under strong local `L³`
convergence. -/
theorem stability_energy_cubicTerm_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto (fun n => eLpNorm (u n - v) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, ∑ j : Fin 3,
        u n z i * u n z i * u n z j * spatialPartial ψ j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          v z i * v z i * v z j * spatialPartial ψ j z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have huN (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hcomp (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ u v huN huConv i
  have hFn (n : ℕ) (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => u n z i * u n z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp ((fun z => u n z i) * (fun z => u n z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp (huN n)) i).mul ((memLp_pi_iff.mp (huN n)) i)
    convert h using 1
  have hFg (i : Fin 3) : MemLp
      (fun z : ParabolicPoint => v z i * v z i)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp ((fun z => v z i) * (fun z => v z i))
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp hv) i).mul ((memLp_pi_iff.mp hv) i)
    convert h using 1
  have hQconv (i : Fin 3) :=
    stability_tendsto_eLpNorm_product_three
      (fun n z => u n z i) (fun n z => u n z i)
      (fun z => v z i) (fun z => v z i)
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      ((memLp_pi_iff.mp hv) i) ((memLp_pi_iff.mp hv) i)
      (hcomp i) (hcomp i)
  have hIntN (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        u n z i * u n z i * u n z j * spatialPartial ψ j z) μ := by
    have hprod : MemLp
        ((fun z : ParabolicPoint => u n z i * u n z i) *
          (fun z => u n z j)) 1 μ :=
      (hFn n i).mul ((memLp_pi_iff.mp (huN n)) j)
    have htest : MemLp
        ((fun z : ParabolicPoint => spatialPartial ψ j z) •
          ((fun z => u n z i * u n z i) * (fun z => u n z j))) 1 μ :=
      (stability_energySpatial_memLp_top ψ hψ j).smul hprod
    have hres : MemLp (fun z : ParabolicPoint =>
        u n z i * u n z i * u n z j * spatialPartial ψ j z) 1 μ := by
      convert htest using 1
      funext z
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    exact memLp_one_iff_integrable.mp hres
  have hIntG (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        v z i * v z i * v z j * spatialPartial ψ j z) μ := by
    have hprod : MemLp
        ((fun z : ParabolicPoint => v z i * v z i) *
          (fun z => v z j)) 1 μ :=
      (hFg i).mul ((memLp_pi_iff.mp hv) j)
    have htest : MemLp
        ((fun z : ParabolicPoint => spatialPartial ψ j z) •
          ((fun z => v z i * v z i) * (fun z => v z j))) 1 μ :=
      (stability_energySpatial_memLp_top ψ hψ j).smul hprod
    have hres : MemLp (fun z : ParabolicPoint =>
        v z i * v z i * v z j * spatialPartial ψ j z) 1 μ := by
      convert htest using 1
      funext z
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    exact memLp_one_iff_integrable.mp hres
  have hconv (i j : Fin 3) :=
    stability_flux_product_tendsto
      (fun n z => u n z i * u n z i)
      (fun n z => u n z j)
      (fun z => v z i * v z i) (fun z => v z j)
      (fun z => spatialPartial ψ j z)
      (fun n => hFn n i) (fun n => (memLp_pi_iff.mp (huN n)) j)
      (hFg i) ((memLp_pi_iff.mp hv) j)
      (stability_energySpatial_memLp_top ψ hψ j)
      (hQconv i) (hcomp j)
  have hinner (i : Fin 3) :=
    stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n j z =>
        u n z i * u n z i * u n z j * spatialPartial ψ j z)
      (fun j z => v z i * v z i * v z j * spatialPartial ψ j z)
      (fun n j _ => hIntN n i j) (fun j _ => hIntG i j)
      (fun j _ => hconv i j)
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => ∑ j : Fin 3,
      u n z i * u n z i * u n z j * spatialPartial ψ j z)
    (fun i z => ∑ j : Fin 3,
      v z i * v z i * v z j * spatialPartial ψ j z)
    (fun n i _ => integrable_finsetSum Finset.univ (fun j _ => hIntN n i j))
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hIntG i j))
    (fun i _ => hinner i)

end CKN
