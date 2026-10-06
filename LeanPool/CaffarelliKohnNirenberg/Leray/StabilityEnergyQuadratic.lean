/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumNonlinear

/-!
# Stability Energy Quadratic

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

/-- The quadratic term on the right side of (S4) passes to a strong local
`L³` limit. -/
theorem stability_energy_quadraticTerm_tendsto
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
      ∑ i : Fin 3, u n z i * u n z i *
        (timePartial ψ z + ∑ j : Fin 3, spatialSecondPartial ψ j j z)) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, v z i * v z i *
          (timePartial ψ z + ∑ j : Fin 3, spatialSecondPartial ψ j j z))) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have huN (n : ℕ) : MemLp (u n) 3 μ :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v huConv
  have hcompConv (i : Fin 3) :=
    stability_tendsto_eLpNorm_component_three μ u v huN huConv i
  let T : ParabolicPoint → ℝ := fun z =>
    timePartial ψ z + ∑ j : Fin 3, spatialSecondPartial ψ j j z
  have hT : MemLp T ∞ μ := stability_energyLaplacian_memLp_top ψ hψ
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
  have hIntN (n : ℕ) (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => u n z i * u n z i * T z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hFn n i) hT
  have hIntG (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => v z i * v z i * T z) μ :=
    stability_integrable_mul_bounded_test μ hOne (hFg i) hT
  have hconv (i : Fin 3) :=
    stability_tendsto_integral_quadratic_test μ
      (fun n z => u n z i) (fun n z => u n z i)
      (fun z => v z i) (fun z => v z i) T
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      (fun n => (memLp_pi_iff.mp (huN n)) i)
      ((memLp_pi_iff.mp hv) i) ((memLp_pi_iff.mp hv) i)
      hT (hcompConv i) (hcompConv i)
  exact stability_tendsto_integral_finsetSum μ Finset.univ
    (fun n i z => u n z i * u n z i * T z)
    (fun i z => v z i * v z i * T z)
    (fun n i _ => hIntN n i) (fun i _ => hIntG i)
    (fun i _ => hconv i)

end CKN
