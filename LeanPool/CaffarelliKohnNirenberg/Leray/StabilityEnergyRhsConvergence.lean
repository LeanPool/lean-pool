/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyDecompose

/-!
# Stability Energy Rhs Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The right side of the zero-force local energy inequality converges on
each local box under the strong velocity and pressure limits. -/
theorem stability_energy_rhs_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hdata : IsSuitableWeakSolutionData Ω I q v Dv r 0)
    (hbox : localBox Ω I Ω' J)
    (huConv : Tendsto (fun n => eLpNorm (u n - v) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hpConv : Tendsto (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      vec3EuclideanNorm (u n z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (u n z) ^ 2 + 2 * p n z) *
          ∑ i, u n z i * spatialPartial ψ i z +
        2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * u n z i) * ψ z)
      atTop (nhds (∫ z in spaceTimeSet Ω' J,
        vec3EuclideanNorm (v z) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
          (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
            ∑ i, v z i * spatialPartial ψ i z +
          2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z)) := by
  have hA := stability_energy_quadraticTerm_tendsto u Du p v
    hsol hbox huConv ψ hψ
  have hB := stability_energy_cubicTerm_tendsto u Du p v
    hsol hbox huConv ψ hψ
  have hC := stability_energy_pressureTerm_tendsto u Du p v r
    hsol hbox huConv hpConv ψ hψ
  have hsum := (hA.add hB).add (hC.const_mul 2)
  have hseq (n : ℕ) :=
    stability_energy_rhs_decompose_localBox
      (isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
      hbox ψ hψ
  have hlim := stability_energy_rhs_decompose_localBox hdata hbox ψ hψ
  simpa only [hseq, hlim] using hsum

end CKN
