/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyRhsConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeightedGradientMatrix
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox

/-!
# Stability S4

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The local energy inequality (S4) passes to the limit through strong
velocity and pressure convergence and weak gradient convergence. -/
theorem stability_suitable_energy
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hdata : IsSuitableWeakSolutionData Ω I q v Dv r 0)
    (huConv : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDv : ∀ Ω' J, localBox Ω I Ω' J →
      MemLp Dv 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hDuWeak : ∀ Ω' J, localBox Ω I Ω' J →
      ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω').prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, Du n (z.1, z.2) i j * w z
        ∂(volume.restrict Ω').prod (volume.restrict J)) atTop
        (nhds (∫ z, Dv (z.1, z.2) i j * w z
          ∂(volume.restrict Ω').prod (volume.restrict J))))
    (hpConv : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0)) :
    ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq v Dv z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          vec3EuclideanNorm (v z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
            (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
              ∑ i, v z i * spatialPartial ψ i z +
            2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z := by
  intro ψ hψ hψpos
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset
      hdata.isOpen_space hdata.isOpen_time hdata.ordConnected_time hK hKsub
  let A (n : ℕ) : ℝ :=
    ∫ z in spaceTimeSet Ω' J, spatialGradientSq (u n) (Du n) z * ψ z
  let B : ℝ := ∫ z in spaceTimeSet Ω' J,
    spatialGradientSq v Dv z * ψ z
  let C (n : ℕ) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ z in spaceTimeSet Ω' J, Du n z i j * Dv z i j * ψ z
  let R (n : ℕ) : ℝ := ∫ z in spaceTimeSet Ω' J,
    vec3EuclideanNorm (u n z) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
      (vec3EuclideanNorm (u n z) ^ 2 + 2 * p n z) *
        ∑ i, u n z i * spatialPartial ψ i z +
      2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * u n z i) * ψ z
  let S : ℝ := ∫ z in spaceTimeSet Ω' J,
    vec3EuclideanNorm (v z) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
      (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
        ∑ i, v z i * spatialPartial ψ i z +
      2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z
  have hgrad := stability_weighted_gradient_matrix u Du p v Dv
    hsol hbox (hDv Ω' J hbox) (hDuWeak Ω' J hbox) ψ hψ hψpos
  have hCconv : Tendsto C atTop (nhds B) := hgrad.1
  have hpolar : ∀ n, 2 * C n ≤ A n + B := hgrad.2
  have hRconv : Tendsto R atTop (nhds S) :=
    stability_energy_rhs_tendsto u Du p v Dv r hsol hdata hbox
      (huConv Ω' J hbox) (hpConv Ω' J hbox) ψ hψ
  have henergyN (n : ℕ) : 2 * A n ≤ R n := by
    have h := (hsol n).2.2.2.2.2.2.2.2 ψ hψ hψpos
    rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox (u n) (Du n),
      stability_energy_rhs_integral_eq_localBox ψ hψ hKbox (u n) (p n)] at h
    exact h
  have hpoint (n : ℕ) : 4 * C n ≤ R n + 2 * B := by
    linarith only [hpolar n, henergyN n]
  have hlimit : 4 * B ≤ S + 2 * B :=
    le_of_tendsto_of_tendsto' (hCconv.const_mul 4)
      (hRconv.add_const (2 * B)) hpoint
  have hlocal : 2 * B ≤ S := by
    linarith only [hlimit]
  rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox v Dv,
    stability_energy_rhs_integral_eq_localBox ψ hψ hKbox v r]
  exact hlocal

end CKN
