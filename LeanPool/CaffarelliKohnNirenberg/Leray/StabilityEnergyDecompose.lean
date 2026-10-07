/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergySupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumDecompose

/-!
# Stability Energy Decompose

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- On a local box, the zero-force right side of (S4) is the sum of its
quadratic, cubic, and pressure terms. -/
theorem stability_energy_rhs_decompose_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {r : ParabolicPoint → ℝ}
    (hdata : IsSuitableWeakSolutionData Ω I q v Dv r 0)
    (hbox : localBox Ω I Ω' J)
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ z in spaceTimeSet Ω' J,
      vec3EuclideanNorm (v z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
          ∑ i, v z i * spatialPartial ψ i z +
        2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z) =
      (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, v z i * v z i *
          (timePartial ψ z + ∑ j : Fin 3, spatialSecondPartial ψ j j z)) +
      (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          v z i * v z i * v z j * spatialPartial ψ j z) +
      2 * (∫ z in spaceTimeSet Ω' J,
        ∑ j : Fin 3, r z * v z j * spatialPartial ψ j z) := by
  obtain ⟨K, hKcompact, hboxsub, hKsub⟩ :=
    stability_localBox_compact_enclosure hbox
  let S : Set ParabolicPoint := spaceTimeSet Ω' J
  let A : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, v z i * v z i *
      (timePartial ψ z + ∑ j : Fin 3, spatialSecondPartial ψ j j z)
  let B : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      v z i * v z i * v z j * spatialPartial ψ j z
  let C : ParabolicPoint → ℝ := fun z =>
    ∑ j : Fin 3, r z * v z j * spatialPartial ψ j z
  have hheat : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2 *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)) S volume :=
    (localEnergy_heatTerm_integrableOn_of_data hdata hKcompact hKsub hψ).mono_set
      hboxsub
  have hflux : IntegrableOn (fun z =>
      (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
        ∑ i, v z i * spatialPartial ψ i z) S volume :=
    (localEnergy_fluxTerm_integrableOn_of_data hdata hKcompact hKsub hψ).mono_set
      hboxsub
  have hC : IntegrableOn C S volume := by
    change Integrable (fun z => ∑ j : Fin 3,
      r z * v z j * spatialPartial ψ j z) (volume.restrict S)
    apply integrable_finsetSum
    intro j _
    obtain ⟨Cj, hCj⟩ :=
      exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ j
    have hterm : IntegrableOn
        (fun z : ParabolicPoint => r z * v z j * spatialPartial ψ j z)
        K volume :=
      (pressure_mul_velocity_integrableOn_compact_of_data hdata
        hKcompact hKsub j).mul_bdd (c := Cj)
        (g := fun z : ParabolicPoint => spatialPartial ψ j z)
        (spatialPartial_contDiff hψ.1 j).continuous.measurable.aestronglyMeasurable
        (Eventually.of_forall fun z => hCj z)
    exact hterm.mono_set hboxsub
  have hA : IntegrableOn A S volume := by
    refine hheat.congr (Filter.Eventually.of_forall fun z => ?_)
    change vec3EuclideanNorm (v z) ^ 2 *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) = A z
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [A, Fin.sum_univ_three]
    ring
  have hB : IntegrableOn B S volume := by
    have h := hflux.sub (hC.const_mul 2)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    change (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
      (∑ i, v z i * spatialPartial ψ i z) - 2 * C z = B z
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [B, C, Fin.sum_univ_three]
    ring
  have hpoint : (fun z : ParabolicPoint =>
      vec3EuclideanNorm (v z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
          ∑ i, v z i * spatialPartial ψ i z +
        2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z) =
      (fun z => A z + B z + 2 * C z) := by
    funext z
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      mul_zero, add_zero]
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [A, B, C, Fin.sum_univ_three]
    ring
  rw [hpoint]
  change (∫ z in S, A z + B z + 2 * C z) =
    (∫ z in S, A z) + (∫ z in S, B z) +
      2 * (∫ z in S, C z)
  calc
    (∫ z in S, A z + B z + 2 * C z) =
        (∫ z in S, A z + B z) + (∫ z in S, 2 * C z) :=
      integral_add' (hA.add hB) (hC.const_mul 2)
    _ = _ := by
      have hAB : (∫ z in S, A z + B z) =
          (∫ z in S, A z) + (∫ z in S, B z) := by
        simpa only [Pi.add_apply] using (integral_add' hA hB)
      have h2C : (∫ z in S, 2 * C z) =
          2 * (∫ z in S, C z) := by rw [integral_const_mul]
      rw [hAB, h2C]

end CKN
