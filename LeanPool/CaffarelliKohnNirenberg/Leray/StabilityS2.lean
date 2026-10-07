/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityDivergencePairings
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityDivergenceSum
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox

/-!
# Stability S2

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The distributional divergence identity (S2) passes to the strong local
`L³` limit in `thm:stability`. -/
theorem stability_suitable_divergence
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (v : ParabolicPoint → Vec3)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (huConv : ∀ Ω' J, localBox Ω I Ω' J → Tendsto
      (fun n => eLpNorm (u n - v) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0)) :
    ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I,
        ∑ i : Fin 3, v z i * spatialPartial ψ i z = 0 := by
  intro ψ hψ
  have hdata := (isSuitableWeakSolution_iff_integrable.mp (hsol 0)).toData
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset
      hdata.isOpen_space hdata.isOpen_time hdata.ordConnected_time hK hKsub
  have huN (n : ℕ) : MemLp (u n) 3
      (volume.restrict (spaceTimeSet Ω' J)) :=
    stability_velocity_memLp_three_on_localBox (hsol n) hbox
  have hv : MemLp v 3 (volume.restrict (spaceTimeSet Ω' J)) :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) huN v (huConv Ω' J hbox)
  have hzeroN (n : ℕ) :
      (∑ i : Fin 3, ∫ z in spaceTimeSet Ω' J,
        spatialPartial ψ i z * u n z i) = 0 := by
    have h := (hsol n).2.2.2.2.2.2.1 ψ hψ
    rw [stability_divergence_integral_eq_localBox ψ hψ hKbox (u n),
      stability_divergence_sum_integral_eq hbox ψ hψ (u n) (huN n)] at h
    exact h
  have hconv := stability_divergence_pairings_tendsto u Du p v
    hsol hbox (huConv Ω' J hbox) ψ hψ
  have hzero : (∑ i : Fin 3, ∫ z in spaceTimeSet Ω' J,
      spatialPartial ψ i z * v z i) = 0 := by
    have heq : (0 : ℝ) = ∑ i : Fin 3, ∫ z in spaceTimeSet Ω' J,
        spatialPartial ψ i z * v z i :=
      tendsto_const_nhds_iff.mp (by simpa only [hzeroN] using hconv)
    exact heq.symm
  rw [stability_divergence_integral_eq_localBox ψ hψ hKbox v,
    stability_divergence_sum_integral_eq hbox ψ hψ v hv]
  exact hzero

end CKN
