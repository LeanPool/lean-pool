/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumDecompose
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox

/-!
# Stability S3

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The zero-force weak momentum identity (S3) passes to the limits in
`thm:stability`. -/
theorem stability_suitable_momentum
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
    ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, v z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, v z i * v z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, Dv z i j * spatialPartial (fun w => φ w i) j z
          - r z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i = 0 := by
  intro φ hφ
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hφ
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset
      hdata.isOpen_space hdata.isOpen_time hdata.ordConnected_time hK hKsub
  have hT := stability_momentum_timeTerm_tendsto u Du p v hsol hbox
    (huConv Ω' J hbox) φ hφ
  have hN := stability_momentum_nonlinearTerm_tendsto u Du p v hsol hbox
    (huConv Ω' J hbox) φ hφ
  have hV := stability_momentum_viscousTerm_tendsto u Du p Dv hsol hbox
    (hDv Ω' J hbox) (hDuWeak Ω' J hbox) φ hφ
  have hP := stability_momentum_pressureTerm_tendsto u Du p r hsol hbox
    (hpConv Ω' J hbox) φ hφ
  have hconv := ((hT.neg.sub hN).add hV).sub hP
  have hzeroN (n : ℕ) :
      (-(∫ z in spaceTimeSet Ω' J,
        ∑ i, u n z i * timePartial (fun w => φ w i) z))
        - (∫ z in spaceTimeSet Ω' J,
          ∑ i, ∑ j, u n z i * u n z j * spatialPartial (fun w => φ w i) j z)
        + (∫ z in spaceTimeSet Ω' J,
          ∑ i, ∑ j, Du n z i j * spatialPartial (fun w => φ w i) j z)
        - (∫ z in spaceTimeSet Ω' J,
          p n z * ∑ i, spatialPartial (fun w => φ w i) i z) = 0 := by
    have h := (hsol n).2.2.2.2.2.2.2.1 φ hφ
    have hdataN := (isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
    rw [stability_momentum_integral_eq_localBox φ hφ hKbox
      (u n) (Du n) (p n),
      stability_momentum_integral_decompose_localBox hdataN hbox φ hφ] at h
    exact h
  have hzero :
      (-(∫ z in spaceTimeSet Ω' J,
        ∑ i, v z i * timePartial (fun w => φ w i) z))
        - (∫ z in spaceTimeSet Ω' J,
          ∑ i, ∑ j, v z i * v z j * spatialPartial (fun w => φ w i) j z)
        + (∫ z in spaceTimeSet Ω' J,
          ∑ i, ∑ j, Dv z i j * spatialPartial (fun w => φ w i) j z)
        - (∫ z in spaceTimeSet Ω' J,
          r z * ∑ i, spatialPartial (fun w => φ w i) i z) = 0 := by
    have heq : (0 : ℝ) = _ :=
      tendsto_const_nhds_iff.mp (by simpa only [hzeroN] using hconv)
    exact heq.symm
  rw [stability_momentum_integral_eq_localBox φ hφ hKbox v Dv r,
    stability_momentum_integral_decompose_localBox hdata hbox φ hφ]
  exact hzero

end CKN
