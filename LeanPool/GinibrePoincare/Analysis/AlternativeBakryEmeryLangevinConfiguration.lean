/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinConfiguration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobalContinuity
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalStopped
/-!
# Alternative Bakry Emery Langevin configuration

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_configuration_volterra_identification`,
`bakryEmery_configuration_volterra_prefix_identification`.
-/

@[expose] public section
open Set MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
lemma bakryEmery_configuration_real_single (n : ℕ) (j : Fin n) :
    (configurationEuclideanEquiv n).symm (EuclideanSpace.single (j, 0) 1) =
      realCoordinateDirection j := by
  ext k : 1
  by_cases h : k = j <;> simp [configurationEuclideanEquiv_symm_apply, realCoordinateDirection,
      coordinateDirection, h] <;> rfl
lemma bakryEmery_configuration_imaginary_single (n : ℕ) (j : Fin n) :
    (configurationEuclideanEquiv n).symm (EuclideanSpace.single (j, 1) 1) =
      imaginaryCoordinateDirection j := by
  ext k : 1
  by_cases h : k = j <;> simp [configurationEuclideanEquiv_symm_apply, imaginaryCoordinateDirection,
      coordinateDirection, h] <;> rfl

theorem bakryEmeryGibbsConfigurationDrift_gradient (n : ℕ) (W : Configuration n → ℝ)
    (z : Configuration n) (hW : DifferentiableAt ℝ W z) :
    configurationEuclideanEquiv n (bakryEmeryGibbsConfigurationDrift W z) =
      -gradient (W ∘ (configurationEuclideanEquiv n).symm) (configurationEuclideanEquiv n z) := by
  let e := configurationEuclideanEquiv n
  have hder : fderiv ℝ (W ∘ e.symm) (e z) =
      (fderiv ℝ W z).comp e.symm.toContinuousLinearMap := by
    rw [fderiv_comp _ (by simpa using hW) e.symm.differentiableAt]
    rw [e.symm.hasFDerivAt.fderiv]
    simp
  have hgrad (ij : Fin n × Fin 2) :
      gradient (W ∘ e.symm) (e z) ij =
        fderiv ℝ W z (e.symm (EuclideanSpace.single ij 1)) := by
    have hh := inner_gradient_left (f := W ∘ e.symm) (x := e z)
      (y := EuclideanSpace.single ij (1 : ℝ))
    rw [EuclideanSpace.inner_single_right] at hh
    simpa [hder] using hh
  ext ⟨j, k⟩
  fin_cases k
  · simp [bakryEmeryGibbsConfigurationDrift, hgrad, e, bakryEmery_configuration_real_single]
  · simp [bakryEmeryGibbsConfigurationDrift, hgrad, e, bakryEmery_configuration_imaginary_single]

/-- Any actual continuous configuration solution of the gradient Volterra
equation agrees with the internally constructed selected Hilbert-space flow. -/
theorem bakryEmery_configuration_volterra_identification (n : ℕ)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (z : Configuration n) (T : ℝ) (hT : 0 ≤ T)
    (N : C(Icc 0 T, EuclideanSpace ℝ (Fin n × Fin 2)))
    (X : ℝ → Configuration n) (hX : ContinuousOn X (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, X t = z +
      (configurationEuclideanEquiv n).symm (bkWeightedExtension T hT N t) +
      ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) :
    let e := configurationEuclideanEquiv n
    let U := W ∘ e.symm
    let hU : ContDiff ℝ 2 U := hW.comp e.symm.contDiff
    ∀ t ∈ Icc 0 T, e (X t) =
      bakryEmeryLangevinStateOn U κ hκ hU hc (e z) T hT N t := by
  let e := configurationEuclideanEquiv n
  let U := W ∘ e.symm
  have hU : ContDiff ℝ 2 U := hW.comp e.symm.contDiff
  let Z := bakryEmeryLangevinStateOn U κ hκ hU hc (e z) T hT N
  have hZ := bakryEmeryLangevinStateOn_spec U κ hκ hU hc (e z) T hT N
  have hb : Continuous (bakryEmeryLangevinDrift U) := continuous_iff_continuousAt.mpr
    (fun x => (bakryEmeryLangevinDrift_contDiffAt U x hU.contDiffAt).continuousAt)
  have hbridge (x : Configuration n) : e (bakryEmeryGibbsConfigurationDrift W x) =
      bakryEmeryLangevinDrift U (e x) :=
    bakryEmeryGibbsConfigurationDrift_gradient n W x ((hW.differentiable (by norm_num)) x)
  have hbc : Continuous (bakryEmeryGibbsConfigurationDrift W) := by
    have hh := e.symm.continuous.comp (hb.comp e.continuous)
    apply hh.congr
    intro x
    apply e.injective
    change e (e.symm (bakryEmeryLangevinDrift U (e x))) = e (bakryEmeryGibbsConfigurationDrift W x)
    rw [e.apply_symm_apply]
    exact (hbridge x).symm
  have hEX : ContinuousOn (fun t => e (X t)) (Icc 0 T) := e.continuous.comp_continuousOn hX
  have hEqE (t : ℝ) (ht : t ∈ Icc 0 T) : e (X t) = e z + bkWeightedExtension T hT N t +
      ∫ s in (0 : ℝ)..t, bakryEmeryLangevinDrift U (e (X s)) := by
    have he := congrArg e (hEq t ht)
    have hi : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationDrift W (X s)) volume 0 t :=
      ((hbc.comp_continuousOn hX).mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)).intervalIntegrable
    simp only [map_add] at he
    change e (X t) = e z + e (e.symm (bkWeightedExtension T hT N t)) +
      e (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) at he
    rw [e.apply_symm_apply] at he
    have hcomm := e.toContinuousLinearMap.intervalIntegral_comp_comm hi
    change (∫ s in (0 : ℝ)..t, e (bakryEmeryGibbsConfigurationDrift W (X s))) =
      e (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) at hcomm
    rw [← hcomm] at he
    simpa only [ContinuousLinearEquiv.coe_coe, hbridge] using he
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hEX
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
      hZ.1.continuousOn
  obtain ⟨K, hK⟩ := bakryEmeryLangevin_noise_stability_on_ball U hU (max A B)
  change ∀ t ∈ Icc 0 T, e (X t) = Z t
  intro t ht
  have hh := hK (e z) (bkWeightedExtension T hT N) (bkWeightedExtension T hT N)
    (fun s => e (X s)) Z T 0 hT le_rfl hEX hZ.1.continuousOn
    (fun s hs => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hA s hs).trans (le_max_left A B))
    (fun s hs => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hB s hs).trans (le_max_right A B)) hEqE hZ.2
    (by intro s _; simp) t ht
  simp only [zero_mul] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- Any actual continuous configuration solution of the gradient Volterra
equation agrees with the internally constructed selected Hilbert-space flow. -/
theorem bakryEmery_configuration_volterra_prefix_identification (n : ℕ)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (z : Configuration n) (T : ℝ) (hT : 0 ≤ T)
    (N : C(Icc 0 T, EuclideanSpace ℝ (Fin n × Fin 2)))
    (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    (X : ℝ → Configuration n) (hX : ContinuousOn X (Icc 0 τ))
    (hEq : ∀ t ∈ Icc 0 τ, X t = z +
      (configurationEuclideanEquiv n).symm (bkWeightedExtension T hT N t) +
      ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) :
    let e := configurationEuclideanEquiv n
    let U := W ∘ e.symm
    let hU : ContDiff ℝ 2 U := hW.comp e.symm.contDiff
    ∀ t ∈ Icc 0 τ, e (X t) =
      bakryEmeryLangevinStateOn U κ hκ hU hc (e z) T hT N t := by
  let e := configurationEuclideanEquiv n
  let U := W ∘ e.symm
  have hU : ContDiff ℝ 2 U := hW.comp e.symm.contDiff
  let Z := bakryEmeryLangevinStateOn U κ hκ hU hc (e z) T hT N
  have hZ := bakryEmeryLangevinStateOn_spec U κ hκ hU hc (e z) T hT N
  have hb : Continuous (bakryEmeryLangevinDrift U) := continuous_iff_continuousAt.mpr
    (fun x => (bakryEmeryLangevinDrift_contDiffAt U x hU.contDiffAt).continuousAt)
  have hbridge (x : Configuration n) : e (bakryEmeryGibbsConfigurationDrift W x) =
      bakryEmeryLangevinDrift U (e x) :=
    bakryEmeryGibbsConfigurationDrift_gradient n W x ((hW.differentiable (by norm_num)) x)
  have hbc : Continuous (bakryEmeryGibbsConfigurationDrift W) := by
    have hh := e.symm.continuous.comp (hb.comp e.continuous)
    apply hh.congr
    intro x
    apply e.injective
    change e (e.symm (bakryEmeryLangevinDrift U (e x))) = e (bakryEmeryGibbsConfigurationDrift W x)
    rw [e.apply_symm_apply]
    exact (hbridge x).symm
  have hEX : ContinuousOn (fun t => e (X t)) (Icc 0 τ) := e.continuous.comp_continuousOn hX
  have hEqE (t : ℝ) (ht : t ∈ Icc 0 τ) : e (X t) = e z + bkWeightedExtension T hT N t +
      ∫ s in (0 : ℝ)..t, bakryEmeryLangevinDrift U (e (X s)) := by
    have he := congrArg e (hEq t ht)
    have hi : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationDrift W (X s)) volume 0 t :=
      ((hbc.comp_continuousOn hX).mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)).intervalIntegrable
    simp only [map_add] at he
    change e (X t) = e z + e (e.symm (bkWeightedExtension T hT N t)) +
      e (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) at he
    rw [e.apply_symm_apply] at he
    have hcomm := e.toContinuousLinearMap.intervalIntegral_comp_comm hi
    change (∫ s in (0 : ℝ)..t, e (bakryEmeryGibbsConfigurationDrift W (X s))) =
      e (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) at hcomm
    rw [← hcomm] at he
    simpa only [ContinuousLinearEquiv.coe_coe, hbridge] using he
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)).exists_bound_of_continuousOn hEX
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)).exists_bound_of_continuousOn
      hZ.1.continuousOn
  obtain ⟨K, hK⟩ := bakryEmeryLangevin_noise_stability_on_ball U hU (max A B)
  change ∀ t ∈ Icc 0 τ, e (X t) = Z t
  intro t ht
  have hh := hK (e z) (bkWeightedExtension T hT N) (bkWeightedExtension T hT N)
    (fun s => e (X s)) Z τ 0 hτ le_rfl hEX hZ.1.continuousOn
    (fun s hs => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hA s hs).trans (le_max_left A B))
    (fun s hs => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hB s hs).trans (le_max_right A B)) hEqE (fun s hs => hZ.2 s ⟨hs.1, hs.2.trans hτT⟩)
    (by intro s _; simp) t ht
  simp only [zero_mul] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end
end GinibrePoincare
