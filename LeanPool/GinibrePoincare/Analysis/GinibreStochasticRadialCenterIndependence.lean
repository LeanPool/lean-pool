/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRadialCenterIndependence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiFunctional
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiGlobal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialPath
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalFactorization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialBrownian

/-! Whole-process independence of the actual radial Brownian driver and center,
obtained from the measurable Lamperti functional of the relative path. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_radial_driver_eq_Lamperti_functional
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (hα : 0 < α) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    (fun ω t => β t ω) =ᵐ[P] (fun ω => ginibreLampertiPathFunctional n α z
      (fun t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω))) := by
  have hl := ginibreBrownianMaximalProcess_global_Lamperti_identity hn α z hz B P hB hind e β hβC
      hβLim
  have hp := (ginibreBrownianMaximalProcess_radius_path_properties hn α z hz B P hB hind).2
  have hx := (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB
      hind).2
  have hc : 0 < Real.sqrt (2*(α : ℝ)/(n : ℝ)) := Real.sqrt_pos.mpr
    (div_pos (mul_pos (by norm_num) (show 0 < (α : ℝ) from hα)) (by exact_mod_cast (show 0 < n by
                                                                      omega)))
  filter_upwards [hl, hp, hx] with ω hl hp hx
  funext t
  have hX : Continuous (fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) := by
    simpa only [Real.toNNReal_coe] using
      (show Continuous (fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B (s : ℝ).toNNReal ω)
        from hx.1.comp NNReal.continuous_coe)
  have hP : Continuous (fun s : ℝ≥0 => recenteredConfiguration n
      (ginibreBrownianMaximalProcess n α z B s ω)) := by
    simpa only [recenteredCLM_apply] using
      (show Continuous (fun s : ℝ≥0 => recenteredCLM n (ginibreBrownianMaximalProcess n α z B s ω))
        from (recenteredCLM n).continuous.comp hX)
  rw [ginibreLampertiPathFunctional_eq_integral n α z _ hP
    (fun s => by rw [pairwiseRadius_recentered]; exact hp.2.1 s)]
  simp only [pairwiseRadius_recentered]
  have hh := hl t
  change Real.sqrt (pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω))-
    Real.sqrt (pairwiseRadius z) = _ at hh
  apply (eq_div_iff hc.ne').mpr
  nlinarith [hh]

theorem ginibreBrownian_center_radial_driver_independent
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (hα : 0 < α) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
      (fun ω t => β t ω) P := by
  have hi := (ginibreBrownian_center_relative_processes_independent (by omega) α z hz B P hB
      hind).comp
    measurable_id (ginibreLampertiPathFunctional_measurable n α z)
  exact hi.congr Filter.EventuallyEq.rfl
    (ginibreBrownian_radial_driver_eq_Lamperti_functional hn α hα z hz B P hB hind e β hβC
        hβLim).symm
theorem ginibreBrownian_center_zero_speed_constant
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n 0 z B t ω)) =ᵐ[P]
      (fun _ _ => coordinateSum z) := by
  filter_upwards [ginibreBrownian_center_OU_factorization hn 0 z hz B P hB hind,
    ginibreBrownianFullContinuousNoise_ae n B P hB (0 : ℝ)] with ω hc hnoise
  funext t
  have hct := hc t
  simp only [NNReal.coe_zero] at hct
  rw [hct]
  have hN : ∀ s, (ginibreBrownianFullContinuousNoise n B 0 ω).val s = 0 := by
    intro s
    rw [hnoise s]
    funext j
    simp [ginibreConfigurationBrownianNoise]
  have hCenter : ∀ s, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B 0 ω) s
      = 0 := by
    intro s
    change coordinateSumCLM n ((ginibreBrownianFullContinuousNoise n B 0 ω).val s)=0
    rw [hN s, map_zero]
  simp [ginibreCenterOUValue, drivenOUPath, drivenOUCorrection, hCenter]

theorem ginibreBrownian_center_radial_driver_independent_all_speeds
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
      (fun ω t => β t ω) P := by
  by_cases ha : α=0
  · subst α
    exact (indepFun_const_left (fun _ : ℝ≥0 => coordinateSum z) (fun ω t => β t ω)).congr
      (ginibreBrownian_center_zero_speed_constant (by omega) z hz B P hB hind).symm
      Filter.EventuallyEq.rfl
  · exact ginibreBrownian_center_radial_driver_independent hn α (lt_of_le_of_ne (show 0 ≤ α from
      bot_le) (Ne.symm ha))
      z hz B P hB hind e β hβC hβLim
theorem ginibreBrownian_independent_radial_Brownian_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single (⟨0, by omega⟩, 0) 1
    ∃ β : ℝ≥0 → Ω → ℝ, IsBrownianReal β P ∧
      IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
        (fun ω t => β t ω) P ∧
      (∀ t, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i) (fun s ω =>
          ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
          t (k+1) ω) atTop (β t)) := by
  obtain ⟨β, hβ, hM, hL, h0, hLim, hShift, hPast⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  exact ⟨β, hβ, ginibreBrownian_center_radial_driver_independent_all_speeds hn α z hz B P hB hind
    _ β hβ.cont hLim, hLim⟩
end
end GinibrePoincare
