/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterRadialDriverIndependence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBrownian
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiScalarFunctional
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGlobal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialCenterIndependence

/-! The actual center Brownian driver is a measurable functional of the center
path, hence independent of the actual relative-radius Brownian driver. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_driver_eq_Lamperti_functional
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (hα : 0 < α) (z : Configuration n) (hz : CollisionFree z)
    (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t)) :
    (fun ω t => β t ω) =ᵐ[P] (fun ω => ginibreCenterScalarLampertiPathFunctional n α z
      (fun t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))) := by
  have hl := ginibreBrownianMaximalProcess_global_center_Lamperti_identity
    hn α z hz hcenter B P hB hind e β hβC hβLim
  have hnz := ginibreBrownian_center_global_nonvanishing hn α z hz hcenter B P hB hind
  have hx := (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB
      hind).2
  have hc : 0 < Real.sqrt (2*(α : ℝ)/(n : ℝ)) := Real.sqrt_pos.mpr
    (div_pos (mul_pos (by norm_num) (show 0 < (α : ℝ) from hα))
      (by exact_mod_cast (show 0 < n by omega)))
  filter_upwards [hl, hnz, hx] with ω hl hnz hx
  funext t
  have hX : Continuous (fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) := by
    simpa only [Real.toNNReal_coe] using
      (show Continuous (fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B (s : ℝ).toNNReal ω)
        from hx.1.comp NNReal.continuous_coe)
  have hS : Continuous (fun s : ℝ≥0 => coordinateSum (ginibreBrownianMaximalProcess n α z B s ω)) :=
      by
    simpa only [Function.comp_def, coordinateSumCLM_apply] using
      (coordinateSumCLM n).continuous.comp hX
  have hp (s : ℝ≥0) : 0 < Complex.normSq (coordinateSum (ginibreBrownianMaximalProcess n α z B s ω))
      :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnz s))
  rw [ginibreCenterScalarLampertiPathFunctional_eq_integral n α z _ hS hp]
  have hh := hl t
  change Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω))-
    Real.sqrt (ginibreCenterSquared n z) = _ at hh
  change β t ω = (Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω))-
    Real.sqrt (ginibreCenterSquared n z)-_)/Real.sqrt (2*(α : ℝ)/(n : ℝ))
  apply (eq_div_iff hc.ne').mpr
  unfold ginibreCenterSquared at hh ⊢
  nlinarith [hh]

theorem ginibreBrownian_center_radial_Brownian_drivers_independent
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (hα : 0 < α) (z : Configuration n) (hz : CollisionFree z)
    (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (eS eR : EuclideanSpace ℝ (Fin n × Fin 2)) (βS βR : ℝ≥0 → Ω → ℝ)
    (hβSC : ∀ᵐ ω ∂P, Continuous (fun t => βS t ω))
    (hβSLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n eS (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (βS t))
    (hβRC : ∀ᵐ ω ∂P, Continuous (fun t => βR t ω))
    (hβRLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n eR (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (βR t)) :
    IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P := by
  have hi := (ginibreBrownian_center_radial_driver_independent hn α hα z hz B P hB hind
    eR βR hβRC hβRLim).comp
      (ginibreCenterScalarLampertiPathFunctional_measurable n α z) measurable_id
  exact hi.congr
    (ginibreBrownian_center_driver_eq_Lamperti_functional hn α hα z hz hcenter B P hB hind
      eS βS hβSC hβSLim).symm Filter.EventuallyEq.rfl

/-- Two genuine independent original-noise Brownian drivers, with the exact
whole-process center and relative Lamperti equations. -/
theorem ginibreBrownian_independent_center_radial_drivers_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (hα : 0 < α) (z : Configuration n) (hz : CollisionFree z)
    (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B t ω)-
          ginibreSquareRootCenter n z = Real.sqrt (2*(α : ℝ)/(n : ℝ))*βS t ω+
            ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α
              (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B s.toNNReal ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ginibreSquareRootRadius (ginibreBrownianMaximalProcess n α z B t ω)-
          ginibreSquareRootRadius z = Real.sqrt (2*(α : ℝ)/(n : ℝ))*βR t ω+
            ∫ s in (0 : ℝ)..t, ginibreLampertiRadialDrift n α
              (pairwiseRadius (ginibreBrownianMaximalProcess n α z B s.toNNReal ω))) := by
  obtain ⟨βS, hβS, hMS, hLS, h0S, hLimS, hShiftS, hPastS⟩ :=
    ginibreBrownianMaximalProcess_center_Brownian_exists hn α z hz hcenter B P hB hind
  obtain ⟨βR, hβR, hMR, hLR, h0R, hLimR, hShiftR, hPastR⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨βS, βR, hβS, hβR,?_,?_,?_⟩
  · exact ginibreBrownian_center_radial_Brownian_drivers_independent hn α hα z hz hcenter B P hB
      hind
      _ _ βS βR hβS.cont hLimS hβR.cont hLimR
  · exact ginibreBrownianMaximalProcess_global_center_Lamperti_identity hn α z hz hcenter B P hB
      hind
      _ βS hβS.cont hLimS
  · exact ginibreBrownianMaximalProcess_global_Lamperti_identity hn α z hz B P hB hind
      _ βR hβR.cont hLimR

end
end GinibrePoincare
