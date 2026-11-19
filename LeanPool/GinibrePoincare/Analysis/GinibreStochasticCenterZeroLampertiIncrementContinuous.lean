/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementContinuous.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementGlobal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity

/-! Simultaneous positive-start Lamperti identities for the actual center
Brownian driver, including zero initial center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterShiftedDrift_integral (n : ℕ) (α : ℝ)
    (X : ℝ≥0 → Configuration n) (a r : ℝ≥0) :
    (∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (X s.toNNReal))) =
    ∫ s in (0 : ℝ)..r, ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (X (a+s.toNNReal))) := by
  calc
    _ = ∫ s in (0 : ℝ)..r, ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (X (s+(a : ℝ)).toNNReal)) := by
      simpa only [zero_add, add_zero, NNReal.coe_add, add_comm] using
        (intervalIntegral.integral_comp_add_right (f := fun s : ℝ => ginibreLampertiCenterDrift n α
          (ginibreCenterSquared n (X s.toNNReal))) (a := 0) (b := (r : ℝ)) (a : ℝ)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le r.coe_nonneg] at hs
      dsimp only
      rw [Real.toNNReal_add hs.1 a.coe_nonneg, Real.toNNReal_coe, add_comm]

theorem ginibreBrownian_center_Lamperti_positive_start_all
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβShift : ∀ a r, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
      a r (k + 1)) atTop (fun ω => β (a + r) ω - β a ω))
    (a : ℝ≥0) (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ r : ℝ≥0,
      ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B (a+r) ω)-
        ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B a ω) =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*(β (a+r) ω-β a ω)+
          ∫ s in (0 : ℝ)..r, ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (a+s.toNNReal) ω)) := by
  let F := fun r ω => ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B (a+r) ω)-
    ginibreSquareRootCenter n (ginibreBrownianMaximalProcess n α z B a ω)
  let G := fun r ω => Real.sqrt (2*(α : ℝ)/(n : ℝ))*(β (a+r) ω-β a ω)+
    ∫ s in (0 : ℝ)..r, ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (a+s.toNNReal) ω))
  have hX := (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB
      hind).2
  have hFC : ∀ᵐ ω ∂P, Continuous (fun r => F r ω) := by
    filter_upwards [hX] with ω hx
    have hc : Continuous (fun r : ℝ≥0 => ginibreBrownianMaximalProcess n α z B r ω) := by
      simpa only [Function.comp_def, Real.toNNReal_coe] using hx.1.comp NNReal.continuous_coe
    exact (Real.continuous_sqrt.comp ((contDiff_ginibreCenterSquared n).continuous.comp
      (hc.comp (continuous_const.add continuous_id)))).sub continuous_const
  have hGC : ∀ᵐ ω ∂P, Continuous (fun r => G r ω) := by
    filter_upwards [hX, hβC, ginibreBrownian_center_all_positive_times_nonzero hn α hα z hz B P hB
        hind]
      with ω hx hβ hnonzero
    have hc : Continuous (fun r : ℝ≥0 => ginibreBrownianMaximalProcess n α z B r ω) := by
      simpa only [Function.comp_def, Real.toNNReal_coe] using hx.1.comp NNReal.continuous_coe
    have hd : Continuous (fun s : ℝ => ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (a+s.toNNReal) ω))) :=
      (ginibreLampertiCenterDrift_continuousOn n α).comp_continuous
        ((contDiff_ginibreCenterSquared n).continuous.comp (hc.comp (continuous_const.add
            continuous_real_toNNReal)))
        (fun s => lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnonzero _
          (add_pos_of_pos_of_nonneg ha bot_le))))
    have hi := (intervalIntegral.continuous_primitive (μ := volume) (fun b c =>
        hd.intervalIntegrable b c) 0).comp
      (NNReal.continuous_coe : Continuous (fun r : ℝ≥0 => (r : ℝ)))
    exact (continuous_const.mul ((hβ.comp (continuous_const.add continuous_id)).sub
        continuous_const)).add hi
  have hfixed (r : ℝ≥0) : ∀ᵐ ω ∂P, F r ω=G r ω := by
    have hh := ginibreBrownian_center_Lamperti_positive_start_fixed hn α hα z hz B P hB hind e β
        hβShift a r ha
    filter_upwards [hh] with ω hω
    rw [ginibreCenterShiftedDrift_integral n α (fun s => ginibreBrownianMaximalProcess n α z B s ω)
        a r] at hω
    exact hω
  have hm (m : ℕ) : ∀ᵐ ω ∂P, ∀ r ≤ (m : ℝ≥0), F r ω=G r ω :=
    ginibre_ae_continuous_identity_until P F G (fun _ => m) hFC hGC
      (fun r => (hfixed r).mono (fun ω hω _ => hω))
  filter_upwards [ae_all_iff.mpr hm] with ω hω
  intro r
  obtain ⟨m, hm⟩ := exists_nat_ge (r : ℝ)
  exact hω m r (by exact_mod_cast hm)

end
end GinibrePoincare
