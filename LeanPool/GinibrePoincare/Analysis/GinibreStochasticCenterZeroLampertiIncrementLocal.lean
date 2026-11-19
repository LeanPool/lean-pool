/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementLocal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementShift
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityRestriction

/-! Identification of actual positive-start center Lamperti increments by
original shifted Brownian sums, valid without positive initial center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_Lamperti_positive_start_local
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβShift : ∀ a r, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
      a r (k + 1)) atTop (fun ω => β (a + r) ω - β a ω))
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T a r : ℝ≥0) (har : a + r ≤ T)
    (δ : ℝ) (hδ : 0 < δ) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ∀ᵐ ω ∂P, (a+r ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω ∧
      ∀ u ∈ Icc a (a+r), δ < ginibreCenterSquared n (X u ω)) →
      ginibreSquareRootCenter n (X (a+r) ω)-ginibreSquareRootCenter n (X a ω) =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*(β (a+r) ω-β a ω)+
          ∫ s in (a : ℝ)..(a+r : ℝ≥0), ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (X s.toNNReal ω)) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let f := ginibreCenterSquareRootRegularized n δ
  let c := Real.sqrt (2*(α : ℝ)/(n : ℝ))
  let E : Set Ω := {ω | a+r ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω ∧
    ∀ u ∈ Icc a (a+r), δ < ginibreCenterSquared n (X u ω)}
  obtain ⟨J, hJM, hJC, hJL, hJS, hInc⟩ :=
    ginibreBrownianMaximalProcess_center_regularized_increment_exists hn α z hz B P hB hind R hR T δ
        hδ
  have hf : ContDiffOn ℝ 2 f {x | CollisionFree x} :=
    ((contDiff_ginibreCenterSquareRootRegularized n hδ).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  have hJShift := ginibreCompactGradient_shifted_probability_limit n α B P
    (fun i => (hB i).toIsPreBrownianReal) hind X
    (ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted (by omega) α z hz B P hB R hR T)
    (ginibreBrownianHamiltonianStoppedProcess_continuous (by omega) α z hz B R hR T)
    f {x | CollisionFree x} (ginibreHamiltonianSublevel n R) (isOpen_collisionFree n) hf
    (ginibreHamiltonianSublevel_isCompact (by omega) R) (fun x hx => hx.1)
    (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T) T J hJS a r har
  have hQ := ginibre_tendstoInMeasure_const_mul P _ _ c (hβShift a r)
  have hEq : ∀ k ω, ω ∈ E →
      brownianUnitShiftedUniformSum B (ginibreConfigurationBrownianGradientField n α X f) a r (k+1)
          ω =
        c*brownianUnitShiftedUniformSum B
          (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
              a r (k+1) ω := by
    intro k ω hω
    unfold brownianUnitShiftedUniformSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hu : a+itoUniformNNTime r (k+1) j ∈ Icc a (a+r) := by
      constructor
      · exact le_add_of_nonneg_right bot_le
      · exact add_le_add le_rfl (itoUniformNNTime_le_end r (k+1) j (Nat.succ_pos k)
          (Finset.mem_range.mp hj).le)
    have hXeq : X (a+itoUniformNNTime r (k+1) j) ω =
        ginibreBrownianMaximalProcess n α z B (a+itoUniformNNTime r (k+1) j) ω := by
      change ginibreBrownianMaximalProcess n α z B (min _ _) ω = _
      rw [min_eq_left (hu.2.trans hω.1)]
    change (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*fderiv ℝ f (X (a+itoUniformNNTime r (k+1) j) ω)
        (ginibreCoordinateDirection i))*_ = _
    rw [ginibreCenterRegularized_noise_coordinate_interval hn α δ hδ (fun u => X u ω) a (a+r) _ hω.2
        hu e i,
      hXeq, mul_assoc]
  have hAe : ∀ᵐ ω ∂P, ω ∈ E → J (a+r) ω-J a ω=c*(β (a+r) ω-β a ω) := by
    have hp := ginibre_tendstoInMeasure_indicator P E _ _ hJShift
    have hq := ginibre_tendstoInMeasure_indicator P E _ _ hQ
    have he : (fun k => E.indicator (brownianUnitShiftedUniformSum B
        (ginibreConfigurationBrownianGradientField n α X f) a r (k+1))) =
        fun k => E.indicator (fun ω => c*brownianUnitShiftedUniformSum B
          (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
              a r (k+1) ω) := by
      funext k ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω]
        exact hEq k ω hω
      · simp only [Set.indicator_of_notMem hω]
    rw [he] at hp
    filter_upwards [tendstoInMeasure_ae_unique hp hq] with ω hω
    intro he
    simpa only [Set.indicator_of_mem he] using hω
  filter_upwards [hAe, hInc] with ω hAe hInc
  intro hω
  have hh := hInc a (a+r) (le_add_of_nonneg_right bot_le) hω.1 hω.2
  rw [hAe hω] at hh
  exact hh

end
end GinibrePoincare
