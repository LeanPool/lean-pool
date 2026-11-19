/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiNoiseCoefficient
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiRegularization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBeforeHitting
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticIntegralUntilIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion

/-! Actual Lamperti identification of the constructed radial Brownian motion
with the square-root-radius test of the original global solution. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_center_Lamperti_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k + 1) ω) atTop (β t))
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (C δ : ℝ) (hδ : 0 < δ) (hδz : 2 * δ ≤ ginibreCenterSquared n z)
    (hBound : ∀ t ω, ginibreCenterSquared n
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω) ≤ C) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    let θ := fun ω => min (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)
      (hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
        {x : ℝ | C-2*δ ≤ ‖x‖} 0 T ω)
    ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
      (ginibreSquareRootCenter n) (X t ω)-(ginibreSquareRootCenter n) z =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*β t ω+
          ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (ginibreCenterSquared n (X s.toNNReal
              ω)) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let c := Real.sqrt (2*(α : ℝ)/(n : ℝ))
  let θ := fun ω => min (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)
    (hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
      {x : ℝ | C-2*δ ≤ ‖x‖} 0 T ω)
  have hθσ (ω : Ω) : θ ω ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω := min_le_left _ _
  have hlow (ω : Ω) (t : ℝ≥0) (ht : t ≤ θ ω) : δ < ginibreCenterSquared n (X t ω) := by
    have hh := ginibreCenterSquared_ge_until_small_hitting X C (2*δ) T t ω hBound
      ((contDiff_ginibreCenterSquared n).continuous.comp
        (ginibreBrownianHamiltonianStoppedProcess_continuous (by omega) α z hz B R hR T ω))
      (by simpa [X, ginibreBrownianHamiltonianStoppedProcess_initial n α z hz B R T ω] using hδz)
      (ht.trans (min_le_right _ _))
    linarith
  have hf : ContDiffOn ℝ 2 (ginibreCenterSquareRootRegularized n δ) {x | CollisionFree x} :=
    ((contDiff_ginibreCenterSquareRootRegularized n hδ).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind
      R hR T (ginibreCenterSquareRootRegularized n δ) hf
  have heq : ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
      J t ω=c*β t ω := by
    apply ginibreContinuous_probability_limits_eq_until P
      (ginibreConfigurationBrownianGradientSum n B α X (ginibreCenterSquareRootRegularized n δ))
      (fun t k ω => c*∑ i, brownianUniformLeftSum (B i) (fun s ω =>
        ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i) t (k+1) ω)
      J (fun t ω => c*β t ω) (Eventually.of_forall hJC)
      (hβC.mono (fun ω hω => continuous_const.mul hω)) T
      θ
      (fun ω => (hθσ ω).trans (ginibreDrivenHamiltonianBoundedStop_le n α _ z R T)) hJS
      (fun t ht => ginibre_tendstoInMeasure_const_mul P _ _ c (hβLim t))
    intro t ht k ω hts
    classical
    rw [ginibreConfigurationBrownianGradientSum_eq, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold brownianUniformLeftSum
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    have hjt : itoUniformNNTime t (k+1) j ≤ t :=
      itoUniformNNTime_le_end t (k+1) j (Nat.succ_pos k) (Finset.mem_range.mp hj).le
    have hlj := hlow ω _ (hjt.trans hts)
    have he : X (itoUniformNNTime t (k+1) j) ω =
        ginibreBrownianMaximalProcess n α z B (itoUniformNNTime t (k+1) j) ω := by
      change ginibreBrownianMaximalProcess n α z B (min _ _) ω = _
      rw [min_eq_left ((hjt.trans hts).trans (hθσ ω))]
    rw [← mul_assoc, (ginibreCenterSquareRootRegularized_eventuallyEq hδ _ hlj).fderiv_eq]
    rw [ginibre_squareRootCenter_noise_coordinate hn α α.coe_nonneg _ (hδ.trans hlj) e i, he,
        mul_assoc]
  filter_upwards [heq, hIto] with ω hω hItoω
  intro t ht
  have hh := hItoω t (ht.trans (hθσ ω))
  rw [ginibreCenterSquareRootRegularized_eq hδ _ (hlow ω t ht).le,
    ginibreCenterSquareRootRegularized_eq hδ z (by linarith), hω t ht] at hh
  have hi : (∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X s.toNNReal ω)) =
      ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (ginibreCenterSquared n (X s.toNNReal ω)) :=
          by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hst : s.toNNReal ≤ t := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    exact ginibreCenterSquareRootRegularized_generator hn α hδ _
      (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T _ ω).1
      (hlow ω _ (hst.trans ht))
  rw [hi] at hh
  exact hh

end
end GinibrePoincare
