/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementLocalization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral

/-! Actual positive-start increments of the regularized center Itô martingales,
valid also when the original center vanishes at time zero. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterRegularized_generator_continuous
    {n : ℕ} (hn : 0 < n) (α : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (hX : Continuous X)
    (hCF : ∀ u, CollisionFree (X u)) :
    Continuous (fun r : ℝ => ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) := by
  let f := ginibreCenterSquareRootRegularized n δ
  have hf : ContDiffOn ℝ 2 f {x | CollisionFree x} :=
    ((contDiff_ginibreCenterSquareRootRegularized n hδ).of_le (by exact WithTop.coe_le_coe.mpr (show
                                                                    (2 : ENat) ≤ ⊤ from
                                                                        le_top))).contDiffOn
  have hx : Continuous (fun r : ℝ => X r.toNNReal) := hX.comp continuous_real_toNNReal
  have hb : Continuous (fun r : ℝ => ginibreLangevinDrift n α (X r.toNNReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ContinuousAt.comp (f := fun s : ℝ => X s.toNNReal) (x := r)
      (ginibreLangevinDrift_contDiffAt n α _ (hCF _)).continuousAt hx.continuousAt
  have hd := ((hf.continuousOn_fderiv_of_isOpen (isOpen_collisionFree n) (by
      norm_num)).comp_continuous hx
    (fun r => hCF _)).clm_apply hb
  have hl := (itoConfigurationLaplacian_continuousOn f _ (isOpen_collisionFree n)
      hf).comp_continuous hx
    (fun r => hCF _)
  have he : (fun r : ℝ => ginibreRealPaperSpeedGenerator n α f (X r.toNNReal)) =
      fun r => fderiv ℝ f (X r.toNNReal) (ginibreLangevinDrift n α (X r.toNNReal))+
        (α/(n : ℝ)^2)*configurationLaplacian f (X r.toNNReal) :=
    funext (fun r => (ginibreLangevin_fderiv_generator hn α f _ (hCF _)).symm)
  rw [he]
  exact hd.add (continuous_const.mul hl)

theorem ginibreBrownianMaximalProcess_center_regularized_increment_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      (∀ t ≤ T, TendstoInMeasure P (ginibreConfigurationBrownianGradientSum n B α X
        (ginibreCenterSquareRootRegularized n δ) t) atTop (J t)) ∧
      (∀ᵐ ω ∂P, ∀ a t : ℝ≥0, a ≤ t →
        t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω →
        (∀ u ∈ Icc a t, δ < ginibreCenterSquared n (X u ω)) →
        ginibreSquareRootCenter n (X t ω)-ginibreSquareRootCenter n (X a ω) =
          J t ω-J a ω+∫ r in (a : ℝ)..t, ginibreLampertiCenterDrift n α
            (ginibreCenterSquared n (X r.toNNReal ω))) := by
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  have hf : ContDiffOn ℝ 2 (ginibreCenterSquareRootRegularized n δ) {x | CollisionFree x} :=
    ((contDiff_ginibreCenterSquareRootRegularized n hδ).of_le (by exact WithTop.coe_le_coe.mpr (show
                                                                    (2 : ENat) ≤ ⊤ from
                                                                        le_top))).contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind
      R hR T (ginibreCenterSquareRootRegularized n δ) hf
  refine ⟨J, hJM, hJC, hJL, hJS,?_⟩
  filter_upwards [hIto] with ω hIto
  intro a t hat ht hlow
  have hCF (u : ℝ≥0) : CollisionFree (X u ω) :=
    (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T u ω).1
  have hg := ginibreCenterRegularized_generator_continuous (by omega) α δ hδ (fun u => X u ω)
    (ginibreBrownianHamiltonianStoppedProcess_continuous (by omega) α z hz B R hR T ω) hCF
  exact ginibreCenterRegularizedIto_positive_start_increment hn α δ hδ (fun u => X u ω) z
    (fun u => J u ω) a t hat (fun u hu => hCF u) hlow
    (hg.intervalIntegrable 0 a) (hg.intervalIntegrable a t)
    (hIto a (hat.trans ht)) (hIto t ht)

end
end GinibrePoincare
