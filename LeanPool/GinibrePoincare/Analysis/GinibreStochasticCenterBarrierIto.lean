/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterBarrierIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLogRegularization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral

/-! Genuine center-barrier martingales for the original Brownian Ginibre SDE.
The regularization permits zero centers and supplies a uniform drift upper bound. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonianSublevel_centerSquared_bound {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ ginibreHamiltonianSublevel n R, ginibreCenterSquared n x ≤ C := by
  obtain ⟨C, hC⟩ := (ginibreHamiltonianSublevel_isCompact hn R).exists_bound_of_continuousOn
    (contDiff_ginibreCenterSquared n).continuous.continuousOn
  refine ⟨|C|+1, by positivity,?_⟩
  intro x hx
  have hh := hC x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ginibreCenterSquared_nonneg n x)] at hh
  linarith [le_abs_self C]

theorem ginibreBrownian_center_barrier_ito_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        ginibreCenterLogBarrier n ε (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          ginibreCenterLogBarrier n ε z ≤ J t ω+(4*(α : ℝ)/(n : ℝ))*(t : ℝ)) := by
  have hf : ContDiffOn ℝ 2 (ginibreCenterLogBarrier n ε) {x | CollisionFree x} :=
    ((contDiff_ginibreCenterLogBarrier n hε).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLim, hEq, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind
      R hR T (ginibreCenterLogBarrier n ε) hf
  refine ⟨J, hJM, hJC, hJL, hJ0,?_⟩
  filter_upwards [hEq] with ω hω
  intro t ht
  rw [hω t ht]
  apply add_le_add (le_refl _)
  have hcont : Continuous (fun s : ℝ => ginibreRealPaperSpeedGenerator n α (ginibreCenterLogBarrier
      n ε)
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) := by
    let X := fun s : ℝ => ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω
    have hc : Continuous X := (ginibreBrownianHamiltonianStoppedProcess_continuous
      (by omega) α z hz B R hR T ω).comp continuous_real_toNNReal
    have hg : Continuous (fun s : ℝ => (4*(α : ℝ)/(n : ℝ))*(ginibreCenterSquared n (X s)/
      (ginibreCenterSquared n (X s)+ε)-ε/(ginibreCenterSquared n (X s)+ε)^2)) := by
      have hr := (contDiff_ginibreCenterSquared n).continuous.comp hc
      have hp := fun s => (add_pos_of_nonneg_of_pos (ginibreCenterSquared_nonneg n (X s)) hε).ne'
      exact continuous_const.mul ((hr.div (hr.add continuous_const) hp).sub
        (continuous_const.div ((hr.add continuous_const).pow 2) (fun s => pow_ne_zero 2 (hp s))))
    apply hg.congr
    intro s
    exact (ginibreRealPaperSpeedGenerator_centerLogBarrier hn α hε _
      (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s.toNNReal
          ω).1).symm
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ)) := by
      apply intervalIntegral.integral_mono_on t.coe_nonneg (hcont.intervalIntegrable _ _)
          intervalIntegrable_const
      intro s hs
      exact ginibreRealPaperSpeedGenerator_centerLogBarrier_le hn α hε _
        (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s.toNNReal ω).1
    _ = _ := by simp;ring
end
end GinibrePoincare
