/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterBarrierExpectation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBarrierIto
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitContinuous

/-! Expected logarithmic center barrier at any genuine earlier bounded stop.
The actual Itô martingale is constructed internally from the original SDE. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_barrier_stopped_expectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτσ : ∀ ω, τ ω ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    Integrable (fun ω => ginibreCenterLogBarrier n ε
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T (τ ω) ω)) P ∧
    (∫ ω, ginibreCenterLogBarrier n ε
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T (τ ω) ω) ∂P) ≤
      ginibreCenterLogBarrier n ε z+(4*(α : ℝ)/(n : ℝ))*(T : ℝ) := by
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hτT (ω : Ω) : τ ω ≤ T := (hτσ ω).trans (ginibreDrivenHamiltonianBoundedStop_le n α _ z R T)
  have hXA := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted (by omega) α z hz B P hB R hR
      T
  have hXC := ginibreBrownianHamiltonianStoppedProcess_continuous (by omega) α z hz B R hR T
  have hEval : Measurable (fun ω => X (τ ω) ω) := by
    have h := stronglyMeasurable_stoppedValue_of_le (hXA.isStronglyProgressive_of_continuous hXC) hτ
      (fun ω => by exact_mod_cast hτT ω)
    have ha := (h.mono (F.le T)).measurable
    exact ha
  obtain ⟨C, hC⟩ := (ginibreHamiltonianSublevel_isCompact (show 0 < n by omega)
      R).exists_bound_of_continuousOn
    (contDiff_ginibreCenterLogBarrier n hε).continuous.continuousOn
  have hY : Integrable (fun ω => ginibreCenterLogBarrier n ε (X (τ ω) ω)) P :=
    (integrable_const C).mono' ((contDiff_ginibreCenterLogBarrier n hε).continuous.measurable.comp
        hEval).aestronglyMeasurable
      (ae_of_all P (fun ω => hC _ (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz
          B R hR T (τ ω) ω)))
  obtain ⟨J, hJM, hJC, hJL, hJ0, hEq⟩ := ginibreBrownian_center_barrier_ito_exists hn α z hz B P hB
      hind R hR T hε
  obtain ⟨hJStop, hJInt⟩ := continuous_martingale_bounded_stopping_integral hJM (ae_of_all P hJC) hτ
      hτT
  have hJInt0 : (∫ ω, J (τ ω) ω ∂P)=0 := by
    rw [hJInt, integral_congr_ae hJ0]
    simp
  refine ⟨hY,?_⟩
  have hle : (fun ω => ginibreCenterLogBarrier n ε (X (τ ω) ω)) ≤ᵐ[P]
      (fun ω => ginibreCenterLogBarrier n ε z+J (τ ω) ω+(4*(α : ℝ)/(n : ℝ))*(T : ℝ)) := by
    filter_upwards [hEq] with ω hω
    have hh := hω (τ ω) (hτσ ω)
    have hc : 0 ≤ 4*(α : ℝ)/(n : ℝ) := div_nonneg (mul_nonneg (by norm_num) α.coe_nonneg)
        (Nat.cast_nonneg n)
    have hb := mul_le_mul_of_nonneg_left (show (τ ω : ℝ) ≤ T by exact_mod_cast hτT ω) hc
    change ginibreCenterLogBarrier n ε (X (τ ω) ω)-ginibreCenterLogBarrier n ε z ≤ _ at hh
    linarith
  have hb := integral_mono_ae hY (((integrable_const _).add hJStop).add (integrable_const _)) hle
  have hc1 := integrable_const (ginibreCenterLogBarrier n ε z) (μ := P)
  have hc2 := integrable_const ((4*(α : ℝ)/(n : ℝ))*(T : ℝ)) (μ := P)
  have he : (∫ ω, ginibreCenterLogBarrier n ε z+J (τ ω) ω+
      (4*(α : ℝ)/(n : ℝ))*(T : ℝ) ∂P) = ginibreCenterLogBarrier n ε z+
        (4*(α : ℝ)/(n : ℝ))*(T : ℝ) := by
    have he1 := integral_add (hc1.add hJStop) hc2
    have he2 := integral_add hc1 hJStop
    simp only [Pi.add_apply] at he1 he2
    rw [he1, he2, hJInt0]
    simp
  change (∫ ω, ginibreCenterLogBarrier n ε (X (τ ω) ω) ∂P) ≤
    (∫ ω, ginibreCenterLogBarrier n ε z+J (τ ω) ω+(4*(α : ℝ)/(n : ℝ))*(T : ℝ) ∂P) at hb
  rw [he] at hb
  exact hb
end
end GinibrePoincare
