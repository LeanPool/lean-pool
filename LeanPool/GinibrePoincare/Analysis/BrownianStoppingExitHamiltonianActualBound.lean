/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianActualBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianRestrictedVolterra
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianFiniteLifetime
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonian

/-! Actual canonical lifetime probability estimates from a genuine stopped Hamiltonian
martingale decomposition. Compactness supplies all required integrability. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianHamiltonianStoppedGenerator_continuous {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) :
    Continuous (fun s : ℝ => ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n)
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω)) := by
  let X := fun s : ℝ => ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω
  have hX : Continuous X :=
    (ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T ω).comp
        continuous_real_toNNReal
  have hFree (s : ℝ) : CollisionFree (X s) :=
    (ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T (Real.toNNReal s) ω).1
  have hH : ContDiffOn ℝ 2 (ginibreHamiltonian n) {x | CollisionFree x} :=
    fun x hx => ((ginibreHamiltonian_contDiffAt n x hx).of_le (by exact WithTop.coe_le_coe.mpr (show
                                                                    (2 : ENat) ≤ ⊤ from
                                                                        le_top))).contDiffWithinAt
  have hd : Continuous (fun s : ℝ => fderiv ℝ (ginibreHamiltonian n) (X s)) :=
    (hH.continuousOn_fderiv_of_isOpen (isOpen_collisionFree n) (by norm_num)).comp_continuous hX
        hFree
  have hg : Continuous (fun s : ℝ => ginibreHamiltonianGradientNormSq n (X s)) := by
    unfold ginibreHamiltonianGradientNormSq
    apply continuous_finsetSum
    intro j _
    exact ((hd.clm_apply continuous_const).pow 2).add ((hd.clm_apply continuous_const).pow 2)
  have hc : Continuous (fun s : ℝ => 4*α-(α/(n : ℝ)^2)*ginibreHamiltonianGradientNormSq n (X s)) :=
    continuous_const.sub (continuous_const.mul hg)
  apply hc.congr
  intro s
  exact (ginibreRealPaperSpeedGenerator_hamiltonian hn α (X s) (hFree s)).symm

theorem ginibreBrownianMaximalLifetime_probability_bound_of_martingale
    {Ω : Type*} [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (hRlower : -ginibreHamiltonianLowerBoundConstant n < R) (T : ℝ≥0)
    (N : ℝ≥0 → Ω → ℝ)
    (hN : Martingale N (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) P)
    (hNcont : ∀ᵐ ω ∂P, Continuous (fun t => N t ω)) (hN0 : N 0 =ᵐ[P] 0)
    (hIto : (fun ω => ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T
        ω)) =ᵐ[P]
      (fun ω => ginibreHamiltonian n z + N (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ω +
        ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
          ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n)
            (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω))) :
    P.real {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)} ≤
      (ginibreHamiltonian n z + ginibreHamiltonianLowerBoundConstant n + 4*α*(T : ℝ))/
        (R+ginibreHamiltonianLowerBoundConstant n) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  let X := fun s : ℝ => ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s)
  let Y := fun ω => ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω)
  let A := fun ω => ∫ s in (0 : ℝ)..(σ ω : ℝ),
    ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X s ω)
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR T
  have hσT (ω : Ω) : σ ω ≤ T := ginibreDrivenHamiltonianBoundedStop_le n α _ z R T
  have hAdapt := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
  have hYmeas : Measurable Y := (ginibreHamiltonian_measurable n).comp
    ((hAdapt T).mono (F.le T)).measurable
  have hY : Integrable Y P := (integrable_const (|R|+|ginibreHamiltonianLowerBoundConstant
      n|)).mono'
    hYmeas.aestronglyMeasurable (ae_of_all P (fun ω => by
      have hr := ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T T ω
      have hb := ginibreHamiltonian_bounded_below hn _ hr.1
      have hUpper := hr.2
      change ‖ginibreHamiltonian n _‖ ≤ _
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [le_abs_self R, le_abs_self (ginibreHamiltonianLowerBoundConstant n),
        neg_abs_le R, neg_abs_le (ginibreHamiltonianLowerBoundConstant n)]))
  have hstop := (continuous_martingale_bounded_stopping_integral hN hNcont hσ hσT).1
  have hAeq : (fun ω => Y ω-ginibreHamiltonian n z-N (σ ω) ω) =ᵐ[P] A := hIto.mono (fun ω h => by
    change Y ω = ginibreHamiltonian n z+N (σ ω) ω+A ω at h
    linarith)
  have hA : Integrable A P := ((hY.sub (integrable_const _)).sub hstop).congr hAeq
  have hEnd (ω : Ω) : X (σ ω : ℝ) ω = ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω := by
    change ginibreBrownianMaximalProcess n α z B (min (Real.toNNReal (σ ω : ℝ)) (σ ω)) ω =
      ginibreBrownianMaximalProcess n α z B (min T (σ ω)) ω
    rw [Real.toNNReal_coe, min_self, min_eq_right (hσT ω)]
  have hIto' : (fun ω => ginibreHamiltonian n (X (σ ω : ℝ) ω)) =ᵐ[P]
      (fun ω => ginibreHamiltonian n z + N (σ ω) ω + A ω) := by
    filter_upwards [hIto] with ω h
    rw [hEnd]
    exact h
  have hExit := ginibreHamiltonian_stopped_exit_bound hN hNcont hN0 hσ hσT hn hα X z
    (ae_of_all P (fun ω t _ => (ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T
        (Real.toNNReal t) ω).1))
    (ae_of_all P (fun ω => (ginibreBrownianHamiltonianStoppedGenerator_continuous hn α z hz B R hR T
        ω).intervalIntegrable _ _))
    hA hIto' R hRlower
  have hSubset : {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)} ⊆
      {ω | R ≤ ginibreHamiltonian n (X (σ ω : ℝ) ω)} := by
    intro ω hω
    change R ≤ ginibreHamiltonian n (X (σ ω : ℝ) ω)
    rw [hEnd ω, ginibreBrownianMaximalLifetime_le_stopped_hamiltonian_eq hn α z hz B R hR T ω hω]
  exact (measureReal_mono hSubset).trans hExit

end
end GinibrePoincare
