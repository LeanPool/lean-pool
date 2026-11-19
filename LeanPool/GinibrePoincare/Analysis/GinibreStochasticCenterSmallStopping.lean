/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterSmallStopping.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

/-! Actual small-center hitting times in the compact Hamiltonian localization. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_small_stopping_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ t ω, ginibreCenterSquared n (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω) ≤ C)
          ∧
      let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
      let u := fun t ω => C-ginibreCenterSquared n (X t ω)
      let θ := hittingBtwn u {x : ℝ | C-δ ≤ ‖x‖} 0 T
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧
      (∀ ω, θ ω ≤ T) ∧
      (∀ ω, (∃ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        ginibreCenterSquared n (X t ω) ≤ δ) →
        θ ω ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω ∧
          ginibreCenterSquared n (X (θ ω) ω) ≤ δ) := by
  classical
  obtain ⟨C, hC, hBound⟩ := ginibreHamiltonianSublevel_centerSquared_bound hn R
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  have hCX : ∀ t ω, ginibreCenterSquared n (X t ω) ≤ C := fun t ω =>
    hBound _ (ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T t ω)
  let u := fun t ω => C-ginibreCenterSquared n (X t ω)
  have huC (ω : Ω) : Continuous (fun t => u t ω) := continuous_const.sub
    ((contDiff_ginibreCenterSquared n).continuous.comp
      (ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T ω))
  have huA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) u := by
    intro t
    exact (measurable_const.sub ((contDiff_ginibreCenterSquared n).continuous.measurable.comp
      (ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
          t).measurable)).stronglyMeasurable
  have huNorm (t : ℝ≥0) (ω : Ω) : ‖u t ω‖=C-ginibreCenterSquared n (X t ω) :=
    (Real.norm_eq_abs _).trans (abs_of_nonneg (sub_nonneg.mpr (hCX t ω)))
  let S := {x : ℝ | C-δ ≤ ‖x‖}
  have hS : IsClosed S := isClosed_le continuous_const continuous_norm
  let θ := hittingBtwn u S 0 T
  refine ⟨C, hC, hCX, ginibreContinuous_norm_exit_isStoppingTime _ u huA huC (C-δ) T,
    fun ω => hittingBtwn_le ω,?_⟩
  intro ω hh
  obtain ⟨t, ht, hr⟩ := hh
  have htT : t ≤ T := ht.trans (ginibreDrivenHamiltonianBoundedStop_le n α _ z R T)
  have hit : u t ω ∈ S := by change C-δ ≤ ‖u t ω‖; rw [huNorm]; linarith
  have hHit : ∃ t ∈ Icc 0 T, u t ω ∈ S := ⟨t, ⟨bot_le, htT⟩, hit⟩
  refine ⟨(hittingBtwn_le_of_mem (u := u) (s := S) (bot_le : 0 ≤ t) htT hit).trans ht,?_⟩
  have hm := drivenContinuous_closed_hitting_mem u S hS T ω (huC ω) hHit
  change C-δ ≤ ‖u (θ ω) ω‖ at hm
  rw [huNorm] at hm
  linarith
end
end GinibrePoincare
