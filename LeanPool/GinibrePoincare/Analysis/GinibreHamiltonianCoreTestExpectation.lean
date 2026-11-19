/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCoreTestExpectation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianStoppedTestExpectation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ginibre Hamiltonian core test expectation

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_core_test_expectation`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_core_test_expectation_with_integrability
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), ginibreRealPaperSpeedGenerator n α f
      (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) P ∧
    (∫ ω, f (ginibreBrownianMaximalProcess n α z B T ω) ∂P) =
      f z+∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) ∂P := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let R : ℕ → ℝ := fun m => ginibreHamiltonian n z+m
  have hR (m : ℕ) : ginibreHamiltonian n z ≤ R m := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ)
                                                         m]
  let σ := fun m => ginibreBrownianHamiltonianBoundedStop n α z B (R m) T
  let X := fun m => ginibreBrownianHamiltonianStoppedProcess n α z B (R m) T
  let Y := fun m ω => f (X m T ω)
  let A := fun m ω => ∫ s in (0 : ℝ)..(σ m ω : ℝ), ginibreRealPaperSpeedGenerator n α f (X m
      s.toNNReal ω)
  let Ylim := fun ω => f (ginibreBrownianMaximalProcess n α z B T ω)
  let Alim := fun ω => ∫ s in (0 : ℝ)..(T : ℝ), ginibreRealPaperSpeedGenerator n α f
      (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)
  obtain ⟨C, hC⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  have hLf : Continuous (ginibreRealPaperSpeedGenerator n α f) :=
    (continuous_ginibrePregenerator_of_core hf).const_mul _
  have hLc : HasCompactSupport (ginibreRealPaperSpeedGenerator n α f) :=
    by
      change HasCompactSupport ((fun _ => (α : ℝ)/(n : ℝ))*ginibrePregenerator n f)
      exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨D, hD⟩ := hLc.exists_bound_of_continuous hLf
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD z)
  have hYm (m : ℕ) : Integrable (Y m) P := by
    have hXa : Measurable (X m T) :=
      ((ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB (R m) (hR m) T
          T).mono (F.le T)).measurable
    exact (integrable_const C).mono' (hf.1.continuous.measurable.comp hXa).aestronglyMeasurable
      (ae_of_all P (fun ω => hC (X m T ω)))
  have hAm (m : ℕ) : Integrable (A m) P :=
    (ginibreBrownian_stopped_core_test_expectation hn α z hz B P hB hind (R m) (hR m) T f hf).1
  have hEq (m : ℕ) : (∫ ω, Y m ω ∂P)=f z+∫ ω, A m ω ∂P :=
    (ginibreBrownian_stopped_core_test_expectation hn α z hz B P hB hind (R m) (hR m) T f hf).2
  have hσlim : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, σ m ω=T := by
    filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
    obtain ⟨c, hc⟩ := ginibreDrivenHamiltonianBoundedStop_eventually_eq_cap hn α
      (ginibreBrownianFullContinuousNoise n B α ω) z hz hω T
    have hr : Tendsto R atTop atTop := tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hr.eventually (eventually_gt_atTop c)] with m hm
    exact (hc (R m) hm).2
  have hYlim : ∀ᵐ ω ∂P, Tendsto (fun m => Y m ω) atTop (𝓝 (Ylim ω)) := by
    filter_upwards [hσlim] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with m hm
    dsimp only [σ] at hm
    simp only [Y, Ylim, X, ginibreBrownianHamiltonianStoppedProcess, hm, min_self]
  have hAlim : ∀ᵐ ω ∂P, Tendsto (fun m => A m ω) atTop (𝓝 (Alim ω)) := by
    filter_upwards [hσlim] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with m hm
    dsimp only [A, Alim]
    rw [hm]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (show (0 : ℝ) ≤ T from T.property)] at hs
    have hsT : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    dsimp only [σ] at hm
    simp only [X, ginibreBrownianHamiltonianStoppedProcess, hm, min_eq_left hsT]
  have hAbound (m : ℕ) : ∀ᵐ ω ∂P, ‖A m ω‖ ≤ D*(T : ℝ) := ae_of_all P (fun ω => by
    have hb : ‖A m ω‖ ≤ D*|(σ m ω : ℝ)-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => hD (X m s.toNNReal ω))
    have hσT : σ m ω ≤ T := ginibreDrivenHamiltonianBoundedStop_le n α _ z (R m) T
    exact hb.trans (by simpa only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ (σ m ω : ℝ) from (σ m
                         ω).property)] using
      mul_le_mul_of_nonneg_left (show (σ m ω : ℝ) ≤ T from hσT) hD0))
  have hYT := tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun m => (hYm m).aestronglyMeasurable) (integrable_const C)
    (fun m => ae_of_all P (fun ω => hC (X m T ω))) hYlim
  have hAT := tendsto_integral_of_dominated_convergence (fun _ : Ω => D*(T : ℝ))
    (fun m => (hAm m).aestronglyMeasurable) (integrable_const _) hAbound hAlim
  have he : (fun m => ∫ ω, Y m ω ∂P)=(fun m => f z+∫ ω, A m ω ∂P) := funext hEq
  rw [he] at hYT
  have hAlimMeas : AEStronglyMeasurable Alim P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hAm m).aestronglyMeasurable) hAlim
  have hAlimBound : ∀ᵐ ω ∂P, ‖Alim ω‖ ≤ D*(T : ℝ) := by
    filter_upwards [hAlim, ae_all_iff.mpr hAbound] with ω hω hb
    exact le_of_tendsto hω.norm (Eventually.of_forall hb)
  refine ⟨(integrable_const (D*(T : ℝ))).mono' hAlimMeas hAlimBound,?_⟩
  exact tendsto_nhds_unique hYT (tendsto_const_nhds.add hAT)

theorem ginibreBrownian_core_test_expectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (∫ ω, f (ginibreBrownianMaximalProcess n α z B T ω) ∂P) =
      f z+∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) ∂P :=
  (ginibreBrownian_core_test_expectation_with_integrability hn α z hz B P hB hind T f hf).2

end
end GinibrePoincare
