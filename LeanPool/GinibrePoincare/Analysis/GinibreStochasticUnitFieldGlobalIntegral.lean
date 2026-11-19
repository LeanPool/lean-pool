/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticUnitFieldGlobalIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity

/-! Global continuous martingale integration by actual compatible finite-horizon
limits. Compatibility is derived from uniqueness of convergence in probability. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreContinuousMartingale_global_of_horizon_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (S : ℝ≥0 → ℕ → Ω → ℝ) (M : ℕ → ℝ≥0 → Ω → ℝ)
    (hM : ∀ n, Martingale (M n) F P)
    (hMC : ∀ n ω, Continuous (fun t => M n t ω))
    (hML : ∀ n t, MemLp (M n t) 2 P)
    (hM0 : ∀ n, M n 0 =ᵐ[P] (fun _ => 0))
    (hlim : ∀ (n : ℕ) (t : ℝ≥0), t ≤ (n + 1 : ℝ≥0) → TendstoInMeasure P (S t) atTop (M n t)) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧
      (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      ∀ t, TendstoInMeasure P (S t) atTop (J t) := by
  classical
  have hpair (n m : ℕ) : ∀ᵐ ω ∂P,
      ∀ t ≤ min (n+1 : ℝ≥0) (m+1 : ℝ≥0), M n t ω=M m t ω := by
    apply ginibre_ae_continuous_identity_until P (M n) (M m)
      (fun _ => min (n+1 : ℝ≥0) (m+1 : ℝ≥0))
      (Eventually.of_forall (hMC n)) (Eventually.of_forall (hMC m))
    intro t
    by_cases ht : t ≤ min (n+1 : ℝ≥0) (m+1 : ℝ≥0)
    · filter_upwards [tendstoInMeasure_ae_unique (hlim n t (ht.trans (min_le_left _ _)))
        (hlim m t (ht.trans (min_le_right _ _)))] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall (fun ω hω => (ht hω).elim)
  have hcompat : ∀ᵐ ω ∂P, ∀ (n m : ℕ), ∀ t ≤ min (n+1 : ℝ≥0) (m+1 : ℝ≥0),
      M n t ω=M m t ω := ae_all_iff.mpr (fun n => ae_all_iff.mpr (hpair n))
  have hex (t : ℝ≥0) : ∃ n : ℕ, t < (n+1 : ℝ≥0) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    refine ⟨n,?_⟩
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hn.trans (lt_add_one (n :
        ℝ))
  choose idx hidx using hex
  let J := fun t ω => M (idx t) t ω
  have heq (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n+1 : ℝ≥0)) : J t =ᵐ[P] M n t := by
    filter_upwards [hcompat] with ω hω
    exact hω (idx t) n t (le_min (hidx t).le ht)
  have hJM : Martingale J F P := by
    refine ⟨fun t => (hM (idx t)).1 t,?_⟩
    intro s t hst
    have ht := heq t (idx t) (hidx t).le
    have hs := heq s (idx t) (hst.trans (hidx t).le)
    exact (condExp_congr_ae ht).trans (((hM (idx t)).2 s t hst).trans hs.symm)
  have hJC : ∀ᵐ ω ∂P, Continuous (fun t => J t ω) := by
    filter_upwards [hcompat] with ω hω
    apply continuous_iff_continuousAt.mpr
    intro t
    have he : (fun s => J s ω) =ᶠ[nhds t] (fun s => M (idx t) s ω) := by
      filter_upwards [isOpen_Iio.mem_nhds (hidx t)] with s hs
      exact hω (idx s) (idx t) s (le_min (hidx s).le hs.le)
    exact ((hMC (idx t) ω).continuousAt).congr he.symm
  refine ⟨J, hJM, hJC, fun t => hML (idx t) t,?_, fun t => hlim (idx t) t (hidx t).le⟩
  exact (heq 0 0 (by norm_num)).trans (hM0 0)

theorem ginibreUnitField_global_continuous_integral_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω)) (i₀ : ι) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (J t)) ∧
      (∀ t, HasLaw (J t) (gaussianReal 0 t) P) := by
  classical
  classical
  have hex (n : ℕ) := ginibreUnitField_continuous_integral_exists B P hB hind u hu hunit
    (n+1 : ℝ≥0) (hc.mono (fun ω hω => hω.continuousOn)) i₀
  choose M hM hMC hML hM0 hMS hMlaw using hex
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS⟩ := ginibreContinuousMartingale_global_of_horizon_limits P
    (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
    (fun t k ω => ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω)
    M hM hMC hML hM0 hMS
  refine ⟨J, hJM, hJC, hJL, hJ0, hJS,?_⟩
  intro t
  exact brownianUnitField_integral_limit_gaussian B P (fun i => (hB i).toIsPreBrownianReal)
    hind u hu hunit i₀ t (J t) (hJS t)

end
end GinibrePoincare
