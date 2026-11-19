/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticPuncturedUnitFieldPartialMeanSquare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialContinuous
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionFinite
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldBrownian

/-! Genuine partial-sum mean-square convergence for the punctured unit-field
Brownian integral, identified by its terminal law and martingale property. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem realMartingale_eq_until_of_terminal_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M N : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P) (hN : Martingale N ℱ P)
    (T t : ℝ≥0) (ht : t ≤ T) (he : M T =ᵐ[P] N T) : M t =ᵐ[P] N t :=
  ((hM.condExp_ae_eq ht).symm.trans (condExp_congr_ae he)).trans (hN.condExp_ae_eq ht)

theorem ginibrePuncturedUnitField_partial_meanSquare_of_horizon_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Ioi 0))
    (β : ℝ≥0 → Ω → ℝ)
    (hβM : Martingale β (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) P)
    (hβlim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k + 1) ω) atTop (β t))
    (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformPartialSum (B i) (fun s ω => u s ω i) T (k+1) t ω)-β t ω)^2 ∂P)
      atTop (𝓝 0) := by
  classical
  classical
  let ℱ := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let A := fun i s ω => u s ω i
  have hA (i : ι) (s : ℝ≥0) : @Measurable Ω ℝ (ℱ s) _ (A i s) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable.comp (hu s)
  have hb (i : ι) (s : ℝ≥0) (ω : Ω) : ‖A i s ω‖ ≤ 1 := by
    simpa only [A, hunit s ω] using PiLp.norm_apply_le (u s ω) i
  have hAc (i : ι) : ∀ᵐ ω ∂P, ContinuousOn (fun s => A i s ω) (Ioi 0) :=
    hc.mono (fun ω hω => (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp_continuousOn hω)
  have hAL (i : ι) (s : ℝ≥0) : MemLp (A i s) 2 P := MemLp.of_bound
    ((hA i s).mono (ℱ.le s) le_rfl).aestronglyMeasurable 1 (ae_of_all P (hb i s))
  have hex (i : ι) := brownianPuncturedPartialIntegral_exists B P hB hind i (A i) (hA i)
    (hAc i) 1 (by norm_num) (hb i) T hT
  choose M hM hMC hML hM0 hMS using hex
  have hPL (i : ι) (k : ℕ) (r : ℝ≥0) : MemLp (brownianUniformPartialSum (B i) (A i) T (k+1) r) 2 P
      :=
    brownianUniformPartialSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (A i) (hA i) (hAL i) T (k+1) r
  have hterminal (i : ι) (k : ℕ) : brownianUniformPartialSum (B i) (A i) T (k+1) T =
      brownianUniformLeftSum (B i) (A i) T (k+1) := funext fun ω =>
    brownianUniformPartialSum_terminal (B i) (A i) T (k+1) ω
  have hPT (i : ι) : TendstoInMeasure P (fun k => brownianUniformLeftSum (B i) (A i) T (k+1))
      atTop (M i T) := by
    have hh := ginibre_tendstoInMeasure_of_meanSquare P _ _
      (fun k => ((hPL i k T).sub (hML i T)).integrable_sq) (hMS i T le_rfl)
    simpa only [hterminal] using hh
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (A i) T (k+1)) (fun i => M i T)
    (fun i k => by simpa only [hterminal] using (hPL i k T).aestronglyMeasurable) hPT
  let J : ℝ≥0 → Ω → ℝ := ∑ i, M i
  have hJM : Martingale J ℱ P := by
    have hh (S : Finset ι) : Martingale (∑ i ∈ S, M i) ℱ P := by
      induction S using Finset.induction_on with
      | empty => simpa using martingale_zero ℝ ℱ P
      | @insert i S hi ih => rw [Finset.sum_insert hi]; exact (hM i).add ih
    exact hh Finset.univ
  have hJT : J T =ᵐ[P] β T := by
    have hh := tendstoInMeasure_ae_unique hsum (hβlim T)
    convert hh using 1
    funext ω
    simp only [J, Finset.sum_apply]
  have he := realMartingale_eq_until_of_terminal_ae P ℱ J β hJM hβM T t ht hJT
  have hz := actualMeanSquareZero_finset_sum P Finset.univ
    (fun i k ω => brownianUniformPartialSum (B i) (A i) T (k+1) t ω-M i t ω)
    (fun i k => (hPL i k t).sub (hML i t)) (fun i => hMS i t ht)
  have hEq (k : ℕ) : (∫ ω,
      ((∑ i, brownianUniformPartialSum (B i) (fun s ω => u s ω i) T (k+1) t ω)-β t ω)^2 ∂P) =
      ∫ ω, (∑ i, (brownianUniformPartialSum (B i) (A i) T (k+1) t ω-M i t ω))^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    have hh : (∑ i, M i t ω)=β t ω := by simpa only [J, Finset.sum_apply] using hω
    rw [← hh, Finset.sum_sub_distrib]
  simp_rw [hEq]
  exact hz

end
end GinibrePoincare
