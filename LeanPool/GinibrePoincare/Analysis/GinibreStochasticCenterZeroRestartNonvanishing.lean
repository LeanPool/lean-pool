/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroRestartNonvanishing.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroPathEvent
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroPositiveTime
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMarkovLaw

/-! A positive deterministic restart time gives genuine nonhitting thereafter,
without any assumption on the initial center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance centerZeroRestartPathMeasurableSpace (n : ℕ) : MeasurableSpace C(ℝ, Configuration n)
    := borel _
local instance centerZeroRestartPathBorelSpace (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

theorem ginibreBrownian_center_nonzero_after_positive_restart
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (s+t) ω) ≠ 0 := by
  let Z := ginibreBrownianStateProcess α ⟨z, hz⟩ B s
  let N := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  let μ := P.map Z
  let ν := P.map (ginibreBrownianFullContinuousNoise n B α)
  have hZpast := ginibreBrownianStateProcess_adapted (by omega) α ⟨z, hz⟩ B P hB s
  have hZm : Measurable Z := hZpast.mono
    ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le s) le_rfl
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have hNm : Measurable N := ginibreBrownianFullContinuousNoise_measurable n _ P hBs α
  have hOrigN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure μ := (by infer_instance)
  let : IsProbabilityMeasure ν := (by infer_instance)
  let q := fun p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
    0 < ginibreCenterSquared n p.1.val →
      ginibreDrivenGlobalPathElement α p ∈ ginibrePositiveCenterPaths n
  have hq : MeasurableSet {p | q p} := by
    apply MeasurableSet.imp
    · exact measurableSet_lt measurable_const
        ((contDiff_ginibreCenterSquared n).continuous.measurable.comp
          (measurable_subtype_coe.comp measurable_fst))
    · exact (ginibreDrivenGlobalPathElement_measurable (by omega) α)
        (ginibrePositiveCenterPaths_measurable n)
  have hp : ∀ᵐ p ∂μ.prod ν, q p := by
    apply (Measure.ae_prod_iff_ae_ae hq).mpr
    apply ae_of_all
    intro x
    by_cases hx : 0 < ginibreCenterSquared n x.val
    · exact (ginibreDrivenGlobalPathElement_center_nonhitting_noise_ae hn α x hx B P hB hind).mono
        (fun N hN _ => hN)
    · exact ae_of_all ν (fun N h => (hx h).elim)
  have hi := (brownianFamily_future_continuous_noise_independent_augmented_variable
    n B P hB hind α s Z hZpast).symm
  have hLaw := hi.map_prod_eq_prod_map_map hZm.aemeasurable hNm.aemeasurable
  have hp' : ∀ᵐ ω ∂P, q (Z ω, N ω) := by
    have hν : P.map N = ν := brownianFamily_shift_continuous_noise_law_eq n B P hB hind α s
    rw [← hν,← hLaw] at hp
    exact ae_of_ae_map (hZm.prodMk hNm).aemeasurable hp
  filter_upwards [hp', ginibreBrownian_center_positive_time_nonzero (by omega) α hα z hz B P hB hind
      s hs,
    ginibreBrownianMaximalProcess_canonical_restart (by omega) α z hz B P hB hind s]
    with ω hqω hcenter hrestart
  have hpositive : 0 < ginibreCenterSquared n (Z ω).val :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hcenter)
  have hpath := hqω hpositive
  intro t
  have ht := hpath (t : ℝ) t.coe_nonneg
  have htop : ginibreDrivenMaximalLifetime n α (N ω).val (Z ω).val = ⊤ := hrestart.1
  simp only [ginibreDrivenGlobalPathElement, dite_eq_left htop, ContinuousMap.coe_mk,
    Real.toNNReal_coe] at ht
  have hval : (Z ω).val = ginibreBrownianMaximalProcess n α z B s ω := rfl
  rw [hval] at ht
  dsimp only [N] at ht
  rw [hrestart.2 t] at ht
  exact ht.ne'

/-- For every deterministic collision-free initial configuration, the actual
center is nonzero at every strictly positive time, even when it starts at zero. -/
theorem ginibreBrownian_center_all_positive_times_nonzero
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω) ≠ 0 := by
  have hlocal (k : ℕ) := ginibreBrownian_center_nonzero_after_positive_restart
    hn α hα z hz B P hB hind (1/(k+1 : ℝ≥0)) (by positivity)
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  intro t ht
  have hl := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨k, hk⟩ := (hl.eventually (gt_mem_nhds (show 0 < (t : ℝ) from ht))).exists
  have hkt : 1/(k+1 : ℝ≥0) ≤ t := by exact_mod_cast hk.le
  have hh := hω k (t-1/(k+1 : ℝ≥0))
  rw [add_tsub_cancel_of_le hkt] at hh
  exact hh

end
end GinibrePoincare
