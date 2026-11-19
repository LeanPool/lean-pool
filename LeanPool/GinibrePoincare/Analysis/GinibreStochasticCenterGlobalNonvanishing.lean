/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterGlobalNonvanishing.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLocalNonvanishing
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion

/-! The actual center cannot hit zero at any finite time when its initial
squared radius is positive. Hamiltonian localization is exhausted using the
proved global lifetime of the original Brownian solution. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_global_nonvanishing
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω) ≠ 0 := by
  have hLocal (k : ℕ) : ∀ᵐ ω ∂P, ¬ ∃ t ≤
      ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω,
      ginibreCenterSquared n (ginibreBrownianHamiltonianStoppedProcess n α z B
        (ginibreHamiltonian n z+k) k t ω)=0 := by
    apply ae_iff.mpr
    simpa only [not_not] using ginibreBrownian_center_local_zero_hitting_null hn α z hz hcenter
      B P hB hind (ginibreHamiltonian n z+k)
      (le_add_of_nonneg_right (Nat.cast_nonneg k)) k
  filter_upwards [ae_all_iff.mpr hLocal,
    ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind]
    with ω hω hExhaust
  intro t ht
  obtain ⟨k, hkt⟩ := (hExhaust t).exists
  apply hω k
  refine ⟨t, hkt,?_⟩
  change ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (min t _) ω)=0
  rw [min_eq_left hkt]
  exact ht

/-- The genuine center radius has a strictly positive lower bound on every
finite time interval, derived from non-hitting and continuous original paths. -/
theorem ginibreBrownian_center_compact_positive_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ≥0) T,
      c ≤ ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω) := by
  filter_upwards [ginibreBrownian_center_global_nonvanishing hn α z hz hcenter B P hB hind,
    (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB hind).2]
    with ω hnonzero hsolution
  intro T
  let r := fun t : ℝ≥0 => ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω)
  have hc : Continuous r := (contDiff_ginibreCenterSquared n).continuous.comp
    (by simpa only [Function.comp_def, Real.toNNReal_coe] using hsolution.1.comp
          NNReal.continuous_coe)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ≥0) T).Nonempty from ⟨0, le_rfl, bot_le⟩) hc.continuousOn
  refine ⟨r t,?_, hmin⟩
  exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnonzero t))

end
end GinibrePoincare
